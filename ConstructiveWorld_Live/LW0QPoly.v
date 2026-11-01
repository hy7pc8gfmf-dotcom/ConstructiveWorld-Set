(* ========================================================================= *)
(* LW0QPoly - polynomials with rational coefficients and their formal       *)
(* differential calculus in one indeterminate t.                            *)
(* 模块名：LW0QPoly.  数学使命：the ring Q[t] presented by coefficient      *)
(* lists, with addition, scalar multiplication, multiplication, evaluation  *)
(* at a point, formal differentiation, the substitution t |-> c*t, and      *)
(* iterated derivatives.  Main statements: the product rule (f*g)' =        *)
(* f'*g + f*g', the chain rule d/dt P(c*t) = c * P'(c*t), and the           *)
(* recursion identities for iterated derivatives.                          *)
(* 次序约定：coefficients are listed from the constant term upward (the     *)
(* head is the coefficient of t^0); the empty list is the zero polynomial;  *)
(* the degree of the zero polynomial is 0 by convention; lists carrying     *)
(* trailing zeros (and the derivative of a constant, the one-element zero   *)
(* list) denote the same polynomial as their trimmed form, and every        *)
(* arithmetic statement is phrased pointwise, valid at all t.  Equalities   *)
(* of lists are Leibniz; equalities of rationals are the field equality ==  *)
(* (Qeq), since the numeral pairs of Q are not canonical.                   *)
(* 依赖清单：Stdlib.QArith only.                                            *)
(* 对标行：no external benchmark imported; the coefficient-list             *)
(* arrangement follows the usual treatment (cf. stdlib Poly, not Required). *)
(* 构造性注记：every operation is a structurally recursive Fixpoint with    *)
(* computing content (Defined), list constructors written nil/cons in word  *)
(* form; statements are quantified equations between data with no logical   *)
(* premises, no admitted goals, no classical principles; the exported       *)
(* constants extract to plain Q arithmetic.                                 *)
(* 编译配方：@echo off; set COQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq;    *)
(* set ROCQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq;                        *)
(* "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe" -q -Q . "" LW0QPoly.v        *)
(* (ASCII .cmd batch with CRLF endings, current directory = sandbox).       *)
(* ========================================================================= *)

From Stdlib Require Import QArith.

(* A polynomial is its coefficient list, constant term first. *)
Definition QPoly := list Q.

(* Coefficientwise addition, padding the shorter list with zeros. *)
Fixpoint qpoly_add (p q : QPoly) : QPoly :=
  match p with
  | nil => q
  | cons a p' =>
      match q with
      | nil => p
      | cons b q' => cons (a + b) (qpoly_add p' q')
      end
  end.

(* Scalar multiplication by a rational number. *)
Fixpoint qpoly_scalar (a : Q) (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons b p' => cons (a * b) (qpoly_scalar a p')
  end.

(* Multiplication, using (a + t * P) * Q = a * Q + t * (P * Q). *)
Fixpoint qpoly_mul (p q : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' =>
      qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p' q))
  end.

(* Evaluation at x, by Horner recursion on the coefficient list. *)
Fixpoint qpoly_eval (p : QPoly) (x : Q) : Q :=
  match p with
  | nil => 0
  | cons a p' => a + x * qpoly_eval p' x
  end.

(* Nontriviality test: does any coefficient differ from zero? *)
Fixpoint qpoly_is_nonzero (p : QPoly) : bool :=
  match p with
  | nil => false
  | cons a p' => negb (Qeq_bool a 0) || qpoly_is_nonzero p'
  end.

(* Degree: the index of the highest nonzero coefficient.  The zero          *)
(* polynomial has degree 0 by convention.                                   *)
Fixpoint qpoly_degree (p : QPoly) : nat :=
  match p with
  | nil => 0
  | cons a p' => if qpoly_is_nonzero p' then S (qpoly_degree p') else 0
  end.

(* Formal derivative: the coefficient of t^i becomes i * a_i, so            *)
(* d/dt (a + t * P) = P + t * P'  (the derivative of a constant is the      *)
(* one-element zero list).                                                  *)
Fixpoint qpoly_deriv (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' => qpoly_add p' (cons 0 (qpoly_deriv p'))
  end.

(* Helper for the substitution t |-> c * t: cc is the running power c^i,    *)
(* so the coefficient of t^i becomes a_i * cc. *)
Fixpoint qpoly_comp_aux (c cc : Q) (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' => cons (a * cc) (qpoly_comp_aux c (cc * c) p')
  end.

(* The substitution t |-> c * t, coefficientwise: a_i becomes a_i * c^i. *)
Definition qpoly_comp_scale (c : Q) (p : QPoly) : QPoly :=
  qpoly_comp_aux c 1 p.

(* The n-th formal derivative. *)
Fixpoint qpoly_deriv_iter (n : nat) (p : QPoly) : QPoly :=
  match n with
  | 0 % nat => p
  | S m => qpoly_deriv (qpoly_deriv_iter m p)
  end.

(* ------------------------------------------------------------------ *)
(* Evaluation identities.                                             *)
(* ------------------------------------------------------------------ *)

Lemma qpoly_add_r_nil : forall p : QPoly, qpoly_add p nil = p.
Proof.
  induction p as [|a p IH]; simpl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma qpoly_eval_add : forall p q x,
  qpoly_eval (qpoly_add p q) x == qpoly_eval p x + qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x; simpl.
  - ring.
  - destruct q as [|b q]; simpl.
    + ring.
    + rewrite (IH q x); ring.
Qed.

Lemma qpoly_eval_scalar : forall a p x,
  qpoly_eval (qpoly_scalar a p) x == a * qpoly_eval p x.
Proof.
  intros a p x; induction p as [|b p IH]; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(* The derivative of a nonempty list, evaluated pointwise: this is the    *)
(* identity P' = P + t * P' written for P = a + t * rest.                 *)
Lemma qpoly_eval_deriv_cons : forall a p x,
  qpoly_eval (qpoly_deriv (cons a p)) x ==
  qpoly_eval p x + x * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros a p x.
  change (qpoly_deriv (cons a p))
    with (qpoly_add p (cons 0 (qpoly_deriv p))).
  rewrite (qpoly_eval_add p (cons 0 (qpoly_deriv p)) x).
  change (qpoly_eval (cons 0 (qpoly_deriv p)) x)
    with (0 + x * qpoly_eval (qpoly_deriv p) x).
  ring.
Qed.

(* Differentiation is additive, pointwise. *)
Lemma qpoly_eval_deriv_add : forall p q x,
  qpoly_eval (qpoly_deriv (qpoly_add p q)) x ==
  qpoly_eval (qpoly_add (qpoly_deriv p) (qpoly_deriv q)) x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl; ring.
  - destruct q as [|b q].
    + change (qpoly_deriv nil) with (@nil Q).
      rewrite (qpoly_add_r_nil (qpoly_deriv (cons a p))).
      rewrite (qpoly_add_r_nil (cons a p)).
      ring.
    + replace (qpoly_add (cons a p) (cons b q))
        with (cons (a + b) (qpoly_add p q)) by reflexivity.
      change (qpoly_deriv (cons (a + b) (qpoly_add p q)))
        with (qpoly_add (qpoly_add p q)
                (cons 0 (qpoly_deriv (qpoly_add p q)))).
      rewrite (qpoly_eval_add (qpoly_add p q)
                 (cons 0 (qpoly_deriv (qpoly_add p q))) x).
      change (qpoly_eval (cons 0 (qpoly_deriv (qpoly_add p q))) x)
        with (0 + x * qpoly_eval (qpoly_deriv (qpoly_add p q)) x).
      rewrite (IH q x).
      rewrite (qpoly_eval_add p q x).
      rewrite (qpoly_eval_add (qpoly_deriv p) (qpoly_deriv q) x).
      rewrite (qpoly_eval_add (qpoly_deriv (cons a p))
                 (qpoly_deriv (cons b q)) x).
      rewrite (qpoly_eval_deriv_cons a p x).
      rewrite (qpoly_eval_deriv_cons b q x).
      ring.
Qed.

(* Differentiation commutes with scalar multiplication, pointwise. *)
Lemma qpoly_eval_deriv_scalar : forall a p x,
  qpoly_eval (qpoly_deriv (qpoly_scalar a p)) x ==
  qpoly_eval (qpoly_scalar a (qpoly_deriv p)) x.
Proof.
  intros a p x; induction p as [|b p IH].
  - simpl; ring.
  - change (qpoly_scalar a (cons b p)) with (cons (a * b) (qpoly_scalar a p)).
    change (qpoly_deriv (cons (a * b) (qpoly_scalar a p)))
      with (qpoly_add (qpoly_scalar a p)
              (cons 0 (qpoly_deriv (qpoly_scalar a p)))).
    rewrite (qpoly_eval_add (qpoly_scalar a p)
               (cons 0 (qpoly_deriv (qpoly_scalar a p))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (qpoly_scalar a p))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (qpoly_scalar a p)) x).
    rewrite IH.
    rewrite (qpoly_eval_scalar a p x).
    rewrite (qpoly_eval_scalar a (qpoly_deriv p) x).
    rewrite (qpoly_eval_scalar a (qpoly_deriv (cons b p)) x).
    rewrite (qpoly_eval_deriv_cons b p x).
    change (qpoly_eval (cons b p) x) with (b + x * qpoly_eval p x).
    ring.
Qed.

(* Evaluation is multiplicative. *)
Lemma qpoly_eval_mul : forall p q x,
  qpoly_eval (qpoly_mul p q) x == qpoly_eval p x * qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl; ring.
  - replace (qpoly_mul (cons a p) q)
      with (qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)))
        by reflexivity.
    rewrite (qpoly_eval_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)) x).
    rewrite (qpoly_eval_scalar a q x).
    change (qpoly_eval (cons 0 (qpoly_mul p q)) x)
      with (0 + x * qpoly_eval (qpoly_mul p q) x).
    rewrite (IH q x).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    ring.
Qed.

(* The product rule, stated pointwise:                                     *)
(* (p * q)' evaluated at x equals (p' * q + p * q') evaluated at x.        *)
Lemma qpoly_deriv_mul : forall p q x,
  qpoly_eval (qpoly_deriv (qpoly_mul p q)) x ==
  qpoly_eval
    (qpoly_add (qpoly_mul (qpoly_deriv p) q) (qpoly_mul p (qpoly_deriv q))) x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl; ring.
  - replace (qpoly_mul (cons a p) q)
      with (qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)))
        by reflexivity.
    rewrite (qpoly_eval_deriv_add (qpoly_scalar a q)
               (cons 0 (qpoly_mul p q)) x).
    rewrite (qpoly_eval_add (qpoly_deriv (qpoly_scalar a q))
               (qpoly_deriv (cons 0 (qpoly_mul p q))) x).
    rewrite (qpoly_eval_deriv_scalar a q x).
    rewrite (qpoly_eval_scalar a (qpoly_deriv q) x).
    rewrite (qpoly_eval_deriv_cons 0 (qpoly_mul p q) x).
    rewrite (IH q x).
    rewrite (qpoly_eval_mul p q x).
    rewrite (qpoly_eval_add (qpoly_mul (qpoly_deriv p) q)
               (qpoly_mul p (qpoly_deriv q)) x).
    rewrite (qpoly_eval_mul (qpoly_deriv p) q x).
    rewrite (qpoly_eval_mul p (qpoly_deriv q) x).
    rewrite (qpoly_eval_add (qpoly_mul (qpoly_deriv (cons a p)) q)
               (qpoly_mul (cons a p) (qpoly_deriv q)) x).
    rewrite (qpoly_eval_mul (qpoly_deriv (cons a p)) q x).
    rewrite (qpoly_eval_mul (cons a p) (qpoly_deriv q) x).
    rewrite (qpoly_eval_deriv_cons a p x).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The substitution t |-> c * t and its chain rule.                   *)
(* ------------------------------------------------------------------ *)

Lemma qpoly_comp_aux_eval : forall p c cc x,
  qpoly_eval (qpoly_comp_aux c cc p) x == cc * qpoly_eval p (c * x).
Proof.
  intros p c; induction p as [|a p IH]; intros cc x.
  - simpl; ring.
  - change (qpoly_comp_aux c cc (cons a p))
      with (cons (a * cc) (qpoly_comp_aux c (cc * c) p)).
    change (qpoly_eval (cons (a * cc) (qpoly_comp_aux c (cc * c) p)) x)
      with (a * cc + x * qpoly_eval (qpoly_comp_aux c (cc * c) p) x).
    change (qpoly_eval (cons a p) (c * x))
      with (a + (c * x) * qpoly_eval p (c * x)).
    rewrite (IH (cc * c) x).
    ring.
Qed.

Lemma qpoly_comp_aux_deriv_eval : forall p c cc x,
  qpoly_eval (qpoly_deriv (qpoly_comp_aux c cc p)) x ==
  cc * c * qpoly_eval (qpoly_deriv p) (c * x).
Proof.
  intros p c; induction p as [|a p IH]; intros cc x.
  - simpl; ring.
  - change (qpoly_comp_aux c cc (cons a p))
      with (cons (a * cc) (qpoly_comp_aux c (cc * c) p)).
    change (qpoly_deriv (cons (a * cc) (qpoly_comp_aux c (cc * c) p)))
      with (qpoly_add (qpoly_comp_aux c (cc * c) p)
              (cons 0 (qpoly_deriv (qpoly_comp_aux c (cc * c) p)))).
    rewrite (qpoly_eval_add (qpoly_comp_aux c (cc * c) p)
               (cons 0 (qpoly_deriv (qpoly_comp_aux c (cc * c) p))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (qpoly_comp_aux c (cc * c) p))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (qpoly_comp_aux c (cc * c) p)) x).
    rewrite (qpoly_comp_aux_eval p c (cc * c) x).
    rewrite (IH (cc * c) x).
    rewrite (qpoly_eval_deriv_cons a p (c * x)).
    change (qpoly_eval (cons a p) (c * x))
      with (a + (c * x) * qpoly_eval p (c * x)).
    ring.
Qed.

(* The chain rule for the substitution t |-> c * t, stated pointwise:      *)
(* d/dt P(c*t) evaluated at x equals c * P' evaluated at c*x.              *)
Lemma qpoly_deriv_comp_scale : forall p c x,
  qpoly_eval (qpoly_deriv (qpoly_comp_scale c p)) x ==
  c * qpoly_eval (qpoly_deriv p) (c * x).
Proof.
  intros p c x; destruct p as [|a [|b p]].
  - unfold qpoly_comp_scale; simpl; ring.
  - unfold qpoly_comp_scale; simpl; ring.
  - unfold qpoly_comp_scale.
    change (qpoly_comp_aux c 1 (cons a (cons b p)))
      with (cons (a * 1)
                (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))).
    change (qpoly_deriv
              (cons (a * 1)
                 (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))))
      with (qpoly_add
              (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))
              (cons 0 (qpoly_deriv
                         (cons (b * (1 * c))
                            (qpoly_comp_aux c (1 * c * c) p))))).
    rewrite (qpoly_eval_add
               (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))
               (cons 0 (qpoly_deriv
                          (cons (b * (1 * c))
                             (qpoly_comp_aux c (1 * c * c) p)))) x).
    change (qpoly_eval
              (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p)) x)
      with (b * (1 * c)
              + x * qpoly_eval (qpoly_comp_aux c (1 * c * c) p) x).
    change (qpoly_eval
              (cons 0
                 (qpoly_deriv
                    (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p)))) x)
      with (0 + x * qpoly_eval
                       (qpoly_deriv
                          (cons (b * (1 * c))
                             (qpoly_comp_aux c (1 * c * c) p))) x).
    rewrite (qpoly_eval_deriv_cons (b * (1 * c))
               (qpoly_comp_aux c (1 * c * c) p) x).
    rewrite (qpoly_comp_aux_eval p c (1 * c * c) x).
    rewrite (qpoly_comp_aux_deriv_eval p c (1 * c * c) x).
    rewrite (qpoly_eval_deriv_cons a (cons b p) (c * x)).
    rewrite (qpoly_eval_deriv_cons b p (c * x)).
    change (qpoly_eval (cons b p) (c * x))
      with (b + (c * x) * qpoly_eval p (c * x)).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Iterated derivatives: recursion identities.                        *)
(* ------------------------------------------------------------------ *)

(* One step of the recursion defining iterated derivatives. *)
Lemma qpoly_deriv_iter_succ : forall n p,
  qpoly_deriv_iter (S n) p = qpoly_deriv (qpoly_deriv_iter n p).
Proof.
  reflexivity.
Qed.

(* Iterated derivatives may be taken in any order:                         *)
(* the (n+1)-st derivative equals the n-th derivative of the derivative.   *)
Lemma qpoly_deriv_iter_commute : forall n p,
  qpoly_deriv_iter (S n) p = qpoly_deriv_iter n (qpoly_deriv p).
Proof.
  induction n as [|n IH]; intros p.
  - reflexivity.
  - change (qpoly_deriv_iter (S (S n)) p)
      with (qpoly_deriv (qpoly_deriv_iter (S n) p)).
    rewrite (IH p).
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Extraction probe and assumption checks.                            *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Extraction.
Separate Extraction qpoly_mul qpoly_deriv qpoly_eval.

Print Assumptions qpoly_deriv_mul.
Print Assumptions qpoly_deriv_comp_scale.
Print Assumptions qpoly_deriv_iter_succ.
Print Assumptions qpoly_deriv_iter_commute.
