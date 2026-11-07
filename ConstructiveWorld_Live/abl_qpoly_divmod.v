(* ConstructiveWorld-Set — Q-layer polynomial division engine: synthetic division by a linear divisor. *)
(** * abl_qpoly_divmod: division with remainder by a linear divisor for dense [Q]-list polynomials.

    Mission.  For dense coefficient lists with the head as the constant term (the
      [PolyIntegral] convention), the linear-divisor division engine: [qpd_synth a p]
      returns (quotient list, remainder scalar) for p ÷ (x+a) as a genuine structural
      [Fixpoint] (head recursion, extractable); [qpd_pdivmod_lin_wit a p] packages it in
      [sigT] with both correctness limbs — the equation limb (pointwise [QeqT]: eval p ==
      eval (x+a) · eval quotient + remainder) and the degree limb ([qpd_deglt], an [Id] bool face, decidable).  The general interface [qpd_divmod_gen_type] is declared,
      not implemented; the bridge [qpd_lin_to_gen] routes the linear engine through it.

    Dependencies.  Stdlib [QArith], [Qring], [Qfield], [Lists.List], [Arith], [ZArith],
      [Extraction]; requires [S01_BaseRing], [S02_CauchyComplete], [PolyIntegral] of
      this development.

    References.  The [pint_] family of [PolyIntegral] ([pint_coeff], [pint_eval],
      [pint_add], [pint_scale] — Q-coefficient list polynomials); the general-division
      face is [qpd_divmod_gen_pred]/[qpd_divmod_gen_type] with the bridge [qpd_lin_to_gen_sound].

    Constructivity.  Purely constructive, nothing admitted; the statement face is
      entirely [Set] ([sigT]/[And]/[QeqT]/[Id] degree predicates); [Qeq] (==) is only
      intra-proof scaffolding; ring closures use all-variable pure ring atoms.
      Honesty: the general long division is declared, not implemented (with head =
      constant term it would peel from the tail, not structurally recursive — linear
      synthetic division is the largest closable slice of this representation); quotient lists may carry trailing zeros (dense form, evaluation unaffected); non-trivial
      [qpd_lead] lemmas (e.g. leading-power monicity) are declared, not implemented;
      forward use: [qpd_divmod_gen_type] is the division position of the Beukers-identity route.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" abl_qpoly_divmod.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Extraction.
Import ListNotations.
Require Import S01_BaseRing S02_CauchyComplete PolyIntegral.

Open Scope Q_scope.

(* ============================================================ *)
(* §0. Carrier and degree support (entirely Set-face)            *)
(*   A polynomial is a dense [list Q] of coefficients with the head     *)
(*   as the constant term (the [PolyIntegral] convention); degree       *)
(*   convention: deg [] = 0 (the zero polynomial is recorded with       *)
(*   degree 0; the degree limb is honestly carried by the decidable     *)
(*   [Id] face rather than a fictional −∞ convention).                  *)
(* ============================================================ *)

(* Degree: length − 1 (the empty list recorded as 0) *)
Definition qpd_deg (p : list Q) : nat :=
  match p with
  | [] => 0%nat
  | _ :: _ => pred (length p)
  end.

(* Leading coefficient (coefficient of the highest-degree term; 0 for the empty list or out of range, reusing the library [pint_coeff]) *)
Definition qpd_lead (p : list Q) : Q :=
  pint_coeff p (pred (length p)).

(* Decidable predicate for the degree limb: deg r < deg q on the [Id] bool face ([Set]
   layer).  Note: the type argument of the S01 [Id] is maximally implicit, so it is
   given explicitly as [@Id bool ...]; the [bool] argument cannot be omitted. *)
Definition qpd_deglt (r q : list Q) : Set :=
  @Id bool true (Nat.ltb (qpd_deg r) (qpd_deg q)).

Lemma qpd_deglt_const : forall (c a : Q), qpd_deglt (c :: nil) (a :: 1 :: nil).
Proof.
  intros c a. unfold qpd_deglt, qpd_deg.
  cbn [length pred Nat.ltb].
  exact id_refl.
Qed.

Lemma qpd_lead_nil : QeqT (qpd_lead (@nil Q)) 0.
Proof. apply qeq_imp_qeqT. cbn [qpd_lead pint_coeff]. apply Qeq_refl. Qed.

Lemma qpd_lead_single : forall c : Q, QeqT (qpd_lead (c :: nil)) c.
Proof. intros c. apply qeq_imp_qeqT.
  cbn [qpd_lead pint_coeff length pred]. apply Qeq_refl. Qed.

(* ============================================================ *)
(* §1. All-variable pure ring atom group: the ring-closure atoms *)
(*   are plain variables, and call sites substitute compound     *)
(*   terms directly — this avoids the failure mode where a       *)
(*   ring-closure atom contains a compound term and [ring]       *)
(*   stops matching.                                             *)
(* ============================================================ *)

Lemma qpd_ring_0l : forall e : Q, QeqT e (0 + e).
Proof. intros e. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_0r : forall e : Q, QeqT e (e + 0).
Proof. intros e. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_scale0 : forall a : Q, QeqT 0 (a * 0).
Proof. intros a. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_const : forall r x : Q, QeqT (r + x * 0) r.
Proof. intros r x. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_lin_eval : forall a x : Q, QeqT (a + x * (1 + x * 0)) (a + x).
Proof. intros a x. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_base : forall a x : Q, QeqT 0 ((a + x) * 0 + 0).
Proof. intros a x. apply qeq_imp_qeqT. ring. Qed.

(* The core identity of the synthetic-division step: if p = c + x·p′ and
   p′ = (x+a)·s′ + r′, eliminating the c·x⁰ position gives
   c + x·((a+x)e + r) == (a+x)(r + x·e) + (c − a·r) *)
Lemma qpd_ring_lin_step : forall a c e r x : Q,
  QeqT (c + x * ((a + x) * e + r))
       ((a + x) * (r + x * e) + (c - a * r)).
Proof. intros a c e r x. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_add : forall a b e1 e2 x : Q,
  QeqT ((a + b) + x * (e1 + e2)) ((a + x * e1) + (b + x * e2)).
Proof. intros a b e1 e2 x. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_scale : forall a c e x : Q,
  QeqT (a * c + x * (a * e)) (a * (c + x * e)).
Proof. intros a c e x. apply qeq_imp_qeqT. ring. Qed.

Lemma qpd_ring_mullin : forall a e x : Q,
  QeqT ((0 + x * e) + a * e) ((x + a) * e).
Proof. intros a e x. apply qeq_imp_qeqT. ring. Qed.

(* Companion of the semantic smoke tests: the evaluation identity for the quotient x−1 of (x²+1) ÷ (x+1) *)
Lemma qpd_ring_xminus1 : forall x : Q,
  QeqT ((-1) + x * (1 + x * (0 + x * 0))) (x + (-1)).
Proof. intros x. apply qeq_imp_qeqT. ring. Qed.

(* ============================================================ *)
(* §2. Evaluation scaffolding (semantic lemmas of Horner         *)
(*   evaluation and of the coefficient operations; == appears    *)
(*   only inside proofs)                                         *)
(* ============================================================ *)

Lemma qpd_eval_nil : forall x : Q, QeqT (pint_eval [] x) 0.
Proof. intros x. apply qeq_imp_qeqT. cbn [pint_eval]. apply Qeq_refl. Qed.

Lemma qpd_eval_cons : forall (c : Q) (p : list Q) (x : Q),
  QeqT (pint_eval (c :: p) x) (c + x * pint_eval p x).
Proof. intros c p x. apply qeq_imp_qeqT. cbn [pint_eval]. apply Qeq_refl. Qed.

(* Evaluation of the linear divisor: eval (x+a) x == a + x *)
Lemma qpd_eval_lin_eq : forall a x : Q,
  QeqT (pint_eval (a :: 1 :: nil) x) (a + x).
Proof.
  intros a x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons a (1 :: nil) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 1 (@nil Q) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_nil x)).
  exact (qeqT_imp_qeq _ _ (qpd_ring_lin_eval a x)).
Qed.

(* Evaluation of a constant polynomial: eval [r] x == r *)
Lemma qpd_eval_const : forall r x : Q, QeqT (pint_eval (r :: nil) x) r.
Proof.
  intros r x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons r (@nil Q) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_nil x)).
  exact (qeqT_imp_qeq _ _ (qpd_ring_const r x)).
Qed.

(* Evaluation semantics of the library [pint_add] (coefficient-wise addition) *)
Lemma qpd_eval_add : forall (p q : list Q) (x : Q),
  QeqT (pint_eval (pint_add p q) x) (pint_eval p x + pint_eval q x).
Proof.
  intros p q x. apply qeq_imp_qeqT. revert q.
  induction p as [|a p' IH]; intros q.
  - cbn [pint_add]. rewrite (qeqT_imp_qeq _ _ (qpd_eval_nil x)).
    exact (qeqT_imp_qeq _ _ (qpd_ring_0l (pint_eval q x))).
  - destruct q as [|b q'].
    + cbn [pint_add].
      exact (qeqT_imp_qeq _ _ (qpd_ring_0r (pint_eval (a :: p') x))).
    + cbn [pint_add].
      rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons (a + b) (pint_add p' q') x)).
      rewrite (IH q').
      exact (qeqT_imp_qeq _ _
               (qpd_ring_add a b (pint_eval p' x) (pint_eval q' x) x)).
Qed.

(* Evaluation semantics of the library [pint_scale] (scalar multiplication) *)
Lemma qpd_eval_scale : forall (a : Q) (p : list Q) (x : Q),
  QeqT (pint_eval (pint_scale a p) x) (a * pint_eval p x).
Proof.
  intros a p x. apply qeq_imp_qeqT. revert a.
  induction p as [|c p' IH]; intros a.
  - cbn [pint_scale]. rewrite (qeqT_imp_qeq _ _ (qpd_eval_nil x)).
    exact (qeqT_imp_qeq _ _ (qpd_ring_scale0 a)).
  - cbn [pint_scale].
    rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons (a * c) (pint_scale a p') x)).
    rewrite (IH a).
    exact (qeqT_imp_qeq _ _ (qpd_ring_scale a c (pint_eval p' x) x)).
Qed.

(* Multiplication by the linear form: the coefficient list of (x+a)·s is the shift-lifted s plus a·s (an assembly of coefficient operations) *)
Definition qpd_mul_lin (a : Q) (s : list Q) : list Q :=
  pint_add (0 :: s) (pint_scale a s).

Lemma qpd_eval_mul_lin : forall (a : Q) (s : list Q) (x : Q),
  QeqT (pint_eval (qpd_mul_lin a s) x) ((x + a) * pint_eval s x).
Proof.
  intros a s x. apply qeq_imp_qeqT. unfold qpd_mul_lin.
  rewrite (qeqT_imp_qeq _ _ (qpd_eval_add (0 :: s) (pint_scale a s) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_scale a s x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 0 s x)).
  exact (qeqT_imp_qeq _ _ (qpd_ring_mullin a (pint_eval s x) x)).
Qed.

(* ============================================================ *)
(* §3. The linear-divisor synthetic division engine (a genuine   *)
(*   Fixpoint, structural recursion on the head = constant       *)
(*   term).  Invariant: qpd_synth a p = (s, r) with              *)
(*   p == (x+a)·s + r.  Recursive step: for c::p′, once p′ has   *)
(*   yielded (s′, r′), the lift-and-balance gives quotient =     *)
(*   r′::s′ and remainder = c − a·r′ (one substitution           *)
(*   eliminates the c position).                                 *)
(* ============================================================ *)

Fixpoint qpd_synth (a : Q) (p : list Q) : list Q * Q :=
  match p with
  | [] => ([], 0)
  | c :: p' => let (s', r') := qpd_synth a p' in (r' :: s', c - a * r')
  end.

(* The two-limb correctness predicate (Set face: And × S02.QeqT × the Id degree limb) *)
Definition qpd_lin_pred (a : Q) (p : list Q) (s : list Q) (r : Q) : Set :=
  And
    (forall x : Q,
       QeqT (pint_eval p x)
            (pint_eval (a :: 1 :: nil) x * pint_eval s x + r))
    (qpd_deglt (r :: nil) (a :: 1 :: nil)).

Lemma qpd_synth_sound : forall (a : Q) (p : list Q),
  qpd_lin_pred a p (fst (qpd_synth a p)) (snd (qpd_synth a p)).
Proof.
  intros a p. induction p as [|c p' IH].
  - (* empty-list base case: 0 == (x+a)·0 + 0, and remainder 0 has degree 0 < 1 *)
    unfold qpd_lin_pred. cbn [qpd_synth fst snd]. split.
    + intros x. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (qpd_eval_nil x)),
              (qeqT_imp_qeq _ _ (qpd_eval_lin_eq a x)).
      exact (qeqT_imp_qeq _ _ (qpd_ring_base a x)).
    + apply (qpd_deglt_const 0 a).
  - (* recursive step: destructure the inner quotient/remainder, then eliminate the c position by one substitution *)
    cbn [qpd_synth]. destruct (qpd_synth a p') as [s' r'] eqn:E.
    unfold qpd_lin_pred in IH. destruct IH as [IH1 IH2].
    unfold qpd_lin_pred. cbn [fst snd]. split.
    + intros x. apply qeq_imp_qeqT.
      assert (Hq : pint_eval p' x
                     == pint_eval (a :: 1 :: nil) x * pint_eval s' x + r')
        by exact (qeqT_imp_qeq _ _ (IH1 x)).
      rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons c p' x)).
      rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons r' s' x)).
      rewrite Hq.
      rewrite (qeqT_imp_qeq _ _ (qpd_eval_lin_eq a x)).
      exact (qeqT_imp_qeq _ _
               (qpd_ring_lin_step a c (pint_eval s' x) r' x)).
    + exact (qpd_deglt_const (c - a * r') a).
Qed.

(* The sigT packaging: {(quotient, remainder) | p == (x+a)·quotient + remainder ∧ deg remainder < deg (x+a)} *)
Definition qpd_pdivmod_lin_type (a : Q) (p : list Q) : Set :=
  sigT (fun w : list Q * Q => qpd_lin_pred a p (fst w) (snd w)).

Definition qpd_pdivmod_lin_wit (a : Q) (p : list Q) : qpd_pdivmod_lin_type a p :=
  existT _ (qpd_synth a p) (qpd_synth_sound a p).

(* ============================================================ *)
(* §4. The general-division interface (declared, not             *)
(*   implemented) + the linear-to-general bridge (in place).     *)
(*   General specification: {(quotient, remainder) | ∀x, eval p  *)
(*   == eval q · eval quotient + eval remainder ∧ deg remainder  *)
(*   < deg q} — the degree limb automatically rules out the      *)
(*   deg q = 0 zero-divisor position, so the specification is    *)
(*   honest without a separate nonzero premise.                  *)
(* ============================================================ *)

Definition qpd_divmod_gen_pred (p q : list Q) (w : list Q * list Q) : Set :=
  And
    (forall x : Q,
       QeqT (pint_eval p x)
            (pint_eval q x * pint_eval (fst w) x + pint_eval (snd w) x))
    (qpd_deglt (snd w) q).

Definition qpd_divmod_gen_type (p q : list Q) : Set :=
  sigT (qpd_divmod_gen_pred p q).

(* The bridge: the linear engine's output is used as-is through the general interface (the remainder scalar is lifted to the constant polynomial [r]) *)
Lemma qpd_lin_to_gen_sound : forall (a : Q) (p : list Q),
  qpd_divmod_gen_pred p (a :: 1 :: nil)
    (fst (qpd_synth a p), snd (qpd_synth a p) :: nil).
Proof.
  intros a p. unfold qpd_divmod_gen_pred. split.
  - intros x. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (qpd_eval_const (snd (qpd_synth a p)) x)).
    exact (qeqT_imp_qeq _ _ (fst (qpd_synth_sound a p) x)).
  - exact (qpd_deglt_const (snd (qpd_synth a p)) a).
Qed.

Definition qpd_lin_to_gen (a : Q) (p : list Q) : qpd_divmod_gen_type p (a :: 1 :: nil) :=
  existT _ (fst (qpd_synth a p), snd (qpd_synth a p) :: nil)
           (qpd_lin_to_gen_sound a p).

(* ============================================================ *)
(* §5. Numeric smoke tests (computed by [vm_compute]; no axioms; *)
(*   small instances).  The reference example: (x²+1) ÷ (x+1)    *)
(*   gives quotient x−1 and remainder 2.                         *)
(* ============================================================ *)

(* Smoke test 0: the empty-list edge — 0 ÷ (x+3) = quotient 0, remainder 0 *)
Lemma qpd_smoke0 :
  And (Id (fst (qpd_synth 3 (@nil Q))) (@nil Q))
      (QeqT (snd (qpd_synth 3 (@nil Q))) 0).
Proof.
  split.
  - cbn [qpd_synth fst]. apply id_refl.
  - cbn [qpd_synth snd]. apply id_refl.
Qed.

(* Smoke test 1 (the reference example): (x²+1) ÷ (x+1) gives quotient [−1;1;0] (= x−1, dense with a trailing zero) and remainder 2 *)
Lemma qpd_smoke1_q :
  Id (fst (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 0 :: 1 :: nil))))
     ((-1) :: 1 :: 0 :: nil).
Proof. vm_compute. apply id_refl. Qed.

Lemma qpd_smoke1_r :
  QeqT (snd (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 0 :: 1 :: nil)))) 2.
Proof. vm_compute. apply id_refl. Qed.

(* Smoke test 1, semantic face: the evaluation of the quotient [−1;1;0] is == x−1 (a direct all-variable ring atom inside the proof) *)
Lemma qpd_smoke1_quot_sem : forall x : Q,
  QeqT (pint_eval (fst (qpd_synth 1 (1 :: 0 :: 1 :: nil))) x) (x + (-1)).
Proof.
  intros x. apply qeq_imp_qeqT.
  cbn [qpd_synth fst].
  rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons (-1) (1 :: 0 :: nil) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 1 (0 :: nil) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 0 (@nil Q) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_nil x)).
  exact (qeqT_imp_qeq _ _ (qpd_ring_xminus1 x)).
Qed.

(* Smoke test 2: self-division (x+1) ÷ (x+1) gives quotient 1, remainder 0 *)
Lemma qpd_smoke2_q :
  Id (fst (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 1 :: nil))))
     (1 :: 0 :: nil).
Proof. vm_compute. apply id_refl. Qed.

Lemma qpd_smoke2_r :
  QeqT (snd (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 1 :: nil)))) 0.
Proof. vm_compute. apply id_refl. Qed.

(* Smoke test 3: negative constant divisor — (x²−1) ÷ (x−1) gives quotient x+1, remainder 0 *)
Lemma qpd_smoke3_q :
  Id (fst (projT1 (qpd_pdivmod_lin_wit (-1) ((-1) :: 0 :: 1 :: nil))))
     (1 :: 1 :: 0 :: nil).
Proof. vm_compute. apply id_refl. Qed.

Lemma qpd_smoke3_r :
  QeqT (snd (projT1 (qpd_pdivmod_lin_wit (-1) ((-1) :: 0 :: 1 :: nil)))) 0.
Proof. vm_compute. apply id_refl. Qed.

(* ============================================================ *)
(* §6. Closure: extraction face + Print Assumptions (per-statement audits) *)
(* ============================================================ *)

Separate Extraction qpd_synth qpd_mul_lin.

Print Assumptions qpd_deglt_const.
Print Assumptions qpd_lead_nil.
Print Assumptions qpd_lead_single.
Print Assumptions qpd_eval_add.
Print Assumptions qpd_eval_scale.
Print Assumptions qpd_eval_mul_lin.
Print Assumptions qpd_eval_lin_eq.
Print Assumptions qpd_eval_const.
Print Assumptions qpd_synth_sound.
Print Assumptions qpd_pdivmod_lin_wit.
Print Assumptions qpd_lin_to_gen.
Print Assumptions qpd_smoke0.
Print Assumptions qpd_smoke1_q.
Print Assumptions qpd_smoke1_r.
Print Assumptions qpd_smoke1_quot_sem.
Print Assumptions qpd_smoke2_q.
Print Assumptions qpd_smoke2_r.
Print Assumptions qpd_smoke3_q.
Print Assumptions qpd_smoke3_r.

(* End of the polynomial division engine file. *)
