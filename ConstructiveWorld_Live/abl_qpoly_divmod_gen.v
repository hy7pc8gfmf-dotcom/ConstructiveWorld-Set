(* ===================================================================== *)
(*  Five-field pointer | Mission.  Q-polynomial division-with-remainder    *)
(*    engine, GENERAL form (CK). Closes the interface qpd_divmod_gen_type *)
(*    registered by CC: constructive long division for divisors of any    *)
(*    degree (genuinely nonzero leading coefficient + degree >= 1).  Constructivity.  all proofs close by Qed/Defined; zero axioms.  Build.  rocq c -native-compiler no -Q <tree> "".       *)
(*  Dependencies.  Stdlib QArith/Qring/Qfield/Lists/Arith/ZArith/Lia/      *)
(*    Extraction; S01_BaseRing S02_CauchyComplete PolyIntegral            *)
(*    (world-tree files); predecessor abl_qpoly_divmod (in-pool CC first  *)
(*    piece: qpd_divmod_gen_pred/type containers, qpd_eval_add/cons/nil   *)
(*    evaluation limbs, qpd_deglt degree limb, qpd_deg/qpd_lead).         *)
(*  Constructivity: purely constructive, zero admitted pieces; statement  *)
(*    surface entirely Set-level (sigT + S01.And + S02.QeqT + S01.Id).    *)
(*    Prop-elimination born-clean: bare = -> Id (id_cong bridge),         *)
(*    == -> QeqT (two-way gates qeq_imp_qeqT/qeqT_imp_qeq), nat <= ->     *)
(*    NatLe (NatLe_drop/NatLe_lift bridges); Qeq/== appear only as        *)
(*    proof-internal reasoning scaffolding; ring closures all go through  *)
(*    the "all-variable pure ring leaf" pattern (pitfall cards AL/AX,     *)
(*    same as predecessor §1). No magic values, no Prop cast shims, no    *)
(*    Prop-ification.                                                     *)
(*  Compile recipe: source Live/toolchain/env.sh && unset COQLIB ROCQLIB  *)
(*    && ulimit -s 65532 && rocq c -native-compiler no -Q <world> ""      *)
(*    abl_qpoly_divmod_gen.v (compile predecessor abl_qpoly_divmod.v      *)
(*    first; lane gate <= 1 = single-process serial, cpu_guard wrapped).  *)
(*  Benchmarks: CC abl_qpoly_divmod (linear synthetic division first      *)
(*    piece); PolyIntegral pint_* (Q coefficient list precedent); BT §    *)
(*    honest boundary route 3; AE §3.3 route 3.                           *)
(* ===================================================================== *)
(*  abl_qpoly_divmod_gen.v -- Q-layer polynomial division engine,         *)
(*  general form (second stage).                                          *)
(*                                                                        *)
(*  Mission: close the CC-registered qpd_divmod_gen_type p q container    *)
(*    (using its shape verbatim: sigT wrap of (quotient, remainder)       *)
(*    plus the two correctness limbs                                      *)
(*      (1) equation limb: forall x, QeqT (eval p x)                      *)
(*            (eval q x * eval quotient x + eval remainder x)             *)
(*      (2) degree limb:   qpd_deglt remainder q (decidable Id bool face) *)
(*    delivering qpg_divmod_gen : forall p q, qpg_divisor_ok q ->         *)
(*                            qpd_divmod_gen_type p q).                   *)
(*                                                                        *)
(*  Route (constructive classic long division): recurse by leading-term   *)
(*    elimination -- quotient coefficient c = lead p / lead q (Q-level    *)
(*    Qdiv, in-world); p - c*x^k*q has its top term cancel to zero,       *)
(*    truncating the top yields p1 with deg p1 = deg p - 1 strictly       *)
(*    decreasing; fuel = length p, genuine structural Fixpoint (nat fuel  *)
(*    recursion, nontrivial algorithm body, extractable). Termination =   *)
(*    length measure; correctness = inductive-step ring equation (taken   *)
(*    directly from all-variable pure ring leaves).                       *)
(*                                                                        *)
(*  Diff vs CC interface (honest boundary): the divisor precondition is   *)
(*    strengthened to qpg_divisor_ok q =                                  *)
(*    (1) deg q >= 1 (Id bool face: ltb 0 (deg q) = true -- the degree    *)
(*        limb then rules out constant divisors automatically),           *)
(*    (2) lead q ≠ 0 (Qcompare Set face: genuinely nonzero leading coeff).*)
(*    Reason: with head = constant term dense tables, listdeg is not the  *)
(*    true degree (tail-zero example q=[1;2;0] has listdeg=2 but true     *)
(*    degree=1 and lead=0); leading-term elimination requires a genuinely *)
(*    nonzero leading coefficient to divide. The task brief's single      *)
(*    precondition "deg q >= 1" is insufficient for this engine; this is  *)
(*    an honest representation-level widening, with the container face    *)
(*    and the CC registration unchanged.                                  *)
(*                                                                        *)
(*  First-piece strategy (45-minute slice): this piece closes the         *)
(*    "recursion engine + existence limb"; the uniqueness limb            *)
(*    (quotient/remainder uniqueness) is §5-registered only, not built.   *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Lia Extraction.
Import ListNotations.
Require Import S01_BaseRing S02_CauchyComplete PolyIntegral abl_qpoly_divmod.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 Divisor well-formedness face and predecessor-use pieces    *)
(*     (all Set face; Qeq/Prop only proof-internal)              *)
(* ============================================================ *)

(* Degree >= 1 in the decidable Id bool face (same shape as the
   predecessor's qpd_deglt) *)
Definition qpg_degge1 (q : list Q) : Set :=
  @Id bool true (Nat.ltb 0 (qpd_deg q)).

(* Genuinely nonzero leading coefficient, Qcompare Set face (the Eq
   branch being uninhabited is exactly "nonzero") *)
Definition qpg_leadne0 (q : list Q) : Set :=
  match Qcompare (qpd_lead q) 0 with
  | Datatypes.Eq => Empty_set
  | Datatypes.Lt => unit
  | Datatypes.Gt => unit
  end.

(* Divisor well-formedness = degree>=1 AND nonzero lead (S01 Set-level And) *)
Definition qpg_divisor_ok (q : list Q) : Set :=
  And (qpg_degge1 q) (qpg_leadne0 q).

(* Id bool face use: from Id true b take the mirrored boolean identity *)
Lemma qpg_id_true_inv : forall b : bool, @Id bool true b -> @Id bool b true.
Proof. intros b H. destruct H. exact id_refl. Qed.

Lemma qpg_degge1_inv : forall q : list Q,
  qpg_degge1 q -> NatLe 1 (qpd_deg q).
Proof. intros q H. exact (id_sym H). Qed.

Lemma qpg_leadne0_inv : forall q : list Q,
  qpg_leadne0 q -> QeqT (qpd_lead q) 0 -> Empty_set.
Proof.
  intros q H Hz. unfold qpg_leadne0 in H. unfold QeqT in Hz.
  (* destruct substitutes the scrutinee inside H/Hz directly (Eq branch:
     H becomes Empty_set; Lt/Gt branches: Hz becomes Id false true) *)
  destruct (Qcompare (qpd_lead q) 0) eqn:E.
  - exact H.
  - inversion Hz.
  - inversion Hz.
Qed.

(* §1 Two preliminaries (used by qpg_div_cancel; all-variable pure ring
   leaves) *)
Lemma qpg_ring_assoc : forall w i v : Q, QeqT (w * i * v) (w * (i * v)).
Proof. intros w i v. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_mul1 : forall a : Q, QeqT (a * 1) a.
Proof. intros a. apply qeq_imp_qeqT. ring. Qed.

(* Q-level division cancellation (Qdiv in-world): with b nonzero,
   a / b * b == a *)
Lemma qpg_div_cancel : forall a b : Q, (QeqT b 0 -> Empty_set) -> QeqT (a / b * b) a.
Proof.
  intros a b Hb. apply qeq_imp_qeqT. unfold Qdiv.
  assert (Hb' : ~ b == 0).
  { intros Hz. destruct (Hb (qeq_imp_qeqT b 0 Hz)). }
  assert (H1 : b * (/ b) == 1) by exact (Qmult_inv_r b Hb').
  assert (H2 : (/ b) * b == 1)
    by exact (Qeq_trans _ _ _ (Qmult_comm (/ b) b) H1).
  assert (H3 : a * (/ b) * b == a * ((/ b) * b))
    by exact (qeqT_imp_qeq _ _ (qpg_ring_assoc a (/ b) b)).
  rewrite H2 in H3.
  exact (Qeq_trans _ _ _ H3 (Qmult_1_r a)).
Qed.

(* Cancellation-slot zeroing: a - a / b * b == 0 *)
Lemma qpg_lead_cancel : forall a b : Q, (QeqT b 0 -> Empty_set) -> QeqT (a - a / b * b) 0.
Proof.
  intros a b Hb. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (qpg_div_cancel a b Hb)). ring.
Qed.

(* ============================================================ *)
(* §1 All-variable pure ring leaf group (pitfall cards AL/AX      *)
(*    pattern: ring-closure atoms are all variables; call sites   *)
(*    substitute compound terms directly; assoc/mul1 two leaves   *)
(*    are pre-declared in §0)                                     *)
(* ============================================================ *)

Lemma qpg_ring_leaf : forall e : Q, QeqT 0 (e * 0 + 0).
Proof. intros e. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_lt : forall h t e : Q, QeqT (h + t) (e * 0 + (h + t)).
Proof. intros h t e. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_remlast0 : forall e f : Q, QeqT e (e + f * 0).
Proof. intros e f. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_align0 : forall e c : Q, QeqT e (e - c * 0).
Proof. intros e c. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_align : forall h c q x e1 e2 : Q,
  QeqT ((h - c * q) + x * (e1 - c * e2)) ((h + x * e1) - c * (q + x * e2)).
Proof. intros h c q x e1 e2. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_shift0 : forall e c d : Q, QeqT (e - c * d) (e - 1 * (c * d)).
Proof. intros e c d. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_shift : forall h x e1 p c d : Q,
  QeqT (h + x * (e1 - p * (c * d))) ((h + x * e1) - (x * p) * (c * d)).
Proof. intros h x e1 p c d. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_mono0 : forall c x : Q, QeqT (c + x * 0) (1 * c).
Proof. intros c x. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_monoS : forall x p c : Q, QeqT (0 + x * (p * c)) (x * p * c).
Proof. intros x p c. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_main : forall w c d s r : Q,
  QeqT (w * (c * d) + (d * s + r)) (d * (w * c + s) + r).
Proof. intros w c d s r. apply qeq_imp_qeqT. ring. Qed.

Lemma qpg_ring_shift_edge : forall h x c : Q,
  QeqT (h + x * 0) ((h + x * 0) - x * 1 * (c * 0)).
Proof. intros h x c. apply qeq_imp_qeqT. ring. Qed.

(* Qeq transfer: b == a - x implies a == x + b (born-clean: QeqT in,
   QeqT out, two-way gates inside) *)
Lemma qpg_qeq_move : forall a b x : Q, QeqT b (a - x) -> QeqT a (x + b).
Proof.
  intros a b x H. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ H). ring.
Qed.

(* Smoke-test companion: evaluation identity for (x^2+2x+1) / (x+1) *)
Lemma qpg_ring_smokeA : forall x : Q,
  QeqT (1 + x * (2 + x * (1 + x * 0)))
       ((1 + x * (1 + x * 0)) * (1 + x * (1 + x * 0)) + (0 + x * 0)).
Proof. intros x. apply qeq_imp_qeqT. ring. Qed.

(* ============================================================ *)
(* §2 Basic table operations: power, zero segment, monomial,      *)
(*    tail truncation (all genuine Fixpoints, extractable)        *)
(* ============================================================ *)

Fixpoint qpg_pow (x : Q) (k : nat) : Q :=
  match k with
  | 0%nat => 1
  | Datatypes.S k' => x * qpg_pow x k'
  end.

Fixpoint qpg_zeros (k : nat) : list Q :=
  match k with
  | 0%nat => []
  | Datatypes.S k' => 0 :: qpg_zeros k'
  end.

(* Coefficient table of the monomial c*x^k: k zeros followed by one c *)
Definition qpg_mono (c : Q) (k : nat) : list Q := qpg_zeros k ++ c :: nil.

(* Tail truncation (drop the highest-degree slot; in head=constant-term
   dense tables the highest-degree slot sits at the table tail) *)
Fixpoint qpg_remlast (p : list Q) : list Q :=
  match p with
  | [] => []
  | a :: p' =>
      match p' with
      | [] => []
      | _ :: _ => a :: qpg_remlast p'
      end
  end.

(* Definitional equation of tail truncation on two-layer cons (guards
   recursion sites against over-unfolding by cbn inside proofs);
   born-clean: bare = -> Id *)
Lemma qpg_remlast_cons2 : forall (a b : Q) (L : list Q),
  @Id (list Q) (qpg_remlast (a :: b :: L)) (a :: qpg_remlast (b :: L)).
Proof. intros a b L. exact id_refl. Qed.

Lemma qpg_eval_mono : forall (k : nat) (c x : Q),
  QeqT (pint_eval (qpg_mono c k) x) (qpg_pow x k * c).
Proof.
  unfold qpg_mono. induction k as [|k' IH]; intros c x.
  - cbn [qpg_zeros app pint_eval qpg_pow]. exact (qpg_ring_mono0 c x).
  - cbn [qpg_zeros app pint_eval qpg_pow]. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (IH c x)). ring.
Qed.

(* Born-clean: bare = -> Id, proved by id_cong + conversion (no Prop) *)
Lemma qpg_remlast_length : forall p : list Q,
  @Id nat (length (qpg_remlast p)) (Nat.pred (length p)).
Proof.
  induction p as [|a p' IH].
  - exact id_refl.
  - destruct p' as [|b p''].
    + exact id_refl.
    + exact (id_cong (fun n => Datatypes.S n) IH).
Qed.

(* Set-face nonemptiness witness (list non-nil; Empty_set slot for nil) *)
Definition qpg_nonnil (l : list Q) : Set :=
  match l with
  | [] => Empty_set
  | _ :: _ => unit
  end.

(* Constructor-slot witness: a cons table is never empty *)
Lemma qpg_nonnil_cons : forall (h : Q) (t : list Q), qpg_nonnil (h :: t).
Proof. intros h t. exact tt. Qed.

(* For a table with nonempty tail, truncating one slot keeps the leading
   coefficient (alignment piece between the degree account and the
   evaluation account); born-clean: Prop <> premise -> Set-face
   qpg_nonnil witness, conclusion == -> QeqT *)
Lemma qpg_lead_cons_ne : forall (a : Q) (rest : list Q),
  qpg_nonnil rest -> QeqT (qpd_lead (a :: rest)) (qpd_lead rest).
Proof.
  intros a rest Hnn. destruct rest as [|b rest'].
  - cbn [qpg_nonnil] in Hnn. destruct Hnn.
  - cbn [qpd_lead pint_coeff length pred]. apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* For a table with zero leading coefficient, tail truncation preserves
   the evaluation (evaluation face of the elimination step's top-term
   zeroing); born-clean: premise == -> QeqT, conclusion == -> QeqT *)
Lemma qpg_eval_remlast0 : forall (p : list Q) (x : Q),
  QeqT (qpd_lead p) 0 -> QeqT (pint_eval (qpg_remlast p) x) (pint_eval p x).
Proof.
  induction p as [|a p' IH]; intros x H.
  - cbn [qpg_remlast pint_eval]. apply qeq_imp_qeqT. apply Qeq_refl.
  - destruct p' as [|b p''].
    + cbn [qpd_lead pint_coeff length pred] in H.
      cbn [qpg_remlast pint_eval]. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ H). ring.
    + assert (H2 : QeqT (qpd_lead (b :: p'')) 0).
      { apply qeq_imp_qeqT.
        exact (Qeq_trans _ _ _
                 (Qeq_sym _ _ (qeqT_imp_qeq _ _
                    (qpg_lead_cons_ne a (b :: p'') (qpg_nonnil_cons b p''))))
                 (qeqT_imp_qeq _ _ H)). }
      destruct (id_sym (qpg_remlast_cons2 a b p'')). cbn [pint_eval].
      apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (IH x H2)). apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §3 Elimination step: qpg_align_sub (aligned subtraction of c*q) *)
(*    and qpg_shift_sub (degree shift). Under the head=constant-  *)
(*    term representation, q's head slot aligns with p's k-th     *)
(*    slot (expansion of x^k*q)                                   *)
(* ============================================================ *)

Fixpoint qpg_align_sub (c : Q) (q p : list Q) : list Q :=
  match q with
  | [] => p
  | qh :: qt =>
      match p with
      | [] => []
      | ph :: pt => (ph - c * qh) :: qpg_align_sub c qt pt
      end
  end.

Fixpoint qpg_shift_sub (c : Q) (k : nat) (q p : list Q) : list Q :=
  match k with
  | 0%nat => qpg_align_sub c q p
  | Datatypes.S k' =>
      match p with
      | [] => []
      | ph :: pt => ph :: qpg_shift_sub c k' q pt
      end
  end.

(* Born-clean: nat <= premise -> NatLe, bare = conclusion -> Id *)
Lemma qpg_length_align : forall (c : Q) (q p : list Q),
  NatLe (length q) (length p) -> @Id nat (length (qpg_align_sub c q p)) (length p).
Proof.
  intros c q. induction q as [|qh qt IH]; intros p H.
  - exact id_refl.
  - destruct p as [|ph pt].
    + exfalso. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia.
    + assert (H2 : NatLe (length qt) (length pt)).
      { apply NatLe_lift. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia. }
      exact (id_cong (fun n => Datatypes.S n) (IH pt H2)).
Qed.

(* Born-clean: nat <= premise -> NatLe, bare = conclusion -> Id *)
Lemma qpg_length_shift : forall (c : Q) (k : nat) (q p : list Q),
  NatLe (k + length q) (length p) ->
  @Id nat (length (qpg_shift_sub c k q p)) (length p).
Proof.
  intros c k. induction k as [|k' IH]; intros q p H.
  - cbn [qpg_shift_sub]. apply (qpg_length_align c q p). exact H.
  - destruct p as [|ph pt].
    + exfalso. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia.
    + destruct pt as [|b pt'].
      * pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd.
        destruct k' as [|k''].
        -- assert (Hq0 : (length q = 0)%nat) by lia.
           destruct q as [|q1 q2].
           ++ exact id_refl.
           ++ exfalso. cbn [length] in Hq0. lia.
        -- exfalso. lia.
      * assert (H2 : NatLe (k' + length q) (Datatypes.S (length pt'))).
        { apply NatLe_lift. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia. }
        exact (id_cong (fun n => Datatypes.S n) (IH q (b :: pt') H2)).
Qed.

(* Evaluation semantics of aligned subtraction:
   eval (p - c*q) == eval p - c*eval q (born-clean both faces) *)
Lemma qpg_eval_align : forall (c : Q) (q p : list Q) (x : Q),
  NatLe (length q) (length p) ->
  QeqT (pint_eval (qpg_align_sub c q p) x) (pint_eval p x - c * pint_eval q x).
Proof.
  intros c q. induction q as [|qh qt IH]; intros p x H.
  - cbn [qpg_align_sub]. exact (qpg_ring_align0 (pint_eval p x) c).
  - destruct p as [|ph pt].
    + exfalso. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia.
    + assert (H2 : NatLe (length qt) (length pt)).
      { apply NatLe_lift. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia. }
      cbn [qpg_align_sub pint_eval]. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (IH pt x H2)). ring.
Qed.

(* Evaluation semantics of shifted subtraction:
   eval (p - c*x^k*q) == eval p - x^k*(c*eval q) (born-clean both faces) *)
Lemma qpg_eval_shift : forall (c : Q) (k : nat) (q p : list Q) (x : Q),
  NatLe (k + length q) (length p) ->
  QeqT (pint_eval (qpg_shift_sub c k q p) x)
       (pint_eval p x - qpg_pow x k * (c * pint_eval q x)).
Proof.
  intros c k. induction k as [|k' IH]; intros q p x H.
  - cbn [qpg_shift_sub qpg_pow]. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (qpg_eval_align c q p x H)). ring.
  - destruct p as [|ph pt].
    + exfalso. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia.
    + destruct pt as [|b pt'].
      * pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd.
        destruct k' as [|k''].
        -- assert (Hq0 : (length q = 0)%nat) by lia.
           destruct q as [|q1 q2].
           ++ cbn [qpg_shift_sub qpg_align_sub qpg_pow pint_eval].
              apply qeq_imp_qeqT. ring.
           ++ exfalso. cbn [length] in Hq0. lia.
        -- exfalso. lia.
      * assert (H2 : NatLe (k' + length q) (Datatypes.S (length pt'))).
        { apply NatLe_lift. pose proof (NatLe_drop _ _ H) as Hd. cbn [length] in Hd. lia. }
        cbn [qpg_shift_sub qpg_pow pint_eval]. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (IH q (b :: pt') x H2)). cbn [pint_eval]. ring.
Qed.

(* Length-to-degree conversion for nonempty tables (engine equation
   account); born-clean: Prop <> hypothesis dropped by restating over a
   concrete cons, bare = -> Id (definitional) *)
Lemma qpg_length_deg : forall (q1 : Q) (q2 : list Q),
  @Id nat (length (q1 :: q2)) (Datatypes.S (qpd_deg (q1 :: q2))).
Proof. intros q1 q2. exact id_refl. Qed.

(* Leading-coefficient account of aligned subtraction (top-aligned
   version: when length q = length p, q's leading slot matches p's
   leading slot exactly): lead (p - c*q) == lead p - c*lead q.
   Born-clean: nat = hypothesis -> Id, conclusion == -> QeqT *)
Lemma qpg_lead_align : forall (c : Q) (q p : list Q),
  @Id nat (length q) (length p) ->
  QeqT (qpd_lead (qpg_align_sub c q p)) (qpd_lead p - c * qpd_lead q).
Proof.
  intros c q. induction q as [|qh qt IH]; intros p H.
  - destruct p as [|ph pt].
    + cbn [qpg_align_sub qpd_lead pint_coeff length pred].
      exact (qpg_ring_align0 0 c).
    + inversion H.
  - destruct p as [|ph pt].
    + inversion H.
    + assert (H2 : @Id nat (length qt) (length pt))
        by exact (id_cong Nat.pred H).
      destruct qt as [|a qt'].
      * (* qt = []: equal lengths force pt = [] *)
        destruct pt as [|b pt'].
        -- cbn [qpg_align_sub qpd_lead pint_coeff length pred].
           apply qeq_imp_qeqT. apply Qeq_refl.
        -- inversion H.
      * destruct pt as [|b pt'].
        -- inversion H.
        -- assert (H2le : NatLe (length (a :: qt')) (length (b :: pt')))
             by (destruct H2; apply NatLe_lift; apply Nat.le_refl).
           assert (Hnn3 : qpg_nonnil (qpg_align_sub c (a :: qt') (b :: pt'))).
           { destruct (qpg_align_sub c (a :: qt') (b :: pt')) as [|h t] eqn:Ed.
             - exfalso.
               assert (Hlen : (length (qpg_align_sub c (a :: qt') (b :: pt'))
                               = length (b :: pt'))%nat)
                 by (destruct (qpg_length_align c (a :: qt') (b :: pt') H2le);
                     reflexivity).
               rewrite Ed in Hlen. cbn [length] in Hlen. discriminate Hlen.
             - exact tt. }
           apply qeq_imp_qeqT.
           cbn [qpg_align_sub].
           rewrite (qeqT_imp_qeq _ _
             (qpg_lead_cons_ne (ph - c * qh)
                (qpg_align_sub c (a :: qt') (b :: pt')) Hnn3)).
           rewrite (qeqT_imp_qeq _ _ (IH (b :: pt') H2)).
           rewrite (qeqT_imp_qeq _ _ (qpg_lead_cons_ne ph (b :: pt')
                                        (qpg_nonnil_cons b pt'))).
           rewrite (qeqT_imp_qeq _ _ (qpg_lead_cons_ne qh (a :: qt')
                                        (qpg_nonnil_cons a qt'))).
           apply Qeq_refl.
Qed.

(* Leading-coefficient account of shifted subtraction (equality version:
   when length p = k + length q the top slot is exactly the annihilated
   slot): lead (p - c*x^k*q) == lead p - c*lead q (source of top-term
   zeroing). Born-clean: nat = hypothesis -> Id, conclusion == -> QeqT *)
Lemma qpg_lead_shift : forall (c : Q) (k : nat) (q p : list Q),
  @Id nat ((k + length q)%nat) (length p) ->
  QeqT (qpd_lead (qpg_shift_sub c k q p)) (qpd_lead p - c * qpd_lead q).
Proof.
  intros c k. induction k as [|k' IH]; intros q p H.
  - cbn [qpg_shift_sub]. apply (qpg_lead_align c q p). exact H.
  - destruct p as [|ph pt].
    + inversion H.
    + destruct pt as [|b pt'].
      * (* pt = []: forces k' = 0 AND q = [], shift-sub degenerates to a
           single-slot table *)
        cbn [length] in H.
        assert (Hprop : (Datatypes.S k' + length q = 1)%nat)
          by (destruct H; reflexivity).
        destruct k' as [|k''].
        -- assert (Hq0 : (length q = 0)%nat) by lia.
           destruct q as [|q1 q2].
           ++ cbn [qpg_shift_sub qpg_align_sub qpd_lead pint_coeff length pred].
              exact (qpg_ring_align0 ph c).
           ++ exfalso. cbn [length] in Hq0. lia.
        -- exfalso. lia.
      * cbn [length] in H.
        assert (Hprop : (Datatypes.S k' + length q = Datatypes.S (Datatypes.S (length pt')))%nat)
          by (destruct H; reflexivity).
        assert (H2 : (k' + length q = Datatypes.S (length pt'))%nat) by lia.
        assert (H2eq : @Id nat ((k' + length q)%nat) (Datatypes.S (length pt')))
          by (destruct H2; exact id_refl).
        assert (H2le : (k' + length q <= Datatypes.S (length pt'))%nat) by lia.
        assert (H2nat : NatLe (k' + length q) (Datatypes.S (length pt')))
          by (apply NatLe_lift; exact H2le).
        assert (Hnn2 : qpg_nonnil (qpg_shift_sub c k' q (b :: pt'))).
        { destruct (qpg_shift_sub c k' q (b :: pt')) as [|h t] eqn:Ed.
          - exfalso.
            assert (Hlen : (length (qpg_shift_sub c k' q (b :: pt'))
                            = length (b :: pt'))%nat)
              by (destruct (qpg_length_shift c k' q (b :: pt') H2nat); reflexivity).
            rewrite Ed in Hlen. cbn [length] in Hlen. discriminate Hlen.
          - exact tt. }
        apply qeq_imp_qeqT.
        cbn [qpg_shift_sub].
        rewrite (qeqT_imp_qeq _ _
          (qpg_lead_cons_ne ph (qpg_shift_sub c k' q (b :: pt')) Hnn2)).
        rewrite (qeqT_imp_qeq _ _ (IH q (b :: pt') H2eq)).
        rewrite (qeqT_imp_qeq _ _ (qpg_lead_cons_ne ph (b :: pt')
                                        (qpg_nonnil_cons b pt'))).
        apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §4 Recursion engine (genuine Fixpoint: nat fuel structural      *)
(*    recursion) + existence limb + top level. Invariant:         *)
(*    p == q*s + r; each step shrinks the remainder length        *)
(*    strictly by one (termination measure).                      *)
(* ============================================================ *)

Fixpoint qpg_engine (fuel : nat) (q p : list Q) : list Q * list Q :=
  match fuel with
  | 0%nat => ([], p)
  | Datatypes.S f =>
      if Nat.ltb (qpd_deg p) (qpd_deg q) then ([], p)
      else
        let k := Nat.sub (qpd_deg p) (qpd_deg q) in
        let c := qpd_lead p / qpd_lead q in
        match qpg_engine f q (qpg_remlast (qpg_shift_sub c k q p)) with
        | (sq, rr) => (pint_add (qpg_mono c k) sq, rr)
        end
  end.

(* Existence limb: with fuel = length p the engine output satisfies the
   CC-registered general-form correctness pair. Born-clean: nat <=
   hypothesis -> NatLe (NatLe bridge); the length/degree bookkeeping
   stays proof-internal Prop scaffolding fed by NatLe_drop *)
Lemma qpg_engine_sound : forall (fuel : nat) (q p : list Q),
  qpg_divisor_ok q -> NatLe (length p) fuel ->
  qpd_divmod_gen_pred p q (qpg_engine fuel q p).
Proof.
  induction fuel as [|f IH]; intros q p Hq Hlen.
  - (* fuel exhausted: p must be empty; 0 == eval q * 0 + 0, remainder []
     of degree 0 < deg q (from degge1) *)
    pose proof (NatLe_drop _ _ Hlen) as HlenD.
    destruct p as [|a p'].
    + cbn [qpg_engine fst snd]. unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
      * intros x. cbn [pint_eval].
        exact (qpg_ring_leaf (pint_eval q x)).
      * exact (fst Hq).
    + cbn [length] in HlenD. lia.
  - destruct p as [|a p'].
    + (* empty dividend: the deg q >= 1 limb is taken directly; base
         branch fires *)
      destruct Hq as [Hd Hl].
      cbn [qpg_engine qpd_deg].
      destruct (Nat.ltb 0 (qpd_deg q)) eqn:E.
      * cbn [fst snd]. unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
        -- intros x. cbn [pint_eval].
           exact (qpg_ring_leaf (pint_eval q x)).
        -- exact Hd.
      * unfold qpg_degge1 in Hd. rewrite E in Hd. inversion Hd.
    + (* main elimination step: leading-coefficient division annihilates
         the top slot; remainder length strictly decreases by one *)
      destruct Hq as [Hd Hl].
      cbn [qpg_engine].
      destruct (Nat.ltb (qpd_deg (a :: p')) (qpd_deg q)) eqn:E.
      * (* deg p < deg q: base case, quotient 0 remainder p *)
        cbn [fst snd]. unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
        -- intros x. cbn [pint_eval].
           exact (qpg_ring_lt a (x * pint_eval p' x) (pint_eval q x)).
        -- unfold qpd_deglt. rewrite E. exact id_refl.
      * (* deg q <= deg p: eliminate one step, then recurse *)
        assert (Hge : (qpd_deg q <= qpd_deg (a :: p'))%nat)
          by (apply Nat.ltb_ge; exact E).
        assert (Hdp : qpd_deg (a :: p') = length p') by reflexivity.
        rewrite Hdp in Hge.
        remember (Nat.sub (qpd_deg (a :: p')) (qpd_deg q)) as k eqn:Hk.
        remember (qpd_lead (a :: p') / qpd_lead q) as c eqn:Hc.
        (* q is nonempty: its degree is >= 1 (from degge1) *)
        assert (Hneq : q <> []).
        { intro E0. unfold qpg_degge1 in Hd. rewrite E0 in Hd.
          cbn [qpd_deg Nat.ltb Nat.leb] in Hd. inversion Hd. }
        (* length account (Prop scaffolding): k + length q = length p *)
        assert (Hlen_q1 : (length q = Datatypes.S (qpd_deg q))%nat).
        { destruct q as [|q1 q2].
          - exfalso. apply Hneq. reflexivity.
          - reflexivity. }
        assert (F1prop : (k + length q = length (a :: p'))%nat).
        { rewrite Hk, Hdp, Hlen_q1. cbn [length]. lia. }
        assert (F1 : NatLe (k + length q) (length (a :: p')))
          by (apply NatLe_lift; lia).
        assert (F1eq : @Id nat ((k + length q)%nat) (length (a :: p')))
          by (destruct F1prop; exact id_refl).
        assert (Hlen3 : (length (qpg_remlast (qpg_shift_sub c k q (a :: p'))) <= f)%nat).
        { assert (Hrl : (length (qpg_remlast (qpg_shift_sub c k q (a :: p')))
                         = Nat.pred (length (qpg_shift_sub c k q (a :: p'))))%nat)
            by (destruct (qpg_remlast_length (qpg_shift_sub c k q (a :: p')));
                reflexivity).
          assert (Hls : (length (qpg_shift_sub c k q (a :: p')) = length (a :: p'))%nat)
            by (destruct (qpg_length_shift c k q (a :: p') F1); reflexivity).
          rewrite Hrl, Hls. cbn [length]. cbn [Nat.pred].
          pose proof (NatLe_drop _ _ Hlen) as HlenD. cbn [length] in HlenD. lia. }
        (* top-term zeroing: lead (shift-sub) == 0 (Qdiv cancellation
           enters here) *)
        assert (Hlead0 : qpd_lead (qpg_shift_sub c k q (a :: p')) == 0).
        { rewrite (qeqT_imp_qeq _ _ (qpg_lead_shift c k q (a :: p') F1eq)).
          rewrite Hc.
          exact (qeqT_imp_qeq _ _
                   (qpg_lead_cancel (qpd_lead (a :: p')) (qpd_lead q)
                                     (qpg_leadne0_inv q Hl))). }
        (* recursive engine destructuring and induction limb *)
        destruct (qpg_engine f q (qpg_remlast (qpg_shift_sub c k q (a :: p'))))
          as [sq rr] eqn:Eeng.
        specialize (IH q (qpg_remlast (qpg_shift_sub c k q (a :: p')))
                         (pair Hd Hl) (NatLe_lift _ _ Hlen3)).
        rewrite Eeng in IH. unfold qpd_divmod_gen_pred in IH. cbn [fst snd] in IH.
        destruct IH as [IH1 IH2].
        (* evaluation account: eval p == x^k*(c*eval q) + eval remainder *)
        assert (Hev1 : forall x : Q,
          pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x
          == pint_eval (qpg_shift_sub c k q (a :: p')) x).
        { intros x0.
          exact (qeqT_imp_qeq _ _
                   (qpg_eval_remlast0 (qpg_shift_sub c k q (a :: p')) x0
                                      (qeq_imp_qeqT _ _ Hlead0))). }
        assert (Hev2 : forall x : Q,
          pint_eval (qpg_shift_sub c k q (a :: p')) x
          == pint_eval (a :: p') x - qpg_pow x k * (c * pint_eval q x)).
        { intros x0. exact (qeqT_imp_qeq _ _ (qpg_eval_shift c k q (a :: p') x0 F1)). }
        assert (Hp : forall x : Q,
          pint_eval (a :: p') x
          == qpg_pow x k * (c * pint_eval q x)
             + pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x).
        { intros x0.
          exact (qeqT_imp_qeq _ _
                   (qpg_qeq_move (pint_eval (a :: p') x0)
                      (pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x0)
                      (qpg_pow x0 k * (c * pint_eval q x0))
                      (qeq_imp_qeqT _ _ (Qeq_trans _ _ _ (Hev1 x0) (Hev2 x0))))). }
        assert (HIH : forall x : Q,
          pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x
          == pint_eval q x * pint_eval sq x + pint_eval rr x).
        { intros x0. exact (qeqT_imp_qeq _ _ (IH1 x0)). }
        unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
        -- intros x. apply qeq_imp_qeqT.
           rewrite (Hp x), (HIH x),
                   (qeqT_imp_qeq _ _
                      (qpd_eval_add (qpg_mono c k) sq x)).
           rewrite (qeqT_imp_qeq _ _ (qpg_eval_mono k c x)).
           exact (qeqT_imp_qeq _ _
                    (qpg_ring_main (qpg_pow x k) c (pint_eval q x)
                                   (pint_eval sq x) (pint_eval rr x))).
        -- exact IH2.
Qed.

(* Top level: general-form delivery in the CC-registered container --
   division with remainder for any-degree divisors (well-formedness
   precondition); NatLe reflexivity via NatLe_lift *)
Definition qpg_divmod_gen (p q : list Q) (Hq : qpg_divisor_ok q)
  : qpd_divmod_gen_type p q :=
  existT _ (qpg_engine (length p) q p)
           (qpg_engine_sound (length p) q p Hq
                             (NatLe_lift _ _ (Nat.le_refl (length p)))).

(* ============================================================ *)
(* §5 Uniqueness limb interface (registered only, not built --     *)
(*    first-piece strategy 45-minute slice, as planned).          *)
(*    Quotient/remainder uniqueness: if two decompositions both   *)
(*    satisfy the correctness pair, the quotient/remainder tables *)
(*    are Id-equal. (Statement face already Set-level.)           *)
(* ============================================================ *)

Definition qpg_gen_unique_type (p q : list Q) : Set :=
  forall (s r s' r' : list Q),
    And (qpd_divmod_gen_pred p q (s, r)) (qpd_divmod_gen_pred p q (s', r')) ->
    And (@Id (list Q) s s') (@Id (list Q) r r').

(* ============================================================ *)
(* §6 Numeric smoke tests (BF pattern: vm_compute, zero-axiom     *)
(*    setting, small instances; bare = statements born-clean      *)
(*    as Id)                                                      *)
(* ============================================================ *)

(* Divisor well-formedness witnesses: q = x+1 (table [1;1]) and
   q = x+2 (table [2;1]) *)
Definition qpg_ok_xp1 : qpg_divisor_ok (1 :: 1 :: nil).
Proof.
  unfold qpg_divisor_ok. split.
  - unfold qpg_degge1. cbn [qpd_deg length pred Nat.ltb Nat.leb]. exact id_refl.
  - unfold qpg_leadne0. cbn [qpd_lead pint_coeff length pred Qcompare]. exact tt.
Defined.

Definition qpg_ok_xp2 : qpg_divisor_ok (2 :: 1 :: nil).
Proof.
  unfold qpg_divisor_ok. split.
  - unfold qpg_degge1. cbn [qpd_deg length pred Nat.ltb Nat.leb]. exact id_refl.
  - unfold qpg_leadne0. cbn [qpd_lead pint_coeff length pred Qcompare]. exact tt.
Defined.

(* Smoke A (exact division): (x+1)^2 / (x+1) => quotient [1;1] (=x+1),
   remainder [0] *)
Lemma qpg_smokeA_q :
  @Id (list Q)
      (fst (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil) (1 :: 1 :: nil) qpg_ok_xp1)))
      (1 :: 1 :: nil).
Proof. vm_compute. exact id_refl. Qed.

Lemma qpg_smokeA_r :
  @Id (list Q)
      (snd (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil) (1 :: 1 :: nil) qpg_ok_xp1)))
      (0 :: nil).
Proof. vm_compute. exact id_refl. Qed.

(* Smoke A semantic face: the full QeqT equation p == q*quotient +
   remainder (dividend evaluation included) *)
Lemma qpg_smokeA_sem : forall x : Q,
  QeqT (pint_eval (1 :: 2 :: 1 :: nil) x)
       (pint_eval (1 :: 1 :: nil) x
          * pint_eval (fst (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil)
                                                   (1 :: 1 :: nil) qpg_ok_xp1))) x
        + pint_eval (snd (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil)
                                                 (1 :: 1 :: nil) qpg_ok_xp1))) x).
Proof.
  intros x. apply qeq_imp_qeqT.
  assert (Heng : projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil) (1 :: 1 :: nil) qpg_ok_xp1)
                 = ((1 :: 1 :: nil), (0 :: nil)%list)) by (vm_compute; reflexivity).
  rewrite Heng. cbn [fst snd].
  rewrite (qeqT_imp_qeq _ _ (qpd_eval_cons 1 (2 :: 1 :: nil) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 2 (1 :: nil) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 1 (1 :: nil) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 1 (@nil Q) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_cons 0 (@nil Q) x)),
          (qeqT_imp_qeq _ _ (qpd_eval_nil x)).
  exact (qeqT_imp_qeq _ _ (qpg_ring_smokeA x)).
Qed.

(* Smoke B (with remainder): (x^2+1) / (x+2) => quotient [-2;1] (=x-2),
   remainder [5] *)
Lemma qpg_smokeB_q :
  @Id (list Q)
      (fst (projT1 (qpg_divmod_gen (1 :: 0 :: 1 :: nil) (2 :: 1 :: nil) qpg_ok_xp2)))
      ((-2) :: 1 :: nil).
Proof. vm_compute. exact id_refl. Qed.

Lemma qpg_smokeB_r :
  @Id (list Q)
      (snd (projT1 (qpg_divmod_gen (1 :: 0 :: 1 :: nil) (2 :: 1 :: nil) qpg_ok_xp2)))
      (5 :: nil).
Proof. vm_compute. exact id_refl. Qed.

(* Smoke C (degree-0 dividend): 3 / (x+2) => quotient [] (=0),
   remainder [3] *)
Lemma qpg_smokeC :
  @Id (list Q * list Q)
      (projT1 (qpg_divmod_gen (3 :: nil) (2 :: 1 :: nil) qpg_ok_xp2))
      ((@nil Q), (3 :: nil)%list).
Proof. vm_compute. exact id_refl. Qed.

(* Smoke D (empty dividend edge case): 0 / (x+2) => quotient [],
   remainder [] *)
Lemma qpg_smokeD :
  @Id (list Q * list Q)
      (projT1 (qpg_divmod_gen (@nil Q) (2 :: 1 :: nil) qpg_ok_xp2))
      ((@nil Q), (@nil Q)%list).
Proof. vm_compute. exact id_refl. Qed.

(* Smoke E (quadratic / linear, third instance): (x^2-1) / (x+3) =>
   quotient x-3, remainder 8 *)
Lemma qpg_smokeE_q :
  @Id (list Q)
      (fst (projT1 (qpg_divmod_gen ((-1) :: 0 :: 1 :: nil) (3 :: 1 :: nil) qpg_ok_xp2)))
      ((-3) :: 1 :: nil).
Proof. vm_compute. exact id_refl. Qed.

Lemma qpg_smokeE_r :
  @Id (list Q)
      (snd (projT1 (qpg_divmod_gen ((-1) :: 0 :: 1 :: nil) (3 :: 1 :: nil) qpg_ok_xp2)))
      (8 :: nil).
Proof. vm_compute. exact id_refl. Qed.

(* ============================================================ *)
(* §7 Closure: extraction face + Print Assumptions (red-line four  *)
(*    clauses, PA on each)                                        *)
(* ============================================================ *)

Separate Extraction qpg_engine qpg_shift_sub qpg_align_sub qpg_remlast
  qpg_pow qpg_zeros qpg_mono.

Print Assumptions qpg_id_true_inv.
Print Assumptions qpg_degge1_inv.
Print Assumptions qpg_leadne0_inv.
Print Assumptions qpg_div_cancel.
Print Assumptions qpg_lead_cancel.
Print Assumptions qpg_ring_main.
Print Assumptions qpg_ring_shift.
Print Assumptions qpg_ring_align.
Print Assumptions qpg_eval_mono.
Print Assumptions qpg_length_align.
Print Assumptions qpg_length_shift.
Print Assumptions qpg_remlast_length.
Print Assumptions qpg_lead_cons_ne.
Print Assumptions qpg_eval_remlast0.
Print Assumptions qpg_eval_align.
Print Assumptions qpg_eval_shift.
Print Assumptions qpg_lead_align.
Print Assumptions qpg_lead_shift.
Print Assumptions qpg_engine_sound.
Print Assumptions qpg_divmod_gen.
Print Assumptions qpg_ok_xp1.
Print Assumptions qpg_ok_xp2.
Print Assumptions qpg_smokeA_q.
Print Assumptions qpg_smokeA_r.
Print Assumptions qpg_smokeA_sem.
Print Assumptions qpg_smokeB_q.
Print Assumptions qpg_smokeB_r.
Print Assumptions qpg_smokeC.
Print Assumptions qpg_smokeD.
Print Assumptions qpg_smokeE_q.
Print Assumptions qpg_smokeE_r.

(* CK: polynomial division engine, general form -- end (born-green
   target) *)
