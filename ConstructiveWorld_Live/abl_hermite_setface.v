(* ConstructiveWorld-Set -- LW2Hermite core identity face in Set-carrier form. *)

(** * abl_hermite_setface: Set-carrier restatement of the LW2Hermite core identity face.

    Mission.  This file restates the identity face of the LW2Hermite machine,
      the purely polynomial form of the Hermite 1873 integral identity, on the
      Set carrier [hst_QeqT]: the evaluation table [lw2_eps K f] satisfies the
      kernel equation relating its derivative to the table minus [f], and the
      evaluation-sum structure together with the pointwise summation laws is
      reproved natively on [Set].  Main statements: [hst_eps_deriv_kernel],
      [hst_eps_exact], [hst_eps_eval_sum_T], [hst_eps_deriv_sum_T],
      [hst_qsum0_ext_T], [hst_qsum0_add_T], [hst_qsum0_shift_T],
      [hst_eval_add_T].

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Extraction].  Requires
      [LW0QPoly], [LW2Hermite] of this development.

    References.  This development, abl_hermite_setface.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_hermite_setface.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import QArith Lia Arith.
Require Import LW0QPoly LW2Hermite.

Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Section 0.  Set-carrier toolkit: the Set-level identity type        *)
(* [hst_Id], the rational equality wrapper [hst_QeqT], the identity    *)
(* operations, the two bridges between [hst_QeqT] and [Qeq], and the   *)
(* congruence family on the Set carrier.                               *)
(* ------------------------------------------------------------------ *)

(* Set-level identity type, with the standard carrier shape; declared *)
(* here so the file needs no further Require. *)
Inductive hst_Id {A : Set} (x : A) : A -> Set :=
| hst_id_refl : hst_Id x x.

Arguments hst_id_refl {A} {x}.

(* Identity operations: elimination into the propositional equality *)
(* (a lawful downward elimination), symmetry, and transitivity. *)
Definition hst_id_eq {A : Set} {x y : A} (p : hst_Id x y) : x = y :=
  match p with
  | hst_id_refl => eq_refl
  end.

Definition hst_id_sym {A : Set} {x y : A} (p : hst_Id x y) : hst_Id y x :=
  match p with
  | hst_id_refl => hst_id_refl
  end.

(* [hst_QeqT]: the Set-carrier form of equality on [Q], packaged over *)
(* the boolean comparison [Qcompare]. *)
Definition hst_QeqT (a b : Q) : Set :=
  hst_Id (match Qcompare a b with
          | Eq => true
          | _ => false
          end) true.

(* Forward bridge: [Qcompare] = Eq yields [hst_QeqT], by definition *)
(* unfolding and construction. *)
Lemma hst_qeqT_of_compare : forall a b : Q, Qcompare a b = Eq -> hst_QeqT a b.
Proof.
  intros a b H.
  unfold hst_QeqT.
  rewrite H.
  cbn.
  apply hst_id_refl.
Qed.

(* Inversion on the comparison component, stated before [a] and [b] *)
(* appear so that case analysis does not abstract over the terms. *)
Lemma hst_compare_of_bool : forall c : comparison,
  (match c with Eq => true | _ => false end) = true -> c = Eq.
Proof.
  intros c H.
  destruct c.
  - reflexivity.
  - discriminate H.
  - discriminate H.
Qed.

(* Reverse bridge: [hst_QeqT] yields back [Qcompare] = Eq, through the *)
(* identity elimination [hst_id_eq]. *)
Lemma hst_compare_of_qeqT : forall a b : Q, hst_QeqT a b -> Qcompare a b = Eq.
Proof.
  intros a b H.
  apply hst_compare_of_bool.
  unfold hst_QeqT in H.
  exact (hst_id_eq H).
Qed.

(* The two bridges between [hst_QeqT] and the propositional equality *)
(* [Qeq]; every statement face stays on [Set]. *)
Lemma hst_qeqT_imp_qeq : forall a b : Q, hst_QeqT a b -> a == b.
Proof.
  intros a b H.
  apply (proj2 (Qeq_alt a b)).
  apply hst_compare_of_qeqT.
  exact H.
Qed.

Lemma hst_qeqT_of_qeq : forall a b : Q, a == b -> hst_QeqT a b.
Proof.
  intros a b Hab.
  apply hst_qeqT_of_compare.
  apply (proj1 (Qeq_alt a b)).
  exact Hab.
Qed.

(* Leaf rule: a pure ring identity closes a [hst_QeqT] goal in one step. *)
Ltac hst_ring := apply hst_qeqT_of_qeq; ring.

(* Congruence family on the Set carrier: reflexivity, symmetry, *)
(* transitivity, and addition, subtraction, multiplication in right- *)
(* and left-biased forms. *)
Lemma hst_qeqT_refl : forall a : Q, hst_QeqT a a.
Proof.
  intros a.
  apply hst_qeqT_of_qeq.
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_sym : forall a b : Q, hst_QeqT a b -> hst_QeqT b a.
Proof.
  intros a b H.
  apply hst_qeqT_of_qeq.
  apply (Qeq_sym a b).
  apply hst_qeqT_imp_qeq.
  exact H.
Qed.

Lemma hst_qeqT_trans : forall a b c : Q,
  hst_QeqT a b -> hst_QeqT b c -> hst_QeqT a c.
Proof.
  intros a b c H1 H2.
  assert (Hab : a == b) by (apply hst_qeqT_imp_qeq; exact H1).
  assert (Hbc : b == c) by (apply hst_qeqT_imp_qeq; exact H2).
  rewrite <- Hab in Hbc.
  apply hst_qeqT_of_qeq.
  exact Hbc.
Qed.

Lemma hst_qeqT_add : forall a b c d : Q,
  hst_QeqT a b -> hst_QeqT c d -> hst_QeqT (a + c) (b + d).
Proof.
  intros a b c d H1 H2.
  apply hst_qeqT_of_qeq.
  rewrite (hst_qeqT_imp_qeq a b H1).
  rewrite (hst_qeqT_imp_qeq c d H2).
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_sub : forall a b c d : Q,
  hst_QeqT a b -> hst_QeqT c d -> hst_QeqT (a - c) (b - d).
Proof.
  intros a b c d H1 H2.
  apply hst_qeqT_of_qeq.
  rewrite (hst_qeqT_imp_qeq a b H1).
  rewrite (hst_qeqT_imp_qeq c d H2).
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_mul : forall a b c d : Q,
  hst_QeqT a b -> hst_QeqT c d -> hst_QeqT (a * c) (b * d).
Proof.
  intros a b c d H1 H2.
  apply hst_qeqT_of_qeq.
  rewrite (hst_qeqT_imp_qeq a b H1).
  rewrite (hst_qeqT_imp_qeq c d H2).
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_add_r : forall a c d : Q,
  hst_QeqT c d -> hst_QeqT (a + c) (a + d).
Proof.
  intros a c d H.
  apply (hst_qeqT_add a a c d).
  - apply hst_qeqT_refl.
  - exact H.
Qed.

Lemma hst_qeqT_add_l : forall a b c : Q,
  hst_QeqT a b -> hst_QeqT (a + c) (b + c).
Proof.
  intros a b c H.
  apply (hst_qeqT_add a b c c).
  - exact H.
  - apply hst_qeqT_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 1.  Evaluation-sum structure: the pointwise laws restated   *)
(* on Set carriers.  Every induction is reproved natively on the Set   *)
(* face; arithmetic leaves go through [hst_ring].                      *)
(* ------------------------------------------------------------------ *)

(* Pointwise evaluation of a polynomial sum: the Set-face form of *)
(* [qpoly_eval_add]. *)
Lemma hst_eval_add_T : forall p q x,
  hst_QeqT (qpoly_eval (qpoly_add p q) x)
           (qpoly_eval p x + qpoly_eval q x).
Proof.
  induction p as [|a p IH]; intros q x.
  - destruct q as [|b q'].
    + cbn [qpoly_add qpoly_eval]. hst_ring.
    + cbn [qpoly_add qpoly_eval]. hst_ring.
  - destruct q as [|b q'].
    + cbn [qpoly_add qpoly_eval]. hst_ring.
    + replace (qpoly_add (cons a p) (cons b q'))
        with (cons (a + b) (qpoly_add p q')) by reflexivity.
      cbn [qpoly_eval].
      eapply hst_qeqT_trans.
      * apply hst_qeqT_add.
        -- apply hst_qeqT_refl.
        -- apply hst_qeqT_mul.
           ++ apply hst_qeqT_refl.
           ++ apply (IH q' x).
      * hst_ring.
Qed.

(* One-step unfolding of the sum: definitional, both sides *)
(* syntactically equal after [cbn]. *)
Lemma hst_qsum0_succ_T : forall (F : nat -> Q) n,
  hst_QeqT (lw2_qsum0 F (S n)) (lw2_qsum0 F n + F n).
Proof.
  intros F n.
  cbn [lw2_qsum0].
  apply hst_qeqT_refl.
Qed.

(* Pointwise additivity of the sum: the Set-face form of *)
(* [lw2_qsum0_add], with the induction on the Set face. *)
Lemma hst_qsum0_add_T : forall n (g h : nat -> Q),
  hst_QeqT (lw2_qsum0 (fun j => g j + h j) n)
           (lw2_qsum0 g n + lw2_qsum0 h n).
Proof.
  intros n g h.
  induction n as [|n IH].
  - cbn [lw2_qsum0]. hst_ring.
  - cbn [lw2_qsum0].
    eapply hst_qeqT_trans.
    + apply hst_qeqT_add.
      * exact IH.
      * apply hst_qeqT_refl.
    + hst_ring.
Qed.

(* Pointwise extensionality of the sum: the Set-face form of *)
(* [lw2_qsum0_ext]; the pointwise premise is stated in [hst_QeqT] form. *)
Lemma hst_qsum0_ext_T : forall n (g h : nat -> Q),
  (forall j, (j < n)%nat -> hst_QeqT (g j) (h j)) ->
  hst_QeqT (lw2_qsum0 g n) (lw2_qsum0 h n).
Proof.
  intros n g h.
  induction n as [|n IH]; intros H.
  - cbn [lw2_qsum0]. apply hst_qeqT_refl.
  - cbn [lw2_qsum0].
    apply hst_qeqT_add.
    + apply IH.
      intros j Hj.
      apply H.
      lia.
    + apply (H n). apply Nat.lt_succ_diag_r.
Qed.

(* Shift law of the sum, the Set-face form of [lw2_qsum0_shift]: the *)
(* sum over [g (S k)] equals the sum over [g] minus [g 0] plus [g n]. *)
Lemma hst_qsum0_shift_T : forall n (g : nat -> Q),
  hst_QeqT (lw2_qsum0 (fun k => g (S k)) n)
           (lw2_qsum0 g n - g (0%nat) + g n).
Proof.
  intros n g.
  induction n as [|n IH].
  - cbn [lw2_qsum0]. hst_ring.
  - cbn [lw2_qsum0].
    apply (hst_qeqT_trans
             (lw2_qsum0 (fun k => g (S k)) n + g (S n))%Q
             (lw2_qsum0 g n - g (0%nat) + g n + g (S n))%Q
             (lw2_qsum0 g n + g n - g (0%nat) + g (S n))%Q).
    + apply hst_qeqT_add.
      * exact IH.
      * apply hst_qeqT_refl.
    + hst_ring.
Qed.

(* Evaluation sum of the table [lw2_eps K f]: its evaluation equals      *)
(* [sum_{k<K} f^{(k)}] (the Set-face form of [lw2_eps_eval_sum]), the    *)
(* evaluation-sum structure of the kernel identity.                      *)
Lemma hst_eps_eval_sum_T : forall K f x,
  hst_QeqT (qpoly_eval (lw2_eps K f) x)
           (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) x) K).
Proof.
  intros K f x.
  induction K as [|K IH].
  - cbn [lw2_eps qpoly_eval lw2_qsum0]. apply hst_qeqT_refl.
  - cbn [lw2_eps].
    eapply hst_qeqT_trans.
    + apply hst_eval_add_T.
    + eapply hst_qeqT_trans.
      * apply hst_qeqT_add.
        -- apply hst_qeqT_refl.
        -- exact IH.
      * change (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) x) (S K))
          with (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) x) K
                + qpoly_eval (qpoly_deriv_iter K f) x)%Q.
        hst_ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  Anchor of the kernel identity: the derivative sum and   *)
(* the kernel equation of the eps table, on Set carriers.              *)
(* ------------------------------------------------------------------ *)

(* Derivative sum of the table [lw2_eps K f]: its derivative evaluates  *)
(* to [sum_{k<K} f^{(k+1)}] (the Set-face form of [lw2_eps_deriv_sum]). *)
(* The induction runs on the Set face; the derivative-interaction step  *)
(* enters through the already proven propositional-face lemmas.         *)
Lemma hst_eps_deriv_sum_T : forall K f x,
  hst_QeqT (qpoly_eval (qpoly_deriv (lw2_eps K f)) x)
           (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter (S k) f) x) K).
Proof.
  intros K f x.
  induction K as [|K IH].
  - cbn [lw2_eps qpoly_deriv qpoly_eval lw2_qsum0]. apply hst_qeqT_refl.
  - cbn [lw2_eps].
    eapply hst_qeqT_trans.
    + (* Leaf step: [qpoly_eval_deriv_add] and [qpoly_eval_add] supply *)
      (* the propositional congruence. *)
      apply hst_qeqT_of_qeq.
      rewrite (qpoly_eval_deriv_add (qpoly_deriv_iter K f) (lw2_eps K f) x).
      apply (qpoly_eval_add (qpoly_deriv (qpoly_deriv_iter K f))
                            (qpoly_deriv (lw2_eps K f)) x).
    + rewrite <- (qpoly_deriv_iter_succ K f).
      cbn [lw2_qsum0].
      eapply hst_qeqT_trans.
      * apply hst_qeqT_add_r.
        exact IH.
      * hst_ring.
Qed.

(* Anchor: the Set-carrier form of the kernel identity.  The table       *)
(* [lw2_eps K f] satisfies the kernel equation                           *)
(*   (eps K f)' == eps K f - f  whenever  length f <= K.                 *)
(* The assembly runs entirely on the Set face: HA (the derivative sum),  *)
(* HC (the shift), transport along the congruences (HE0, HD), and Hsw    *)
(* carrying the evaluation sum back to eps through [hst_qeqT_sym] and    *)
(* [hst_qeqT_sub].                                                       *)
Theorem hst_eps_deriv_kernel : forall K f x,
  (length f <= K)%nat ->
  hst_QeqT (qpoly_eval (qpoly_deriv (lw2_eps K f)) x)
           (qpoly_eval (lw2_eps K f) x - qpoly_eval f x).
Proof.
  intros K f x HN.
  assert (HA := hst_eps_deriv_sum_T K f x).
  assert (HB := hst_eps_eval_sum_T K f x).
  assert (HC := hst_qsum0_shift_T K (fun j => qpoly_eval (qpoly_deriv_iter j f) x)).
  assert (HE0 : hst_QeqT (qpoly_eval (qpoly_deriv_iter 0 f) x) (qpoly_eval f x)).
  { apply hst_qeqT_of_qeq. reflexivity. }
  (* Tail-zero leaf: [f^{(K)}] evaluates to zero once [length f <= K], *)
  (* quoted from the Set-carrier-face lemma [lw2_deriv_iter_zero_eval]  *)
  (* (its conclusion is the [S02_CauchyComplete.QeqT] carrier) and      *)
  (* bridged one layer to [Qeq] via [qeqT_imp_qeq] before entering the  *)
  (* Set-face congruence.                                               *)
  assert (HD : hst_QeqT (qpoly_eval (qpoly_deriv_iter K f) x) 0%Q).
  { apply hst_qeqT_of_qeq.
    apply (S02_CauchyComplete.qeqT_imp_qeq _ _ (lw2_deriv_iter_zero_eval K f x HN)). }
  (* Carry the evaluation sum back to the eps table: HB enters the left *)
  (* side of the subtraction through symmetry. *)
  assert (Hsw : hst_QeqT (lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                          - qpoly_eval f x)
                         (qpoly_eval (lw2_eps K f) x - qpoly_eval f x)).
  { apply hst_qeqT_sub.
    - apply hst_qeqT_sym. exact HB.
    - apply hst_qeqT_refl. }
  (* Assembly chain on the Set face: HA, then HC, then transport along *)
  (* the congruences (HE0, HD), then the zero term drops, then Hsw. *)
  eapply hst_qeqT_trans.
  { exact HA. }
  { eapply hst_qeqT_trans.
    { exact HC. }
    { eapply hst_qeqT_trans.
      { apply hst_qeqT_add.
        { apply hst_qeqT_sub.
          { apply hst_qeqT_refl. }
          { exact HE0. } }
        { exact HD. } }
      { apply (hst_qeqT_trans
                 ((lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                   - qpoly_eval f x) + 0)%Q
                 (lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                  - qpoly_eval f x)%Q
                 (qpoly_eval (lw2_eps K f) x - qpoly_eval f x)%Q).
        { hst_ring. }
        { exact Hsw. } } } }
Qed.

(* Exact kernel identity, the premise-free form (the Set restatement of  *)
(* [lw2i_eps_exact]): (eps K f)' == eps K f - f + f^{(K)} holds for      *)
(* every K without any side condition.                                   *)
Theorem hst_eps_exact : forall K f x,
  hst_QeqT (qpoly_eval (qpoly_deriv (lw2_eps K f)) x)
           (qpoly_eval (lw2_eps K f) x - qpoly_eval f x
            + qpoly_eval (qpoly_deriv_iter K f) x).
Proof.
  intros K f x.
  assert (HA := hst_eps_deriv_sum_T K f x).
  assert (HB := hst_eps_eval_sum_T K f x).
  assert (HC := hst_qsum0_shift_T K (fun j => qpoly_eval (qpoly_deriv_iter j f) x)).
  assert (HE0 : hst_QeqT (qpoly_eval (qpoly_deriv_iter 0 f) x) (qpoly_eval f x))
    by (apply hst_qeqT_of_qeq; reflexivity).
  assert (Hsw : hst_QeqT (lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                          - qpoly_eval f x)
                         (qpoly_eval (lw2_eps K f) x - qpoly_eval f x)).
  { apply hst_qeqT_sub.
    - apply hst_qeqT_sym. exact HB.
    - apply hst_qeqT_refl. }
  eapply hst_qeqT_trans.
  { exact HA. }
  { eapply hst_qeqT_trans.
    { exact HC. }
    { eapply hst_qeqT_trans.
      { apply hst_qeqT_add_l.
        { apply hst_qeqT_sub.
          { apply hst_qeqT_refl. }
          { exact HE0. } } }
      { apply hst_qeqT_add_l.
        exact Hsw. } } }
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  Formal derivative interaction: interface signatures.    *)
(* The two faces below fix the interface; this file registers their    *)
(* types and leaves the proofs to the files that consume them.         *)
(* ------------------------------------------------------------------ *)

Definition hst_eval_di_add_face : Type :=
  forall k u v x,
    hst_QeqT (qpoly_eval (qpoly_deriv_iter k (qpoly_add u v)) x)
             (qpoly_eval (qpoly_deriv_iter k u) x
              + qpoly_eval (qpoly_deriv_iter k v) x).

Definition hst_trans_deriv_iter_eval_face : Type :=
  forall k f c x,
    hst_QeqT (qpoly_eval (qpoly_deriv_iter k (lw2_trans f c)) x)
             (qpoly_eval (qpoly_deriv_iter k f) (x + c)).

(* ------------------------------------------------------------------ *)
(* Section 4.  Extraction checks and assumption audits.                *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Extraction.
Separate Extraction hst_eps_deriv_kernel hst_eps_exact hst_eps_eval_sum_T
  hst_eps_deriv_sum_T hst_qsum0_shift_T hst_qsum0_ext_T hst_eval_add_T.

Print Assumptions hst_eps_deriv_kernel.
Print Assumptions hst_eps_exact.
Print Assumptions hst_eps_eval_sum_T.
Print Assumptions hst_eps_deriv_sum_T.
Print Assumptions hst_qsum0_ext_T.
Print Assumptions hst_eval_add_T.
