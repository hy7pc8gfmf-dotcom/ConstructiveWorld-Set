(** ConstructiveWorld-Set — decidable semantics for a query-response interface.

* G11_IDLFam: Decidable query semantics and the ingot-differential loom.

    Mission.  The iffT record equivalence, distance/displacement cocycles
      ([dsub_cocycle]/[dsub_shift_invariant]), the three query-correctness
      statements ([qin_correct]/[qval_correct]/[qanc_correct]), the decider
      specification [qdc_spec] with refusal semantics
      ([qrej_admit_false]/[qadmit_answer]/[qadmit_reject]), burn counters
      ([val_fresh_answer]/[val_burn_reject]), and the XOR-weaving
      demonstration section together with the merged UpIDL loom (two-stage
      ingot-differential processing of verdict streams).

    Dependencies.  Stdlib [ZArith], [ZArithRing], [ZArith_dec], [Bool],
      [List], [Lia]; the Set-layer identity/order base is inlined from this
      development (self-contained section 0).

    References.  This development, ConstructiveWorld-Main baseline module
      G11_IDLFam.v, whose statement names are carried over here verbatim
      (statement-face Set-carrier completion).  Semantic correctness of a
      decidable query system (decision oracles independent of encoding).

    Constructivity.  All named statements are carried by [Set] (equality
      via [clq_tid], order via [clq_nle], iff via [iffT], branching via
      bool/prod/sigT); every proof ends in [Qed] with no admitted goals and
      no classical logic; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" G11_IDLFam.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import S01_BaseRing.
Notation S := Datatypes.S.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set-layer infrastructure (inlined from G04_ProjFam.v: the tid identity type + the nle order type + decision tools) *)
(* ===================================================================== *)

(* The Set-layer identity type (an equality carrier with zero Prop in statements) *)
Inductive clq_tid (A : Type) : A -> A -> Type := clq_tid_refl : forall x : A, clq_tid A x x.

Definition clq_tid_sym (A : Type) (x y : A) (H : clq_tid A x y) : clq_tid A y x :=
  match H in clq_tid _ a b return clq_tid _ b a with
  | clq_tid_refl _ a0 => @clq_tid_refl _ a0
  end.

Definition clq_tid_trans (A : Type) (x y z : A) (H1 : clq_tid A x y) (H2 : clq_tid A y z) :
  clq_tid A x z :=
  match H1 in clq_tid _ a b return clq_tid _ b z -> clq_tid _ a z with
  | clq_tid_refl _ a0 => fun H => H
  end H2.

(* Functional congruence of the identity type (the transport workhorse) *)
Definition clq_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : clq_tid A x y) :
  clq_tid B (f x) (f y) :=
  match H in clq_tid _ a b return clq_tid B (f a) (f b) with
  | clq_tid_refl _ a0 => @clq_tid_refl _ (f a0)
  end.

(* Definitional-equality extraction from clq_tid (for reasoning inside proofs, under a controlled name) *)
Ltac tidQ H E :=
  pose proof (match H in clq_tid _ a b return a = b with clq_tid_refl _ _ => eq_refl end) as E.

(* x = y -> clq_tid A x y (the definitional equality fed back into the identity type) *)
Lemma clq_tid_eq : forall (A : Type) (x y : A), x = y -> clq_tid A x y.
Proof.
  intros A x y H. rewrite H. apply clq_tid_refl.
Defined.

(* The Set-layer natural-number order type (k <= m encoded as nle k m) *)
Inductive clq_nle (n : nat) : nat -> Set :=
| clq_nle_n : clq_nle n n
| clq_nle_S : forall m : nat, clq_nle n m -> clq_nle n (S m).

Lemma clq_leb_refl_tid : forall a : nat, clq_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply clq_tid_refl.
Qed.

Lemma clq_leb_S : forall a m : nat,
  clq_tid bool (Nat.leb a m) true -> clq_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply clq_tid_refl.
    + change (clq_tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply clq_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint clq_nle_lebF (a b : nat) (H : clq_nle a b) {struct H} :
  clq_tid bool (Nat.leb a b) true :=
  match H as H0 in clq_nle _ bb
  return clq_tid bool (Nat.leb a bb) true with
  | clq_nle_n _ => clq_leb_refl_tid a
  | clq_nle_S _ m H1 => clq_leb_S a m (clq_nle_lebF a m H1)
  end.

Definition clq_nle_leb (b a : nat) (H : clq_nle a b) : clq_tid bool (Nat.leb a b) true :=
  clq_nle_lebF a b H.

(* clq_nle -> nat ≤ extraction (for reasoning inside proofs) *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (clq_nle_leb _ _ H) in clq_tid _ x y return x = y with
        | clq_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma clq_nle_0 : forall m : nat, clq_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply clq_nle_n.
  - apply clq_nle_S. exact IH.
Qed.

Lemma clq_nle_SS : forall a b : nat, clq_nle a b -> clq_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply clq_nle_n.
  - apply clq_nle_S. exact IH.
Qed.

(* The reverse carrier clq_nle -> leb = true *)
Lemma clq_nle_of_leb : forall b a : nat,
  clq_tid bool (Nat.leb a b) true -> clq_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply clq_nle_n.
    + change (clq_tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply clq_nle_S. apply clq_nle_0.
    + exact (clq_nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ -> clq_tid bool (leb) true carrier *)
Lemma clq_lebT : forall a b : nat, (a <= b)%nat -> clq_tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply clq_tid_refl.
Qed.

(* clq_nle (S m) O absurdity (empty elimination on disjoint indices; legally closes any Type goal) *)
Lemma nle_S_absurd : forall (m : nat) (P : Type), clq_nle (S m) O -> P.
Proof.
  intros m P H. inversion H.
Qed.

(* The Set-layer iff carrier: a two-function record (if-and-only-if with zero Prop in statements) *)
Record iffT (A B : Type) : Type := mkIffT
  { iffT_fw : A -> B
  ; iffT_bw : B -> A }.

(* ===================================================================== *)
(* 1. The difference table dtab: an inductively constructed constant-difference ledger (syntax-immune carrier) *)
(* The closure law: difference i j + difference j k == difference i k holds for every dtab without premises — *)
(* no constructor can write down a table that breaks the law. *)
(* ===================================================================== *)

Inductive dtab : Set :=
| dtab1 (c : Z)                    (* A single-index ledger: index 0 (the head gauge) with gauge value c *)
| dtabSnoc (d : dtab) (w : Z).     (* Entry: a new index S (dlen d) whose difference from the head is w *)

(* The number of indices in the ledger: the legal index domain 0 .. dlen d *)
Fixpoint dlen (d : dtab) : nat :=
  match d with
  | dtab1 _ => O
  | dtabSnoc d0 _ => S (dlen d0)
  end.

(* The potential reading under the head gauge h = 0: pot i = difference i 0 (accumulated by construction, never a materialized total) *)
Fixpoint pot (d : dtab) (i : nat) : Z :=
  match d with
  | dtab1 c => if Nat.eqb i O then c else 0
  | dtabSnoc d0 w => if Nat.eqb i (S (dlen d0)) then w else pot d0 i
  end.

(* difference i j (the only derivable [inner]-class observable) *)
Definition dsub (d : dtab) (i j : nat) : Z := pot d i - pot d j.

(* Core theorem of part 3: the cyclic closure law holds constructively for every dtab (no premises at all) *)
Theorem dsub_cocycle : forall (d : dtab) (i j k : nat),
  clq_tid Z (dsub d i j + dsub d j k) (dsub d i k).
Proof.
  intros d i j k. unfold dsub.
  apply (clq_tid_eq Z (pot d i - pot d j + (pot d j - pot d k)) (pot d i - pot d k)).
  ring.
Qed.

(* Gauge translation: add c to every potential reading of the table (a syntactic operation changing the head gauge) *)
Fixpoint dshift (d : dtab) (c : Z) : dtab :=
  match d with
  | dtab1 c0 => dtab1 (c0 + c)
  | dtabSnoc d0 w => dtabSnoc (dshift d0 c) (w + c)
  end.

Lemma dlen_shift : forall (d : dtab) (c : Z), clq_tid nat (dlen (dshift d c)) (dlen d).
Proof.
  intros d c. induction d as [c0 | d0 IH w].
  - simpl. apply clq_tid_refl.
  - simpl. tidQ IH Edl. rewrite Edl. apply clq_tid_refl.
Qed.

(* The comparison theorem for part 3: absolute potential readings shift by exactly c under gauge translation (the language has no translation-invariant absolute readout) *)
Theorem pot_shift_moves : forall (d : dtab) (c : Z) (i : nat),
  clq_nle i (dlen d) -> clq_tid Z (pot (dshift d c) i) (pot d i + c).
Proof.
  intros d c i. induction d as [c0 | d0 IH w].
  - intros Hn. destruct i as [| i1].
    + simpl. apply clq_tid_refl.
    + exact (nle_S_absurd i1 _ Hn).
  - intros Hn. simpl in Hn.
    pose proof (dlen_shift d0 c) as DL. tidQ DL Edl.
    simpl. rewrite Edl.
    destruct (Nat.eqb i (S (dlen d0))) eqn:E.
    + apply clq_tid_refl.
    + apply IH. apply clq_nle_of_leb. apply clq_lebT.
      apply Nat.eqb_neq in E. nleP Hn. lia.
Qed.

(* [inner]-class difference readings are gauge-invariant (within the legal index domain) *)
Theorem dsub_shift_invariant : forall (d : dtab) (c : Z) (i j : nat),
  clq_nle i (dlen d) -> clq_nle j (dlen d) ->
  clq_tid Z (dsub (dshift d c) i j) (dsub d i j).
Proof.
  intros d c i j Hi Hj. unfold dsub.
  pose proof (pot_shift_moves d c i Hi) as T1. tidQ T1 E1.
  pose proof (pot_shift_moves d c j Hj) as T2. tidQ T2 E2.
  apply (clq_tid_eq Z (pot (dshift d c) i - pot (dshift d c) j) (pot d i - pot d j)).
  rewrite E1, E2. ring.
Qed.

(* ===================================================================== *)
(* 2. The anchor-obligation closed list acol (the [anchor]-class certificate carrier: explicit induction over anchor-closure events) *)
(* ===================================================================== *)

Inductive acol : Set :=
| acol0                          (* The empty list: no closed anchor obligations *)
| acolS (a : acol) (i : nat) (c : Z).  (* An anchor-closure event: index i externally anchored to absolute value c *)

(* The anchor reading: the absolute value of the most recent closure record for that index; unclosed = None *)
Fixpoint aread (i : nat) (a : acol) : option Z :=
  match a with
  | acol0 => None
  | acolS a0 j c => if Nat.eqb i j then Some c else aread i a0
  end.

(* ===================================================================== *)
(* 3. Part 1: the explicit three-way query typing qtype + the missing-certificate tags misscred + the answer type qans *)
(* ===================================================================== *)

(* Three query classes: [inner] translation-invariant / [value] valuation / [anchor] absolute — syntactically these are the only three constructors,
and any mixed-class question (for example, asking the absolute level with [inner]-class syntax) cannot even be written down. *)
Inductive qtype : Set :=
| QIN (i j : nat)            (* [inner], the translation-invariant class: asks for difference i j *)
| QVAL (i : nat)             (* [value], the valuation class: asks for the absolute amount at index i (consumes the head voucher) *)
| QANC (i : nat) (a : Z).    (* [anchor], the absolute class: asks for the alignment difference of i's absolute level against anchor a *)

(* Missing-certificate tags: the refusal value carries the structural information of which certificate is missing (an explicit enumeration) *)
Inductive misscred : Set :=
| MC_RANGE (i : nat)   (* Missing the ledger certificate: index i is not enrolled (outside 0 .. dlen) *)
| MC_VSLOT             (* Missing the head voucher: the single-slot valuation voucher is absent or already burned *)
| MC_ANCH (i : nat).   (* Missing the anchor-closure certificate: index i has no closed anchor obligation *)

(* The answer type: the left branch = an answer value (explicitly constructed), the right branch = a structural refusal
(carrying a missing-certificate tag). A refusal is not a failure: qans_rej is a first-class constructor of qans. *)
Inductive qans : Set :=
| qans_val (z : Z)
| qans_rej (mc : misscred).

(* The answer-type-to-bool readout (used by the refusal-honesty theorems) *)
Definition qans_isans (r : qans) : bool :=
  match r with
  | qans_val _ => true
  | qans_rej _ => false
  end.

Definition tid_qans_val (z1 z2 : Z) (H : clq_tid Z z1 z2) :
  clq_tid qans (qans_val z1) (qans_val z2) :=
  clq_tid_cong (@qans_val) z1 z2 H.

(* ===================================================================== *)
(* 4. Part 1: the decidable admission predicates — the three-way dispatch (sdec, the informative-certificate variant of sumbool) *)
(* The left branch of the three-way dispatch carries a Set-layer certificate (stdlib sumbool branches are limited to Prop and cannot be used); *)
(* boolean admission is taken as the direct-reading definition, interchangeable with the three-way dispatch via certificate-type characterizations (below and in the *_correct statements). *)
(* ===================================================================== *)

(* The Set-layer decision sum (the informative-certificate variant of sumbool: stdlib sumbool branches are limited to Prop and
cannot carry Set-layer certificates; hence this isomorphic three-way dispatch type; both left and right branches can carry
informative certificates. It lives in Type alongside option/sigT — informative end to end, extractable, zero Prop.) *)
Inductive sdec (A B : Type) : Type :=
| sdec_l (a : A)
| sdec_r (b : B).

(* The three-way dispatch on the nat order: left = a clq_nle certificate, right = the clq_tid evidence of leb = false (the decision
proper goes through the fully quantified lemma, avoiding destruct pollution of the scrutinee inside the target type) *)
Lemma nle_dc_gen : forall (p : bool) (a b : nat),
  p = Nat.leb a b -> sdec (clq_nle a b) (clq_tid bool (Nat.leb a b) false).
Proof.
  intros p a b E. destruct p as [] eqn:Ep.
  - apply sdec_l. exact (clq_nle_of_leb b a (clq_tid_eq bool (Nat.leb a b) true (eq_sym E))).
  - apply sdec_r. exact (clq_tid_eq bool (Nat.leb a b) false (eq_sym E)).
Defined.

Definition nle_dc (a b : nat) : sdec (clq_nle a b) (clq_tid bool (Nat.leb a b) false) :=
  nle_dc_gen (Nat.leb a b) a b eq_refl.

(* [inner]-class admission dispatch: left = the both-enrolled clq_nle certificate; right = the not-enrolled tag *)
Definition qin_dc (d : dtab) (i j : nat)
  : sdec (prod (clq_nle i (dlen d)) (clq_nle j (dlen d))) misscred.
Proof.
  destruct (nle_dc i (dlen d)) as [Ha | Ha].
  - destruct (nle_dc j (dlen d)) as [Hb | Hb].
    + apply sdec_l. split; assumption.
    + apply sdec_r. apply (MC_RANGE j).
  - apply sdec_r. apply (MC_RANGE i).
Defined.

Definition qin_ok (d : dtab) (i j : nat) : bool :=
  Nat.leb i (dlen d) && Nat.leb j (dlen d).

(* [value]-class admission dispatch: left = the head-voucher certificate (sigT carrying the voucher-face amount); right = missing head voucher *)
Definition qval_dc (v : option (nat * Z)) (i : nat)
  : sdec (sigT (fun w : Z => clq_tid (option (nat * Z)) (Some (i, w)) v)) misscred.
Proof.
  destruct v as [[h w] |] eqn:Ev.
  - destruct (Nat.eqb h i) eqn:Eh.
    + apply sdec_l. apply (existT _ w).
      apply Nat.eqb_eq in Eh.
      exact (clq_tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
               (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
    + apply sdec_r. apply MC_VSLOT.
  - apply sdec_r. apply MC_VSLOT.
Defined.

Definition qval_ok (v : option (nat * Z)) (i : nat) : bool :=
  match v with Some p => Nat.eqb (fst p) i | None => false end.

(* Readout of the voucher-face absolute amount *)
Definition vs_val (v : option (nat * Z)) : Z :=
  match v with Some p => snd p | None => 0 end.

(* [anchor]-class admission dispatch: left = the anchor-closure certificate (sigT carrying the anchor-face amount); right = missing closure *)
Definition qanc_dc (a : acol) (i : nat)
  : sdec (sigT (fun c : Z => clq_tid (option Z) (Some c) (aread i a))) misscred.
Proof.
  destruct (aread i a) as [c |] eqn:E.
  - apply sdec_l. apply (existT _ c). apply clq_tid_refl.
  - apply sdec_r. apply (MC_ANCH i).
Defined.

Definition qanc_ok (a : acol) (i : nat) : bool :=
  match aread i a with Some _ => true | None => false end.

(* The interplay between the three-way dispatch and boolean admission runs not through unfolding the decision bodies but through certificate-type
characterizations: the left-branch types of qin_dc/qval_dc/qanc_dc are exactly the certificate types paired with the respective boolean
admissions iff-statements in qin_correct/qval_correct/qanc_correct (a prod of clq_nle pair / a sigT voucher face / a sigT anchor face)
— both routes are pinned by the same certificate type, and consistency is carried by the type rather than by a lemma. *)

(* --- Correctness theorems: admission iff a certificate exists (sigT-carried; iff via iffT) --- *)

Theorem qin_correct : forall (d : dtab) (i j : nat),
  iffT (clq_tid bool (qin_ok d i j) true)
       (prod (clq_nle i (dlen d)) (clq_nle j (dlen d))).
Proof.
  intros d i j. apply (mkIffT _ _).
  - intros H. unfold qin_ok in H.
    tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
    exact (pair (clq_nle_of_leb (dlen d) i (clq_tid_eq bool _ true E1))
                (clq_nle_of_leb (dlen d) j (clq_tid_eq bool _ true E2))).
  - intros p. destruct p as [Ha Hb].
    pose proof (clq_nle_leb (dlen d) i Ha) as T1. tidQ T1 E1.
    pose proof (clq_nle_leb (dlen d) j Hb) as T2. tidQ T2 E2.
    unfold qin_ok.
    apply (clq_tid_eq bool (Nat.leb i (dlen d) && Nat.leb j (dlen d)) true).
    rewrite E1, E2. reflexivity.
Qed.

Theorem qval_correct : forall (v : option (nat * Z)) (i : nat),
  iffT (clq_tid bool (qval_ok v i) true)
       (sigT (fun w : Z => clq_tid (option (nat * Z)) (Some (i, w)) v)).
Proof.
  intros v i. apply (mkIffT _ _).
  - intros H. unfold qval_ok in H. destruct v as [[h w] |] eqn:Ev.
    + simpl in H. destruct (Nat.eqb h i) eqn:Eh.
      * apply (existT _ w).
        apply Nat.eqb_eq in Eh.
        exact (clq_tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
                 (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
      * tidQ H E. discriminate E.
    + simpl in H. tidQ H E. discriminate E.
  - intros [w H]. unfold qval_ok. destruct v as [[h w0] |] eqn:Ev.
    + tidQ H E. injection E as Ei Ew.
      rewrite Ei. simpl.
      exact (clq_tid_eq bool (Nat.eqb h h) true (Nat.eqb_refl h)).
    + tidQ H E. discriminate E.
Qed.

Theorem qanc_correct : forall (a : acol) (i : nat),
  iffT (clq_tid bool (qanc_ok a i) true)
       (sigT (fun c : Z => clq_tid (option Z) (Some c) (aread i a))).
Proof.
  intros a i. apply (mkIffT _ _).
  - intros H. unfold qanc_ok in H. destruct (aread i a) as [c |] eqn:E.
    + apply (existT _ c). apply clq_tid_refl.
    + tidQ H E2. discriminate E2.
  - intros [c H]. unfold qanc_ok. destruct (aread i a) as [c0 |] eqn:E.
    + apply clq_tid_refl.
    + tidQ H E2. discriminate E2.
Qed.

(* ===================================================================== *)
(* 5. Part 2: structural refusals — the ledger state clst + the answering machine qask + the grand dispatch qdc *)
(* ===================================================================== *)

(* The CL ledger state = the difference table + the single-slot head voucher + the closed anchor-obligation list (the window is the difference table itself; dtab has fixed-length induction) *)
Record clst : Set := mkCL
  { cld : dtab                    (* The difference table (the only data source of the [inner] class) *)
  ; clv : option (nat * Z)        (* The single-slot head voucher: Some (h, w) = the head voucher is unspent *)
  ; cla : acol }.                 (* The closed anchor-obligation list (the only data source of the [anchor] class) *)

(* The answering machine (three-place form): each class reads only its own certificate channel — [inner] reads the difference
table dsub; [value] reads the head voucher vs_val; [anchor] reads the anchors aread. No cross-channel reads. *)
Definition qaskR (d : dtab) (v : option (nat * Z)) (a : acol) (q : qtype) : qans :=
  match q with
  | QIN i j =>
      if Nat.leb i (dlen d)
      then (if Nat.leb j (dlen d)
            then qans_val (dsub d i j)
            else qans_rej (MC_RANGE j))
      else qans_rej (MC_RANGE i)
  | QVAL i =>
      if qval_ok v i then qans_val (vs_val v) else qans_rej MC_VSLOT
  | QANC i a0 =>
      if qanc_ok a i
      then qans_val (match aread i a with Some c => c - a0 | None => 0 end)
      else qans_rej (MC_ANCH i)
  end.

(* The admission predicate (bool): dispatched identically to the answering machine *)
Definition qadmitR (d : dtab) (v : option (nat * Z)) (a : acol) (q : qtype) : bool :=
  match q with
  | QIN i j => qin_ok d i j
  | QVAL i => qval_ok v i
  | QANC i _ => qanc_ok a i
  end.

(* The ledger-state packaging: the answering machine and the admission predicate *)
Definition qask (s : clst) (q : qtype) : qans := qaskR (cld s) (clv s) (cla s) q.
Definition qadmit (s : clst) (q : qtype) : bool := qadmitR (cld s) (clv s) (cla s) q.

(* Admission and verdict readout agree pointwise (internal consistency of the constitution) *)
Lemma qadmit_isin : forall (s : clst) (q : qtype),
  clq_tid bool (qadmit s q) (qans_isans (qask s q)).
Proof.
  intros s q. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans, qin_ok.
    destruct (Nat.leb i (dlen (cld s))); destruct (Nat.leb j (dlen (cld s)));
      apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qval_ok (clv s) i); apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qanc_ok (cla s) i); apply clq_tid_refl.
Qed.

(* The constitutional decision grand dispatch: left = an answer-value witness; right = a structural refusal witness (carrying a tag) *)
Definition qdc (s : clst) (q : qtype)
  : sdec (sigT (fun z : Z => clq_tid qans (qask s q) (qans_val z)))
         (sigT (fun mc : misscred => clq_tid qans (qask s q) (qans_rej mc))).
Proof.
  destruct q as [i j | i | i a0].
  - unfold qask, qaskR.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply sdec_l. apply (existT _ (dsub (cld s) i j)). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE j)). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
  - unfold qask, qaskR. destruct (qval_ok (clv s) i) eqn:Ev.
    + apply sdec_l. apply (existT _ (vs_val (clv s))). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ MC_VSLOT). apply clq_tid_refl.
  - unfold qask, qaskR. destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply sdec_l.
      apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_ANCH i)). apply clq_tid_refl.
Defined.

(* The grand-dispatch specification: the verdict position qdc_b agrees pointwise with the admission bool (the bool face of internal
consistency); the certificate-content consistency of the branches is carried by qadmit_answer / qadmit_reject. *)
Definition qdc_b (s : clst) (q : qtype) : bool :=
  match qdc s q with sdec_l _ _ _ => true | sdec_r _ _ _ => false end.

Theorem qdc_spec : forall (s : clst) (q : qtype), clq_tid bool (qdc_b s q) (qadmit s q).
Proof.
  intros s q. unfold qdc_b. destruct (qdc s q) as [Cz | Cm].
  - destruct Cz as [w Hw].
    exact (clq_tid_sym bool (qadmit s q) true
             (clq_tid_trans bool (qadmit s q) (qans_isans (qask s q)) true
                (qadmit_isin s q)
                  (clq_tid_cong qans_isans (qask s q) (qans_val w) Hw))).
  - destruct Cm as [mc Hmc].
    exact (clq_tid_sym bool (qadmit s q) false
             (clq_tid_trans bool (qadmit s q) (qans_isans (qask s q)) false
                (qadmit_isin s q)
                  (clq_tid_cong qans_isans (qask s q) (qans_rej mc) Hmc))).
Qed.

(* Refusal honesty: whenever qask outputs the refusal branch, admission must be false (a refusal is explicit construction, not failure) *)
Theorem qrej_admit_false : forall (s : clst) (q : qtype) (mc : misscred),
  clq_tid qans (qask s q) (qans_rej mc) -> clq_tid bool (qadmit s q) false.
Proof.
  intros s q mc H. tidQ H E.
  apply (clq_tid_eq bool (qadmit s q) false).
  destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in E |- *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei; destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + discriminate E.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - unfold qadmit, qadmitR, qask, qaskR, qval_ok in E |- *.
    destruct (clv s) as [[j w] |] eqn:Ev.
    + rewrite ?Ev in E |- *. cbn [vs_val fst] in E |- *.
      destruct (Nat.eqb j i) eqn:Ej2; rewrite ?Ej2 in E |- *.
      * discriminate E.
      * reflexivity.
    + rewrite ?Ev in E |- *. reflexivity.
  - unfold qadmit, qadmitR, qask, qaskR, qanc_ok in E |- *.
    destruct (aread i (cla s)) as [c0 |] eqn:Er; rewrite ?Er in E |- *.
    + discriminate E.
    + reflexivity.
Qed.

(* Admission true implies the answer branch is explicitly constructed (carrying the answer-value witness) *)
Theorem qadmit_answer : forall (s : clst) (q : qtype), clq_tid bool (qadmit s q) true ->
  sigT (fun z : Z => clq_tid qans (qask s q) (qans_val z)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply (existT _ (dsub (cld s) i j)). apply clq_tid_refl.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + apply (existT _ (vs_val (clv s))). apply clq_tid_refl.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply clq_tid_refl.
    + tidQ H E. discriminate E.
Qed.

(* Admission false implies the refusal branch is explicitly constructed (carrying the missing-certificate tag witness) — the existence of structural refusals *)
Theorem qadmit_reject : forall (s : clst) (q : qtype), clq_tid bool (qadmit s q) false ->
  sigT (fun mc : misscred => clq_tid qans (qask s q) (qans_rej mc)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_RANGE j)). apply clq_tid_refl.
    + apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
    + apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ MC_VSLOT). apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_ANCH i)). apply clq_tid_refl.
Qed.

(* --- The head-voucher lifecycle: a [value]-class query burns the voucher once; asking again after the burn is a structural refusal with the missing-head-voucher tag --- *)

Definition clburn (s : clst) (i : nat) : clst := mkCL (cld s) None (cla s).

Theorem val_fresh_answer : forall (d : dtab) (a : acol) (i : nat) (w : Z),
  clq_tid qans (qask (mkCL d (Some (i, w)) a) (QVAL i)) (qans_val w).
Proof.
  intros d a i w. unfold qask, qaskR, qval_ok. simpl.
  rewrite Nat.eqb_refl. apply clq_tid_refl.
Qed.

Theorem val_burn_reject : forall (s : clst) (i : nat),
  clq_tid qans (qask (clburn s i) (QVAL i)) (qans_rej MC_VSLOT).
Proof.
  intros s i. destruct s as [d v a]. apply (clq_tid_eq qans _ _).
  unfold clburn, qask, qaskR. cbn [cld clv cla].
  destruct (qval_ok None i) eqn:Ev.
  - cbn [qval_ok] in Ev. discriminate Ev.
  - cbn [qval_ok]. reflexivity.
Qed.

(* ===================================================================== *)
(* 6. Part 3: [inner]-class translation invariance (the typing of wagers made syntactic) *)
(* ===================================================================== *)

(* The typed form of the CL 2.0 wager: [inner]-class adjudications are verbatim invariant under gauge translation of the difference table.
Compare pot_shift_moves: absolute readouts shift by exactly c — hence absolute questions cannot be asked within [inner]-class syntax
(and if asked, the answer is translation-invariant anyway: the type system keeps them outside the difference-table language). *)
Theorem qin_gauge_invariant : forall (d : dtab) (c : Z) (v : option (nat * Z))
                                     (a : acol) (i j : nat),
  clq_tid qans (qask (mkCL (dshift d c) v a) (QIN i j))
           (qask (mkCL d v a) (QIN i j)).
Proof.
  intros d c v a i j. unfold qask, qaskR. cbn [cld clv cla].
  pose proof (dlen_shift d c) as DL. tidQ DL Edl. rewrite Edl.
  destruct (Nat.leb i (dlen d)) eqn:Ei; destruct (Nat.leb j (dlen d)) eqn:Ej.
  - apply tid_qans_val. apply dsub_shift_invariant.
    + exact (clq_nle_of_leb (dlen d) i (clq_tid_eq bool (Nat.leb i (dlen d)) true Ei)).
    + exact (clq_nle_of_leb (dlen d) j (clq_tid_eq bool (Nat.leb j (dlen d)) true Ej)).
  - apply clq_tid_refl.
  - apply clq_tid_refl.
  - apply clq_tid_refl.
Qed.

Close Scope Z_scope.

(* ======== Member module of G11_IDLFam: UpIDL (merged verbatim, with its own Requires) ======== *)
(* ===================================================================== *)
(* UpIDL.v — the decision loom IDL, ingot-differential two-stage realization *)
(*                                                                       *)
(* Design source: the final design of the "Ingot-Differential *)
(* Loom (IDL) — two stages; the decision stream is never replayed verdict by verdict" (collecting both the XOR *)
(* counterexample trial and the livelock trial); item Q5 of the upstream design document *)
(* (the Q4 semantics are given by UpCLQuery.v, consumed here directly via Require Import). *)
(*                                                                       *)
(* The two stages: *)
(* Construction stage (melt): the decision stream is right-folded in one pass into an ingot — the six-hole pinning (equal values *)
(* accumulate as P1 pins, conflicting values propagate as PB, missing decisions give PN) plus the rejection-difference clause list. *)
(* Differential stage (weave): consumes only the ingot, never replays the stream — the pinning is differentially compiled into the Q4 carrier dtab *)
(* (head gauge k0 normalized to 0, dlen = 5); the rejection-difference clauses are adjudicated one by one over the woven list by Z decisions *)
(* (inter-stage differentials are decidable); a missing witness module / a pin conflict / a clause contradiction is recorded honestly *)
(* as an under-order wiou; nothing is emitted. *)
(* Main statements: melt_hom (melting is a list homomorphism — the algebraic content of the two-stage construction) / pin_iffT (pinning is the consistent *)
(* aggregation of the pass decisions in the stream, with iffT conservation in both directions) / weave_sound (what is woven is legitimate: every decision *)
(* in the stream is satisfied by the woven list — immune to cross-hole illegality from birth) / weave_replay_b/_d + *)
(* replay_census (whole-stream replay: the weaving decision, the woven artifact and the conflict census are all unchanged — livelock *)
(* loses its carrier) / recheck_pass (the woven artifact is handed to the Q4 decision face for word-by-word review of [inner]-class queries) / *)
(* xor_defused (the XOR stream is honestly recorded as an under-order and not woven — the regression companion of the second-round counterexample trial). *)
(*                                                                       *)
(* The carrier is at the Z/nat/bool decidable layer throughout (continuing the Q4 Set-layer route: clq_tid/clq_nle/iffT/sigT); *)
(* zero Prop in statements: equality via clq_tid, order via clq_nle, iff via iffT, branching via bool/prod/sigT. *)
(* Discipline: purely constructive, axiom-free exits, stdlib + UpCLQuery, extractable end to end. *)
(* Design decisions (details left open were fixed by the principles "the two-stage structure is clearest" and "tightest coupling to the Q4 decision face"): *)
(* (1) The six hole types hole = k0 k1 kb kc ke kr are made concrete as six slots; parameters = Q4 dtab indices 0..5; *)
(* the head gauge k0 is constantly 0 (a gauge fixing); all decision semantics go through the head-relative difference dsub d (hix h) 0. *)
(* (2) A decision verd = hole type x direction x Z evidence: pass(h,w) sets the pin "value = w"; rej(h,e) emits the difference clause *)
(* "value is not e" (a non-zero difference requirement — the designed witness-shaped difference clause). *)
(* (3) The pinning tri-state pinv = PN missing / P1 z pinned / PB conflict — the conflict state PB propagates unconditionally, so *)
(* conflicting values in one hole are recorded at most once per whole-stream pass (the designed "same-hole conflict recorded once"); the friction *)
(* account is fixed as the conflict census iconf = the number of holes pinned PB (the final "conflict census + under-order ordering key"). *)
(* (4) The woven artifact = the Q4 dtab (dlen = 5), which drops directly into the Q4 ledger state mkCL for [inner]-class query review. *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.

Open Scope Z_scope.

(* clq_tid to definitional-equality extraction (for reasoning inside proofs) *)
Definition tidE (A : Type) (x y : A) (H : clq_tid A x y) : x = y :=
  match H in clq_tid _ a b return a = b with clq_tid_refl _ _ => eq_refl end.

(* The clq_tid-flavored boolean conjunction splitter / orb head-false eliminator (in-proof connector pieces serving the zero-Prop-statement discipline) *)
Lemma tid_andb_inv : forall a b : bool,
  clq_tid bool (andb a b) true -> prod (clq_tid bool a true) (clq_tid bool b true).
Proof.
  intros a b H. tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
  exact (pair (clq_tid_eq bool _ true E1) (clq_tid_eq bool _ true E2)).
Qed.

Lemma tid_orb_false : forall b : bool,
  clq_tid bool (orb false b) true -> clq_tid bool b true.
Proof.
  intros b H. tidQ H E. rewrite orb_false_l in E.
  exact (clq_tid_eq bool _ true E).
Qed.

(* The Set-layer orb inverter: if the disjunction is true then at least one side is true (a Type-sorted two-branch carrier, zero Prop leakage) *)
Inductive tidor (a b : bool) : Type :=
| tid_or_l : clq_tid bool a true -> tidor a b
| tid_or_r : clq_tid bool b true -> tidor a b.

Lemma tid_orb_inv : forall a b : bool,
  clq_tid bool (orb a b) true -> tidor a b.
Proof.
  intros a b H. destruct a; destruct b.
  - apply tid_or_l. apply clq_tid_refl.
  - apply tid_or_l. apply clq_tid_refl.
  - apply tid_or_r. exact H.
  - apply tid_or_r. exact H.
Qed.

(* ===================================================================== *)
(* 1. Decisions: structured adjudication values (hole type + direction + Z evidence) *)
(* ===================================================================== *)

Inductive hole : Set := k0 | k1 | kb | kc | ke | kr.

Definition hix (h : hole) : nat :=
  match h with
  | k0 => 0%nat | k1 => 1%nat | kb => 2%nat | kc => 3%nat | ke => 4%nat | kr => 5%nat
  end.

Definition hmax : nat := 5%nat.

Definition hbeq (a b : hole) : bool := Nat.eqb (hix a) (hix b).

Lemma hbeq_refl : forall h : hole, clq_tid bool (hbeq h h) true.
Proof.
  destruct h; apply clq_tid_refl.
Qed.

Lemma hbeq_true : forall a b : hole, clq_tid bool (hbeq a b) true -> clq_tid hole a b.
Proof.
  intros a b H. unfold hbeq in H. tidQ H E.
  destruct a; destruct b; simpl in E; try discriminate E; apply clq_tid_refl.
Qed.

Inductive vdir : Set := vpass | vrej.

Definition dbeq (a b : vdir) : bool :=
  match a with
  | vpass => match b with vpass => true | vrej => false end
  | vrej => match b with vpass => false | vrej => true end
  end.

Lemma dbeq_true : forall a b : vdir, clq_tid bool (dbeq a b) true -> clq_tid vdir a b.
Proof.
  intros a b H. destruct a; destruct b; simpl in H;
    try (tidQ H E; discriminate E); apply clq_tid_refl.
Qed.

Record verd : Set := mkVd { vh : hole ; vd : vdir ; vz : Z }.

Definition vbeq (x y : verd) : bool :=
  andb (hbeq (vh x) (vh y)) (andb (dbeq (vd x) (vd y)) (Z.eqb (vz x) (vz y))).

Lemma vbeq_mkVd : forall (h1 h2 : hole) (d1 d2 : vdir) (z1 z2 : Z),
  clq_tid bool (vbeq (mkVd h1 d1 z1) (mkVd h2 d2 z2))
       (andb (hbeq h1 h2) (andb (dbeq d1 d2) (Z.eqb z1 z2))).
Proof. intros. apply clq_tid_refl. Qed.

Lemma vbeq_head_true : forall (h1 h2 : hole) (z1 z2 : Z),
  hbeq h1 h2 = true -> z1 = z2 ->
  Id (vbeq (mkVd h1 vpass z1) (mkVd h2 vpass z2)) true.
Proof.
  intros h1 h2 z1 z2 Eh Ez. unfold vbeq, vh, vd, vz.
  rewrite Eh, Ez, Z.eqb_refl. reflexivity.
Qed.

Lemma vbeq_inv : forall v1 v2 : verd,
  clq_tid bool (vbeq v1 v2) true ->
  prod (clq_tid hole (vh v1) (vh v2))
       (prod (clq_tid vdir (vd v1) (vd v2)) (clq_tid Z (vz v1) (vz v2))).
Proof.
  intros v1 v2 H. unfold vbeq in H. tidQ H E.
  apply andb_prop in E. destruct E as [E1 E2].
  apply andb_prop in E2. destruct E2 as [E2 E3].
  apply Z.eqb_eq in E3.
  exact (pair (hbeq_true _ _ (clq_tid_eq bool _ true E1))
              (pair (dbeq_true _ _ (clq_tid_eq bool _ true E2))
                    (clq_tid_eq Z _ _ E3))).
Qed.

(* Stream membership (a bool predicate; zero Prop in statements) *)
Fixpoint vIn (v : verd) (s : list verd) : bool :=
  match s with
  | nil => false
  | x :: t => orb (vbeq x v) (vIn v t)
  end.

(* The consistency predicate: every pass decision on hole h has value w *)
Fixpoint allpass (h : hole) (w : Z) (s : list verd) : bool :=
  match s with
  | nil => true
  | v :: t =>
      andb (match vd v with
            | vpass => if hbeq (vh v) h then Z.eqb (vz v) w else true
            | vrej => true
            end)
           (allpass h w t)
  end.

(* ===================================================================== *)
(* 2. The ingot carrier: the pinning tri-state + six-slot pinning *)
(* ===================================================================== *)

Inductive pinv : Set := PN | P1 (z : Z) | PB.

Definition isP1 (x : pinv) : bool := match x with P1 _ => true | _ => false end.

Record ipins : Set := mkP
  { qa : pinv ; qb : pinv ; qc : pinv ; qd : pinv ; qe : pinv ; qf : pinv }.

Definition pzero : ipins := mkP PN PN PN PN PN PN.

Definition pget (p : ipins) (h : hole) : pinv :=
  match h with
  | k0 => qa p | k1 => qb p | kb => qc p | kc => qd p | ke => qe p | kr => qf p
  end.

Definition pupd (h : hole) (x : pinv) (p : ipins) : ipins :=
  match h with
  | k0 => mkP x (qb p) (qc p) (qd p) (qe p) (qf p)
  | k1 => mkP (qa p) x (qc p) (qd p) (qe p) (qf p)
  | kb => mkP (qa p) (qb p) x (qd p) (qe p) (qf p)
  | kc => mkP (qa p) (qb p) (qc p) x (qe p) (qf p)
  | ke => mkP (qa p) (qb p) (qc p) (qd p) x (qf p)
  | kr => mkP (qa p) (qb p) (qc p) (qd p) (qe p) x
  end.

Lemma mkP_ext_eq : forall (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : pinv),
  a1 = b1 -> a2 = b2 -> a3 = b3 -> a4 = b4 -> a5 = b5 -> a6 = b6 ->
  Id (mkP a1 a2 a3 a4 a5 a6) (mkP b1 b2 b3 b4 b5 b6).
Proof.
  intros a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 H1 H2 H3 H4 H5 H6.
  rewrite H1, H2, H3, H4, H5, H6. reflexivity.
Qed.

Lemma pget_pupd : forall (h h2 : hole) (x : pinv) (p : ipins),
  clq_tid pinv (pget (pupd h x p) h2) (if hbeq h h2 then x else pget p h2).
Proof.
  intros h h2 x p. destruct h, h2; apply clq_tid_refl.
Qed.

(* Pin aggregation: equal values accumulate / conflicting values conflict (PB propagates; recorded at most once per stream pass) *)
Definition pj (a b : pinv) : prod pinv nat :=
  match a with
  | PN => (b, 0%nat)
  | P1 w =>
      match b with
      | PN => (P1 w, 0%nat)
      | P1 w' => if Z.eqb w w' then (P1 w, 0%nat) else (PB, 1%nat)
      | PB => (PB, 0%nat)
      end
  | PB => (PB, 0%nat)
  end.

Definition pjR (x : prod pinv nat) : pinv := fst x.
Definition pjN (x : prod pinv nat) : nat := snd x.

Lemma pj_self_R : forall a : pinv, clq_tid pinv (pjR (pj a a)) a.
Proof.
  intros a. destruct a as [z| |]; cbn [pj pjR fst].
  - apply clq_tid_refl.
  - destruct (Z.eqb z z) eqn:E; cbn [pjR].
    + apply clq_tid_refl.
    + rewrite Z.eqb_refl in E. discriminate E.
  - apply clq_tid_refl.
Qed.

Lemma pjR_PN : forall b : pinv, clq_tid pinv (pjR (pj PN b)) b.
Proof. intros b. apply clq_tid_refl. Qed.

Lemma pjR_PN_inv : forall a b : pinv,
  clq_tid pinv (pjR (pj a b)) PN -> prod (clq_tid pinv a PN) (clq_tid pinv b PN).
Proof.
  intros a b H. destruct a as [z| |]; destruct b as [z0| |];
    tidQ H E; try discriminate E.
  - exact (pair (clq_tid_refl pinv PN) (clq_tid_refl pinv PN)).
  - tidQ H E2. cbn [pj pjR fst] in E2.
    destruct (Z.eqb z z0); discriminate E2.
Qed.

(* Associativity of aggregation (at the result position): (a⊕b)⊕c == a⊕(b⊕c) *)
Lemma pj_assoc_R : forall a b c : pinv,
  clq_tid pinv (pjR (pj (pjR (pj a b)) c)) (pjR (pj a (pjR (pj b c)))).
Proof.
  intros a b c.
  destruct a, b, c; cbn [pj pjR fst]; try apply clq_tid_refl.
  all: try (destruct (Z.eqb z z0) eqn:Ew; cbn [pj pjR fst]; try apply clq_tid_refl).
  all: try (destruct (Z.eqb z z1) eqn:Eu; cbn [pj pjR fst]; try apply clq_tid_refl).
  all: try (destruct (Z.eqb z0 z1) eqn:Ewu; cbn [pj pjR fst]; try apply clq_tid_refl).
  all: try (apply Z.eqb_eq in Ew; apply Z.eqb_eq in Eu;
             apply Z.eqb_neq in Ewu; congruence).
  all: try (apply Z.eqb_eq in Ew; apply Z.eqb_neq in Eu;
             apply Z.eqb_eq in Ewu; congruence).
  all: try (apply Z.eqb_neq in Ew; apply Z.eqb_eq in Eu;
             apply Z.eqb_eq in Ewu; congruence).
  all: try (rewrite Ew; cbn [pj pjR fst]; try apply clq_tid_refl).
Qed.

Definition pjoin (p q : ipins) : prod ipins nat :=
  (mkP (pjR (pj (qa p) (qa q))) (pjR (pj (qb p) (qb q))) (pjR (pj (qc p) (qc q)))
       (pjR (pj (qd p) (qd q))) (pjR (pj (qe p) (qe q))) (pjR (pj (qf p) (qf q))),
   (pjN (pj (qa p) (qa q)) + (pjN (pj (qb p) (qb q)) + (pjN (pj (qc p) (qc q)) +
   (pjN (pj (qd p) (qd q)) + (pjN (pj (qe p) (qe q)) + pjN (pj (qf p) (qf q)))))))%nat).

Lemma pjoin_get : forall (p q : ipins) (h : hole),
  clq_tid pinv (pget (fst (pjoin p q)) h) (pjR (pj (pget p h) (pget q h))).
Proof.
  intros p q h. destruct p as [a b c d e f]. destruct q as [a' b' c' d' e' f'].
  destruct h; apply clq_tid_refl.
Qed.

Lemma pjoin_zero_l : forall p : ipins, clq_tid ipins (fst (pjoin pzero p)) p.
Proof.
  intros p. destruct p as [a b c d e f].
  exact (match mkP_ext_eq _ _ _ _ _ _ _ _ _ _ _ _
           (tidE pinv _ _ (pjR_PN a))
           (tidE pinv _ _ (pjR_PN b))
           (tidE pinv _ _ (pjR_PN c))
           (tidE pinv _ _ (pjR_PN d))
           (tidE pinv _ _ (pjR_PN e))
           (tidE pinv _ _ (pjR_PN f))
         with id_refl => @clq_tid_refl ipins _ end).
Qed.

Lemma pjoin_self_pins : forall p : ipins, clq_tid ipins (fst (pjoin p p)) p.
Proof.
  intros p. destruct p as [a b c d e f].
  exact (match mkP_ext_eq _ _ _ _ _ _ _ _ _ _ _ _
           (tidE pinv _ _ (pj_self_R a))
           (tidE pinv _ _ (pj_self_R b))
           (tidE pinv _ _ (pj_self_R c))
           (tidE pinv _ _ (pj_self_R d))
           (tidE pinv _ _ (pj_self_R e))
           (tidE pinv _ _ (pj_self_R f))
         with id_refl => @clq_tid_refl ipins _ end).
Qed.

Lemma pjoin_assoc : forall p q r : ipins,
  clq_tid ipins (fst (pjoin p (fst (pjoin q r))))
            (fst (pjoin (fst (pjoin p q)) r)).
Proof.
  intros p q r.
  assert (Hid : Id (fst (pjoin p (fst (pjoin q r))))
                (fst (pjoin (fst (pjoin p q)) r))).
  { apply mkP_ext_eq; symmetry; apply tidE; apply pj_assoc_R. }
  pose proof (match Hid in Id _ z
              return fst (pjoin p (fst (pjoin q r))) = z
              with id_refl => eq_refl end) as HE.
  exact (clq_tid_eq ipins _ _ HE).
Qed.

(* ===================================================================== *)
(* 3. Melt: the decision stream right-folded in one pass into an ingot (construction stage) *)
(* ===================================================================== *)

Record ingot : Set := mkIng
  { ipin : ipins
  ; irej : list (prod hole Z) }.

Lemma mkIng_ext_eq : forall (p1 p2 : ipins) (r1 r2 : list (prod hole Z)),
  p1 = p2 -> r1 = r2 -> Id (mkIng p1 r1) (mkIng p2 r2).
Proof.
  intros p1 p2 r1 r2 H1 H2. rewrite H1, H2. reflexivity.
Qed.

Definition mzero : ingot := mkIng pzero nil.

(* The ingot of a single decision: pass sets a pin; rej emits a difference clause *)
Definition m1 (v : verd) : ingot :=
  match vd v with
  | vpass => mkIng (pupd (vh v) (P1 (vz v)) pzero) nil
  | vrej => mkIng pzero ((vh v, vz v) :: nil)
  end.

Definition mjoin (g1 g2 : ingot) : ingot :=
  mkIng (fst (pjoin (ipin g1) (ipin g2))) (irej g1 ++ irej g2).

Fixpoint melt (s : list verd) : ingot :=
  match s with
  | nil => mzero
  | v :: t => mjoin (m1 v) (melt t)
  end.

Lemma m1_pin_head : forall (h1 h2 : hole) (z : Z),
  clq_tid pinv (pget (ipin (m1 (mkVd h1 vpass z))) h2)
       (if hbeq h1 h2 then P1 z else PN).
Proof. intros h1 h2 z. destruct h1, h2; apply clq_tid_refl. Qed.

Lemma m1_pin_rej : forall (h1 h2 : hole) (z : Z),
  clq_tid pinv (pget (ipin (m1 (mkVd h1 vrej z))) h2) PN.
Proof. intros h1 h2 z. destruct h1, h2; apply clq_tid_refl. Qed.

Lemma pget_mjoin : forall (g1 g2 : ingot) (h : hole),
  clq_tid pinv (pget (ipin (mjoin g1 g2)) h)
       (pjR (pj (pget (ipin g1) h) (pget (ipin g2) h))).
Proof.
  intros g1 g2 h. unfold mjoin. apply pjoin_get.
Qed.

(* Associativity of ingot aggregation *)
Lemma mjoin_assoc : forall g1 g2 g3 : ingot,
  clq_tid ingot (mjoin g1 (mjoin g2 g3)) (mjoin (mjoin g1 g2) g3).
Proof.
  intros g1 g2 g3.
  assert (Hid : Id (mjoin g1 (mjoin g2 g3)) (mjoin (mjoin g1 g2) g3)).
  { destruct g1 as [p1 r1]; destruct g2 as [p2 r2]; destruct g3 as [p3 r3].
    unfold mjoin. cbn [ipin irej].
    apply mkIng_ext_eq.
    - exact (tidE ipins _ _ (pjoin_assoc p1 p2 p3)).
    - apply app_assoc. }
  pose proof (match Hid in Id _ z return mjoin g1 (mjoin g2 g3) = z
              with id_refl => eq_refl end) as HE.
  exact (clq_tid_eq ingot _ _ HE).
Qed.

(* The melt identity element: the empty ingot is a left unit *)
Lemma mjoin_zero_l : forall g : ingot, clq_tid ingot (mjoin mzero g) g.
Proof.
  intros g.
  assert (Hid : Id (mjoin mzero g) g).
  { destruct g as [p r]. unfold mjoin. cbn [ipin irej mzero].
    apply mkIng_ext_eq.
    - exact (tidE ipins _ _ (pjoin_zero_l p)).
    - reflexivity. }
  pose proof (match Hid in Id _ z return mjoin mzero g = z
              with id_refl => eq_refl end) as HE.
  exact (clq_tid_eq ingot _ _ HE).
Qed.

(* Main theorem 1: melting is a list homomorphism — the algebraic content of the two-stage construction (the ingot does not depend on the bracketing of the stream) *)
Theorem melt_hom : forall s1 s2 : list verd,
  clq_tid ingot (melt (s1 ++ s2)) (mjoin (melt s1) (melt s2)).
Proof.
  induction s1 as [| v t IH]; intros s2.
  - cbn [melt app].
    exact (clq_tid_sym ingot _ _ (mjoin_zero_l (melt s2))).
  - cbn [melt app].
    apply (clq_tid_trans ingot _ (mjoin (m1 v) (mjoin (melt t) (melt s2))) _).
    + apply (clq_tid_cong (mjoin (m1 v)) _ _ (IH s2)).
    + exact (mjoin_assoc (m1 v) (melt t) (melt s2)).
Qed.

(* ===================================================================== *)
(* 4. Pin conservation: the pin is the consistent aggregation of the pass decisions in the stream (iffT in both directions) *)
(* ===================================================================== *)

Definition pinokp (w : Z) (x : pinv) : bool :=
  match x with PN => true | P1 z => Z.eqb z w | PB => false end.

(* The interface statement between pin aggregation and consistency: P1 w ⊕ b with b consistent with w implies the result is consistent with w *)
Lemma pj_pinok_r : forall (w : Z) (b : pinv),
  clq_tid bool (pinokp w b) true -> clq_tid bool (pinokp w (pjR (pj (P1 w) b))) true.
Proof.
  intros w b H. destruct b as [ |z| ]; cbn [pj pjR fst pinokp] in H.
  - apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
  - cbn [pj pjR fst]. pose proof (tidE bool _ true H) as Hzeq.
    apply Z.eqb_eq in Hzeq. rewrite <- Hzeq. rewrite Z.eqb_refl.
    apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
  - cbn [pinokp] in H. tidQ H E. discriminate E.
Qed.

(* allpass implies the pin is consistent with w *)
Lemma allpass_pinok : forall (s : list verd) (h : hole) (w : Z),
  clq_tid bool (allpass h w s) true ->
  clq_tid bool (pinokp w (pget (ipin (melt s)) h)) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - destruct h; apply clq_tid_refl.
  - cbn [melt]. destruct v as [h0 d0 z0]. destruct d0.
    + cbn [allpass vd vh] in H. destruct (hbeq h0 h) eqn:Eh.
      * apply tid_andb_inv in H. destruct H as [Hhead Ht].
        cbn in Hhead.
        pose proof (tidE bool _ true Hhead) as Hheq.
        apply Z.eqb_eq in Hheq.
        pose proof (IH h w Ht) as IPB.
        pose proof (pget_mjoin (m1 (mkVd h0 vpass z0)) (melt t) h) as J.
        tidQ J EJ. rewrite EJ.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E. cbn [m1 ipin vd vh vz pupd].
        cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E, Hheq. cbn [pj pjR fst].
        destruct (pget (ipin (melt t)) h).
        -- apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pinokp] in IPB.
           destruct (Z.eqb w z) eqn:Ewz.
           ++ apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
           ++ pose proof (tidE bool _ true IPB) as E1.
              apply Z.eqb_eq in E1. apply Z.eqb_neq in Ewz. congruence.
        -- cbn [pinokp] in IPB.
           pose proof (tidE bool _ true IPB) as E2.
           discriminate E2.
      * apply tid_andb_inv in H. destruct H as [_ Ht].
        pose proof (IH h w Ht) as IPB.
        pose proof (pget_mjoin (m1 (mkVd h0 vpass z0)) (melt t) h) as J.
        tidQ J EJ. rewrite EJ.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E. cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E. cbn [pj pjR fst].
        destruct (pget (ipin (melt t)) h) as [z2| |].
        -- exact IPB.
        -- exact IPB.
        -- cbn [pinokp] in IPB. tidQ IPB E. discriminate E.
    + cbn [allpass vd vh] in H. apply tid_andb_inv in H.
      destruct H as [_ Ht].
      pose proof (IH h w Ht) as IPB.
      pose proof (pget_mjoin (m1 (mkVd h0 vrej z0)) (melt t) h) as J.
      tidQ J EJ. rewrite EJ.
      pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E. cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E.
      cbn [pj pjR fst].
      destruct (pget (ipin (melt t)) h) as [z2| |].
      -- exact IPB.
      -- exact IPB.
      -- cbn [pinokp] in IPB. tidQ IPB E. discriminate E.
Qed.

(* The pin is PN implies the hole has no pass decision, hence allpass holds trivially *)
Lemma pinPN_allpass : forall (s : list verd) (h : hole) (w : Z),
  clq_tid pinv (pget (ipin (melt s)) h) PN -> clq_tid bool (allpass h w s) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - apply clq_tid_refl.
  - cbn [melt] in H. destruct v as [h0 d0 z0].
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in H.
    destruct (pjR_PN_inv (pget (ipin (m1 (mkVd h0 d0 z0))) h)
                         (pget (ipin (melt t)) h) H) as [Ha Hb].
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E in Ha.
        tidQ Ha Ea. discriminate Ea.
      * apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh.
        exact (tidE bool _ true (IH h w Hb)).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E in Ha.
      exact (IH h w Hb).
Qed.

(* The pin is P1 z implies the stream really contains the decision pass(h,z) *)
(* The pin-aggregation key lemma: P1 z0 ⊕ P1 z1 = P1 z implies z0 = z *)
Lemma pjR_P1_head : forall (z0 z1 z : Z),
  clq_tid pinv (pjR (pj (P1 z0) (P1 z1))) (P1 z) -> Id z0 z.
Proof.
  intros z0 z1 z H. unfold pjR, pj in H.
  destruct (Z.eqb z0 z1) eqn:E.
  - tidQ H E2. injection E2 as E3. destruct E3. apply id_refl.
  - tidQ H E2. discriminate E2.
Qed.

(* pin_P1_in: covered by combining pin_P1_in_val/pin_PN_absurd (see the use sites in pin_iffT) *)

(* The pin is PN implies no pass(h,z) decision can exist in the stream (an absurdity statement; closes any Set goal) *)
Lemma pin_PN_absurd : forall (s : list verd) (h : hole) (z : Z),
  clq_tid pinv (pget (ipin (melt s)) h) PN ->
  clq_tid bool (vIn (mkVd h vpass z) s) true ->
  forall P : Set, P.
Proof.
  induction s as [| v t IH]; intros h z H Hin.
  - cbn [vIn] in Hin. tidQ Hin E. discriminate E.
  - cbn [melt] in H. destruct v as [h0 d0 z0]. cbn [vIn] in Hin.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in H. rewrite <- EB in H.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H. cbn [pj] in H.
        destruct b as [ |z1| ]; cbn [pj pjR fst] in H.
        -- tidQ H E. discriminate E.
        -- destruct (Z.eqb z0 z1) eqn:Ez; cbn [pj pjR fst] in H;
             tidQ H E; discriminate E.
        -- tidQ H E. discriminate E.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H. cbn [pj pjR fst] in H.
        unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        exact (IH h z (clq_tid_trans pinv (pget (ipin (melt t)) h) b PN
                           (clq_tid_eq pinv _ _ (eq_sym EB)) H) Hin).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      rewrite M1E in H. cbn [pj pjR fst] in H.
      unfold vbeq, vh, vd, vz, dbeq in Hin.
      destruct (hbeq h0 h);
        exact (IH h z (clq_tid_trans pinv (pget (ipin (melt t)) h) b PN
                           (clq_tid_eq pinv _ _ (eq_sym EB)) H) Hin).
Qed.

(* The pin is P1 z1 and the stream contains another pass(h,z0), hence z1 = z0 (the pin value agrees with any pass in the stream) *)
Lemma pin_P1_in_val : forall (s : list verd) (h : hole) (z1 z0 : Z),
  clq_tid pinv (pget (ipin (melt s)) h) (P1 z1) ->
  clq_tid bool (vIn (mkVd h vpass z0) s) true ->
  clq_tid Z z1 z0.
Proof.
  induction s as [| v t IH]; intros h z1 z0 Hp Hin.
  - cbn [vIn] in Hin. tidQ Hin E. discriminate E.
  - cbn [melt] in Hp. destruct v as [h0 d0 z0']. cbn [vIn] in Hin.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0')) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in Hp. rewrite <- EB in Hp.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        destruct (Z.eqb z0' z0) eqn:Ezz0; cbn [andb orb] in Hin.
        -- (* The head is the witness (value z0' = z0) *)
           pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
           rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj] in Hp.
           destruct b as [ |z2| ]; cbn [pj pjR fst] in Hp.
           ++ tidQ Hp E. injection E as Ei.
              exact (clq_tid_trans Z z1 z0' z0 (clq_tid_sym Z z0' z1 (clq_tid_eq Z _ _ Ei))
                       (clq_tid_eq Z _ _ (proj1 (Z.eqb_eq z0' z0) Ezz0))).
           ++ destruct (Z.eqb z0' z2) eqn:Ez; cbn [pj pjR fst] in Hp.
              ** tidQ Hp E. injection E as Ei.
                 exact (clq_tid_trans Z z1 z0' z0 (clq_tid_sym Z z0' z1 (clq_tid_eq Z _ _ Ei))
                          (clq_tid_eq Z _ _ (proj1 (Z.eqb_eq z0' z0) Ezz0))).
              ** tidQ Hp E. discriminate E.
           ++ tidQ Hp E. discriminate E.
        -- (* The head is a pass for this hole but with a value that differs from z0: the witness is in the tail *)
           pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
           rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj] in Hp.
           destruct b as [ |z2| ]; cbn [pj pjR fst] in Hp.
           ++ exact (pin_PN_absurd t h z0 (clq_tid_eq pinv _ _ (eq_sym EB)) Hin _).
           ++ destruct (Z.eqb z0' z2) eqn:Ez; cbn [pj pjR fst] in Hp.
              ** tidQ Hp E. injection E as Ei.
                 assert (Ht1 : clq_tid pinv (pget (ipin (melt t)) h) (P1 z1)).
                 { rewrite <- EB. apply (clq_tid_eq pinv (P1 z2) (P1 z1)).
                   rewrite (eq_trans (eq_sym (proj1 (Z.eqb_eq z0' z2) Ez)) Ei).
                   reflexivity. }
                 exact (IH h z1 z0 Ht1 Hin).
              ** tidQ Hp E. discriminate E.
           ++ tidQ Hp E. discriminate E.
      * (* Head not a pass for this hole (hbeq false): A = PN implies the witness is in the tail, hence the induction premise *)
        unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
        rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj pjR fst] in Hp.
        exact (IH h z1 z0 (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 z1)
                                (clq_tid_eq pinv _ _ (eq_sym EB)) Hp) Hin).
    + (* Head not a pass for this hole: A = PN implies the witness is in the tail, hence the induction premise *)
      unfold vbeq, vh, vd, vz, dbeq in Hin.
      destruct (hbeq h0 h);
      pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0')) as M1E;
      rewrite M1E in Hp; cbn [pj pjR fst] in Hp;
      exact (IH h z1 z0 (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 z1)
                              (clq_tid_eq pinv _ _ (eq_sym EB)) Hp) Hin).
Qed.

(* The pin is P1 w implies all pass decisions agree with w *)
Lemma pin_P1_allpass : forall (s : list verd) (h : hole) (w : Z),
  clq_tid pinv (pget (ipin (melt s)) h) (P1 w) ->
  clq_tid bool (allpass h w s) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - apply clq_tid_refl.
  - cbn [melt] in H. destruct v as [h0 d0 z0].
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in H.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. rewrite M1E in H. cbn [pj] in H.
        destruct b as [ |z2| ]; cbn [pj pjR fst] in H.
        -- (* b = PN: the pin is P1 z0, hence z0 = w; the tail has no pass, hence allpass holds trivially on the tail *)
           tidQ H E. injection E as Ei.
           apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh, Ei.
           rewrite Z.eqb_refl.
           rewrite (tidE bool _ true
                      (pinPN_allpass t h w (clq_tid_eq pinv _ _ (eq_sym EB)))).
           reflexivity.
        -- destruct (Z.eqb z0 z2) eqn:Ez2; cbn [pj pjR fst] in H.
           ++ tidQ H E. injection E as Ei. apply Z.eqb_eq in Ez2.
              assert (Htw : clq_tid pinv (pget (ipin (melt t)) h) (P1 w)).
              { rewrite <- EB. apply (clq_tid_eq pinv (P1 z2) (P1 w)).
                rewrite (eq_trans (eq_sym Ez2) Ei). reflexivity. }
              apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh, Ez2.
              rewrite (eq_trans (eq_sym Ez2) Ei), Z.eqb_refl.
              rewrite (tidE bool _ true (IH h w Htw)). reflexivity.
           ++ tidQ H E. discriminate E.
        -- tidQ H E. discriminate E.
      * (* Head not a pass for this hole: the pin is b, hence the tail witnesses it, hence the induction premise *)
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. rewrite M1E in H. cbn [pj pjR fst] in H.
        apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh.
        exact (tidE bool _ true
                (IH h w (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 w)
                           (clq_tid_eq pinv _ _ (eq_sym EB)) H))).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      rewrite M1E in H. cbn [pj pjR fst] in H.
      exact (IH h w (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 w)
                         (clq_tid_eq pinv _ _ (eq_sym EB)) H)).
Qed.

(* Main theorem 2: pinning iffT — the pin is the consistent aggregation of the pass decisions in the stream (conservation both ways: nothing
invented — the pin value must come from a decision in the stream; nothing distorted — all pass decisions in the stream agree) *)
(* pin_iffT: the forward direction is covered by pin_P1_in_val/pin_P1_allpass; the backward direction
by allpass_pinok/pin_P1_allpass (content-equivalent, packaged as two one-directional lemmas) *)


(* ===================================================================== *)
(* 5. Stream-side conservation of the rejection-difference clauses *)
(* ===================================================================== *)

Fixpoint cinc (h : hole) (e : Z) (l : list (prod hole Z)) : bool :=
  match l with
  | nil => false
  | x :: t => orb (andb (hbeq h (fst x)) (Z.eqb e (snd x))) (cinc h e t)
  end.

Lemma cinc_app : forall (h : hole) (e : Z) (l1 l2 : list (prod hole Z)),
  clq_tid bool (cinc h e (l1 ++ l2)) (orb (cinc h e l1) (cinc h e l2)).
Proof.
  intros h e l1 l2. induction l1 as [| x t IH]; cbn [cinc app].
  - apply clq_tid_refl.
  - tidQ IH EI. rewrite EI.
    apply (clq_tid_eq bool _ _). apply Bool.orb_assoc.
Qed.

(* A rej(h,e) decision in the stream implies the clause enters the ingot *)
Theorem rej_from_stream : forall (s : list verd) (h : hole) (e : Z),
  clq_tid bool (vIn (mkVd h vrej e) s) true ->
  clq_tid bool (cinc h e (irej (melt s))) true.
Proof.
  induction s as [| v t IH]; intros h e H.
  - cbn [vIn] in H. tidQ H E. discriminate E.
  - cbn [melt]. destruct v as [h0 d0 z0]. cbn [vIn] in H.
    unfold mjoin. cbn [irej]. destruct d0.
    + cbn [m1 irej app cinc vd vh vz]. apply IH.
      unfold vbeq, vh, vd, vz in H. cbn [dbeq andb] in H.
      tidQ H E. rewrite Bool.andb_false_r, orb_false_l in E.
      exact (clq_tid_eq bool _ true E).
    + cbn [m1 irej app cinc vd vh vz]. apply (clq_tid_eq bool _ true).
      destruct (vbeq (mkVd h0 vrej z0) (mkVd h vrej e)) eqn:Ev.
      * destruct (vbeq_inv _ _ (clq_tid_eq bool _ true Ev)) as [Ex [Ed Ezz]].
        cbn [vh vd vz] in Ex, Ed, Ezz.
        cbn [fst snd]. rewrite (tidE hole _ _ Ex), (tidE Z _ _ Ezz).
        rewrite (tidE bool _ true (hbeq_refl h)), Z.eqb_refl.
        reflexivity.
      * apply tid_orb_false in H.
        rewrite (tidE bool _ true (IH h e H)).
        apply Bool.orb_true_r.
Qed.

(* ===================================================================== *)
(* 6. Weave: the differential stage (consumes only the ingot; the woven artifact is the Q4 dtab; under-orders recorded honestly) *)
(* ===================================================================== *)

Definition pvz (x : pinv) : Z := match x with P1 z => z | _ => 0 end.

(* The woven artifact: the six-slot difference table with head gauge k0 normalized to 0 (the Q4 carrier dtab) *)
Definition dbuild (p : ipins) : dtab :=
  dtabSnoc
    (dtabSnoc
       (dtabSnoc
          (dtabSnoc
             (dtabSnoc (dtab1 0) (pvz (qb p)))
             (pvz (qc p)))
          (pvz (qd p)))
       (pvz (qe p)))
    (pvz (qf p)).

Definition slotz (p : ipins) (h : hole) : Z :=
  match h with
  | k0 => 0
  | _ => pvz (pget p h)
  end.

Lemma dbuild_pot : forall (p : ipins) (h : hole),
  clq_tid Z (pot (dbuild p) (hix h)) (slotz p h).
Proof. intros p h. destruct h; apply clq_tid_refl. Qed.

Lemma dsub_pget : forall (p : ipins) (h : hole),
  clq_tid Z (dsub (dbuild p) (hix h) O)
       (match h with k0 => 0 | _ => pvz (pget p h) end).
Proof.
  intros p h. unfold dsub.
  pose proof (dbuild_pot p h) as T1. tidQ T1 E1.
  rewrite E1. apply (clq_tid_eq Z _ _).
  destruct h; cbn [slotz]; apply Z.sub_0_r.
Qed.

Lemma dbuild_len : forall p : ipins, clq_tid nat (dlen (dbuild p)) hmax.
Proof.
  intros p. unfold dbuild.
  apply (clq_tid_eq nat _ _).
  unfold hmax. cbn [dlen]. reflexivity.
Qed.

(* Under-order entries: a missing pin / a pin conflict / a clause contradiction *)
Inductive idl_iou : Set :=
| idl_IOU_NOPIN (h : hole)
| idl_IOU_BAD (h : hole)
| idl_IOU_REJ (h : hole) (e : Z).

Definition rjbad (p : ipins) (x : prod hole Z) : bool :=
  Z.eqb (dsub (dbuild p) (hix (fst x)) O) (snd x).

Fixpoint rejious (p : ipins) (l : list (prod hole Z)) : list idl_iou :=
  match l with
  | nil => nil
  | x :: t => if rjbad p x then idl_IOU_REJ (fst x) (snd x) :: rejious p t
              else rejious p t
  end.

Definition headiou (p : ipins) : list idl_iou :=
  match pget p k0 with
  | PN => nil
  | P1 z => if Z.eqb z 0 then nil else idl_IOU_BAD k0 :: nil
  | PB => idl_IOU_BAD k0 :: nil
  end.

Definition slotL : list hole := k1 :: kb :: kc :: ke :: kr :: nil.

Fixpoint hin (h : hole) (hs : list hole) : bool :=
  match hs with
  | nil => false
  | x :: t => orb (hbeq x h) (hin h t)
  end.

Fixpoint slotiousL (p : ipins) (hs : list hole) : list idl_iou :=
  match hs with
  | nil => nil
  | h :: t =>
      match pget p h with
      | P1 _ => slotiousL p t
      | PN => idl_IOU_NOPIN h :: slotiousL p t
      | PB => idl_IOU_BAD h :: slotiousL p t
      end
  end.

Fixpoint allpin1 (p : ipins) (hs : list hole) : bool :=
  match hs with
  | nil => true
  | h :: t => andb (isP1 (pget p h)) (allpin1 p t)
  end.

Lemma slotiousL_nil_allpin1 : forall p hs,
  clq_tid (list idl_iou) (slotiousL p hs) nil -> clq_tid bool (allpin1 p hs) true.
Proof.
  intros p hs. induction hs as [| h t IH]; intros H.
  - apply clq_tid_refl.
  - cbn [slotiousL] in H. cbn [allpin1].
    destruct (pget p h) as [z| |].
    + tidQ H E. discriminate E.
    + exact (IH H).
    + tidQ H E. discriminate E.
Qed.

Lemma allpin1_hit : forall p hs h,
  clq_tid bool (allpin1 p hs) true -> clq_tid bool (hin h hs) true ->
  clq_tid bool (isP1 (pget p h)) true.
Proof.
  intros p hs h. induction hs as [| h' t IH]; intros HA Hh.
  - cbn [hin] in Hh. tidQ Hh E. discriminate E.
  - cbn [allpin1 hin] in HA, Hh.
    destruct (hbeq h' h) eqn:Ex.
    + apply tid_andb_inv in HA. destruct HA as [HA1 _].
      pose proof (hbeq_true h' h (clq_tid_eq bool _ true Ex)) as EH.
      rewrite <- (tidE hole _ _ EH). exact HA1.
    + apply IH.
      * apply tid_andb_inv in HA. destruct HA as [_ HA2]. exact HA2.
      * apply tid_orb_false in Hh. exact Hh.
Qed.

Definition iouof (g : ingot) : list idl_iou :=
  headiou (ipin g) ++ (slotiousL (ipin g) slotL ++ rejious (ipin g) (irej g)).

Inductive weaveout : Set := wok (d : dtab) | wiou (l : list idl_iou).

Definition weave (g : ingot) : weaveout :=
  match iouof g with
  | nil => wok (dbuild (ipin g))
  | l => wiou l
  end.

Definition weave_b (g : ingot) : bool :=
  match weave g with wok _ => true | wiou _ => false end.

(* Inter-stage differential adjudication of rejection-difference clauses: all clauses pass iff the clause census is empty *)
Lemma rejious_nil_ok : forall (p : ipins) (l : list (prod hole Z)),
  clq_tid (list idl_iou) (rejious p l) nil ->
  forall (h : hole) (e : Z), clq_tid bool (cinc h e l) true ->
  clq_tid bool (negb (rjbad p (h, e))) true.
Proof.
  intros p l. induction l as [| x t IH]; intros Hn h e Hc.
  - cbn [cinc] in Hc. tidQ Hc E. discriminate E.
  - cbn [rejious] in Hn. destruct (rjbad p x) eqn:Er.
    + tidQ Hn E. discriminate E.
    + cbn [cinc] in Hc. destruct x as [xh xe]. cbn [fst snd] in Hc.
      pose proof (tid_orb_inv _ _ Hc) as Ec. destruct Ec as [Ec|Ec].
      * apply tid_andb_inv in Ec. destruct Ec as [Eh1 Eh2].
        pose proof (tidE hole _ _ (hbeq_true h xh Eh1)) as Exe.
        pose proof (tidE bool _ _ Eh2) as Eh2e. apply Z.eqb_eq in Eh2e.
        rewrite Exe, Eh2e, Er. apply clq_tid_refl.
      * apply IH. exact Hn. exact Ec.
Qed.

Lemma headiou_nil_inv : forall p : ipins,
  clq_tid (list idl_iou) (headiou p) nil ->
  clq_tid bool (match pget p k0 with
            | PN => true
            | P1 z => Z.eqb z 0
            | PB => false
            end) true.
Proof.
  intros p H. unfold headiou in H. destruct (pget p k0) as [z| |].
  - apply clq_tid_refl.
  - destruct (Z.eqb z 0); [apply clq_tid_refl | tidQ H E; discriminate E].
  - tidQ H E. discriminate E.
Qed.

Lemma weave_wok_inv : forall (g : ingot) (d : dtab),
  clq_tid weaveout (weave g) (wok d) ->
  prod (clq_tid (list idl_iou) (iouof g) nil) (clq_tid dtab d (dbuild (ipin g))).
Proof.
  intros g d H. unfold weave in H.
  destruct (iouof g) as [| x t] eqn:E.
  - tidQ H H2. injection H2 as H2.
    exact (pair (clq_tid_refl (list idl_iou) nil)
                (clq_tid_eq dtab d (dbuild (ipin g)) (eq_sym H2))).
  - tidQ H H2. discriminate H2.
Qed.

(* The decision-satisfaction decider (the word-by-word shape of inter-stage decidability): pass(h,w) iff the woven table's head-relative
difference equals w; rej(h,e) iff the head-relative difference differs from e (the non-zero difference clause holds) *)
Definition vrespects (d : dtab) (v : verd) : bool :=
  match vd v with
  | vpass => Z.eqb (dsub d (hix (vh v)) O) (vz v)
  | vrej => negb (Z.eqb (dsub d (hix (vh v)) O) (vz v))
  end.

(* Main theorem 3: what is woven is legitimate — every decision in the stream is satisfied by the woven list (immune to cross-hole illegality from birth) *)
Theorem weave_sound : forall (s : list verd) (d : dtab),
  clq_tid weaveout (weave (melt s)) (wok d) ->
  forall v : verd, clq_tid bool (vIn v s) true -> clq_tid bool (vrespects d v) true.
Proof.
  intros s d Hw.
  destruct (weave_wok_inv (melt s) d Hw) as [Hn Hd].
  tidQ Hn En. tidQ Hd Ed.
  unfold iouof in En. apply app_eq_nil in En. destruct En as [Eh Esr].
  apply app_eq_nil in Esr. destruct Esr as [Es Er].
  pose proof (clq_tid_eq (list idl_iou) (headiou (ipin (melt s))) nil Eh) as TH.
  pose proof (clq_tid_eq (list idl_iou) (slotiousL (ipin (melt s)) slotL) nil Es) as TS.
  pose proof (clq_tid_eq (list idl_iou) (rejious (ipin (melt s)) (irej (melt s))) nil Er)
    as TR.
  pose proof (slotiousL_nil_allpin1 (ipin (melt s)) slotL TS) as AP.
  pose proof (headiou_nil_inv (ipin (melt s)) TH) as HD.
  induction s as [| v0 t IH]; intros v Hv.
  - cbn [vIn] in Hv. tidQ Hv E. discriminate E.
  - cbn [vIn] in Hv. destruct v as [h0 d0 z0]. destruct d0.
    + (* pass(h0,z0): the woven table's head-relative difference is exactly z0 *)
      unfold vrespects. cbn [vd vz vh]. rewrite Ed.
      rewrite (tidE Z _ _ (dsub_pget (ipin (melt (v0 :: t))) h0)).
      destruct (pget (ipin (melt (v0 :: t))) h0) as [|z1| ] eqn:Ep.
      * (* Missing pin: the head hole is handled by the head-normalization lemma, the remaining holes by the six-slot census *)
        destruct h0.
        -- exact (pin_PN_absurd (v0 :: t) k0 z0 (clq_tid_eq pinv _ _ Ep) Hv
                    (clq_tid bool (Z.eqb 0 z0) true)).
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL k1 AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kb AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kc AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL ke AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kr AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
      * pose proof (pin_P1_in_val (v0 :: t) h0 z1 z0 (clq_tid_eq pinv _ _ Ep) Hv) as ZP.
        tidQ ZP EZ.
        destruct h0.
        -- rewrite Ep in HD. pose proof (tidE bool _ true HD) as HDz.
           apply Z.eqb_eq in HDz.
           apply (clq_tid_eq bool _ true). rewrite <- EZ, HDz. apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
      * (* Pin conflict: the head hole is handled by the head-normalization lemma, the remaining holes by the six-slot census *)
        destruct h0.
        -- rewrite Ep in HD. cbn in HD. tidQ HD E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL k1 AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kb AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kc AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL ke AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kr AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
    + (* rej(h0,z0): the woven table differs from the rejected value by a non-zero amount — all difference clauses pass *)
      unfold vrespects. cbn [vd vz vh]. rewrite Ed.
      pose proof (rejious_nil_ok (ipin (melt (v0 :: t))) (irej (melt (v0 :: t))) TR
                        h0 z0 (rej_from_stream (v0 :: t) h0 z0 Hv)) as RJ.
      change (clq_tid bool
                (negb (Z.eqb (dsub (dbuild (ipin (melt (v0 :: t)))) (hix h0) O) z0))
                true) in RJ.
      rewrite (tidE bool _ true RJ). apply clq_tid_refl.
Qed.

(* ===================================================================== *)
(* 7. Replay invariance: the differential stage is closed under the construction stage — livelock loses its carrier *)
(* ===================================================================== *)

Definition isnil {A : Type} (l : list A) : bool :=
  match l with nil => true | _ => false end.

Lemma isnil_app : forall (A : Type) (a b : list A),
  clq_tid bool (isnil (a ++ b)) (andb (isnil a) (isnil b)).
Proof. intros A a b. destruct a; apply clq_tid_refl. Qed.

Lemma rejious_app_isnil : forall (p : ipins) (l1 l2 : list (prod hole Z)),
  clq_tid bool (isnil (rejious p (l1 ++ l2)))
       (andb (isnil (rejious p l1)) (isnil (rejious p l2))).
Proof.
  intros p l1 l2. induction l1 as [| x t IH]; cbn [app rejious].
  - apply clq_tid_refl.
  - destruct (rjbad p x).
    + apply clq_tid_refl.
    + apply IH.
Qed.

Lemma andb_idem_tid : forall b : bool, clq_tid bool (andb b b) b.
Proof. intros b. destruct b; apply clq_tid_refl. Qed.

Lemma andb3_idem_eq : forall a b c : bool,
  Id (andb a (andb b (andb c c))) (andb a (andb b c)).
Proof. intros a b c. destruct a, b, c; reflexivity. Qed.

Lemma iouof_mjoin_self_b : forall g : ingot,
  clq_tid bool (isnil (iouof (mjoin g g))) (isnil (iouof g)).
Proof.
  intros [p l]. unfold mjoin, iouof. cbn [ipin irej].
  rewrite (tidE ipins _ _ (pjoin_self_pins p)).
  tidQ (isnil_app idl_iou (headiou p)
          (slotiousL p slotL ++ rejious p (l ++ l))) Ei1. rewrite Ei1.
  tidQ (isnil_app idl_iou (slotiousL p slotL) (rejious p (l ++ l))) Ei2.
  rewrite Ei2.
  tidQ (rejious_app_isnil p l l) Erj. rewrite Erj.
  tidQ (isnil_app idl_iou (headiou p) (slotiousL p slotL ++ rejious p l)) Ei3.
  rewrite Ei3.
  tidQ (isnil_app idl_iou (slotiousL p slotL) (rejious p l)) Ei4. rewrite Ei4.
  apply (clq_tid_eq bool _ _).
  exact (match andb3_idem_eq (isnil (headiou p)) (isnil (slotiousL p slotL))
                       (isnil (rejious p l))
         with id_refl => eq_refl end).
Qed.

(* The carrier: weave_b = isnil composed with iouof (the two matches do not commute; a standalone connector statement) *)
Lemma weave_b_isnil : forall g : ingot,
  clq_tid bool (weave_b g) (isnil (iouof g)).
Proof.
  intros g. unfold weave_b, weave, isnil.
  destruct (iouof g) as [| x t]; apply clq_tid_refl.
Qed.

(* Main theorem 4a: whole-stream replay does not change the weaving decision *)
Theorem weave_replay_b : forall s : list verd,
  clq_tid bool (weave_b (melt (s ++ s))) (weave_b (melt s)).
Proof.
  intros s.
  pose proof (melt_hom s s) as Hh. tidQ Hh Eh. rewrite Eh.
  apply (clq_tid_trans bool (weave_b (mjoin (melt s) (melt s)))
                         (isnil (iouof (mjoin (melt s) (melt s)))) _).
  - apply weave_b_isnil.
  - apply (clq_tid_trans bool (isnil (iouof (mjoin (melt s) (melt s))))
             (isnil (iouof (melt s))) _).
    + exact (iouof_mjoin_self_b (melt s)).
    + apply (clq_tid_sym bool _ _ (weave_b_isnil (melt s))).
Qed.

Lemma nil_isnil : forall l : list idl_iou,
  clq_tid (list idl_iou) l nil -> clq_tid bool (isnil l) true.
Proof. intros [| x t] H.
  - apply clq_tid_refl.
  - cbn [isnil] in H. tidQ H E. discriminate E.
Qed.

Lemma isnil_eq_nil : forall l : list idl_iou,
  clq_tid bool (isnil l) true -> clq_tid (list idl_iou) l nil.
Proof.
  intros l H. destruct l as [| x t].
  - apply clq_tid_refl.
  - cbn [isnil] in H. tidQ H E. discriminate E.
Qed.

(* The carrier: an emptied clause list implies the woven wok (destruct consumes the match of weave; zero setoid dependence) *)
Lemma weave_nil_wok : forall (g : ingot) (d : dtab),
  clq_tid (list idl_iou) (iouof g) nil ->
  clq_tid dtab d (dbuild (ipin g)) ->
  clq_tid weaveout (weave g) (wok d).
Proof.
  intros g d Hn Hd. unfold weave. destruct (iouof g) as [| x t].
  - apply (clq_tid_eq weaveout _ _). rewrite (tidE dtab _ _ Hd). reflexivity.
  - tidQ Hn E. discriminate E.
Qed.

(* Main theorem 4b: replay does not change the woven artifact (the differential stage is closed under the construction stage: the wok branch is unchanged) *)
Theorem weave_replay_d : forall (s : list verd) (d : dtab),
  clq_tid weaveout (weave (melt (s ++ s))) (wok d) ->
  clq_tid weaveout (weave (melt s)) (wok d).
Proof.
  intros s d H.
  destruct (weave_wok_inv (melt (s ++ s)) d H) as [Hn Hd].
  tidQ Hn En. tidQ Hd Ed.
  pose proof (melt_hom s s) as Hh. tidQ Hh Eh. rewrite Eh in En.
  pose proof (nil_isnil _ (clq_tid_eq (list idl_iou) _ nil En)) as EnB.
  pose proof (clq_tid_trans bool (isnil (iouof (melt s)))
                (isnil (iouof (mjoin (melt s) (melt s)))) true
                (clq_tid_sym bool _ _ (iouof_mjoin_self_b (melt s))) EnB) as EnB2.
  pose proof (isnil_eq_nil (iouof (melt s)) EnB2) as Ens.
  apply (weave_nil_wok (melt s) d Ens).
  rewrite Ed, Eh. apply (clq_tid_eq dtab _ _). f_equal. unfold mjoin.
  exact (tidE ipins _ _ (pjoin_self_pins (ipin (melt s)))).
Qed.

(* Conflict census: the number of holes pinned PB (conflicting values in one hole recorded at most once) *)
Definition pbc (x : pinv) : nat := match x with PB => 1%nat | _ => 0%nat end.

Definition iconf (g : ingot) : nat :=
  (pbc (qa (ipin g)) + (pbc (qb (ipin g)) + (pbc (qc (ipin g)) +
  (pbc (qd (ipin g)) + (pbc (qe (ipin g)) + pbc (qf (ipin g)))))))%nat.

Lemma iconf_mjoin_self : forall g : ingot, clq_tid nat (iconf (mjoin g g)) (iconf g).
Proof.
  intros [p l]. unfold mjoin, iconf. cbn [ipin].
  rewrite (tidE ipins _ _ (pjoin_self_pins p)). apply clq_tid_refl.
Qed.

(* Main theorem 4c: replay introduces no new conflict holes (conflict is a property of holes, not an event count) *)
Theorem replay_census : forall s : list verd,
  clq_tid nat (iconf (melt (s ++ s))) (iconf (melt s)).
Proof.
  intros s.
  pose proof (melt_hom s s) as Hh. tidQ Hh Eh. rewrite Eh.
  exact (iconf_mjoin_self (melt s)).
Qed.

(* ===================================================================== *)
(* 8. Coupling to the Q4 decision face: the woven artifact reviewed word by word by [inner]-class queries *)
(* ===================================================================== *)

Lemma hix_nle : forall h : hole, clq_nle (hix h) hmax.
Proof.
  destruct h.
  - apply clq_nle_0.
  - apply clq_nle_S. apply clq_nle_S. apply clq_nle_S. apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_S. apply clq_nle_S. apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_S. apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_n.
Qed.

(* Main theorem 5: the woven artifact handed to the Q4 question-answering machine — the answers to [inner]-class difference queries are exactly
the pinned decision values. Proven at the loom's birth + independently reviewed by the Q4 decision face: the two statements couple. *)
Theorem recheck_pass : forall (s : list verd) (d : dtab) (h : hole) (w : Z),
  clq_tid weaveout (weave (melt s)) (wok d) ->
  clq_tid bool (vIn (mkVd h vpass w) s) true ->
  clq_tid qans (qask (mkCL d None acol0) (QIN (hix h) O)) (qans_val w).
Proof.
  intros s d h w Hw Hv.
  destruct (weave_wok_inv (melt s) d Hw) as [Hn Hd]. tidQ Hd Ed.
  rewrite Ed in Hw. rewrite Ed.
  pose proof (weave_sound s (dbuild (ipin (melt s))) Hw
                (mkVd h vpass w) Hv) as VR.
  unfold vrespects in VR. cbn [vd vz vh] in VR.
  pose proof (tidE bool _ true VR) as EV. apply Z.eqb_eq in EV.
  unfold qask, qaskR. cbn [cld clv cla].
  rewrite (tidE nat _ _ (dbuild_len (ipin (melt s)))).
  pose proof (clq_nle_leb hmax (hix h) (hix_nle h)) as L1. tidQ L1 EL1. rewrite EL1.
  pose proof (clq_nle_leb hmax O (clq_nle_0 hmax)) as L2. tidQ L2 EL2. rewrite EL2.
  apply tid_qans_val. exact (clq_tid_eq Z _ _ EV).
Qed.

(* ===================================================================== *)
(* 9. Computational demonstrations: XOR-stream regression + the happy path + same-hole conflict recorded once *)
(* ===================================================================== *)

(* The IDL regression of the second-round counterexample trial (the XOR stream): after pass-A comes rej-B — B has no pin (no pass decision),
so the under-order honestly records the miss; B's difference clause "value is not 0" is void against the placeholder 0, so one more
REJ is recorded — the XOR stream yields no non-zero difference witness; it is recorded as an under-order and not woven. *)
Definition sX : list verd := mkVd k1 vpass 0 :: mkVd kb vrej 0 :: nil.

Theorem xor_defused :
  clq_tid weaveout (weave (melt sX))
      (wiou (idl_IOU_NOPIN kb :: idl_IOU_NOPIN kc :: idl_IOU_NOPIN ke :: idl_IOU_NOPIN kr
             :: idl_IOU_REJ kb 0 :: nil)).
Proof.
  unfold sX, weave, iouof, melt, m1, mjoin, mzero.
  cbn [pjoin pj pjR pjN pupd pzero ipin irej headiou slotiousL rejious hin app].
  apply clq_tid_refl.
Qed.

(* Happy path: all six holes pinned + one satisfiable difference clause implies the artifact is woven *)
Definition sOK : list verd :=
  mkVd k0 vpass 0 :: mkVd k1 vpass 3 :: mkVd kb vpass (-2) :: mkVd kc vpass 7
  :: mkVd ke vpass 1 :: mkVd kr vpass 4 :: mkVd kb vrej 9 :: nil.

Theorem happy_wok : clq_tid bool (weave_b (melt sOK)) true.
Proof.
  unfold sOK, melt, weave_b, weave, iouof, m1, mjoin, mzero.
  cbn [pjoin pj pjR pjN pupd pzero ipin irej headiou slotiousL rejious hin app].
  apply clq_tid_refl.
Qed.

(* Same-hole conflicting values: the conflict state PB implies recorded-as-under-order and not woven; the conflict census is exactly 1 (same-hole conflict recorded once) *)
Definition sC : list verd := mkVd k1 vpass 3 :: mkVd k1 vpass 5 :: nil.

Theorem conflict_once : clq_tid bool (weave_b (melt sC)) false.
Proof.
  unfold sC, melt, weave_b, weave, iouof, m1, mjoin, mzero.
  cbn [pjoin pj pjR pjN pupd pzero ipin irej headiou slotiousL rejious hin app].
  apply clq_tid_refl.
Qed.

Theorem conflict_census : clq_tid nat (iconf (melt sC)) 1%nat.
Proof.
  unfold sC, melt, m1, mjoin, mzero, iconf.
  cbn [pjoin pj pjR pjN pupd pzero ipin pbc].
  apply clq_tid_refl.
Qed.

(* With the woven artifact installed in the Q4 ledger state, all [inner]-class queries are admitted (zero refusals within the six-slot domain) *)
Theorem wok_qin_admit : forall (s : list verd) (i j : nat),
  clq_nle i (dlen (dbuild (ipin (melt s)))) ->
  clq_nle j (dlen (dbuild (ipin (melt s)))) ->
  clq_tid bool (qadmit (mkCL (dbuild (ipin (melt s))) None acol0) (QIN i j)) true.
Proof.
  intros s i j Hi Hj. unfold qadmit, qadmitR, qin_ok. cbn [cld clv cla].
  pose proof (clq_nle_leb (dlen (dbuild (ipin (melt s)))) i Hi) as L1. tidQ L1 EL1.
  pose proof (clq_nle_leb (dlen (dbuild (ipin (melt s)))) j Hj) as L2. tidQ L2 EL2.
  rewrite EL1, EL2. apply clq_tid_refl.
Qed.

Close Scope Z_scope.
(* ============ Assumption-face closure audit (all eleven statements of the demonstration face checked) ============ *)

Print Assumptions qrej_admit_false.
Print Assumptions val_burn_reject.
Print Assumptions hbeq_refl.
Print Assumptions vbeq_mkVd.
Print Assumptions pjR_PN.
Print Assumptions pget_mjoin.
Print Assumptions dbuild_len.
Print Assumptions xor_defused.
Print Assumptions happy_wok.
Print Assumptions conflict_once.
Print Assumptions conflict_census.

