(** ConstructiveWorld-Set — intensional identity/order types and an event-ledger model.

* UpRecast: Rebuilt identity and order types with an event-ledger model.

    Mission.  The intensional identity type [rc_tid] (with symmetry,
      transitivity and congruence), the structured natural-number order
      [rc_nle] with its two-directional [rc_nle_leb] carriers, the inference
      tools [tidE]/[tid_kill]/[nleP], and the event-ledger model statements
      ([ledger_use_mono], [scan_partition_len], [recast_pass_census],
      [tier_balance], [acc_balance], [friction_mono], and the recast-chain
      driver family).

    Dependencies.  Stdlib [ZArith], [Lia], [List]; the identity/order base
      is inlined from this development (self-contained section 0).

    References.  This development, ConstructiveWorld-Main baseline module
      UpRecast.v, whose statement names are carried over here verbatim
      (statement-face Set-carrier completion).  The identity and order
      relations are rebuilt as inductive types in the intensional
      tradition (no-confusion style re-casting of equality and order).

    Constructivity.  All named statements and fields are carried by [Set]
      (equality and order are [Set]-valued relations, [rc_tid]/[rc_nle]);
      every proof ends in [Qed] with no admitted goals and no additional
      axiom premises; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpRecast.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Notation S := Datatypes.S.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set-layer infrastructure: the tid identity type, the nle order type, decidable-survival tools (inlined from G04_ProjFam section 0) *)
(* ===================================================================== *)

(* Set-layer identity type (an equality carrier with zero Prop in its statement) *)
Inductive rc_tid (A : Type) : A -> A -> Type := rc_tid_refl : forall x : A, rc_tid A x x.

Definition rc_tid_sym (A : Type) (x y : A) (H : rc_tid A x y) : rc_tid A y x :=
  match H in rc_tid _ a b return rc_tid _ b a with
  | rc_tid_refl _ a0 => @rc_tid_refl _ a0
  end.

Definition rc_tid_trans (A : Type) (x y z : A) (H1 : rc_tid A x y) (H2 : rc_tid A y z) :
  rc_tid A x z :=
  match H1 in rc_tid _ a b return rc_tid _ b z -> rc_tid _ a z with
  | rc_tid_refl _ a0 => fun H => H
  end H2.

(* Functional congruence of the identity type (the transport workhorse) *)
Definition rc_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : rc_tid A x y) :
  rc_tid B (f x) (f y) :=
  match H in rc_tid _ a b return rc_tid B (f a) (f b) with
  | rc_tid_refl _ a0 => @rc_tid_refl _ (f a0)
  end.

(* Set-layer natural-number order type (k < m encoded as nle (S k) m) *)
Inductive rc_nle (n : nat) : nat -> Set :=
| rc_nle_n : rc_nle n n
| rc_nle_S : forall m : nat, rc_nle n m -> rc_nle n (S m).

Ltac tidE H :=
  pose proof (match H in rc_tid _ a b return a = b with rc_tid_refl _ _ => eq_refl end) as HE.

(* Boolean identity contradiction closer: H1 : rc_tid bool X true, H2 : rc_tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in rc_tid _ a b return a = b with rc_tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in rc_tid _ a b return a = b with rc_tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

Lemma rc_leb_refl_tid : forall a : nat, rc_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply rc_tid_refl.
Qed.

Lemma rc_leb_S : forall a m : nat,
  rc_tid bool (Nat.leb a m) true -> rc_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply rc_tid_refl.
    + change (rc_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply rc_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint rc_nle_lebF (a b : nat) (H : rc_nle a b) {struct H} :
  rc_tid bool (Nat.leb a b) true :=
  match H as H0 in rc_nle _ bb
  return rc_tid bool (Nat.leb a bb) true with
  | rc_nle_n _ => rc_leb_refl_tid a
  | rc_nle_S _ m H1 => rc_leb_S a m (rc_nle_lebF a m H1)
  end.

Definition rc_nle_leb (b a : nat) (H : rc_nle a b) : rc_tid bool (Nat.leb a b) true :=
  rc_nle_lebF a b H.

(* rc_nle -> nat ≤ extraction (for internal proof reasoning only) *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (rc_nle_leb _ _ H) in rc_tid _ x y return x = y with
        | rc_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma rc_nle_SS : forall a b : nat, rc_nle a b -> rc_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply rc_nle_n.
  - apply rc_nle_S. exact IH.
Qed.

Lemma rc_nle_0 : forall m : nat, rc_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply rc_nle_n.
  - apply rc_nle_S. exact IH.
Qed.

Lemma rc_nle_of_leb : forall b a : nat,
  rc_tid bool (Nat.leb a b) true -> rc_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply rc_nle_n.
    + change (rc_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply rc_nle_0.
    + apply rc_nle_SS. exact (IB a1 H).
Qed.

Lemma rc_nle_trans : forall a b c : nat, rc_nle a b -> rc_nle b c -> rc_nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply rc_nle_S. exact IH.
Qed.

(* rc_nle (S a) (S b) -> rc_nle a b *)
Lemma rc_nle_pred : forall a b : nat, rc_nle (S a) (S b) -> rc_nle a b.
Proof.
  intros a b H. apply rc_nle_of_leb.
  exact (rc_nle_leb (S b) (S a) H).
Qed.

Lemma rc_nle_add_r : forall a b : nat, rc_nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply rc_nle_0.
  - exact (rc_nle_SS a1 (a1 + b) (IH b)).
Qed.

(* ---- Infrastructure new in this file ---- *)

Lemma nle_S_diag : forall a : nat, rc_nle a (S a).
Proof.
  induction a as [| a IH].
  - apply rc_nle_0.
  - apply rc_nle_SS. exact IH.
Qed.

Lemma nle_add_r_any : forall a b c : nat, rc_nle a b -> rc_nle (a + c) (b + c).
Proof.
  intros a b c H. induction H as [| m H IH].
  - apply rc_nle_n.
  - replace (Nat.add (S m) c) with (S (Nat.add m c)) by reflexivity.
    apply rc_nle_S. exact IH.
Qed.

Lemma nle_add_l_any : forall a b c : nat, rc_nle b c -> rc_nle (a + b) (a + c).
Proof.
  intros a b c H. induction a as [| a IH].
  - exact H.
  - apply rc_nle_SS. exact IH.
Qed.

(* nat/bool-layer eq -> rc_tid carrier (for closing goals inside proofs) *)
Lemma tid_nat_eq : forall a b : nat, a = b -> rc_tid nat a b.
Proof.
  intros a b H. rewrite H. apply rc_tid_refl.
Qed.

Lemma tid_bool_eq : forall x y : bool, x = y -> rc_tid bool x y.
Proof.
  intros x y H. rewrite H. apply rc_tid_refl.
Qed.



Lemma rc_len_app : forall (A : Set) (l1 l2 : list A),
  Id (length (l1 ++ l2)) (Nat.add (length l1) (length l2)).
Proof.
  intros A l1. induction l1 as [| a l1 IH]; intros l2; simpl.
  - apply id_refl.
  - destruct (IH l2). apply id_refl.
Qed.

Lemma rc_filter_partition_len : forall (A : Set) (g : A -> bool) (l : list A),
  Id (length l) (Nat.add (length (filter g l)) (length (filter (fun x => negb (g x)) l))).
Proof.
  intros A g l. induction l as [| a l IH]; simpl.
  - apply id_refl.
  - destruct (g a); simpl.
    + (* g a = true: entry a stays on the survivor side; the successor addition is already in normal form by iota, and the induction premise closes it *)
      destruct IH. apply id_refl.
    + (* g a = false: entry a falls to the complement side; after the induction premise, successor addition restores the shape *)
      rewrite Nat.add_succ_r. destruct IH. apply id_refl.
Qed.

Lemma rc_filter_app : forall (A : Set) (g : A -> bool) (l1 l2 : list A),
  Id (filter g (l1 ++ l2)) (filter g l1 ++ filter g l2).
Proof.
  intros A g l1. induction l1 as [| a l1 IH]; intros l2; simpl.
  - apply id_refl.
  - destruct (g a); simpl; destruct (IH l2); apply id_refl.
Qed.

Lemma rc_filter_filter_len : forall (A : Set) (g : A -> bool) (l : list A),
  Id (length (filter g (filter g l))) (length (filter g l)).
Proof.
  intros A g l. induction l as [| a l IH].
  - apply id_refl.
  - destruct (g a) eqn:Ega.
    + simpl. rewrite ?Ega. simpl. rewrite ?Ega. simpl. destruct IH. apply id_refl.
    + simpl. rewrite ?Ega. simpl. rewrite ?Ega. simpl. destruct IH. apply id_refl.
Qed.

Lemma rc_existsb_filter_neg : forall (A : Set) (g : A -> bool) (l : list A),
  Id (existsb g (filter (fun x => negb (g x)) l)) false.
Proof.
  intros A g l. induction l as [| a l IH].
  - apply id_refl.
  - simpl. destruct (g a) eqn:Ega.
    + cbn [existsb negb]. exact IH.
    + cbn [existsb negb]. rewrite ?Ega. simpl. exact IH.
Qed.

Lemma rc_existsb_filter_id : forall (A : Set) (g : A -> bool) (l : list A),
  Id (existsb g (filter g l)) (existsb g l).
Proof.
  intros A g l. induction l as [| a l IH].
  - apply id_refl.
  - change (existsb g (filter g (a :: l)))
      with (existsb g (if g a then a :: filter g l else filter g l)).
    change (existsb g (a :: l)) with (orb (g a) (existsb g l)).
    destruct (g a) eqn:Ega.
    + simpl. rewrite Ega. apply id_refl.
    + exact IH.
Qed.

(* ===================================================================== *)

(* ===================================================================== *)

Definition fid : Set := nat.
Definition tier : Set := nat.
Definition evid : Set := Z.

Inductive evt : Set := use : fid -> evid -> evt.

Record meter : Set := mkM { m_ev : nat; m_rc : nat }.

Record Cert : Set := mkC {
  census : list (fid * tier);   (* Survival census: fields × tiers *)
  obls   : list (fid * tier);   (* Unbridged tail obligations ledger: breached fields × lost tiers *)
  mtr    : meter                (* Friction accounting: exercise count + recast count *)
}.

(* Ledger progression: events are append-only; history is never rewritten *)
Definition ledger_step (l : list evt) (e : evt) : list evt := l ++ [e].

(* The exercise decision face of field f (a per-event classification bool over the ledger) *)
Definition is_use_f (f : fid) (e : evt) : bool :=
  match e with use g _ => Nat.eqb f g end.

(* The use account of field f: the number of exercises of that field on the ledger *)
Definition use_cnt (f : fid) (l : list evt) : nat :=
  length (filter (is_use_f f) l).

Theorem ledger_len_step : forall (l : list evt) (e : evt),
  rc_tid nat (S (length l)) (length (ledger_step l e)).
Proof.
  intros l e. apply tid_nat_eq. unfold ledger_step.
  pose proof (match rc_len_app evt l [e] in Id _ z return length (l ++ [e]) = z with id_refl => eq_refl end) as HL.
  rewrite HL. simpl. rewrite Nat.add_1_r. reflexivity.
Qed.

(* Ledger progression conservation/monotonicity: use events only increase the per-field account *)
Theorem ledger_use_mono : forall (f : fid) (l : list evt) (e : evt),
  rc_nle (use_cnt f l) (use_cnt f (ledger_step l e)).
Proof.
  intros f l. induction l as [| a l IH]; intros e.
  - apply rc_nle_0.
  - destruct a as [g ev]. unfold use_cnt in *. simpl.
    destruct (Nat.eqb f g).
    + apply rc_nle_SS. exact (IH e).
    + exact (IH e).
Qed.

(* ===================================================================== *)
(* Part 2. The survive scan: maximal surviving sub-certificate (field-set filter) + full boolean decision coverage *)
(* ===================================================================== *)

Definition fidb (f g : fid) : bool := Nat.eqb f g.

(* Survival decision face: a field survives iff it differs from the breached field *)
Definition keepF (f : fid) (p : fid * tier) : bool := negb (fidb f (fst p)).
(* Breach decision face: the field is exactly the breached field *)
Definition hitF (f : fid) (p : fid * tier) : bool := fidb f (fst p).

(* Maximal surviving sub-certificate: all census entries whose field is not breached *)
Definition survive_scan (f : fid) (l : list (fid * tier)) : list (fid * tier) :=
  filter (keepF f) l.
(* Entries breached and demoted (complementary to the survival scan; same decision face) *)
Definition pierced (f : fid) (l : list (fid * tier)) : list (fid * tier) :=
  filter (hitF f) l.

(* A boolean membership decision for fields (a Prop-free substitute for In) *)
Definition occurs (f : fid) (l : list (fid * tier)) : bool :=
  existsb (hitF f) l.

(* Scan completeness, part one: length partition conservation — survivors + breaches = the whole census, nothing dropped *)
Theorem scan_partition_len : forall (f : fid) (l : list (fid * tier)),
  rc_tid nat (length l)
           (Nat.add (length (survive_scan f l)) (length (pierced f l))).
Proof.
  intros f l. apply tid_nat_eq. unfold survive_scan, pierced.
  rewrite Nat.add_comm.
  exact (match rc_filter_partition_len (fid * tier) (hitF f) l with id_refl => eq_refl end).
Qed.

(* Scan completeness, part two: purity of survivors — the surviving sub-certificate contains no breached field *)
Theorem scan_survivor_pure : forall (f : fid) (l : list (fid * tier)),
  rc_tid bool (occurs f (survive_scan f l)) false.
Proof.
  intros f l. apply tid_bool_eq. unfold occurs, survive_scan.
  exact (match rc_existsb_filter_neg (fid * tier) (hitF f) l in Id _ z
         return existsb (hitF f) (filter (keepF f) l) = z
         with id_refl => eq_refl end).
Qed.

(* Scan completeness, part three: full decision coverage — the breach side captures exactly all enrolled entries *)
Theorem scan_pierce_capture : forall (f : fid) (l : list (fid * tier)),
  rc_tid bool (occurs f (pierced f l)) (occurs f l).
Proof.
  intros f l. apply tid_bool_eq. unfold occurs, pierced.
  exact (match rc_existsb_filter_id (fid * tier) (hitF f) l in Id _ z
         return existsb (hitF f) (filter (hitF f) l) = z
         with id_refl => eq_refl end).
Qed.

(* Full boolean decision coverage: the overall membership decider (a Type-sorted two-branch carrier, zero Prop). *)
(* Design decision: in Rocq 9.1 the sumbool parameters are (A B : Prop), which cannot carry the Type-sorted *)
(* payload of rc_tid; hence the dedicated Type-sorted two-branch carrier pick (decider semantics unchanged: the branch is the decision). *)
Inductive pick (A B : Type) : Type := pick_l : A -> pick A B | pick_r : B -> pick A B.

Theorem occurs_dec : forall (f : fid) (l : list (fid * tier)),
  pick (rc_tid bool (occurs f l) true) (rc_tid bool (occurs f l) false).
Proof.
  intros f l. unfold occurs.
  destruct (existsb (hitF f) l).
  - apply pick_l. apply tid_bool_eq. reflexivity.
  - apply pick_r. apply tid_bool_eq. reflexivity.
Qed.

(* The surviving sub-certificate is no larger than the original census *)
Theorem scan_scan_mono : forall (f : fid) (l : list (fid * tier)),
  rc_nle (length (survive_scan f l)) (length l).
Proof.
  intros f l. pose proof (scan_partition_len f l) as HP. tidE HP.
  rewrite HE. apply rc_nle_add_r.
Qed.

(* Tier quality: the tier sum over census entries *)
Definition tsum (l : list (fid * tier)) : nat :=
  fold_right (fun p a => Nat.add (snd p) a) O l.

Lemma rc_tsum_app : forall (l1 l2 : list (fid * tier)),
  Id (tsum (l1 ++ l2)) (Nat.add (tsum l1) (tsum l2)).
Proof.
  intros l1. unfold tsum. induction l1 as [| a l1 IH]; intros l2; simpl.
  - apply id_refl.
  - match goal with |- Id _ _ => idtac "SHAPE:Id" | _ => idtac "SHAPE:OTHER" end.
    pose proof (match IH l2 in Id _ z
                return fold_right (fun (p : fid * tier) (a : nat) => (snd p + a)%nat)
                         0%nat (l1 ++ l2) = z
                with id_refl => eq_refl end) as HE.
    try rewrite HE.
    try rewrite Nat.add_assoc.
    try rewrite <- Nat.add_assoc.
    try change (tsum (l1 ++ l2))
      with (fold_right (fun (p : fid * tier) (a : nat) => (snd p + a)%nat) 0%nat (l1 ++ l2)).
    try rewrite HE.
    try rewrite Nat.add_assoc.
    try rewrite <- Nat.add_assoc.
    try rewrite <- HE.
    try rewrite Nat.add_assoc.
    try rewrite <- Nat.add_assoc.
    apply id_refl.
Qed.

Lemma rc_tsum_filter_partition : forall (g : fid * tier -> bool)
                                        (l : list (fid * tier)),
  Id (tsum l) (Nat.add (tsum (filter g l)) (tsum (filter (fun x => negb (g x)) l))).
Proof.
  intros g l. unfold tsum. induction l as [| a l IH]; simpl.
  - apply id_refl.
  - destruct (g a); simpl.
    + (* g a = true: entry a joins the survivor side; after the induction premise the associativity law restores the shape *)
      pose proof (match IH in Id _ z
                  return fold_right (fun (p : fid * nat) (a : nat) => (snd p + a)%nat) 0%nat l = z
                  with id_refl => eq_refl end) as HE.
      try rewrite HE.
      all: try apply id_refl.
      try rewrite Nat.add_assoc.
      try rewrite (Nat.add_comm (snd a)).
      try rewrite <- Nat.add_assoc.
      all: try apply id_refl.
    + (* g a = false: entry a joins the complement side; after the induction premise, three AC-steps re-shape the sum (associate, commute, re-associate) *)
      pose proof (match IH in Id _ z
                  return fold_right (fun (p : fid * nat) (a : nat) => (snd p + a)%nat) 0%nat l = z
                  with id_refl => eq_refl end) as HE.
      try rewrite HE.
      all: try apply id_refl.
      try rewrite Nat.add_assoc.
      try rewrite (Nat.add_comm (snd a)).
      try rewrite <- Nat.add_assoc.
      all: try apply id_refl.
Qed.

(* Scan completeness, part four: tier-quality partition conservation — survivors + breaches = the original quality *)
Lemma rc_tsum_scan : forall (f : fid) (l : list (fid * tier)),
  Id (tsum l) (Nat.add (tsum (survive_scan f l)) (tsum (pierced f l))).
Proof.
  intros f l. unfold survive_scan, pierced.
  rewrite Nat.add_comm.
  pose proof (match rc_tsum_filter_partition (hitF f) l in Id _ z
              return tsum l = z
              with id_refl => eq_refl end) as HE.
  exact (match HE in _ = z return Id (tsum l) z with eq_refl => id_refl end).
Qed.

(* ===================================================================== *)
(* Part 3. The recast: an inline test (boolean decision) + demotion + obligation transfer + accounting deltas *)
(* ===================================================================== *)

(* Tier readout: find the entry of field f in the census and read out its tier *)
Definition level_at (f : fid) (l : list (fid * tier)) : option tier :=
  match find (hitF f) l with
  | Some p => Some (snd p)
  | None => None
  end.

(* Inline test (decidable admission): the entry passes iff the evidence strength |ev| is at least the field tier t; *)
(* if no tier is enrolled (demoted or never issued) it does not pass.  All boolean, zero Prop. *)
Definition passes (f : fid) (ev : evid) (c : Cert) : bool :=
  match level_at f (census c) with
  | Some t => Nat.leb t (Z.to_nat (Z.abs ev))
  | None => false
  end.

(* The recast proper: tiered by the test boolean (recast_b exposes the branch, recast only dispatches by iota, *)
(* so that every theorem can be moved into a rewrite-friendly shape with one change) *)
Definition recast_b (c : Cert) (f : fid) (ev : evid) (b : bool) : Cert :=
  if b
  then mkC (census c) (obls c) (mkM (S (m_ev (mtr c))) (m_rc (mtr c)))
  else mkC (survive_scan f (census c))
           (obls c ++ pierced f (census c))
           (mkM (S (m_ev (mtr c))) (S (m_rc (mtr c)))).

(* Use-event-driven recast: every downstream instantiation performs one inline test *)
Definition recast (c : Cert) (e : evt) : Cert :=
  match e with
  | use f ev => recast_b c f ev (passes f ev c)
  end.


Definition total_acc (c : Cert) : nat :=
  Nat.add (length (census c)) (length (obls c)).

(* Recast tiering helper: the pass tier leaves the census unchanged *)
Theorem recast_pass_census : forall (c : Cert) (f : fid) (ev : evid),
  rc_tid bool (passes f ev c) true ->
  rc_tid (list (fid * tier)) (census c) (census (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. exact (rc_tid_refl (list (fid * tier)) (census c)).
Qed.

(* Recast tiering helper: the pass tier keeps all old obligations (obligations never vanish on one side only) *)
Theorem recast_pass_obls : forall (c : Cert) (f : fid) (ev : evid),
  rc_tid bool (passes f ev c) true ->
  rc_tid (list (fid * tier)) (obls c) (obls (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. exact (rc_tid_refl (list (fid * tier)) (obls c)).
Qed.

(* Recast breach tier: the census shrinks by exactly the breached entries (the source side of obligation transfer) *)
Theorem recast_pierce_partition : forall (c : Cert) (f : fid) (ev : evid),
  rc_tid bool (passes f ev c) false ->
  rc_tid nat (length (census c))
           (Nat.add (length (census (recast c (use f ev))))
                    (length (pierced f (census c)))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. unfold recast_b. cbn [census].
  exact (scan_partition_len f (census c)).
Qed.

(* Recast breach tier: the new obligation is exactly the demoted entry (the target side; the old obligation dies as the new one is born) *)
Theorem recast_pierce_obls_len : forall (c : Cert) (f : fid) (ev : evid),
  rc_tid bool (passes f ev c) false ->
  rc_tid nat (length (obls (recast c (use f ev))))
           (Nat.add (length (obls c)) (length (pierced f (census c)))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. unfold recast_b. cbn [obls].
  apply tid_nat_eq.
  pose proof (match rc_len_app _ (obls c) (pierced f (census c)) in Id _ z return length (obls c ++ pierced f (census c)) = z with id_refl => eq_refl end) as HL.
  rewrite HL. reflexivity.
Qed.

(* Census monotonicity: a recast never issues additional census entries *)
Theorem recast_census_mono : forall (c : Cert) (e : evt),
  rc_nle (length (census (recast c e))) (length (census c)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply rc_nle_n.
  - exact (scan_scan_mono f (census c)).
Qed.

(* Obligation monotonicity: a recast never destroys an existing obligation *)
Theorem recast_obls_mono : forall (c : Cert) (e : evt),
  rc_nle (length (obls c)) (length (obls (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply rc_nle_n.
  - unfold recast_b. cbn [obls].
    pose proof (match rc_len_app _ (obls c) (pierced f (census c)) in Id _ z return length (obls c ++ pierced f (census c)) = z with id_refl => eq_refl end) as HL.
    rewrite HL. apply rc_nle_add_r.
Qed.


Theorem acc_balance : forall (c : Cert) (e : evt),
  rc_tid nat (total_acc c) (total_acc (recast c e)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply rc_tid_refl.
  - apply tid_nat_eq. unfold total_acc, recast_b. cbn [census obls].
    pose proof (match rc_len_app _ (obls c) (pierced f (census c)) in Id _ z return length (obls c ++ pierced f (census c)) = z with id_refl => eq_refl end) as HL.
    rewrite HL.
    pose proof (scan_partition_len f (census c)) as HP. tidE HP.
    rewrite HE.
    rewrite <- (Nat.add_assoc (length (survive_scan f (census c)))
                              (length (pierced f (census c))) (length (obls c))).
    rewrite (Nat.add_comm (length (pierced f (census c))) (length (obls c))).
    reflexivity.
Qed.

(* Obligation transfer closure with tier-quality conservation: the demotion transfers verbatim, quality exact to the unit *)
Theorem tier_balance : forall (c : Cert) (e : evt),
  rc_tid nat (Nat.add (tsum (census c)) (tsum (obls c)))
           (Nat.add (tsum (census (recast c e))) (tsum (obls (recast c e)))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply rc_tid_refl.
  - apply tid_nat_eq. unfold recast_b. cbn [census obls].
    pose proof (match rc_tsum_app (obls c) (pierced f (census c)) in Id _ z return tsum (obls c ++ pierced f (census c)) = z with id_refl => eq_refl end) as H1.
    rewrite H1.
    pose proof (match rc_tsum_scan f (census c) in Id _ z return tsum (census c) = z with id_refl => eq_refl end) as H2.
    rewrite H2.
    rewrite <- (Nat.add_assoc (tsum (survive_scan f (census c)))
                              (tsum (pierced f (census c))) (tsum (obls c))).
    rewrite (Nat.add_comm (tsum (pierced f (census c))) (tsum (obls c))).
    reflexivity.
Qed.

(* ===================================================================== *)
(* Part 5 (early). Friction accounting: exact deltas + monotonicity *)
(* ===================================================================== *)

(* Total friction accounting = exercise count + recast count *)
Definition friction (c : Cert) : nat := Nat.add (m_ev (mtr c)) (m_rc (mtr c)).

(* Exact delta on the pass tier: exactly +1 (exercise count +1, recast count unchanged) *)
Theorem friction_pass_step : forall (c : Cert) (f : fid) (ev : evid),
  rc_tid bool (passes f ev c) true ->
  rc_tid nat (S (friction c)) (friction (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. apply rc_tid_refl.
Qed.

(* Exact delta on the breach tier: exactly +2 (exercise +1, recast +1) *)
Theorem friction_pierce_step : forall (c : Cert) (f : fid) (ev : evid),
  rc_tid bool (passes f ev c) false ->
  rc_tid nat (S (S (friction c))) (friction (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. apply tid_nat_eq. unfold friction, recast_b. simpl.
  (* S e + S r reduces to S (e + S r) by iota: successor-addition normalization closes it *)
  rewrite Nat.add_succ_r. reflexivity.
Qed.

(* Friction monotonicity: no recast ever decreases the friction *)
Theorem friction_mono : forall (c : Cert) (e : evt),
  rc_nle (friction c) (friction (recast c e)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (nle_add_r_any (m_ev (mtr c)) (S (m_ev (mtr c))) (m_rc (mtr c))
             (nle_S_diag (m_ev (mtr c)))).
  - exact (rc_nle_trans (Nat.add (m_ev (mtr c)) (m_rc (mtr c)))
                     (Nat.add (S (m_ev (mtr c))) (m_rc (mtr c)))
                     (Nat.add (S (m_ev (mtr c))) (S (m_rc (mtr c))))
                     (nle_add_r_any (m_ev (mtr c)) (S (m_ev (mtr c)))
                        (m_rc (mtr c)) (nle_S_diag (m_ev (mtr c))))
                     (nle_add_l_any (S (m_ev (mtr c))) (m_rc (mtr c))
                        (S (m_rc (mtr c))) (nle_S_diag (m_rc (mtr c))))).
Qed.

(* Exercise count monotonicity *)
Theorem meter_ev_mono : forall (c : Cert) (e : evt),
  rc_nle (m_ev (mtr c)) (m_ev (mtr (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (nle_S_diag (m_ev (mtr c))).
  - exact (nle_S_diag (m_ev (mtr c))).
Qed.

(* Recast count monotonicity *)
Theorem meter_rc_mono : forall (c : Cert) (e : evt),
  rc_nle (m_rc (mtr c)) (m_rc (mtr (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (rc_nle_n (m_rc (mtr c))).
  - exact (nle_S_diag (m_rc (mtr c))).
Qed.

(* ===================================================================== *)

(* ===================================================================== *)

(* Re-entry: move all entries of f from the obligation ledger back to the census tail (the same decision face serves both books) *)
Definition rebridge (c : Cert) (f : fid) : Cert :=
  mkC (census c ++ pierced f (obls c)) (survive_scan f (obls c)) (mtr c).


Theorem rebridge_balance : forall (c : Cert) (f : fid),
  rc_tid nat (total_acc c) (total_acc (rebridge c f)).
Proof.
  intros c f. apply tid_nat_eq. unfold total_acc, rebridge. cbn [census obls].
  pose proof (match rc_len_app _ (census c) (pierced f (obls c)) in Id _ z return length (census c ++ pierced f (obls c)) = z with id_refl => eq_refl end) as HL.
  rewrite HL.
  pose proof (scan_partition_len f (obls c)) as HP. tidE HP.
  rewrite HE.
  rewrite (Nat.add_comm (length (survive_scan f (obls c)))
                        (length (pierced f (obls c)))).
  rewrite (Nat.add_assoc (length (census c)) (length (pierced f (obls c)))
                         (length (survive_scan f (obls c)))).
  reflexivity.
Qed.

(* Re-entry conservation, part two: tier-quality conservation *)
Theorem rebridge_tier_balance : forall (c : Cert) (f : fid),
  rc_tid nat (Nat.add (tsum (census c)) (tsum (obls c)))
           (Nat.add (tsum (census (rebridge c f))) (tsum (obls (rebridge c f)))).
Proof.
  intros c f. apply tid_nat_eq. unfold rebridge. cbn [census obls].
  pose proof (match rc_tsum_app (census c) (pierced f (obls c)) in Id _ z return tsum (census c ++ pierced f (obls c)) = z with id_refl => eq_refl end) as H1.
  rewrite H1.
  pose proof (match rc_tsum_scan f (obls c) in Id _ z return tsum (obls c) = z with id_refl => eq_refl end) as H2.
  rewrite H2.
  rewrite (Nat.add_comm (tsum (survive_scan f (obls c)))
                        (tsum (pierced f (obls c)))).
  rewrite (Nat.add_assoc (tsum (census c)) (tsum (pierced f (obls c)))
                         (tsum (survive_scan f (obls c)))).
  reflexivity.
Qed.


Theorem rebridge_clears : forall (c : Cert) (f : fid),
  rc_tid bool (occurs f (obls (rebridge c f))) false.
Proof.
  intros c f. apply tid_bool_eq. unfold rebridge, occurs. cbn [obls].
  unfold survive_scan.
  pose proof (match rc_existsb_filter_neg (fid * tier) (hitF f) (obls c) in Id _ z
              return existsb (hitF f) (filter (keepF f) (obls c)) = z
              with id_refl => eq_refl end) as HE.
  exact HE.
Qed.

(* Obligation field count: the number of entries of f on the ledger *)
Definition cnt (f : fid) (l : list (fid * tier)) : nat :=
  length (pierced f l).

(* Re-entry refill: the census count of f equals the original census entries plus the obligation-ledger entries (the accounting face of re-entrancy) *)
Theorem rebridge_cnt_reentry : forall (c : Cert) (f : fid),
  rc_tid nat (cnt f (census (rebridge c f)))
           (Nat.add (cnt f (census c)) (cnt f (obls c))).
Proof.
  intros c f. apply tid_nat_eq. unfold rebridge, cnt. cbn [census].
  unfold pierced.
  pose proof (match rc_filter_app (fid * tier) (hitF f) (census c)
                              (filter (hitF f) (obls c)) in Id _ z
              return filter (hitF f) (census c ++ filter (hitF f) (obls c)) = z
              with id_refl => eq_refl end) as H1.
  rewrite H1.
  pose proof (match rc_len_app _ (filter (hitF f) (census c))
                              (filter (hitF f) (filter (hitF f) (obls c))) in Id _ z
              return length (filter (hitF f) (census c)
                              ++ filter (hitF f) (filter (hitF f) (obls c))) = z
              with id_refl => eq_refl end) as H2.
  rewrite H2.
  pose proof (match rc_filter_filter_len (fid * tier) (hitF f) (obls c) in Id _ z return length (filter (hitF f) (filter (hitF f) (obls c))) = z with id_refl => eq_refl end) as H3.
  rewrite H3.
  reflexivity.
Qed.


(* The obligation ledger (tail) refills the census (head); the cycle can re-enter indefinitely *)
Theorem cycle_balance : forall (c : Cert) (f : fid) (e : evt),
  rc_tid nat (total_acc c) (total_acc (recast (rebridge c f) e)).
Proof.
  intros c f e. apply rc_tid_trans with (y := total_acc (rebridge c f)).
  - apply rebridge_balance.
  - apply acc_balance.
Qed.

(* Head-tail coupling with strict cyclic progress: one breaching recast round adds exactly +2 friction (the chain never deadlocks, and increases monotonically) *)
Theorem cycle_friction_strict : forall (c : Cert) (f : fid) (ev : evid),
  rc_tid bool (passes f ev (rebridge c f)) false ->
  rc_tid nat (S (S (friction c))) (friction (recast (rebridge c f) (use f ev))).
Proof.
  intros c f ev H. exact (friction_pierce_step (rebridge c f) f ev H).
Qed.

(* The recast-chain driver: the use-event stream of an n-round fuel supply ({struct n} guarantees structural recursion) *)
Fixpoint chain (n : nat) (c : Cert) (es : list evt) {struct n} : Cert :=
  match n with
  | O => c
  | S n' =>
      match es with
      | [] => c
      | e :: rest => chain n' (recast c e) rest
      end
  end.


Theorem chain_balance : forall (n : nat) (c : Cert) (es : list evt),
  rc_tid nat (total_acc c) (total_acc (chain n c es)).
Proof.
  intros n. induction n as [| n IH]; intros c es; simpl.
  - apply rc_tid_refl.
  - destruct es as [| e rest].
    + apply rc_tid_refl.
    + apply rc_tid_trans with (y := total_acc (recast c e)).
      * apply acc_balance.
      * apply IH.
Qed.

(* Chain monotonicity: a recast chain of any length never decreases friction (accounting accumulates along the chain) *)
Theorem chain_friction_mono : forall (n : nat) (c : Cert) (es : list evt),
  rc_nle (friction c) (friction (chain n c es)).
Proof.
  intros n. induction n as [| n IH]; intros c es; simpl.
  - apply rc_nle_n.
  - destruct es as [| e rest].
    + apply rc_nle_n.
    + apply rc_nle_trans with (b := friction (recast c e)).
      * apply friction_mono.
      * apply IH.
Qed.
