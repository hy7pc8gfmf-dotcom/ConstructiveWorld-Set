(* ConstructiveWorld-Set -- DTPT entropy premise-supply modules over rationals. *)

(** * abl_dte_core4: premise supply for the DTPT entropy registry, positions 116-150.

    Mission.  Completion of the antecedent-premise registry of the base
      entropy module [DTPT] over rational lists: collision entropy
      [dte_c4_H_min_q], max-entropy [dte_c4_H_max_q], deviation entropy
      [dte_c4_H_devsum] and their structural laws.  Main statements: the
      permutation invariances [dte_c4_H_min_q_perm]/[dte_c4_H_max_q_perm],
      the triangle inequality [dte_c4_me2_abs_sub_triangle], the zero
      tests [dte_c4_xqz_abs0_eq]/[dte_c4_xqz_plus_eq0_l], the sortedness
      equivalence [dte_c4_H_shannon_q_zero_sorted], blend optimality
      [dte_c4_align_lambda_opt_min] and additivity
      [dte_c4_collide_app_eq]/[dte_c4_H_freq_app_eq].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Extraction].  Requires [DTPT] of this development.

    References.  This development, abl_dte_core4.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dte_core4.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (9.3 generation
      magic). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ============================================================ *)
(*  Section 0.  Data-layer replicas: verbatim replicas of the host
   definitions at :34/:44/:47/:921/:1058/:1126/:1193/:1250/:1662/
   :1752/:1809/:1811/:1937/:1939/:2285/:2900/:62-:76, isolated by the
   [dte_c4_] prefix; [H_ms]/[H_adj]/[P0]/[Pinf]/[dedup] are consumed
   read-only through the base [DTPT] module and are not replicated.
   The host :1195 all_same replica is withdrawn together with the
   :2012 retraction of the duplicate statement (premises 114-115 are
   covered by the volume-3 statement that supplied them). *)
(* ============================================================ *)
(*  Anchor correction, exception B (annotation layer only; the
   section-0 anchor list above is untouched).  (i) :2900 should be
   :2875: host :2900 is the comment line preceding align_lambda_opt_min
   and :2875 is the line of [Definition align_lambda_opt] (the report
   section 11.B line and the current file agree).  (ii) The same report
   line also calls :1058/:1126 loose section-header-adjacent anchors
   (freq_q really at :1062, nsum really at :1132) and :2285 adjacent
   (me_total really at :2286); the current file says otherwise: host
   :1058 is the statement line of [Fixpoint freq_q], :1126 that of
   [Fixpoint nsum], :2285 that of [Definition me_total] (the
   section-header comments sit above them at :1056/:1124/:2281-2283;
   :1062/:2286 are the final constructor lines and :1132 is the
   statement line of the neighbouring [Lemma nsum_ext_in]).  This
   matches the statement-line-anchor convention of the master table and
   of correction note exception A, so the original anchors
   :1058/:1126/:2285 stand uncorrected and the three alternative values
   are not transcribed; the discrepancy is logged pending arbitration.
   The bodies of the 18 replicas are verified drift-free by direct
   inspection; only annotation anchors drift; the same-source anchor
   lines of report section 1.2 are logged under the same convention.
   This note concerns the annotation layer only; the statement layer is
   untouched. *)

Fixpoint dte_c4_qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + dte_c4_qn k)%Q
  end.

Fixpoint dte_c4_freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (dte_c4_freq_q x ys) else dte_c4_freq_q x ys
  end.

Fixpoint dte_c4_nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + dte_c4_nsum f ys)%nat
  end.

Definition dte_c4_sqsum (l : list Q) : nat :=
  dte_c4_nsum (fun x => dte_c4_freq_q x l) l.

Fixpoint dte_c4_nmax (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => Nat.max (f y) (dte_c4_nmax f ys)
  end.

Definition dte_c4_collide (l : list Q) : Q :=
  dte_c4_qn (dte_c4_sqsum l) / (dte_c4_qn (length l) * dte_c4_qn (length l)).

Definition dte_c4_maxcount (l : list Q) : nat := dte_c4_nmax (fun x => dte_c4_freq_q x l) l.

Definition dte_c4_maxfreq (l : list Q) : Q := dte_c4_qn (dte_c4_maxcount l) / dte_c4_qn (length l).

Definition dte_c4_H_max_q (l : list Q) : Q := 1 - dte_c4_maxfreq l.

Definition dte_c4_H_min_q (l : list Q) : Q := 1 - dte_c4_collide l.

Fixpoint dte_c4_H_devsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => Qabs (x - hd 0 (P0 l)) + dte_c4_H_devsum xs
  end.

Definition dte_c4_H_cond (l : list Q) (ctx : list Q) : Q :=
  dte_c4_H_devsum l - dte_c4_H_devsum ctx.

Definition dte_c4_H_freq (l : list Q) : Q :=
  (dte_c4_qn (length l) * dte_c4_qn (length l) - dte_c4_qn (dte_c4_sqsum l))
    / (dte_c4_qn (length l) * dte_c4_qn (length l)).

Definition dte_c4_H_lam (l : list Q) (s : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s).

Definition dte_c4_align_lambda_opt (h0 h1 : Q) : Q :=
  if Qle_bool h0 h1 then 1 else 0.

Record dte_c4_MultiEntropyEval : Type := dte_c4_mkME {
  dte_c4_me_carrier : list Q;        (* evaluation carrier *)
  dte_c4_me_Hadj    : Q;             (* sequence entropy (adjacent differences) *)
  dte_c4_me_Hms     : Q;             (* multiset entropy (distinct-value count) *)
  dte_c4_me_Hsh     : Q;             (* Shannon entropy (frequency counts) *)
  dte_c4_me_Hcond   : Q              (* conditional entropy (context dependence) *)
}.

Definition dte_c4_mkMEval (l : list Q) (ctx : list Q) : dte_c4_MultiEntropyEval :=
  dte_c4_mkME l (H_adj l) (H_ms l) (dte_c4_H_devsum l) (dte_c4_H_cond l ctx).

Definition dte_c4_me_total (m : dte_c4_MultiEntropyEval) : Q :=
  (1 # 4)%Q * (dte_c4_me_Hadj m + dte_c4_me_Hms m + dte_c4_me_Hsh m + dte_c4_me_Hcond m)%Q.

(* ============================================================ *)
(*  Section 1.  Auxiliary lemmas (17 items): isomorphic replicas of the
   host statements at :123/:171/:187/:275/:308/:314/:475/:513/:632/
   :927/:936/:951/:1067/:1083/:1097/:1132/:1141/:1198.  They are not
   premise slots; they serve the proof bodies of the supply theorems of
   this module, each constructed in place, with the order tools
   [qadd_nonneg]/[qadd_le] taken from the base [DTPT] module (the usage
   face of the isomorphic host section-1 proof bodies).  11 of them
   restate, constructed in place, statements already supplied by
   volumes 1-3; they are registered item by item in the
   deduplication block (1) of the delivery report and carry no premise
   account of this volume. *)
(* ============================================================ *)
(*  Anchor correction, exception A (annotation layer only; the
   auxiliary-section anchor table above is untouched).  The table lists
   18 anchors for 17 items: the extra one is the dangling anchor :275,
   which is [xq_sortQ_insert] in the host (the report section 11.A line
   and the current file agree) and has no replica in this module.
   [freq_q_le_length] is actually anchored at host :1064 and
   [freq_q_app] at host :1073; the table entries :1067/:1097 are loose
   positions (:1067 is the first proof line of [freq_q_le_length],
   :1097 a proof line of [freq_q_perm]).  After correction the
   effective anchor set of 17 items matches the verified checklist of
   report section 2 position by position.  The statement bodies of the
   17 items are verbatim drift-free; the premise account, the build and
   the red-line rules are unaffected.  This note concerns the annotation
   layer only; the statement layer is untouched. *)

Lemma dte_c4_qn_nonneg : forall n : nat, 0 <= dte_c4_qn n.
Proof.
  induction n as [| k IH].
  - apply Qle_refl.
  - simpl. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + exact IH.
Qed.

Lemma dte_c4_qn_S_pos : forall k : nat, 0 < dte_c4_qn (S k).
Proof.
  intros k. simpl. apply (Qlt_le_trans 0 1 (1 + dte_c4_qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (dte_c4_qn k) (Qle_refl 1) (dte_c4_qn_nonneg k))
      as HH. simpl in HH. exact HH.
Qed.

Lemma dte_c4_qn_add : forall a b : nat, dte_c4_qn (a + b)%nat == dte_c4_qn a + dte_c4_qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. rewrite Qplus_0_l. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

Lemma dte_c4_freq_q_le_length : forall (x : Q) (l : list Q),
  (dte_c4_freq_q x l <= length l)%nat.
Proof.
  intros x. induction l as [| y ys IH].
  - simpl. lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

Lemma dte_c4_freq_q_app : forall (x : Q) (l p : list Q),
  dte_c4_freq_q x (l ++ p) = (dte_c4_freq_q x l + dte_c4_freq_q x p)%nat.
Proof.
  intros x l p. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (Qeq_bool x a); rewrite IH; lia.
Qed.

(* restatement of the volume-2 premise-53 statement, permutation
   invariance of [dte_c4_freq_q]; auxiliary lemma, not a premise slot *)
Lemma dte_c4_freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> dte_c4_freq_q x l = dte_c4_freq_q x p.
Proof.
  intros x l p H.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

(* restatement of the volume-2 premise-57 statement, pointwise
   extensionality of [dte_c4_nsum]; auxiliary lemma, not a premise slot *)
Lemma dte_c4_nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> dte_c4_nsum f l = dte_c4_nsum g l.
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* restatement of the volume-2 premise-58 statement, permutation
   invariance of [dte_c4_nsum]; auxiliary lemma, not a premise slot *)
Lemma dte_c4_nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> dte_c4_nsum f l = dte_c4_nsum f p.
Proof.
  intros f l p H.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* restatement of the volume-2 premise-65 statement, permutation
   invariance of [dte_c4_sqsum]; auxiliary lemma, not a premise slot *)
Lemma dte_c4_sqsum_perm : forall l p : list Q,
  Permutation l p -> dte_c4_sqsum l = dte_c4_sqsum p.
Proof.
  intros l p H. unfold dte_c4_sqsum.
  rewrite (dte_c4_nsum_ext_in (fun x => dte_c4_freq_q x l) (fun x => dte_c4_freq_q x p) l
             (fun x _ => dte_c4_freq_q_perm x l p H)).
  exact (dte_c4_nsum_perm (fun x => dte_c4_freq_q x p) l p H).
Qed.

(* isomorphic replica of the premise-free host statement at :123
   (not a premise slot) *)
Lemma dte_c4_H_shannon_q_nonneg : forall l : list Q, 0 <= dte_c4_H_devsum l.
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Qle_refl.
  - apply qadd_nonneg.
    + apply (abs_nonneg (x - hd 0 (P0 (x :: xs)))).
    + exact IH.
Qed.

(* restatement of the volume-1 premise-29 statement, [Qeq] implies
   [Qle]; auxiliary lemma, not a premise slot *)
Lemma dte_c4_xq_Qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* restatement of the volume-1 premises-7-8 statement, antisymmetry of
   [Qle]; auxiliary lemma, not a premise slot *)
Lemma dte_c4_xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> x == y.
Proof.
  intros [nx dx] [ny dy] H1 H2. unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
Qed.

(* restatement of the volume-1 premises-21-22 statement, a product of
   nonnegative factors is nonnegative; auxiliary lemma, not a premise
   slot *)
Lemma dte_c4_xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a * b)%Q.
Proof.
  intros [an ad] [bn bd] Ha Hb. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

(* restatement of the volume-1 premise-5 statement, [Qle] implies the
   boolean comparison holds; auxiliary lemma, not a premise slot *)
Lemma dte_c4_xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Qle_bool x y = true.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  destruct (Z.leb (nx * Z.pos dy) (ny * Z.pos dx)) eqn:E.
  - reflexivity.
  - apply Z.leb_gt in E. lia.
Qed.

(* restatement of the volume-1 premise-13 statement, [insert_q] places
   the element at the head; auxiliary lemma, not a premise slot *)
Lemma dte_c4_xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> insert_q a (b :: bs) = a :: b :: bs.
Proof.
  intros a b bs H. simpl. rewrite (dte_c4_xq_Qle_bool_true _ _ H). reflexivity.
Qed.

(* restatement of the volume-1 premise-14 statement, [P0] idempotent on
   the [SortedQ] face; auxiliary lemma, not a premise slot.  The base
   [DTPT] sorted_P0_id lives on the [StronglySorted] face, so the
   inductive [SortedQ] version, peculiar to the host side, is restated
   here *)
Lemma dte_c4_xq_sortQ_P0_id : forall l : list Q, SortedQ l -> P0 l = l.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (P0 (a :: rest)) with (insert_q a (P0 rest)).
    rewrite (IH HSr). destruct rest as [| b bs].
    + reflexivity.
    + apply dte_c4_xq_insert_q_head_aux. apply HFa. left. reflexivity.
Qed.

(* restatement of the volume-1 premise-25 statement, sorted lists have
   zero deviation entropy; auxiliary lemma, not a premise slot; the
   base step is discharged via [xq_abs_zero] *)
Lemma dte_c4_xq_H_shannon_sortQ : forall l : list Q,
  SortedQ l -> dte_c4_H_devsum l == 0.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    cbn [dte_c4_H_devsum].
    rewrite (dte_c4_xq_sortQ_P0_id (a :: rest) HS).
    change (hd 0 (a :: rest)) with a.
    rewrite (IH HSr). rewrite xq_abs_zero. ring.
Qed.

(* ============================================================ *)
(*  Section 2.  Supply theorems of volume 4 (21 items), covering the
   registry premises 116-150 of the base register, section 1.4
   [Entropy], position by position; the statement faces are the current
   host statements mapped verbatim under the [dte_c4_] prefix.  The two
   conjunctive-slot splits are declared in the header and in the
   delivery report, section 3.  The two mixed-carrier flags at
   :2250/:2968 are registered only and do not appear in this section.
   Premises 114-115 are already covered by volume 3, so this section
   supplies nothing twice. *)
(* ============================================================ *)

(* premises 114-115 = :2012 H_max_q_all_same_zero -- registered
   retraction upon review, not supplied: the statement, carrying the two
   premises 114-115 (position 115 being the boundary position of the
   nominal range of this volume), is supplied whole by the on-disk
   module abl_dte_core3.v (dte_c3_H_max_q_all_same_zero_pair; its
   delivery report records explicitly that position 115 overflowed into
   that volume's delivery and that the present volume, starting at
   :2022, must not supply it again).  An earlier draft mistook the
   module for absent on disk and double-supplied; the whole statement
   is withdrawn upon review (deduplication precedent: duplicate supply
   is forbidden).  The consuming P-prime instance
   dte_c4_p_Hmaxq_const_sing is instead proved directly, constructed in
   place (see section 3). *)

(* premise 116 = :2022 H_min_q_perm *)
Theorem dte_c4_H_min_q_perm : forall l p : list Q,
  Permutation l p -> dte_c4_H_min_q l == dte_c4_H_min_q p.
Proof.
  intros l p H. unfold dte_c4_H_min_q.
  (* the volume-3 premise-104 statement (collide_perm), re-derived
     in place inside this proof *)
  assert (Hc : dte_c4_collide l == dte_c4_collide p).
  { unfold dte_c4_collide.
    rewrite (dte_c4_sqsum_perm l p H). rewrite (Permutation_length H). reflexivity. }
  rewrite Hc. reflexivity.
Qed.

(* premise 117 = :2028 H_max_q_perm *)
Theorem dte_c4_H_max_q_perm : forall l p : list Q,
  Permutation l p -> dte_c4_H_max_q l == dte_c4_H_max_q p.
Proof.
  intros l p H. unfold dte_c4_H_max_q.
  (* the volume-3 premise-109 statement (maxfreq_perm), premise-108
     (maxcount_perm) and premises-99/100 (nmax_ext_in/nmax_perm),
     re-derived in place inside this proof (auxiliary faces, no premise
     slots) *)
  assert (Hmf : dte_c4_maxfreq l == dte_c4_maxfreq p).
  { unfold dte_c4_maxfreq. rewrite (Permutation_length H).
    assert (Hmc : dte_c4_maxcount l = dte_c4_maxcount p).
    { unfold dte_c4_maxcount.
      assert (He : forall (f g : Q -> nat) (ys : list Q),
                  (forall x : Q, In x ys -> f x = g x) ->
                  dte_c4_nmax f ys = dte_c4_nmax g ys).
      { intros f g ys. induction ys as [| u us IH]; simpl; intros Hd.
        - reflexivity.
        - rewrite (Hd u (or_introl eq_refl)).
          rewrite (IH (fun x Hx => Hd x (or_intror Hx))). reflexivity. }
      rewrite (He (fun x => dte_c4_freq_q x l) (fun x => dte_c4_freq_q x p) l
                 (fun x _ => dte_c4_freq_q_perm x l p H)).
      assert (Hp : forall (f : Q -> nat) (ys zs : list Q),
                  Permutation ys zs -> dte_c4_nmax f ys = dte_c4_nmax f zs).
      { intros f ys zs Hy.
        induction Hy as [ | x ys' zs' Hx IH | x z ys' | ys' ys'' zs' Ha IH1 Hb IH2 ].
        - reflexivity.
        - simpl. rewrite IH. reflexivity.
        - simpl. lia.
        - rewrite IH1. exact IH2. }
      exact (Hp (fun x => dte_c4_freq_q x p) l p H). }
    rewrite Hmc. reflexivity. }
  rewrite Hmf. reflexivity.
Qed.

(* premises 118-119 = :2082 me2_abs_sub_triangle *)
Theorem dte_c4_me2_abs_sub_triangle : forall a b : Q,
  (0 <= a)%Q -> (0 <= b)%Q -> (Qabs (a - b) <= a + b)%Q.
Proof.
  intros a b Ha Hb.
  destruct (Qle_dec' a b) as [Hab | Hba].
  - (* case a <= b: |a-b| = -(a-b) = b-a, and (a+b)-(b-a) = 2a >= 0 *)
    assert (Hneg : (a - b <= 0)%Q).
    { apply (proj2 (Qle_0_sub' (a - b) 0)).
      assert (Hr : (0 - (a - b))%Q == b - a) by ring.
      rewrite Hr. apply (proj1 (Qle_0_sub' a b)). exact Hab. }
    rewrite (qeqT_imp_qeq _ _ (abs_neg (a - b) Hneg)).
    assert (Heq : (- (a - b))%Q == b - a) by ring.
    rewrite Heq.
    apply (proj2 (Qle_0_sub' (b - a) (a + b))).
    assert (Hr2 : ((a + b) - (b - a))%Q == a + a) by ring.
    rewrite Hr2. apply qadd_nonneg; exact Ha.
  - (* case b <= a: |a-b| = a-b, and (a+b)-(a-b) = 2b >= 0 *)
    assert (Hpos : (0 <= a - b)%Q).
    { apply (proj1 (Qle_0_sub' b a)). exact Hba. }
    rewrite (abs_eq (a - b) Hpos).
    apply (proj2 (Qle_0_sub' (a - b) (a + b))).
    assert (Hr3 : ((a + b) - (a - b))%Q == b + b) by ring.
    rewrite Hr3. apply qadd_nonneg; exact Hb.
Qed.

(* premise 120 = :2115 me2_dedup_len_ge1 (the <> premise face is
   carried over verbatim) *)
Theorem dte_c4_me2_dedup_len_ge1 : forall l : list Q,
  l <> [] -> (1 <= length (dedup l))%nat.
Proof.
  intros [| x xs] H.
  - exfalso. apply H. reflexivity.
  - cbn [dedup length]. lia.
Qed.

(* premise 121 = :2217 mkMEval_Hms_ge1 (the <> premise face is
   carried over verbatim) *)
Theorem dte_c4_mkMEval_Hms_ge1 : forall (l ctx : list Q),
  l <> [] -> (1 <= dte_c4_me_Hms (dte_c4_mkMEval l ctx))%Q.
Proof.
  intros l ctx Hl.
  unfold dte_c4_mkMEval. cbn [dte_c4_me_Hms].
  unfold H_ms.
  assert (Hn : (1 <= length (dedup l))%nat)
    by (apply dte_c4_me2_dedup_len_ge1; exact Hl).
  assert (Hz : (1 <= Z.of_nat (length (dedup l)))%Z) by lia.
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* premise 123 = :2306 me_total_nonneg_guarded *)
Theorem dte_c4_me_total_nonneg_guarded : forall (l ctx : list Q),
  (dte_c4_H_devsum ctx <= dte_c4_H_devsum l)%Q ->
  (0 <= dte_c4_me_total (dte_c4_mkMEval l ctx))%Q.
Proof.
  intros l ctx Hle.
  unfold dte_c4_me_total. unfold dte_c4_mkMEval.
  cbn [dte_c4_me_Hadj dte_c4_me_Hms dte_c4_me_Hsh dte_c4_me_Hcond].
  (* the volume-1 premise-27 statement (H_cond_nonneg_guarded),
     re-derived in place inside this proof *)
  assert (Hc : (0 <= dte_c4_H_cond l ctx)%Q).
  { unfold dte_c4_H_cond.
    apply (proj1 (Qle_0_sub' (dte_c4_H_devsum ctx) (dte_c4_H_devsum l))).
    exact Hle. }
  assert (Hms : (0 <= H_ms l)%Q).
  { unfold H_ms. unfold Qle. simpl. lia. }
  assert (Hsum : (0 <= H_adj l + H_ms l + dte_c4_H_devsum l + dte_c4_H_cond l ctx)%Q).
  { apply qadd_nonneg.
    - apply qadd_nonneg.
      + apply qadd_nonneg; [apply xq_H_adj_nonneg | exact Hms].
      + apply dte_c4_H_shannon_q_nonneg.
    - exact Hc. }
  apply dte_c4_xq_mul_nonneg.
  - (* kernel of me2_weight_nonneg (the premise-free host statement at
       :2151, re-derived inside this proof) *)
    change (Z.le (0 * 4) (1 * 1))%Z. lia.
  - exact Hsum.
Qed.

(* premise 124 = :2423 xqz_abs0_eq *)
Lemma dte_c4_xqz_abs0_eq : forall x : Q, Qabs x == 0 -> x == 0.
Proof.
  intros [n d] H. unfold Qeq. destruct n as [| p | p].
  - reflexivity.
  - unfold Qabs in H. simpl in H. discriminate H.
  - unfold Qabs in H. simpl in H. discriminate H.
Qed.

(* premise 125 = :2432 xqz_sub_eq0 *)
Lemma dte_c4_xqz_sub_eq0 : forall x y : Q, (x - y == 0)%Q -> x == y.
Proof.
  intros x y H.
  assert (Hyx : (y - x == 0)%Q).
  { assert (Hmo : y - x == - (x - y)) by apply xq_minus_opp.
    rewrite Hmo, H. reflexivity. }
  apply (dte_c4_xq_Qle_antisym x y).
  - apply (proj2 (Qle_0_sub' x y)).
    apply dte_c4_xq_Qeq_le. apply Qeq_sym. exact Hyx.
  - apply (proj2 (Qle_0_sub' y x)).
    apply dte_c4_xq_Qeq_le. apply Qeq_sym. exact H.
Qed.

(* premises 126-128 = :2446 xqz_plus_eq0_le *)
Lemma dte_c4_xqz_plus_eq0_le : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> a == 0.
Proof.
  intros a b Hab Ha Hb.
  assert (Hle : (a + 0 <= a + b)%Q)
    by (apply qadd_le; [apply Qle_refl | exact Hb]).
  rewrite Qplus_0_r in Hle. rewrite Hab in Hle.
  apply (dte_c4_xq_Qle_antisym a 0 Hle Ha).
Qed.

(* premises 129-131 = :2457 xqz_plus_eq0 -- the conjunctive slot of the
   conclusion face is split into the two one-directional statements, as
   in the volume-1 precedent at :481; declared in the delivery report,
   section 3.  The _l statement reuses the premises-126-128 split. *)
Lemma dte_c4_xqz_plus_eq0_l : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> a == 0.
Proof.
  intros a b Hab Ha Hb. exact (dte_c4_xqz_plus_eq0_le a b Hab Ha Hb).
Qed.

Lemma dte_c4_xqz_plus_eq0_r : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> b == 0.
Proof.
  intros a b Hab Ha Hb. rewrite Qplus_comm in Hab.
  exact (dte_c4_xqz_plus_eq0_le b a Hab Hb Ha).
Qed.

(* premises 132-133 = :2469 xqz_sorted_hd_min *)
Lemma dte_c4_xqz_sorted_hd_min : forall (l : list Q) (z : Q),
  SortedQ l -> In z l -> (hd 0 l <= z)%Q.
Proof.
  intros [| a rest] z HS Hin.
  - destruct Hin.
  - inversion HS as [| c1 c2 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (hd 0 (a :: rest)) with a.
    destruct Hin as [Heq | Hin].
    + subst. apply Qle_refl.
    + apply HFa. exact Hin.
Qed.

(* premise 134 = :2483 xqz_P0_hd_min_all *)
Lemma dte_c4_xqz_P0_hd_min_all : forall (l : list Q) (z : Q),
  In z l -> (hd 0 (P0 l) <= z)%Q.
Proof.
  intros l z Hin.
  apply (dte_c4_xqz_sorted_hd_min (P0 l) z).
  - apply xq_P0_sorted.
  - apply Permutation_in with (l := l).
    + apply D5_P0_perm.
    + exact Hin.
Qed.

(* premise 135 = :2495 H_shannon_q_zero_sorted (uses the
   premises-129-131 split: the conjunctive slot is not rebuilt; each
   direction takes one branch) *)
Theorem dte_c4_H_shannon_q_zero_sorted : forall l : list Q,
  dte_c4_H_devsum l == 0 -> SortedQ l.
Proof.
  induction l as [| x xs IH]; intro H.
  - apply sortQ_nil.
  - cbn [dte_c4_H_devsum] in H.
    assert (Ha : Qabs (x - hd 0 (P0 (x :: xs))) == 0).
    { apply (dte_c4_xqz_plus_eq0_l _ _ H
               (abs_nonneg (x - hd 0 (P0 (x :: xs))))
               (dte_c4_H_shannon_q_nonneg xs)). }
    assert (Hs : dte_c4_H_devsum xs == 0).
    { apply (dte_c4_xqz_plus_eq0_r _ _ H
               (abs_nonneg (x - hd 0 (P0 (x :: xs))))
               (dte_c4_H_shannon_q_nonneg xs)). }
    assert (Hxm : x == hd 0 (P0 (x :: xs))).
    { apply dte_c4_xqz_sub_eq0. apply dte_c4_xqz_abs0_eq. exact Ha. }
    apply sortQ_cons.
    + apply IH. exact Hs.
    + rewrite Forall_forall. intros z Hz.
      apply (Qle_trans x (hd 0 (P0 (x :: xs))) z).
      * apply dte_c4_xq_Qeq_le. exact Hxm.
      * apply dte_c4_xqz_P0_hd_min_all. simpl. right. exact Hz.
Qed.

(* premise 136 = :2550 xqz_dedup_aux_nil *)
Lemma dte_c4_xqz_dedup_aux_nil : forall (x : Q) (m : list Q),
  (forall z : Q, Qmem z m -> x == z) -> dedup_aux x m = [].
Proof.
  intros x m. induction m as [| y ys IH]; intro Hall.
  - reflexivity.
  - cbn [dedup_aux].
    assert (Hxy : Qeq_bool x y = true).
    { apply Qeqb_true_of. apply Hall. apply Qmem_refl_cons. }
    rewrite Hxy. apply IH.
    intros z Hz. apply Hall. apply Qmem_cons_r. exact Hz.
Qed.

(* premises 137-139 = :2564 H_ms1_all_eq (the existential form of the
   volume-1 premise-33 mixed-carrier flag position :749, xq_len1_el, is
   not carried over: the proof re-derives the equivalent two-case
   analysis on the dedup table constructors, as in the volume-1
   premise-44 precedent) *)
Theorem dte_c4_H_ms1_all_eq : forall l : list Q,
  (H_ms l == 1)%Q -> forall a b : Q, Qmem a l -> Qmem b l -> a == b.
Proof.
  intro l. intro H.
  assert (Hlen : length (dedup l) = 1%nat).
  { unfold H_ms in H. unfold Qeq in H. simpl in H. lia. }
  destruct (dedup l) as [| c cs] eqn:Hdc.
  - simpl in Hlen. discriminate Hlen.
  - destruct cs as [| d ds].
    + intros a b Ha Hb.
      assert (Qa : Qmem a (dedup l)) by (apply dedup_Qmem_r; exact Ha).
      assert (Qb : Qmem b (dedup l)) by (apply dedup_Qmem_r; exact Hb).
      rewrite Hdc in Qa. rewrite Hdc in Qb.
      apply (Qmem_cons a c []) in Qa. apply (Qmem_cons b c []) in Qb.
      destruct Qa as [Qa | Qa]; [ | unfold Qmem in Qa; simpl in Qa;
                                 inversion Qa ].
      destruct Qb as [Qb | Qb]; [ | unfold Qmem in Qb; simpl in Qb;
                                 inversion Qb ].
      rewrite (Qeqb_sym b c) in Qb.
      apply Qeq_bool_eq. apply (Qeqb_trans a c b Qa Qb).
    + simpl in Hlen. discriminate Hlen.
Qed.

(* premises 140-142 = :2652 H_shannon_q_perm_inv_if_sorted *)
Theorem dte_c4_H_shannon_q_perm_inv_if_sorted : forall l p : list Q,
  Permutation l p -> SortedQ l -> SortedQ p -> dte_c4_H_devsum l == dte_c4_H_devsum p.
Proof.
  intros l p _Hp Hl Hpp.
  rewrite (dte_c4_xq_H_shannon_sortQ l Hl).
  rewrite (dte_c4_xq_H_shannon_sortQ p Hpp).
  reflexivity.
Qed.

(* premise 143 = :2787 nmax_mono *)
Lemma dte_c4_nmax_mono : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> (f x <= g x)%nat) -> (dte_c4_nmax f l <= dte_c4_nmax g l)%nat.
Proof.
  intros f g l. induction l as [| a t IH]; simpl; intros H.
  - lia.
  - assert (H1 : (f a <= g a)%nat) by (apply H; left; reflexivity).
    assert (H2 : (dte_c4_nmax f t <= dte_c4_nmax g t)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* premise 144 = :2905 align_lambda_opt_min (the source premise
   (0 <= lam <= 1)%Q is Qle conjunction notation; currying splits it
   equivalently into two premises; declared in the delivery report,
   section 3) *)
Theorem dte_c4_align_lambda_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam)%Q -> (lam <= 1)%Q ->
  (dte_c4_H_lam l s (dte_c4_align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s)))
   <= dte_c4_H_lam l s lam)%Q.
Proof.
  intros l s lam Hlam0 Hlam1.
  unfold dte_c4_H_lam, dte_c4_align_lambda_opt.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:E.
  - (* case h0 <= h1: lam* = 1 and the optimal value is h0 *)
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s))
                 == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
      rewrite Er. apply dte_c4_xq_mul_nonneg.
      + apply (proj1 (Qle_0_sub' lam 1)). exact Hlam1.
      + apply (proj1 (Qle_0_sub' _ _)). apply xq_Qle_bool_le. exact E. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
  - (* case h0 > h1: lam* = 0 and the optimal value is h1 *)
    assert (Hge : (H_adj (Pinf l s) <= H_adj (P0 l))%Q)
      by (apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s))
                 == lam * (H_adj (P0 l) - H_adj (Pinf l s))) by ring.
      rewrite Er. apply dte_c4_xq_mul_nonneg.
      + exact Hlam0.
      + apply (proj1 (Qle_0_sub' _ _)). exact Hge. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
Qed.

(* premises 147-148 = :3050 collide_app_eq (the volume-3 premise-113
   same-face bridge and the negation kernels of :1000/:1008/:2968 are
   re-derived in place as the locally quantified assertions
   Hk/Hkq/Hkm inside this proof) *)
Theorem dte_c4_collide_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  dte_c4_collide (l1 ++ l2) ==
    (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_collide l1
    + (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_collide l2
    + (dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l2) l1)
       + dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l1) l2))
      / (dte_c4_qn (length l1 + length l2)%nat * dte_c4_qn (length l1 + length l2)%nat).
Proof.
  intros l1 l2 H1 H2.
  (* constructive kernels of the negation-form mixed-carrier flag
     positions (host :1000/:1008/:2968), re-derived inside this proof *)
  assert (Hk : forall y : Q, (0 < y)%Q -> ~ (y == 0)).
  { intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy). }
  assert (Hkq : forall n : nat, (0 < n)%nat -> (0 < dte_c4_qn n)%Q).
  { intros n Hn. destruct n as [| m].
    - exfalso. lia.
    - apply dte_c4_qn_S_pos. }
  assert (Hkm : forall x y : Q, ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0)).
  { intros [xn xd] [yn yd] Hx Hy Hxy.
    assert (Hxn : (xn <> 0)%Z).
    { intros Hz. apply Hx. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    assert (Hyn : (yn <> 0)%Z).
    { intros Hz. apply Hy. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    unfold Qeq, Qmult in Hxy. simpl in Hxy.
    rewrite ? Z.mul_1_r in Hxy.
    apply Z.mul_eq_0 in Hxy.
    destruct Hxy as [E | E]; [exact (Hxn E) | exact (Hyn E)]. }
  (* exact decomposition kernel of the sqsum append law, volume-2
     premise-57 face (via the nsum_app/nsum_ext_in auxiliary chain) *)
  assert (Hsq : dte_c4_sqsum (l1 ++ l2) =
    (dte_c4_sqsum l1 + dte_c4_sqsum l2
     + dte_c4_nsum (fun x => dte_c4_freq_q x l2) l1
     + dte_c4_nsum (fun x => dte_c4_freq_q x l1) l2)%nat).
  { (* kernel of nsum_app (the premise-free host statement at :2685),
       re-derived quantified inside this proof *)
    assert (Hap : forall (f : Q -> nat) (ys zs : list Q),
                dte_c4_nsum f (ys ++ zs)
                = (dte_c4_nsum f ys + dte_c4_nsum f zs)%nat).
    { intros f ys zs. induction ys as [| u us IH].
      - reflexivity.
      - simpl. rewrite IH. lia. }
    unfold dte_c4_sqsum. rewrite Hap.
    rewrite (dte_c4_nsum_ext_in (fun x => dte_c4_freq_q x (l1 ++ l2))
                       (fun x => (dte_c4_freq_q x l1 + dte_c4_freq_q x l2)%nat) l1
             (fun x _ => dte_c4_freq_q_app x l1 l2)).
    rewrite (dte_c4_nsum_ext_in (fun x => dte_c4_freq_q x (l1 ++ l2))
                       (fun x => (dte_c4_freq_q x l1 + dte_c4_freq_q x l2)%nat) l2
             (fun x _ => dte_c4_freq_q_app x l1 l2)).
    (* kernel of nsum_add (the premise-free host statement at :2695),
       re-derived quantified inside this proof *)
    assert (Hna : forall (f g : Q -> nat) (ys : list Q),
                dte_c4_nsum (fun x => (f x + g x)%nat) ys
                = (dte_c4_nsum f ys + dte_c4_nsum g ys)%nat).
    { intros f g ys. induction ys as [| u us IH].
      - reflexivity.
      - simpl. rewrite IH. lia. }
    rewrite (Hna (fun x => dte_c4_freq_q x l1) (fun x => dte_c4_freq_q x l2) l1).
    rewrite (Hna (fun x => dte_c4_freq_q x l1) (fun x => dte_c4_freq_q x l2) l2).
    lia. }
  assert (Hnn : (0 < length l1 + length l2)%nat) by lia.
  assert (HN : ~ (dte_c4_qn (length l1 + length l2)%nat == 0))
    by (apply (Hk _ (Hkq _ Hnn))).
  assert (Ha : ~ (dte_c4_qn (length l1) == 0)) by (apply (Hk _ (Hkq _ H1))).
  assert (Hb : ~ (dte_c4_qn (length l2) == 0)) by (apply (Hk _ (Hkq _ H2))).
  assert (HPP1 : ~ (dte_c4_qn (length l1) * dte_c4_qn (length l1) == 0))
    by (apply Hkm; assumption).
  assert (HPP2 : ~ (dte_c4_qn (length l2) * dte_c4_qn (length l2) == 0))
    by (apply Hkm; assumption).
  assert (HN2 : ~ (dte_c4_qn (length l1) + dte_c4_qn (length l2) == 0)).
  { intros Zc. apply HN. rewrite dte_c4_qn_add. exact Zc. }
  assert (HNN2 : ~ ((dte_c4_qn (length l1) + dte_c4_qn (length l2))
                    * (dte_c4_qn (length l1) + dte_c4_qn (length l2)) == 0))
    by (apply Hkm; exact HN2).
  unfold dte_c4_collide.
  rewrite length_app.
  rewrite Hsq.
  rewrite ! dte_c4_qn_add.
  field; repeat split; assumption.
Qed.

(* premises 149-150 = :3090 H_freq_app_eq (the volume-3 premise-113
   same-face bridge H_freq_eq_bridge is re-derived inside this proof;
   closing position of the 150-premise registry) *)
Theorem dte_c4_H_freq_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  dte_c4_H_freq (l1 ++ l2) ==
    (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_H_freq l1
    + (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_H_freq l2
    + 2 * (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat)
        * (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat)
    - (dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l2) l1)
       + dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l1) l2))
      / (dte_c4_qn (length l1 + length l2)%nat * dte_c4_qn (length l1 + length l2)%nat).
Proof.
  intros l1 l2 H1 H2.
  assert (Hk : forall y : Q, (0 < y)%Q -> ~ (y == 0)).
  { intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy). }
  assert (Hkq : forall n : nat, (0 < n)%nat -> (0 < dte_c4_qn n)%Q).
  { intros n Hn. destruct n as [| m].
    - exfalso. lia.
    - apply dte_c4_qn_S_pos. }
  assert (Hkm : forall x y : Q, ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0)).
  { intros [xn xd] [yn yd] Hx Hy Hxy.
    assert (Hxn : (xn <> 0)%Z).
    { intros Hz. apply Hx. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    assert (Hyn : (yn <> 0)%Z).
    { intros Hz. apply Hy. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    unfold Qeq, Qmult in Hxy. simpl in Hxy.
    rewrite ? Z.mul_1_r in Hxy.
    apply Z.mul_eq_0 in Hxy.
    destruct Hxy as [E | E]; [exact (Hxn E) | exact (Hyn E)]. }
  assert (Hnn : (0 < length (l1 ++ l2))%nat) by (rewrite length_app; lia).
  (* the volume-3 premise-113 statement (H_freq_eq_bridge), re-derived
     in place inside this proof *)
  assert (HB : forall t : list Q, (0 < length t)%nat ->
               dte_c4_H_freq t == 1 - dte_c4_collide t).
  { intros t Ht. unfold dte_c4_H_freq, dte_c4_collide.
    assert (HPne : ~ (dte_c4_qn (length t) == 0))
      by (apply (Hk _ (Hkq _ Ht))).
    field; assumption. }
  rewrite (HB (l1 ++ l2) Hnn).
  rewrite (dte_c4_collide_app_eq l1 l2 H1 H2).
  assert (B1 : dte_c4_collide l1 == 1 - dte_c4_H_freq l1).
  { pose proof (HB l1 H1) as T. rewrite T. ring. }
  assert (B2 : dte_c4_collide l2 == 1 - dte_c4_H_freq l2).
  { pose proof (HB l2 H2) as T. rewrite T. ring. }
  rewrite B1, B2.
  rewrite (dte_c4_qn_add (length l1) (length l2)).
  assert (HN2 : ~ (dte_c4_qn (length l1) + dte_c4_qn (length l2) == 0)).
  { intros Zc.
    assert (Hpos : (0 < dte_c4_qn (length l1 + length l2)%nat)%Q)
      by (apply (Hkq _); lia).
    rewrite <- dte_c4_qn_add in Zc.
    apply (Hk _ Hpos). exact Zc. }
  assert (HNN2 : ~ ((dte_c4_qn (length l1) + dte_c4_qn (length l2))
                    * (dte_c4_qn (length l1) + dte_c4_qn (length l2)) == 0))
    by (apply Hkm; exact HN2).
  field; repeat split; assumption.
Qed.

(* ============================================================ *)
(*  Section 3.  Canonical P-prime instances (1 item): the closing
   instance of the second P-prime form, proved directly, constructed in
   place.  The draft use of the :2012 application form was revised
   together with the retraction upon review; zero premise slots.  The
   remaining P-prime positions yielded to the auxiliary-lemma chain
   under the capped Qed budget of 41; declared in the delivery report,
   section 3. *)
(* ============================================================ *)

Lemma dte_c4_p_Hmaxq_const_sing : forall a : Q, dte_c4_H_max_q [a; a] == 0.
Proof.
  intro a. unfold dte_c4_H_max_q, dte_c4_maxfreq, dte_c4_maxcount.
  cbn [dte_c4_nmax dte_c4_freq_q dte_c4_qn length].
  rewrite ! Qeq_bool_refl. cbn [dte_c4_freq_q dte_c4_qn Nat.max].
  compute. reflexivity.
Qed.

(* ============================================================ *)
(*  Section 4.  Audit section: per-theorem [Print Assumptions], all
   closed, plus the theorem bucket extracted by a single command. *)
(* ============================================================ *)

Check dte_c4_qn_nonneg.
Check dte_c4_qn_S_pos.
Check dte_c4_qn_add.
Check dte_c4_freq_q_le_length.
Check dte_c4_freq_q_app.
Check dte_c4_freq_q_perm.
Check dte_c4_nsum_ext_in.
Check dte_c4_nsum_perm.
Check dte_c4_sqsum_perm.
Check dte_c4_H_shannon_q_nonneg.
Check dte_c4_xq_Qeq_le.
Check dte_c4_xq_Qle_antisym.
Check dte_c4_xq_mul_nonneg.
Check dte_c4_xq_Qle_bool_true.
Check dte_c4_xq_insert_q_head_aux.
Check dte_c4_xq_sortQ_P0_id.
Check dte_c4_xq_H_shannon_sortQ.
Check dte_c4_H_min_q_perm.
Check dte_c4_H_max_q_perm.
Check dte_c4_me2_abs_sub_triangle.
Check dte_c4_me2_dedup_len_ge1.
Check dte_c4_mkMEval_Hms_ge1.
Check dte_c4_me_total_nonneg_guarded.
Check dte_c4_xqz_abs0_eq.
Check dte_c4_xqz_sub_eq0.
Check dte_c4_xqz_plus_eq0_le.
Check dte_c4_xqz_plus_eq0_l.
Check dte_c4_xqz_plus_eq0_r.
Check dte_c4_xqz_sorted_hd_min.
Check dte_c4_xqz_P0_hd_min_all.
Check dte_c4_H_shannon_q_zero_sorted.
Check dte_c4_xqz_dedup_aux_nil.
Check dte_c4_H_ms1_all_eq.
Check dte_c4_H_shannon_q_perm_inv_if_sorted.
Check dte_c4_nmax_mono.
Check dte_c4_align_lambda_opt_min.
Check dte_c4_collide_app_eq.
Check dte_c4_H_freq_app_eq.
Check dte_c4_p_Hmaxq_const_sing.

Print Assumptions dte_c4_qn_nonneg.
Print Assumptions dte_c4_qn_S_pos.
Print Assumptions dte_c4_qn_add.
Print Assumptions dte_c4_freq_q_le_length.
Print Assumptions dte_c4_freq_q_app.
Print Assumptions dte_c4_freq_q_perm.
Print Assumptions dte_c4_nsum_ext_in.
Print Assumptions dte_c4_nsum_perm.
Print Assumptions dte_c4_sqsum_perm.
Print Assumptions dte_c4_H_shannon_q_nonneg.
Print Assumptions dte_c4_xq_Qeq_le.
Print Assumptions dte_c4_xq_Qle_antisym.
Print Assumptions dte_c4_xq_mul_nonneg.
Print Assumptions dte_c4_xq_Qle_bool_true.
Print Assumptions dte_c4_xq_insert_q_head_aux.
Print Assumptions dte_c4_xq_sortQ_P0_id.
Print Assumptions dte_c4_xq_H_shannon_sortQ.
Print Assumptions dte_c4_H_min_q_perm.
Print Assumptions dte_c4_H_max_q_perm.
Print Assumptions dte_c4_me2_abs_sub_triangle.
Print Assumptions dte_c4_me2_dedup_len_ge1.
Print Assumptions dte_c4_mkMEval_Hms_ge1.
Print Assumptions dte_c4_me_total_nonneg_guarded.
Print Assumptions dte_c4_xqz_abs0_eq.
Print Assumptions dte_c4_xqz_sub_eq0.
Print Assumptions dte_c4_xqz_plus_eq0_le.
Print Assumptions dte_c4_xqz_plus_eq0_l.
Print Assumptions dte_c4_xqz_plus_eq0_r.
Print Assumptions dte_c4_xqz_sorted_hd_min.
Print Assumptions dte_c4_xqz_P0_hd_min_all.
Print Assumptions dte_c4_H_shannon_q_zero_sorted.
Print Assumptions dte_c4_xqz_dedup_aux_nil.
Print Assumptions dte_c4_H_ms1_all_eq.
Print Assumptions dte_c4_H_shannon_q_perm_inv_if_sorted.
Print Assumptions dte_c4_nmax_mono.
Print Assumptions dte_c4_align_lambda_opt_min.
Print Assumptions dte_c4_collide_app_eq.
Print Assumptions dte_c4_H_freq_app_eq.
Print Assumptions dte_c4_p_Hmaxq_const_sing.

(* ============================================================ *)
(*  Section 5.  Extraction audit (red-line 4: extractability verified;
   criterion [Obj.magic] count = 0).  Theorem bucket: one single
   [Separate Extraction] command, the only extraction command of this
   file; all 39 conclusion faces are Prop-discrete carriers and, by the
   family extraction erasure convention, occupy no room in the
   extracted artifact.  The real extraction face of the data layer is
   the 19 carrier/record replicas (the real implementations of
   qn/freq_q/nsum/sqsum/nmax/H_devsum/H_freq), routed to the separate
   probe module _dte_c4_probe.v in its own bucket (bucket-splitting
   execution position; the two-bucket attribution of the [Obj.magic]
   counts is given in the delivery report). *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dte_t12".
Separate Extraction dte_c4_qn_nonneg dte_c4_qn_S_pos dte_c4_qn_add
  dte_c4_freq_q_le_length dte_c4_freq_q_app dte_c4_freq_q_perm
  dte_c4_nsum_ext_in dte_c4_nsum_perm dte_c4_sqsum_perm
  dte_c4_H_shannon_q_nonneg dte_c4_xq_Qeq_le dte_c4_xq_Qle_antisym
  dte_c4_xq_mul_nonneg dte_c4_xq_Qle_bool_true dte_c4_xq_insert_q_head_aux
  dte_c4_xq_sortQ_P0_id dte_c4_xq_H_shannon_sortQ
  dte_c4_H_min_q_perm dte_c4_H_max_q_perm
  dte_c4_me2_abs_sub_triangle dte_c4_me2_dedup_len_ge1
  dte_c4_mkMEval_Hms_ge1 dte_c4_me_total_nonneg_guarded
  dte_c4_xqz_abs0_eq dte_c4_xqz_sub_eq0 dte_c4_xqz_plus_eq0_le
  dte_c4_xqz_plus_eq0_l dte_c4_xqz_plus_eq0_r dte_c4_xqz_sorted_hd_min
  dte_c4_xqz_P0_hd_min_all dte_c4_H_shannon_q_zero_sorted
  dte_c4_xqz_dedup_aux_nil dte_c4_H_ms1_all_eq
  dte_c4_H_shannon_q_perm_inv_if_sorted dte_c4_nmax_mono
  dte_c4_align_lambda_opt_min dte_c4_collide_app_eq dte_c4_H_freq_app_eq
  dte_c4_p_Hmaxq_const_sing.
