(* ConstructiveWorld-Set -- max-side list lattice glue over the B-form order. *)
(** * UpReqLatbMaxList: the pointwise [real_max] fold over nonempty real lists.
    Mission.  [latb_max_list] folds [real_max] over a nonempty list, driven by
      the head [h]: an empty tail leaves the head, so no unit-element premise
      is ever required, and the fold is the pointwise [Qmax] coding (a plain
      pointwise function, not a least-upper-bound operator).  The statements:
      [latb_max_list_cons_eq] is the fold's unfold step;
      [latb_lt_max_list_intro] lifts the binary strict-bound rule to lists
      (members strictly below [d] imply the fold strictly below [d]);
      [latb_max_list_le_b] states the upper-bound lattice law (members all
      below [c] in the Bishop sense imply the fold below [c]) and
      [latb_max_list_le_b_ind] proves the same statement by a second,
      induction route; [latb_max_list_le_l], [latb_max_list_le_cons_tail],
      [latb_max_list_le_cons_init] and [latb_max_list_le_prepend] are the lower-bound
      companions (list forms of the E.1/E.2 max bounds).
    Dependencies.  Stdlib [List], [Extraction]; [S01_BaseRing] ..
      [S15_TailFEPUp]; [UpRealLeB], [UpRealLeB2], [UpRealLeB3], [G06_BForm].
    References.  The same-name baseline module in ConstructiveWorld-Main
      (statement names carried over verbatim; statement-face Set-carrier
      completion: the stdlib [In] premises of the two bound lemmas are
      recast at the Set-carried [InT] of [S01_BaseRing]; the binary rules
      consumed here are [G06_BForm.latb_max_le_b], [G06_BForm.latb_lt_max_intro]
      and [G06_BForm.latb_min_glb], the meet-side dual named for contrast).
    Constructivity.  All ten statements are carried by [Set]: conclusions
      live in [real_lt]/[real_le_b] ([QltT]/[sigT] carriers) or in [Id], and
      list membership is the Set-valued [InT]; no statement uses [Prop].
      Every proof ends in [Defined] (transparent, extraction-visible) and is
      axiom-free: [Print Assumptions] reports [Closed] for every name.
    Build.  coqc -Q <root holding the compiled [S01_BaseRing] .. [G06_BForm]
      closure> "" UpReqLatbMaxList.v (exit 0; artifact begins [436f7121 000160bc]). *)
From Stdlib Require Import Extraction.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import G06_BForm.

(* ============================================================ *)
(* Part 1. The fold and its unfold step.                        *)
(* ============================================================ *)

(* Item 0. The pointwise max fold over a nonempty list: the head [h] seeds
   the accumulator and each tail element is merged by [real_max].  The
   head-driven shape has no empty case, so the upper-bound law and its
   lower-bound companions need no unit-element premise. *)
Definition latb_max_list (h : Real) (t : list Real) : Real :=
  fold_right real_max h t.

(* Unfold step: one fold step is one [real_max] merge.  Each direction is
   a delta-iota conversion, usable with [change] to avoid relying on the
   refolding behaviour of [simpl]. *)
Lemma latb_max_list_cons_eq :
  forall (h w : Real) (t : list Real),
    Id (latb_max_list h (w :: t)) (real_max w (latb_max_list h t)).
Proof.
  intros h w t.
  unfold latb_max_list.
  simpl.
  exact (@id_refl _ (real_max w (latb_max_list h t))).
Defined.

(* Membership weakening for the recast premise face: extending a list by
   one tail element preserves membership.  This is the Set-carried
   counterpart of [in_cons]; proved by dependent elimination on the
   membership witness, dispatching on the head and tail positions. *)
Lemma latb_InT_tail_weak : forall (h w x : Real) (t : list Real),
  InT x (h :: t) -> InT x (h :: w :: t).
Proof.
  intros h w x t Hx.
  refine
    (match Hx in InT _ L
            return (match L with
                    | nil => Empty_set
                    | a :: l' => InT x (a :: w :: l')
                    end) with
     | InT_here _ l0 => InT_here x (w :: l0)
     | InT_next _ y0 l0 i1 =>
         InT_next x y0 (w :: l0) (InT_next x w l0 i1)
     end).
Defined.

(* ============================================================ *)
(* Part 2. Strict-bound introduction and the upper-bound lattice law. *)
(* ============================================================ *)

(* Item 1. Strict-bound introduction: if every member of [h :: t] is
   strictly below [d], the fold is strictly below [d].  List induction
   glued by the binary rule [latb_lt_max_intro]; the empty-tail case is
   the head bound itself.  This is the max-side list dual of the meet
   rule [latb_min_glb]; the eps slot of the main bound lemma below lands
   exactly in this conclusion position. *)
Lemma latb_lt_max_list_intro : forall (h : Real) (t : list Real) (d : Real),
  (forall x : Real, InT x (h :: t) -> real_lt x d) ->
  real_lt (latb_max_list h t) d.
Proof.
  intros h t d H. induction t as [| w rest IH].
  - exact (H h (InT_here h nil)).
  - change (real_lt (real_max w (latb_max_list h rest)) d).
    apply latb_lt_max_intro.
    + exact (H w (InT_next w h (w :: rest) (InT_here w rest))).
    + apply IH. intros x Hx.
      exact (H x (latb_InT_tail_weak h w x rest Hx)).
Defined.

(* Item 2 (main). Upper-bound lattice law, list form: if every member is
   below [c] in the Bishop sense [real_le_b], the fold is below [c].
   One-step route: instantiate the margin at [eps], bound the same
   members strictly at [d := real_plus c eps] (Item 1), and close with
   the strict branch of [real_le] through the one-step completer
   [real_le_closure_b_one].  The eps slot sitting inside the conclusion
   of Item 1 is what makes the max side a one-step proof; see the
   binary rule [latb_max_le_b] for the same shape at two arguments. *)
Lemma latb_max_list_le_b : forall (h : Real) (t : list Real) (c : Real),
  (forall x : Real, InT x (h :: t) -> real_le_b x c) ->
  real_le_b (latb_max_list h t) c.
Proof.
  intros h t c H.
  apply real_le_closure_b_one. intros eps Heps. unfold real_le. left.
  apply latb_lt_max_list_intro. intros x Hx.
  exact (H x Hx eps Heps).
Defined.

(* Item 3 (main, second route). The same statement proved by list
   induction, gluing each fold step with the binary law
   [latb_max_le_b]: the empty-tail case is the head bound; the cons
   case bounds the new head and the tail fold separately.  Two routes
   to one statement, kept side by side. *)
Lemma latb_max_list_le_b_ind : forall (h : Real) (t : list Real) (c : Real),
  (forall x : Real, InT x (h :: t) -> real_le_b x c) ->
  real_le_b (latb_max_list h t) c.
Proof.
  intros h t c H. induction t as [| w rest IH].
  - exact (H h (InT_here h nil)).
  - change (real_le_b (real_max w (latb_max_list h rest)) c).
    apply latb_max_le_b.
    + exact (H w (InT_next w h (w :: rest) (InT_here w rest))).
    + apply IH. intros x Hx.
      exact (H x (latb_InT_tail_weak h w x rest Hx)).
Defined.

(* ============================================================ *)
(* Part 3. Lower-bound companions (list forms of E.1/E.2).      *)
(* ============================================================ *)

(* Item 4. The head is below the fold (list form of E.1): the
   empty-tail case is reflexivity, and the cons case chains the
   induction invariant with the right-argument bound. *)
Lemma latb_max_list_le_l : forall (h : Real) (t : list Real),
  real_le_b h (latb_max_list h t).
Proof.
  intros h t. induction t as [| w rest IH].
  - apply leb3_le_b_refl.
  - change (real_le_b h (real_max w (latb_max_list h rest))).
    apply (real_le_b_trans h (latb_max_list h rest)).
    + exact IH.
    + apply real_r_max_le_r_B.
Defined.

(* Item 5. Extending the tail by one element only raises the fold (list
   form of E.1, first half): the new head is below via the left-argument
   bound plus the right-argument lift, and the old fold is below via the
   induction invariant (same head, longer tail) plus the same lift. *)
Lemma latb_max_list_le_cons_tail : forall (h u : Real) (t : list Real),
  real_le_b (latb_max_list h t) (latb_max_list h (u :: t)).
Proof.
  intros h u t. revert h u. induction t as [| v rest IH]; intros h u.
  - change (real_le_b h (real_max u h)). apply real_r_max_le_r_B.
  - change (real_le_b (real_max v (latb_max_list h rest))
             (real_max u (real_max v (latb_max_list h rest)))).
    apply latb_max_le_b.
    + apply (real_le_b_trans v (real_max v (latb_max_list h rest))).
      * apply real_r_max_le_l_B.
      * apply real_r_max_le_r_B.
    + apply (real_le_b_trans (latb_max_list h rest)
               (real_max v (latb_max_list h rest))).
      * exact (IH h v).
      * apply real_r_max_le_r_B.
Defined.

(* Item 6. Absorbing the head: the fold of [h :: t] is below
   [real_max h (latb_max_list x t)] (list form of E.2).  The cons case
   bounds the new head and the old fold separately; the induction
   generalizes the swapped head [x] together with the accumulator, so no
   commutativity lemma for [real_max] is needed anywhere. *)
Lemma latb_max_list_le_cons_init : forall (h x : Real) (t : list Real),
  real_le_b (latb_max_list h t) (real_max h (latb_max_list x t)).
Proof.
  intros h x t. revert x. induction t as [| u rest IH]; intros x.
  - change (real_le_b h (real_max h x)). apply real_r_max_le_l_B.
  - change (real_le_b (real_max u (latb_max_list h rest))
             (real_max h (real_max u (latb_max_list x rest)))).
    apply latb_max_le_b.
    + apply (real_le_b_trans u (real_max u (latb_max_list x rest))).
      * apply real_r_max_le_l_B.
      * apply real_r_max_le_r_B.
    + apply (real_le_b_trans (latb_max_list h rest)
               (real_max h (latb_max_list x rest))).
      * exact (IH x).
      * apply latb_max_le_b.
        { apply real_r_max_le_l_B. }
        { apply (real_le_b_trans (latb_max_list x rest)
                   (real_max u (latb_max_list x rest))).
          { apply real_r_max_le_r_B. }
          { apply real_r_max_le_r_B. } }
Defined.

(* Item 7. Prepending an arbitrary element only raises the fold: a
   corollary of Item 6, since the nested fold of [x :: h :: t] is
   definitionally [real_max h (latb_max_list x t)]. *)
Lemma latb_max_list_le_prepend : forall (x h : Real) (t : list Real),
  real_le_b (latb_max_list h t) (latb_max_list x (h :: t)).
Proof.
  intros x h t.
  exact (latb_max_list_le_cons_init h x t).
Defined.

(* ============================================================ *)
(* Part 4. Assumption audit (all names Closed; evidence in the build log). *)
(* ============================================================ *)

Print Assumptions latb_max_list.
Print Assumptions latb_max_list_cons_eq.
Print Assumptions latb_InT_tail_weak.
Print Assumptions latb_lt_max_list_intro.
Print Assumptions latb_max_list_le_b.
Print Assumptions latb_max_list_le_b_ind.
Print Assumptions latb_max_list_le_l.
Print Assumptions latb_max_list_le_cons_tail.
Print Assumptions latb_max_list_le_cons_init.
Print Assumptions latb_max_list_le_prepend.
