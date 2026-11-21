(** * DTPT_b: the membership-and-dedup stem of the DTPT base library (stem B of fourteen).

    Mission.  The Qeq-membership family [Qmem], the dedup characterization
    [Qnodup], the single-removal operator [remove_one], the same-set
    cardinality law [same_set_length], the permutation-invariance theorem
    [N9_ms_perm_inv] for the dedup-count entropy carrier, and the separating
    witness [N9_seq_separates] for the adjacent-difference entropy carrier.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith],
    [Lia], [Permutation], [Sorting.Sorted]; the preceding stem of this node
    (its verbatim require name is carried by the require lines below).

    References.  The information-theoretic discrete layer of the constructive
    development (judged-code truth-predicate line); statement names carried
    verbatim from the baseline module in ConstructiveWorld-Main.  Consumers
    of this stem appear later in this node.

    Constructivity.  Every statement is carried at the [Set] layer: membership
    and nodup faces are boolean identity carriers ([Qmem] over [Qeq_bool],
    [Qnodup] over Set products with [Empty_set]-valued negation), reorganization
    facts use the single-constructor carrier [PermT], rational equality
    conclusions use [QeqT]/[Id], and the existential witness uses [sigT].
    Zero assumed constants, zero admissions, zero classical logic; definitions
    and constructive statements close transparently ([Defined]).  In-proof
    rational reasoning stays on the constructive Prop layer and erases under
    extraction with both extraction faces cast-free.

    Build.  Rocq 9.3 [coqc -native-compiler no -Q <world root> ""] under the
    load-capped build face; single all-names [Separate Extraction] driver,
    [ocamlc] compiled, sample-driven witness run. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.
Open Scope Q_scope.
Require Import DTPT_a.

(* ========== the Qeq-membership family and its boolean helpers ========== *)

(* Membership of a rational in a list, carried as the boolean identity face
   of the membership scan [existsb]. *)
Definition Qmem (a : Q) (l : list Q) : Set :=
  @Id bool (existsb (fun y => Qeq_bool a y) l) true.

(* Definitional stepping lemmas: they expose one unfolding step of the list
   recursions without relying on reduction heuristics. *)
Lemma dedup_aux_nil : forall x : Q, dedup_aux x [] = [].
Proof. reflexivity. Defined.

Lemma dedup_aux_cons : forall (x y : Q) (l : list Q),
  dedup_aux x (y :: l) =
  (if Qeq_bool x y then dedup_aux x l else y :: dedup_aux x l).
Proof. reflexivity. Defined.

Lemma dedup_nil : dedup [] = [].
Proof. reflexivity. Defined.

Lemma dedup_cons : forall (x : Q) (l : list Q),
  dedup (x :: l) = x :: dedup_aux x (dedup l).
Proof. reflexivity. Defined.

Lemma length_cons : forall (x : Q) (l : list Q),
  length (x :: l) = S (length l).
Proof. reflexivity. Defined.

(* Boolean helpers: a disjunction holds as data exactly when one side does. *)
Lemma orb_id_true_l : forall b1 b2 : bool,
  @Id bool b1 true -> @Id bool (orb b1 b2) true.
Proof.
  intros b1 b2 H. destruct b1.
  - apply id_refl.
  - exfalso. apply id_imp_eq in H. discriminate H.
Defined.

Lemma orb_id_true_r : forall b1 b2 : bool,
  @Id bool b2 true -> @Id bool (orb b1 b2) true.
Proof.
  intros b1 b2 H. destruct b1.
  - apply id_refl.
  - exact H.
Defined.

Lemma orb_id_true_inv : forall b1 b2 : bool,
  @Id bool (orb b1 b2) true -> @Id bool b1 true + @Id bool b2 true.
Proof.
  intros b1 b2 H. destruct b1.
  - left. apply id_refl.
  - right. exact H.
Defined.

(* Symmetry of the rational equality carrier. *)
Lemma qeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof.
  intros a b Hab.
  apply (qeq_imp_qeqT b a). apply Qeq_sym. apply (qeqT_imp_qeq a b Hab).
Defined.

Lemma Qmem_cons : forall a x (l : list Q),
  (Qmem a (x :: l) -> QeqT a x + Qmem a l) *
  (QeqT a x + Qmem a l -> Qmem a (x :: l)).
Proof.
  intros a x l. split.
  - intros H. unfold Qmem in H. cbn [existsb orb] in H.
    destruct (orb_id_true_inv _ _ H) as [Hh | Ht].
    + left. exact Hh.
    + right. exact Ht.
  - intros Hs. destruct Hs as [Hh | Ht].
    + unfold Qmem. cbn [existsb orb]. apply orb_id_true_l. exact Hh.
    + unfold Qmem. cbn [existsb orb]. apply orb_id_true_r. exact Ht.
Defined.

Lemma Qmem_refl_cons : forall x (l : list Q), Qmem x (x :: l).
Proof.
  intros x l. pose proof (Qeq_bool_refl x) as Er.
  unfold Qmem. cbn [existsb orb]. rewrite Er. apply id_refl.
Defined.

Lemma Qmem_weaken : forall a b (l : list Q), Qmem a l -> QeqT a b -> Qmem b l.
Proof.
  intros a b l. revert a b. induction l as [| y ys IH]; intros a b H Hab.
  - exfalso. apply id_imp_eq in H. cbn [existsb orb] in H. discriminate H.
  - unfold Qmem in H |- *. cbn [existsb orb] in H |- *.
    destruct (orb_id_true_inv _ _ H) as [Hh | Ht].
    + apply orb_id_true_l. exact (Qeqb_trans b a y (qeqT_sym a b Hab) Hh).
    + apply orb_id_true_r. exact (IH a b Ht Hab).
Defined.

Lemma Qmem_dedup_aux_keep : forall a x (l : list Q),
  Qmem a (dedup_aux x l) -> Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH].
  - rewrite dedup_aux_nil. intros H. exfalso. apply id_imp_eq in H.
    cbn [existsb orb] in H. discriminate H.
  - rewrite dedup_aux_cons. intros H.
    destruct (Qeq_bool x y) eqn:E.
    + destruct (Qmem_cons a y ys) as [HCf HCr]. apply HCr. right. exact (IH H).
    + destruct (Qmem_cons a y (dedup_aux x ys)) as [HCf' HCr'].
      destruct (HCf' H) as [Hh | Ht].
      * destruct (Qmem_cons a y ys) as [HCf'' HCr''].
        apply HCr''. left. exact Hh.
      * destruct (Qmem_cons a y ys) as [HCf'' HCr''].
        apply HCr''. right. exact (IH Ht).
Defined.

Lemma Qmem_dedup_aux_drop : forall a x (l : list Q),
  Qmem a l -> @Id bool (Qeq_bool a x) false -> Qmem a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH].
  - rewrite dedup_aux_nil. intros H _. exfalso. apply id_imp_eq in H.
    cbn [existsb orb] in H. discriminate H.
  - rewrite dedup_aux_cons. intros H Hax.
    destruct (Qeq_bool x y) eqn:Hxy.
    + destruct (Qmem_cons a y ys) as [HCf HCr]. destruct (HCf H) as [Hh | Ht].
      * exfalso.
        pose proof (qeqT_imp_qeq a y Hh) as Hay.
        pose proof (Qeq_bool_eq x y Hxy) as Hxyq.
        pose proof (qeq_imp_qeqT a x (Qeq_trans a y x Hay (Qeq_sym x y Hxyq)))
          as HaxT.
        pose proof (id_imp_eq bool (Qeq_bool a x) true HaxT) as HT.
        pose proof (id_imp_eq bool (Qeq_bool a x) false Hax) as HF.
        rewrite HT in HF. discriminate HF.
      * exact (IH Ht Hax).
    + destruct (Qmem_cons a y ys) as [HCf HCr]. destruct (HCf H) as [Hh | Ht].
      * destruct (Qmem_cons a y (dedup_aux x ys)) as [HCf' HCr'].
        apply HCr'. left. exact Hh.
      * destruct (Qmem_cons a y (dedup_aux x ys)) as [HCf' HCr'].
        apply HCr'. right. exact (IH Ht Hax).
Defined.

Lemma dedup_aux_duck : forall a (l : list Q), Qmem a (dedup_aux a l) -> Empty_set.
Proof.
  intros a l. induction l as [| y ys IH].
  - rewrite dedup_aux_nil. intros H. exfalso. apply id_imp_eq in H.
    cbn [existsb orb] in H. discriminate H.
  - rewrite dedup_aux_cons. intros H.
    destruct (Qeq_bool a y) eqn:E.
    + exact (IH H).
    + destruct (Qmem_cons a y (dedup_aux a ys)) as [HCf' HCr'].
      destruct (HCf' H) as [Hh | Ht].
      * pose proof (id_imp_eq bool (Qeq_bool a y) true Hh) as HT.
        rewrite E in HT. discriminate HT.
      * exact (IH Ht).
Defined.

(* ========== the dedup characterization ========== *)

(* Noduplication of a list, carried as a Set inductive family: each head is
   absent from the tail (Empty_set-valued negation) and the tail is
   noduplicated.  The family form keeps every value extraction-friendly
   (data-carrying constructors, no cast sites). *)
Inductive Qnodup : list Q -> Set :=
| qnodup_nil : Qnodup []
| qnodup_cons : forall (x : Q) (xs : list Q),
    ((Qmem x xs -> Empty_set) * Qnodup xs)%type -> Qnodup (x :: xs).

(* Consumable product face of the cons case. *)
Lemma Qnodup_cons_inv : forall (x : Q) (xs : list Q), Qnodup (x :: xs) ->
  ((Qmem x xs -> Empty_set) * Qnodup xs)%type.
Proof.
  intros x xs H. inversion H; subst. exact H1.
Defined.

Lemma dedup_aux_Qnodup : forall x (l : list Q), Qnodup l -> Qnodup (dedup_aux x l).
Proof.
  intros x l. induction l as [| y ys IH].
  - rewrite dedup_aux_nil. intros _. apply qnodup_nil.
  - rewrite dedup_aux_cons. intros H.
    destruct (Qnodup_cons_inv y ys H) as [Hny Hys].
    destruct (Qeq_bool x y) eqn:E.
    + apply IH. exact Hys.
    + apply qnodup_cons. split.
      * intros Hm. apply Hny. exact (Qmem_dedup_aux_keep y x ys Hm).
      * apply IH. exact Hys.
Defined.

Lemma dedup_Qnodup : forall l : list Q, Qnodup (dedup l).
Proof.
  induction l as [| x xs IH].
  - rewrite dedup_nil. apply qnodup_nil.
  - rewrite dedup_cons. apply qnodup_cons. split.
    + intros Hm. exact (dedup_aux_duck x (dedup xs) Hm).
    + exact (dedup_aux_Qnodup x (dedup xs) IH).
Defined.

Lemma dedup_Qmem_l : forall (l : list Q) a, Qmem a (dedup l) -> Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a.
  - rewrite dedup_nil. intros H. exfalso. apply id_imp_eq in H.
    cbn [existsb orb] in H. discriminate H.
  - rewrite dedup_cons. intros H.
    destruct (Qmem_cons a x (dedup_aux x (dedup xs))) as [HCf' HCr'].
    destruct (HCf' H) as [Hh | Ht].
    + destruct (Qmem_cons a x xs) as [HCf HCr]. apply HCr. left. exact Hh.
    + destruct (Qmem_cons a x xs) as [HCf HCr]. apply HCr. right.
      exact (IH a (Qmem_dedup_aux_keep a x (dedup xs) Ht)).
Defined.

Lemma dedup_Qmem_r : forall (l : list Q) a, Qmem a l -> Qmem a (dedup l).
Proof.
  induction l as [| x xs IH]; intros a.
  - rewrite dedup_nil. intros H. exfalso. apply id_imp_eq in H.
    cbn [existsb orb] in H. discriminate H.
  - rewrite dedup_cons. intros H.
    destruct (Qmem_cons a x xs) as [HCf HCr]. destruct (HCf H) as [Hh | Ht].
    + destruct (Qmem_cons a x (dedup_aux x (dedup xs))) as [HCf' HCr'].
      apply HCr'. left. exact Hh.
    + destruct (Qeq_bool a x) eqn:Hax.
      * destruct (Qmem_cons a x (dedup_aux x (dedup xs))) as [HCf' HCr'].
        apply HCr'. left. exact (eq_imp_id bool (Qeq_bool a x) true Hax).
      * destruct (Qmem_cons a x (dedup_aux x (dedup xs))) as [HCf' HCr'].
        apply HCr'. right. apply Qmem_dedup_aux_drop.
        -- exact (IH a Ht).
        -- exact (eq_imp_id bool (Qeq_bool a x) false Hax).
Defined.

(* Membership is invariant under reorganization; the reorganization side is
   the single-constructor Set carrier wrapping the stdlib permutation relation.
   The witness extraction stays inside the constructive Prop layer (whose
   reasoning is legal there) and the Set face is assembled at the end. *)
Lemma Qmem_perm : forall (l p : list Q) a, PermT l p ->
  (Qmem a l -> Qmem a p) * (Qmem a p -> Qmem a l).
Proof.
  intros l p a Hp. pose proof (PermT_to_Perm l p Hp) as Hp'. split.
  - intros H.
    assert (Eb : existsb (fun y => Qeq_bool a y) p = true).
    { pose proof (id_imp_eq bool (existsb (fun y => Qeq_bool a y) l) true H)
        as E.
      apply existsb_exists in E. destruct E as [y [Hy Hq]].
      apply existsb_exists. exists y. split.
      - exact (@Permutation_in Q l p y Hp' Hy).
      - exact Hq. }
    apply eq_imp_id. exact Eb.
  - intros H.
    assert (Eb : existsb (fun y => Qeq_bool a y) l = true).
    { pose proof (id_imp_eq bool (existsb (fun y => Qeq_bool a y) p) true H)
        as E.
      apply existsb_exists in E. destruct E as [y [Hy Hq]].
      apply existsb_exists. exists y. split.
      - exact (@Permutation_in Q p l y (Permutation_sym Hp') Hy).
      - exact Hq. }
    apply eq_imp_id. exact Eb.
Defined.

Lemma Qmem_cons_nodup : forall a x (xs : list Q), (Qmem x xs -> Empty_set) ->
  (Qmem a xs -> Qmem a (x :: xs) * @Id bool (Qeq_bool a x) false) *
  (Qmem a (x :: xs) * @Id bool (Qeq_bool a x) false -> Qmem a xs).
Proof.
  intros a x xs Hx. split.
  - intros Ha. split.
    + destruct (Qmem_cons a x xs) as [HCf HCr]. apply HCr. right. exact Ha.
    + destruct (Qeq_bool a x) eqn:E.
      * destruct (Hx (Qmem_weaken a x xs Ha
                       (eq_imp_id bool (Qeq_bool a x) true E))).
      * apply id_refl.
  - intros Hp. destruct Hp as [Ha Hax].
    destruct (Qmem_cons a x xs) as [HCf HCr]. destruct (HCf Ha) as [Hh | Ht].
    + pose proof (id_imp_eq bool (Qeq_bool a x) true Hh) as HT.
      pose proof (id_imp_eq bool (Qeq_bool a x) false Hax) as HF.
      rewrite HT in HF. discriminate HF.
    + exact Ht.
Defined.

(* ========== single removal and the cardinality law ========== *)

Lemma remove_one : forall (x : Q) (n : list Q), Qnodup n -> Qmem x n ->
  sigT (fun n' : list Q =>
    (@Id nat (length n) (S (length n')) *
      (Qnodup n' * (forall a : Q,
        (Qmem a n' -> Qmem a n * @Id bool (Qeq_bool a x) false) *
        (Qmem a n * @Id bool (Qeq_bool a x) false -> Qmem a n'))))%type).
Proof.
  intros x n. induction n as [| y ys IH]; intros Hn Hx.
  - exfalso. apply id_imp_eq in Hx. cbn [existsb orb] in Hx. discriminate Hx.
  - destruct (Qnodup_cons_inv y ys Hn) as [Hy Hys].
    destruct (Qmem_cons x y ys) as [HCf HCr]. destruct (HCf Hx) as [Hxy | Hx'].
    + (* the head equals the removed element: return the tail *)
      exists ys. split.
      * apply eq_imp_id. reflexivity.
      * split.
        -- exact Hys.
        -- intros a. split.
           ++ intros Ha. destruct (Qmem_cons a y ys) as [HCf2 HCr2].
              split.
              ** apply HCr2. right. exact Ha.
              ** destruct (Qeq_bool a x) eqn:E.
                 *** destruct (Hy (Qmem_weaken a y ys Ha
                       (qeq_imp_qeqT a y (Qeq_trans a x y
                          (Qeq_bool_eq a x E) (qeqT_imp_qeq x y Hxy))))).
                 *** apply id_refl.
           ++ intros Hp. destruct Hp as [Ha Hax].
              destruct (Qmem_cons a y ys) as [HCf2 HCr2].
              destruct (HCf2 Ha) as [Hh | Ht].
              ** pose proof (qeqT_imp_qeq a y Hh) as Hay.
                 pose proof (qeqT_imp_qeq x y Hxy) as Hxyq.
                 pose proof (qeq_imp_qeqT a x (Qeq_trans a y x Hay
                                              (Qeq_sym x y Hxyq))) as HaxT.
                 pose proof (id_imp_eq bool (Qeq_bool a x) true HaxT) as HT.
                 pose proof (id_imp_eq bool (Qeq_bool a x) false Hax) as HF.
                 rewrite HT in HF. discriminate HF.
              ** exact Ht.
    + (* the removed element sits deeper: recurse and re-attach the head *)
      destruct (IH Hys Hx') as [ys' [Hlen1 [Hnd1 Hiff1]]].
      exists (y :: ys'). split.
      * apply eq_imp_id. rewrite !length_cons.
        rewrite (id_imp_eq nat (length ys) (S (length ys')) Hlen1).
        reflexivity.
      * split.
        -- apply qnodup_cons. split.
           ++ intros Hm. exact (Hy (fst (fst (Hiff1 y) Hm))).
           ++ exact Hnd1.
        -- intros a. split.
           ++ intros Ha. destruct (Qmem_cons a y ys') as [HCf2 HCr2].
              destruct (HCf2 Ha) as [Hh | Ht].
              ** split.
                 --- destruct (Qmem_cons a y ys) as [HCf3 HCr3].
                     apply HCr3. left. exact Hh.
                 --- destruct (Qeq_bool a x) eqn:E.
                     *** destruct (Hy (Qmem_weaken x y ys Hx'
                           (qeq_imp_qeqT x y
                              (Qeq_trans x a y
                                 (Qeq_sym a x (Qeq_bool_eq a x E))
                                 (qeqT_imp_qeq a y Hh))))).
                     *** apply id_refl.
              ** split.
                 --- destruct (Qmem_cons a y ys) as [HCf3 HCr3].
                     apply HCr3. right. exact (fst (fst (Hiff1 a) Ht)).
                 --- exact (snd (fst (Hiff1 a) Ht)).
           ++ intros Hp. destruct Hp as [Ha Hax].
              destruct (Qmem_cons a y ys) as [HCf2 HCr2].
              destruct (HCf2 Ha) as [Hh | Ht].
              ** destruct (Qmem_cons a y ys') as [HCf3 HCr3].
                 apply HCr3. left. exact Hh.
              ** destruct (Qmem_cons a y ys') as [HCf3 HCr3].
                 apply HCr3. right. exact (snd (Hiff1 a) (Ht, Hax)).
Defined.

Lemma same_set_length : forall m n : list Q,
  Qnodup m -> Qnodup n -> (forall a : Q, (Qmem a m -> Qmem a n) * (Qmem a n -> Qmem a m)) ->
  @Id nat (length m) (length n).
Proof.
  induction m as [| x xs IH]; intros n Hm Hn Heq.
  - destruct n as [| y ys].
    + apply eq_imp_id. reflexivity.
    + exfalso. pose proof (snd (Heq y) (Qmem_refl_cons y ys)) as Hb.
      apply id_imp_eq in Hb. cbn [existsb orb] in Hb. discriminate Hb.
  - destruct n as [| y ys].
    + exfalso. pose proof (fst (Heq x) (Qmem_refl_cons x xs)) as Hb.
      apply id_imp_eq in Hb. cbn [existsb orb] in Hb. discriminate Hb.
    + assert (Hxs : Qmem x (y :: ys))
        by (apply (fst (Heq x)); apply Qmem_refl_cons).
      destruct (remove_one x (y :: ys) Hn Hxs) as [n' [Hlen1 [Hnd1 Hiff1]]].
      destruct (Qnodup_cons_inv x xs Hm) as [Hmx Hmxs].
      assert (Hss : forall a : Q,
        (Qmem a xs -> Qmem a n') * (Qmem a n' -> Qmem a xs)).
      { intros a. split; intros Ha.
        - assert (Hpair := fst (Qmem_cons_nodup a x xs Hmx) Ha).
          apply (snd (Hiff1 a)). split.
          + exact (fst (Heq a) (fst Hpair)).
          + exact (snd Hpair).
        - assert (Hpair := fst (Hiff1 a) Ha).
          apply (snd (Qmem_cons_nodup a x xs Hmx)). split.
          + exact (snd (Heq a) (fst Hpair)).
          + exact (snd Hpair). }
      assert (Hlen2 : @Id nat (length xs) (length n'))
        by (apply IH; [exact Hmxs | exact Hnd1 | exact Hss]).
      apply eq_imp_id. rewrite !length_cons.
      pose proof (id_imp_eq nat (length (y :: ys)) (S (length n')) Hlen1) as E1.
      rewrite !length_cons in E1.
      rewrite E1.
      rewrite (id_imp_eq nat (length xs) (length n') Hlen2).
      reflexivity.
Defined.

(* ========== the permutation-invariance theorem and the separating witness ========== *)

Theorem N9_ms_perm_inv : forall (l p : list Q), PermT l p -> QeqT (H_ms l) (H_ms p).
Proof.
  intros l p Hp. pose proof (PermT_to_Perm l p Hp) as Hp'.
  apply qeq_imp_qeqT. unfold Qeq, H_ms. f_equal.
  - f_equal. f_equal. f_equal.
    apply (id_imp_eq nat (length (dedup l)) (length (dedup p))).
    apply same_set_length.
    + apply dedup_Qnodup.
    + apply dedup_Qnodup.
    + intros a. split; intros H.
      * exact (dedup_Qmem_r p a
                 (fst (Qmem_perm l p a Hp) (dedup_Qmem_l l a H))).
      * exact (dedup_Qmem_r l a
                 (snd (Qmem_perm l p a Hp) (dedup_Qmem_l p a H))).
Defined.

Theorem N9_seq_separates :
  sigT (fun l1 : list Q => sigT (fun l2 : list Q =>
    (PermT l1 l2 * (QeqT (H_adj l1) (H_adj l2) -> Empty_set))%type)).
Proof.
  exists [0; 1; 2], [0; 2; 1]. split.
  - apply permT_intro. apply perm_skip. apply perm_swap.
  - intros Hc. cbv in Hc. apply id_imp_eq in Hc. discriminate Hc.
Defined.
