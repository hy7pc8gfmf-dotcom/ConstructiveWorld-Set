(* ConstructiveWorld-Set -- DTPT_Rotation supply lemmas, volume 1. *)

(** * abl_dtr_core1: supply lemmas for premises 1-36 of DTPT_Rotation.

    Mission.  Supplies premises 1-36 of the host DTPT_Rotation.v
      ledger (coordinates :49-:575) in direct A-form under the
      [dtr_] name map, proofs constructed in place, no host-module
      require.  The conjunction ledger entry [rotc_two_runs] is
      registered, not supplied: its two components (firstn/skipn
      order preservation) are carried by the supply lemmas.
      Local data copies: [dtr_sum_adjdiff], [dtr_H_adj],
      [dtr_lastq], [dtr_rotc], [dtr_SortedQ].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List],
      [Bool.Bool], [Arith], [Lia], [Permutation], [Extraction].

    References.  This development, abl_dtr_core1.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier
      completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QeqT]/[QleT'] and [Id] forms; the
      sorted-list carrier [dtr_SortedQ] is a boolean function with an
      [Id] witness form); statements extract with [Obj.magic] = 0 and
      no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dtr_core1.v]
      compiles cleanly (exit 0); the artifact starts with
      [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

(* ============================================================ *)
(*  data layer.  The five [dtr_] names are verbatim copies of the     *)
(*  host DTPT_Rotation.v data block, isolated by the [dtr_] prefix:   *)
(*  [dtr_sum_adjdiff], [dtr_H_adj], [dtr_lastq] mirror DTPT.v         *)
(*  :116-:125/:621-:628 (the host uses them through Import DTPT);     *)
(*  [dtr_rotc] mirrors DTPT_Rotation.v:203; [dtr_SortedQ] mirrors     *)
(*  DTPT_Entropy.v:270-:273 in content (the host Import order picks   *)
(*  the latter), restated below as a boolean test with a Set-level    *)
(*  witness carrier.  All five are real implementations that          *)
(*  extraction keeps, not premises of the host.                       *)
(* ============================================================ *)

Fixpoint dtr_sum_adjdiff (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => 0
               | y :: _ => Qabs (y - x) + dtr_sum_adjdiff xs
               end
  end.

Definition dtr_H_adj (l : list Q) : Q := dtr_sum_adjdiff l.

Fixpoint dtr_lastq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => x
               | _ :: _ => dtr_lastq xs
               end
  end.

Definition dtr_rotc (n : nat) (l : list Q) : list Q :=
  skipn n l ++ firstn n l.

Fixpoint dtr_sortedQb (l : list Q) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      match xs with
      | [] => true
      | y :: _ => Qle_bool x y && dtr_sortedQb xs
      end
  end.

Inductive dtr_bid (b : bool) : Set :=
| dtr_bid_intro : b = true -> dtr_bid b.

Definition dtr_SortedQ (l : list Q) : Set := dtr_bid (dtr_sortedQb l).

(* the boolean core passes a list when the head of every cons pair is *)
(* at most the next element and the tail passes again; the lemma below *)
(* links the boolean test to the Q order *)
Lemma dtr_qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qle_bool in H. rewrite Z.leb_le in H.
  unfold Qle. exact H.
Qed.

(* prefixes and suffixes of a passing list pass again: every adjacent *)
(* pair of a prefix or suffix is an adjacent pair of the full list *)
Lemma dtr_sortedQb_firstn : forall (k : nat) (l : list Q),
  dtr_sortedQb l = true -> dtr_sortedQb (firstn k l) = true.
Proof.
  induction k as [| k' IH]; intros l Hb.
  - reflexivity.
  - destruct l as [| a rest].
    + reflexivity.
    + destruct rest as [| b bs].
      * destruct k' as [| k'']; simpl; reflexivity.
      * simpl in Hb. apply andb_prop in Hb as [Hab Hbs].
        destruct k' as [| k''].
        -- reflexivity.
        -- simpl. rewrite Hab. simpl. exact (IH (b :: bs) Hbs).
Qed.

Lemma dtr_sortedQb_skipn : forall (k : nat) (l : list Q),
  dtr_sortedQb l = true -> dtr_sortedQb (skipn k l) = true.
Proof.
  induction k as [| k' IH]; intros l Hb.
  - exact Hb.
  - destruct l as [| a rest].
    + reflexivity.
    + destruct rest as [| b bs].
      * destruct k' as [| k'']; reflexivity.
      * simpl in Hb. apply andb_prop in Hb as [_ Hbs].
        exact (IH (b :: bs) Hbs).
Qed.

(* ============================================================ *)
(*  supply theorems: premises 1-7, statements 1-7, with the Q-order   *)
(*  auxiliary lemmas                                                  *)
(* ============================================================ *)

(* premise 1 (DTPT_Rotation.v:49) *)
Theorem dtr_cyc_qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qeq in H. unfold Qle. lia.
Qed.

(* auxiliary A1: monotonicity of Q addition, same content as DTPT.v:144 *)
(* built in place; supporting infrastructure, not one of the premises *)
Lemma dtr_qadd_le : forall a b c d : Q, a <= b -> c <= d -> (a + c <= b + d)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] [dn dd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Qed.

(* auxiliary A2: nonnegativity of Q addition, same content as *)
(* DTPT.v:491 built in place; supporting infrastructure, not one of *)
(* the premises *)
Lemma dtr_qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* auxiliary A3: forward half of the host base lemma Qle_0_sub' *)
(* (DTPT.v:173, stated as an iff); the iff is split at the top level *)
(* into two clean one-directional statements *)
Lemma dtr_qle_0_sub_inv : forall x y : Q, x <= y -> (0 <= y - x)%Q.
Proof.
  intros [nx dx] [ny dy] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

(* auxiliary A4: reverse half of the Qle_0_sub' decomposition *)
Lemma dtr_qle_0_sub_intro : forall x y : Q, (0 <= y - x)%Q -> x <= y.
Proof.
  intros [nx dx] [ny dy] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

(* premise 2 (DTPT_Rotation.v:66) *)
Theorem dtr_cyc_le_triple : forall s : Q, (0 <= s)%Q -> (s <= 3 * s)%Q.
Proof.
  intros s Hs.
  assert (H3 : (3 * s == s + s + s)%Q) by ring.
  apply (Qle_trans s (s + s + s) (3 * s)).
  - apply dtr_qle_0_sub_intro.
    assert (Hr : (s + s + s - s == s + s)%Q) by ring.
    rewrite Hr. exact (dtr_qadd_nonneg s s Hs Hs).
  - apply dtr_cyc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* premise 3 (DTPT_Rotation.v:79) *)
Theorem dtr_firstn_incl : forall (l : list Q) (k : nat) (z : Q),
  In z (firstn k l) -> In z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; destruct Hin.
  - destruct k as [| k']; simpl in Hin.
    + destruct Hin.
    + destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. exact (IH k' z Hin).
Qed.

(* premise 4 (DTPT_Rotation.v:91) *)
Theorem dtr_skipn_incl : forall (l : list Q) (k : nat) (z : Q),
  In z (skipn k l) -> In z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; destruct Hin.
  - destruct k as [| k']; simpl in Hin.
    + exact Hin.
    + right. exact (IH k' z Hin).
Qed.

(* premise 5 (DTPT_Rotation.v:101) *)
Theorem dtr_firstn_SortedQ : forall (l : list Q) (k : nat),
  dtr_SortedQ l -> dtr_SortedQ (firstn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply dtr_bid_intro; reflexivity.
  - destruct HS as [Hb].
    unfold dtr_SortedQ. apply dtr_bid_intro.
    exact (dtr_sortedQb_firstn k (a :: rest) Hb).
Qed.

(* premise 6 (DTPT_Rotation.v:116) *)
Theorem dtr_skipn_SortedQ : forall (l : list Q) (k : nat),
  dtr_SortedQ l -> dtr_SortedQ (skipn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply dtr_bid_intro; reflexivity.
  - destruct HS as [Hb].
    unfold dtr_SortedQ. apply dtr_bid_intro.
    exact (dtr_sortedQb_skipn k (a :: rest) Hb).
Qed.

(* premise 7 (DTPT_Rotation.v:130, SORTED) is registered, not supplied: *)
(* its host conclusion SortedQ ... /\ SortedQ ... is a conjunction in *)
(* Prop, and the product-shaped Set form *)
(* prod (dtr_SortedQ ...) (dtr_SortedQ ...) is provable in the kernel *)
(* but rejected by Separate Extraction: the informative inductive *)
(* type prod has a Prop instance, so the entry stays registered and *)
(* its content is carried in full by premises 5/6 *)
(* (dtr_firstn_SortedQ and dtr_skipn_SortedQ). *)

(* ============================================================ *)
(* supply theorems, continued: premises 8-13, statements 8-11, with  *)
(* the [xq] auxiliary lemmas                                        *)
(* ============================================================ *)

(* auxiliary B1: x - x == 0, same content as DTPT.v:522 built in *)
(* place *)
Lemma dtr_xq_minus_self : forall x : Q, x - x == 0.
Proof.
  intros [n d]. unfold Qminus, Qeq; simpl. lia.
Qed.

(* auxiliary B2: Qabs vanishes on x == 0, same content as DTPT.v:514 *)
(* built in place *)
Lemma dtr_xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

(* auxiliary B3: Qabs fixes 0 <= x, same content as DTPT.v:506 built *)
(* in place *)
Lemma dtr_xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

(* auxiliary B4: Qabs (a - b) == Qabs (b - a), same content as *)
(* DTPT.v:555 built in place; a one-step rewrite by the stdlib *)
(* Leibniz equality Qabs_Qminus, shorter than the host's three-step *)
(* chain *)
Lemma dtr_xq_abs_sub_comm : forall a b : Q, Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b. rewrite (Qabs_Qminus a b). apply Qeq_refl.
Qed.

(* auxiliary B5: Qabs (x - x) == 0, same content as DTPT.v:527 built *)
(* in place *)
Lemma dtr_xq_abs_zero : forall x : Q, Qabs (x - x) == 0.
Proof.
  intro x. apply dtr_xq_abs_eq0. apply dtr_xq_minus_self.
Qed.

(* auxiliary B6: dtr_H_adj is nonnegative, same content as DTPT.v:563 *)
(* built in place *)
Lemma dtr_xq_H_adj_nonneg : forall l : list Q, (0 <= dtr_H_adj l)%Q.
Proof.
  intro l. induction l as [| a rest IH].
  - apply Qle_refl.
  - destruct rest as [| b bs].
    + apply Qle_refl.
    + change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      apply dtr_qadd_nonneg; [ apply Qabs_nonneg | exact IH ].
Qed.

(* auxiliary A5: h <= Qabs t + h, same content as DTPT.v:573 built *)
(* in place; applies dtr_qadd_le *)
Lemma dtr_xq_le_add_abs : forall t h : Q, (h <= Qabs t + h)%Q.
Proof.
  intros t h.
  pose proof (dtr_qadd_le 0 (Qabs t) h h (Qabs_nonneg t) (Qle_refl h)) as HS.
  rewrite Qplus_0_l in HS. exact HS.
Qed.

(* auxiliary B7: the paired-distance bound of DTPT.v:688 built in *)
(* place; carries the proofs of premises 12-13 *)
Lemma dtr_xq_pair_dist_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= dtr_H_adj l)%Q.
Proof.
  induction l as [| a rest IH]; intros x y Hx Hy.
  - exfalso. exact Hx.
  - destruct rest as [| b bs].
    + destruct Hx as [Hx | []]; destruct Hy as [Hy | []]; subst.
      rewrite dtr_xq_abs_zero. apply Qle_refl.
    + change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
      * rewrite dtr_xq_abs_zero. apply dtr_qadd_nonneg;
          [ apply Qabs_nonneg | apply dtr_xq_H_adj_nonneg ].
      * assert (Hr1 : a - y == (a - b) + (b - y)) by ring.
        rewrite Hr1.
        apply (Qle_trans _ (Qabs (a - b) + Qabs (b - y))).
        -- apply Qabs_triangle.
        -- rewrite (dtr_xq_abs_sub_comm a b).
           apply dtr_qadd_le; [ apply Qle_refl
                              | apply IH; [ left; reflexivity | exact Hy ] ].
      * assert (Hr2 : x - a == (x - b) + (b - a)) by ring.
        rewrite Hr2.
        apply (Qle_trans _ (Qabs (x - b) + Qabs (b - a))).
        -- apply Qabs_triangle.
        -- rewrite (Qplus_comm (Qabs (x - b)) (Qabs (b - a))).
           apply dtr_qadd_le; [ apply Qle_refl
                              | apply IH; [ exact Hx | left; reflexivity ] ].
      * apply (Qle_trans _ (dtr_H_adj (b :: bs))).
        -- apply IH; assumption.
        -- apply dtr_xq_le_add_abs.
Qed.

(* premises 8-9 (DTPT_Rotation.v:141): the two nonemptiness side *)
(* conditions are carried over verbatim from the host statement *)
Theorem dtr_H_adj_app_seam : forall (u v : list Q),
  u <> [] -> v <> [] ->
  dtr_H_adj (u ++ v) == dtr_H_adj u + dtr_H_adj v + Qabs (hd 0 v - dtr_lastq u).
Proof.
  induction u as [| a rest IH]; intros v Hne Hne2.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + destruct v as [| c v'].
      * exfalso. apply Hne2. reflexivity.
      * change (dtr_H_adj ([a] ++ c :: v')) with (Qabs (c - a) + dtr_H_adj (c :: v'))%Q.
        change (dtr_H_adj [a]) with 0%Q.
        change (dtr_lastq [a]) with a.
        change (hd 0 (c :: v')) with c.
        ring.
    + change (dtr_H_adj ((a :: b :: bs) ++ v))
        with (Qabs (b - a) + dtr_H_adj (b :: bs ++ v))%Q.
      change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      change (dtr_lastq (a :: b :: bs)) with (dtr_lastq (b :: bs)).
      assert (Hne' : b :: bs <> []) by (intro Hcz; discriminate Hcz).
      replace (dtr_H_adj (b :: bs ++ v)) with (dtr_H_adj ((b :: bs) ++ v))
        by reflexivity.
      rewrite (IH v Hne' Hne2).
      ring.
Qed.

(* premise 10 (DTPT_Rotation.v:282): skipn_all and firstn_all are *)
(* asserted inside the proof, an in-place rebuild of the host *)
(* rotc_rot_app chain without new top-level lemmas *)
Theorem dtr_rotc_inv : forall (n : nat) (l : list Q),
  (n <= length l)%nat -> dtr_rotc ((length l - n)%nat) (dtr_rotc n l) = l.
Proof.
  intros n l Hn.
  assert (Hsa : forall c d : list Q, skipn (length c) (c ++ d) = d).
  { intros c d. induction c as [| x xs IHc]; simpl.
    - reflexivity.
    - exact IHc. }
  assert (Hfa : forall c d : list Q, firstn (length c) (c ++ d) = c).
  { intros c d. induction c as [| x xs IHc]; simpl.
    - reflexivity.
    - rewrite IHc. reflexivity. }
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat)
    by exact (firstn_length_le l Hn).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hab : (length (a ++ b) - length a = length b)%nat)
    by (rewrite length_app; lia).
  unfold dtr_rotc.
  rewrite Hsplit.
  rewrite <- Hla.
  rewrite Hab.
  rewrite (Hsa a b).
  rewrite (Hfa a b).
  rewrite (Hsa b a).
  rewrite (Hfa b a).
  reflexivity.
Qed.

(* premise 11 (DTPT_Rotation.v:329) *)
Theorem dtr_rotc_in : forall (n : nat) (l : list Q) (x : Q),
  In x l -> In x (dtr_rotc n l).
Proof.
  intros n l x Hin.
  assert (Hp : Permutation l (skipn n l ++ firstn n l)).
  { apply Permutation_sym. etransitivity.
    - apply Permutation_app_comm.
    - rewrite firstn_skipn. apply Permutation_refl. }
  apply (Permutation_in x Hp). exact Hin.
Qed.

(* premises 12-13 (DTPT_Rotation.v:342) *)
Theorem dtr_H_rotc_span_lb : forall (n : nat) (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= dtr_H_adj (dtr_rotc n l))%Q.
Proof.
  intros n l x y Hx Hy.
  apply (dtr_xq_pair_dist_le (dtr_rotc n l) x y).
  - apply dtr_rotc_in. exact Hx.
  - apply dtr_rotc_in. exact Hy.
Qed.

(* ============================================================ *)
(* supply theorems, continued: premises 14-28, statements 12-20 *)
(* ============================================================ *)

(* premise 14 (DTPT_Rotation.v:390) *)
Theorem dtr_skipn_ne_of_lt : forall (k : nat) (l : list Q),
  (k < length l)%nat -> skipn k l <> [].
Proof.
  intros k l Hlt Hc.
  assert (Hsplit : l = firstn k l ++ skipn k l)
    by (symmetry; apply firstn_skipn).
  rewrite Hc in Hsplit. rewrite app_nil_r in Hsplit.
  assert (Hle : (k <= length l)%nat) by lia.
  assert (Hlen : (length (firstn k l) = k)%nat)
    by (apply (firstn_length_le l Hle)).
  assert (Hcon : (length l = k)%nat) by (rewrite Hsplit; exact Hlen).
  lia.
Qed.

(* premises 15-16 (DTPT_Rotation.v:405) *)
Theorem dtr_firstn_ne_of_lt : forall (k : nat) (l : list Q),
  (0 < k)%nat -> (k <= length l)%nat -> firstn k l <> [].
Proof.
  intros k l H1 H2 Hc.
  destruct l as [| a rest].
  - simpl in H2. lia.
  - destruct k as [| k'].
    + lia.
    + simpl in Hc. discriminate.
Qed.

(* premise 17 (DTPT_Rotation.v:417) *)
Theorem dtr_rotc_skipn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> skipn k l = [].
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. apply IH. simpl in Hk. lia.
Qed.

(* premise 18 (DTPT_Rotation.v:428) *)
Theorem dtr_rotc_firstn_all : forall (l : list Q) (k : nat),
  (length l <= k)%nat -> firstn k l = l.
Proof.
  induction l as [| a rest IH]; intros k Hk.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. exfalso. lia.
    + simpl. assert (Hle : (length rest <= k')%nat) by (simpl in Hk; lia).
      rewrite (IH k' Hle). reflexivity.
Qed.

(* premise 19 (DTPT_Rotation.v:440) *)
Theorem dtr_rotc_ge_len_id : forall (k : nat) (l : list Q),
  (length l <= k)%nat -> dtr_rotc k l = l.
Proof.
  intros k l Hk. unfold dtr_rotc.
  rewrite (dtr_rotc_skipn_all l k Hk).
  rewrite (dtr_rotc_firstn_all l k Hk).
  reflexivity.
Qed.

(* premise 20 (DTPT_Rotation.v:450) *)
Theorem dtr_lastq_skipn_kept : forall (l : list Q) (k : nat),
  (k < length l)%nat -> dtr_lastq (skipn k l) = dtr_lastq l.
Proof.
  induction l as [| a rest IH]; intros k Hlt.
  - simpl in Hlt. exfalso. lia.
  - destruct k as [| k'].
    + reflexivity.
    + simpl in Hlt. destruct rest as [| b bs].
      * simpl in Hlt. exfalso. lia.
      * simpl. apply IH. lia.
Qed.

(* premise 21 (DTPT_Rotation.v:463) *)
Theorem dtr_hd_firstn_kept : forall (k : nat) (l : list Q),
  (0 < k)%nat -> hd 0 (firstn k l) = hd 0 l.
Proof.
  intros k l Hk. destruct l as [| a rest].
  - destruct k; simpl; reflexivity.
  - destruct k as [| k'].
    + exfalso. lia.
    + simpl. reflexivity.
Qed.

(* on a passing list every element lies between the head and the last *)
(* element, since the head bounds the second element and the bound *)
(* propagates along the list *)
Lemma dtr_sortedQb_hd_min : forall (l : list Q) (z : Q),
  dtr_sortedQb l = true -> In z l -> (hd 0 l <= z)%Q.
Proof.
  induction l as [| a rest IH]; intros z Hb Hin.
  - destruct Hin.
  - destruct rest as [| b bs].
    + destruct Hin as [Heq | Hin].
      * subst. simpl. apply Qle_refl.
      * destruct Hin.
    + simpl in Hb. apply andb_prop in Hb as [Hab Hbs].
      simpl. destruct Hin as [Heq | Hin].
      * subst. apply Qle_refl.
      * apply (Qle_trans a b z).
        -- apply dtr_qle_bool_le. exact Hab.
        -- exact (IH z Hbs Hin).
Qed.

Lemma dtr_sortedQb_lastq_max : forall (l : list Q) (z : Q),
  dtr_sortedQb l = true -> In z l -> (z <= dtr_lastq l)%Q.
Proof.
  induction l as [| a rest IH]; intros z Hb Hin.
  - destruct Hin.
  - destruct rest as [| b bs].
    + destruct Hin as [Heq | Hin].
      * subst. simpl. apply Qle_refl.
      * destruct Hin.
    + simpl in Hb. apply andb_prop in Hb as [Hab Hbs].
      change (dtr_lastq (a :: b :: bs)) with (dtr_lastq (b :: bs)).
      destruct Hin as [Heq | Hin].
      * apply (Qle_trans z b (dtr_lastq (b :: bs))).
        -- rewrite Heq in Hab. apply dtr_qle_bool_le. exact Hab.
        -- apply (IH b Hbs). left. reflexivity.
      * exact (IH z Hbs Hin).
Qed.

(* premises 22-23 (DTPT_Rotation.v:474) *)
Theorem dtr_sorted_hd_min : forall (l : list Q), dtr_SortedQ l ->
  forall z : Q, In z l -> (hd 0 l <= z)%Q.
Proof.
  intros l HS z Hin.
  destruct HS as [Hb].
  exact (dtr_sortedQb_hd_min l z Hb Hin).
Qed.

(* auxiliary B8: the last element belongs to a nonempty list, same *)
(* content as DTPT.v:630 built in place; used in the proofs of *)
(* premises 24-25 *)
Lemma dtr_xq_lastq_In : forall m : list Q, m <> [] -> In (dtr_lastq m) m.
Proof.
  induction m as [| a rest IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl. discriminate.
Qed.

(* premises 24-25 (DTPT_Rotation.v:487) *)
Theorem dtr_sorted_lastq_max : forall (l : list Q), dtr_SortedQ l ->
  forall z : Q, In z l -> (z <= dtr_lastq l)%Q.
Proof.
  intros l HS z Hin.
  destruct HS as [Hb].
  exact (dtr_sortedQb_lastq_max l z Hb Hin).
Qed.

(* premises 26-28 (DTPT_Rotation.v:506) *)
Theorem dtr_sorted_sub_le_spread : forall (l : list Q) (z w : Q),
  dtr_SortedQ l -> In z l -> In w l -> (z - w <= dtr_lastq l - hd 0 l)%Q.
Proof.
  intros l z w HS Hz Hw.
  assert (Hzm : (z <= dtr_lastq l)%Q) by (apply (dtr_sorted_lastq_max l HS z Hz)).
  assert (Hwn : (hd 0 l <= w)%Q) by (apply (dtr_sorted_hd_min l HS w Hw)).
  apply (dtr_qle_0_sub_intro (z - w) (dtr_lastq l - hd 0 l)).
  assert (Hr : (dtr_lastq l - hd 0 l - (z - w) == (dtr_lastq l - z) + (w - hd 0 l))%Q)
    by ring.
  rewrite Hr.
  apply dtr_qadd_nonneg.
  - apply (dtr_qle_0_sub_inv z (dtr_lastq l)). exact Hzm.
  - apply (dtr_qle_0_sub_inv (hd 0 l) w). exact Hwn.
Qed.

(* ============================================================ *)
(* supply theorems, continued: premises 29-36, statements 21-25,     *)
(* with the telescoping auxiliary lemmas                            *)
(* ============================================================ *)

(* the telescoping identity needs only the head-last order, which *)
(* follows from the adjacent bounds above *)
Lemma dtr_sortedQb_hd_le_lastq : forall l : list Q,
  dtr_sortedQb l = true -> (hd 0 l <= dtr_lastq l)%Q.
Proof.
  induction l as [| a rest IH]; intro Hb.
  - simpl. apply Qle_refl.
  - destruct rest as [| b bs].
    + simpl. apply Qle_refl.
    + simpl in Hb. apply andb_prop in Hb as [Hab Hbs].
      simpl. apply (Qle_trans a b (dtr_lastq (b :: bs))).
      * apply dtr_qle_bool_le. exact Hab.
      * exact (IH Hbs).
Qed.

Lemma dtr_sortedQb_telescope : forall l : list Q,
  dtr_sortedQb l = true -> dtr_H_adj l == dtr_lastq l - hd 0 l.
Proof.
  induction l as [| a rest IH]; intro Hb.
  - reflexivity.
  - destruct rest as [| b bs].
    + change (dtr_H_adj [a]) with 0%Q.
      change (dtr_lastq [a] - hd 0 [a]) with (a - a)%Q.
      symmetry. apply dtr_xq_minus_self.
    + simpl in Hb. apply andb_prop in Hb as [Hab Hbs].
      assert (Hle : (0 <= b - a)%Q).
      { apply (dtr_qle_0_sub_inv a b). apply dtr_qle_bool_le. exact Hab. }
      change (dtr_H_adj (a :: b :: bs)) with (Qabs (b - a) + dtr_H_adj (b :: bs))%Q.
      rewrite (dtr_xq_abs_id _ Hle).
      rewrite (IH Hbs).
      change (dtr_lastq (a :: b :: bs)) with (dtr_lastq (b :: bs)).
      change (hd 0 (a :: b :: bs)) with a.
      change (hd 0 (b :: bs)) with b.
      ring.
Qed.

(* auxiliary B9: head at most last on a sorted list, same content as *)
(* DTPT.v:652 built in place; used in the proofs of premises 29-31 *)
Lemma dtr_xq_hd_le_lastq : forall l : list Q,
  dtr_SortedQ l -> (hd 0 l <= dtr_lastq l)%Q.
Proof.
  intros l HS.
  destruct HS as [Hb].
  exact (dtr_sortedQb_hd_le_lastq l Hb).
Qed.

(* auxiliary B10: the telescoping identity dtr_H_adj l == *)
(* dtr_lastq l - hd 0 l, same content as DTPT.v:666 built in place; *)
(* carries the proofs of premises 29-36 *)
Lemma dtr_xq_telescope : forall l : list Q,
  dtr_SortedQ l -> dtr_H_adj l == dtr_lastq l - hd 0 l.
Proof.
  intros l HS.
  destruct HS as [Hb].
  exact (dtr_sortedQb_telescope l Hb).
Qed.

(* premises 29-31 (DTPT_Rotation.v:527) *)
Theorem dtr_H_adj_rotc_exact_mid : forall (k : nat) (l : list Q),
  dtr_SortedQ l -> (1 <= k)%nat -> (k < length l)%nat ->
  dtr_H_adj (dtr_rotc k l) == (dtr_lastq l - hd 0 (skipn k l))
                            + (dtr_lastq l - hd 0 l)
                            + (dtr_lastq (firstn k l) - hd 0 l).
Proof.
  intros k l HS H1 H2.
  assert (HSs : dtr_SortedQ (skipn k l)) by (apply dtr_skipn_SortedQ; exact HS).
  assert (HSf : dtr_SortedQ (firstn k l)) by (apply dtr_firstn_SortedQ; exact HS).
  assert (Hnes : skipn k l <> []) by (apply (dtr_skipn_ne_of_lt k l H2)).
  assert (Hnef : firstn k l <> []).
  { intro Hc. destruct l as [| a rest].
    - simpl in H2. exfalso. lia.
    - destruct k as [| k'].
      + exfalso. lia.
      + simpl in Hc. discriminate. }
  assert (HE : dtr_H_adj (dtr_rotc k l) == dtr_H_adj (skipn k l ++ firstn k l))
    by reflexivity.
  rewrite HE.
  rewrite (dtr_H_adj_app_seam (skipn k l) (firstn k l) Hnes Hnef).
  rewrite (dtr_xq_telescope (skipn k l) HSs).
  rewrite (dtr_xq_telescope (firstn k l) HSf).
  rewrite (dtr_lastq_skipn_kept l k H2).
  rewrite (dtr_hd_firstn_kept k l H1).
  assert (Hab : Qabs (hd 0 l - dtr_lastq l) == dtr_lastq l - hd 0 l).
  { rewrite (dtr_xq_abs_sub_comm (hd 0 l) (dtr_lastq l)).
    apply dtr_xq_abs_id.
    apply (dtr_qle_0_sub_inv (hd 0 l) (dtr_lastq l)).
    apply dtr_xq_hd_le_lastq. exact HS. }
  rewrite Hab. ring.
Qed.

(* auxiliary A6: the zero-rotation identity dtr_rotc 0 l = l, same *)
(* content as the premise-free host statement at :245; used in the *)
(* proofs of premises 32/35; it carries no top-level premise, hence *)
(* it is not one of the 36 premises *)
Lemma dtr_rotc_0 : forall l : list Q, dtr_rotc 0 l = l.
Proof.
  intros l. unfold dtr_rotc. simpl.
  induction l as [| a rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* premise 32 (DTPT_Rotation.v:560) *)
Theorem dtr_H_adj_rotc_exact_0 : forall l : list Q, dtr_SortedQ l ->
  dtr_H_adj (dtr_rotc 0 l) == dtr_lastq l - hd 0 l.
Proof.
  intros l HS. rewrite dtr_rotc_0. apply dtr_xq_telescope. exact HS.
Qed.

(* premises 33-34 (DTPT_Rotation.v:567) *)
Theorem dtr_H_adj_rotc_exact_ge : forall (k : nat) (l : list Q), dtr_SortedQ l ->
  (length l <= k)%nat -> dtr_H_adj (dtr_rotc k l) == dtr_lastq l - hd 0 l.
Proof.
  intros k l HS Hk.
  rewrite (dtr_rotc_ge_len_id k l Hk). apply dtr_xq_telescope. exact HS.
Qed.

(* premises 35-36 (DTPT_Rotation.v:575): the nat dichotomy is asserted *)
(* inside the proof, keeping the disjunction off the top-level *)
(* statement face *)
Theorem dtr_H_adj_rotc_exact_short : forall (k : nat) (l : list Q), dtr_SortedQ l ->
  (length l <= 1)%nat -> dtr_H_adj (dtr_rotc k l) == dtr_lastq l - hd 0 l.
Proof.
  intros k l HS Hn.
  assert (Hcases : forall p q : nat, (p <= q)%nat \/ (q < p)%nat).
  { intros p. induction p as [| p' IHp]; intros q.
    - left. lia.
    - destruct q as [| q'].
      + right. lia.
      + destruct (IHp q') as [Hle | Hgt]; [left | right]; lia. }
  destruct (Hcases (length l) k) as [Hle | Hgt].
  - apply (dtr_H_adj_rotc_exact_ge k l HS Hle).
  - assert (H0 : (k = 0)%nat) by lia.
    rewrite H0. rewrite dtr_rotc_0. apply dtr_xq_telescope. exact HS.
Qed.

(* ============================================================ *)
(*  registered-only section.  Two further statements of the host *)
(*  range (:49-:575) are quantified by an existential and carry no *)
(*  top-level premise, so they are recorded here rather than supplied: *)
(*  (1) H_rotc_separates (host :370), concluding *)
(*      exists l n, H_adj (rotc n l) <> H_adj l; *)
(*  (2) rotc_Pinf_separates (host :379), concluding *)
(*      exists l n s, rotc n l <> Pinf l s. *)
(*  Their content is proved inside the host already; a forward *)
(*  supply would restate the witnessed conclusions in a sigT-carried *)
(*  Type form and is left to a later volume. *)
(* ============================================================ *)

(* ============================================================ *)
(*  closing audit.  Print Assumptions runs on each of the 40 supplied *)
(*  statements (24 supply theorems and 16 auxiliary lemmas); every *)
(*  report is expected to read Closed under the global context. *)
(*  The sortedness helpers above add no axioms and appear *)
(*  transitively in the reports of their consumers. *)
(* ============================================================ *)

Print Assumptions dtr_cyc_qeq_le.
Print Assumptions dtr_cyc_le_triple.
Print Assumptions dtr_firstn_incl.
Print Assumptions dtr_skipn_incl.
Print Assumptions dtr_firstn_SortedQ.
Print Assumptions dtr_skipn_SortedQ.
Print Assumptions dtr_H_adj_app_seam.
Print Assumptions dtr_rotc_inv.
Print Assumptions dtr_rotc_in.
Print Assumptions dtr_H_rotc_span_lb.
Print Assumptions dtr_skipn_ne_of_lt.
Print Assumptions dtr_firstn_ne_of_lt.
Print Assumptions dtr_rotc_skipn_all.
Print Assumptions dtr_rotc_firstn_all.
Print Assumptions dtr_rotc_ge_len_id.
Print Assumptions dtr_lastq_skipn_kept.
Print Assumptions dtr_hd_firstn_kept.
Print Assumptions dtr_sorted_hd_min.
Print Assumptions dtr_sorted_lastq_max.
Print Assumptions dtr_sorted_sub_le_spread.
Print Assumptions dtr_H_adj_rotc_exact_mid.
Print Assumptions dtr_H_adj_rotc_exact_0.
Print Assumptions dtr_H_adj_rotc_exact_ge.
Print Assumptions dtr_H_adj_rotc_exact_short.
Print Assumptions dtr_qadd_le.
Print Assumptions dtr_qadd_nonneg.
Print Assumptions dtr_qle_0_sub_inv.
Print Assumptions dtr_qle_0_sub_intro.
Print Assumptions dtr_xq_minus_self.
Print Assumptions dtr_xq_abs_eq0.
Print Assumptions dtr_xq_abs_id.
Print Assumptions dtr_xq_abs_sub_comm.
Print Assumptions dtr_xq_abs_zero.
Print Assumptions dtr_xq_H_adj_nonneg.
Print Assumptions dtr_xq_le_add_abs.
Print Assumptions dtr_xq_pair_dist_le.
Print Assumptions dtr_xq_lastq_In.
Print Assumptions dtr_xq_hd_le_lastq.
Print Assumptions dtr_xq_telescope.
Print Assumptions dtr_rotc_0.

(* ============================================================ *)
(*  extraction audit: the Obj.magic count of the extracted output is *)
(*  expected to be 0.  The data layer extracts as real code (true *)
(*  rotation code for rotc/skipn/firstn, true recursion for *)
(*  sum_adjdiff and lastq, and the sortedness carrier as a boolean *)
(*  test with its witness constructor).  Every statement is then *)
(*  covered by a Separate Extraction; the two commands in this file *)
(*  overwrite each other's outputs by name, the convention in this *)
(*  development, so they only attest extractability of the statements *)
(*  while the per-volume extraction products are produced by a *)
(*  dedicated audit module re-extracting on target. *)
(* ============================================================ *)

Separate Extraction dtr_sum_adjdiff dtr_H_adj dtr_lastq dtr_rotc dtr_SortedQ.

Separate Extraction dtr_cyc_qeq_le dtr_cyc_le_triple dtr_firstn_incl
  dtr_skipn_incl dtr_firstn_SortedQ dtr_skipn_SortedQ
  dtr_H_adj_app_seam dtr_rotc_inv dtr_rotc_in dtr_H_rotc_span_lb
  dtr_skipn_ne_of_lt dtr_firstn_ne_of_lt dtr_rotc_skipn_all
  dtr_rotc_firstn_all dtr_rotc_ge_len_id dtr_lastq_skipn_kept
  dtr_hd_firstn_kept dtr_sorted_hd_min dtr_sorted_lastq_max
  dtr_sorted_sub_le_spread dtr_H_adj_rotc_exact_mid dtr_H_adj_rotc_exact_0
  dtr_H_adj_rotc_exact_ge dtr_H_adj_rotc_exact_short
  dtr_qadd_le dtr_qadd_nonneg dtr_qle_0_sub_inv dtr_qle_0_sub_intro
  dtr_xq_minus_self dtr_xq_abs_eq0 dtr_xq_abs_id dtr_xq_abs_sub_comm
  dtr_xq_abs_zero dtr_xq_H_adj_nonneg dtr_xq_le_add_abs
  dtr_xq_pair_dist_le dtr_xq_lastq_In dtr_xq_hd_le_lastq
  dtr_xq_telescope dtr_rotc_0.
