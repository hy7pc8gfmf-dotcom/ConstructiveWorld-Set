(* ConstructiveWorld-Set -- Q discrete-order supply lemmas, volume 1. *)

(** * abl_dtd_core1: supply lemmas for premises 1-35 of the DTPT host.

    Mission.  Supplies premises 1-35 of the host DTPT.v premise ledger
      (statement coordinates :129-:532) in direct A-form: each supplied
      statement reproduces the ledger form verbatim under the [dtd_]
      name map, with proofs constructed in place and no host-theorem
      use.  Also carries the local data copies [dtd_dedup],
      [dtd_Qmem], [dtd_Qnodup], [dtd_remove] used by the dedup
      counting family, and the audit exits at the file end.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List],
      [Bool.Bool], [Arith], [Lia], [Permutation], [Extraction].
      Requires no other module of this development.

    References.  This development, abl_dtd_core1.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier
      completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QeqT]/[QleT'] and [Id] forms);
      statements extract with [Obj.magic] = 0 and no erasure;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dtd_core1.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

(* ============================================================ *)
(* 1. Data-layer copies.  The duplicate-removing functions below       *)
(*    mirror the host DTPT.v data layer verbatim, isolated under the   *)
(*    dtd_ prefix to avoid name clashes.  dtd_remove is the element    *)
(*    removal function used by the counting lemmas of section 3.       *)
(* ============================================================ *)

Fixpoint dtd_dedup_aux (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => []
  | y :: ys => if Qeq_bool x y then dtd_dedup_aux x ys else y :: dtd_dedup_aux x ys
  end.

Fixpoint dtd_dedup (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => x :: dtd_dedup_aux x (dtd_dedup xs)
  end.

Definition dtd_H_ms (l : list Q) : Q := (Z.of_nat (length (dtd_dedup l)) # 1)%Q.

(* dtd_bid packages the boolean equation [b = true] into a one-        *)
(* constructor Set carrier: its only constructor takes a proof of      *)
(* [b = true], so a term of type [dtd_bid b] is exactly boolean        *)
(* evidence for [b]. *)
Inductive dtd_bid (b : bool) : Set :=
| dtd_bid_intro : b = true -> dtd_bid b.

(* bid-to-equation bridge: a bid term is exactly the boolean equation it
   packages, so premise-position carriers convert before Prop reasoning *)
Lemma dtd_bid_to_eq : forall b : bool, dtd_bid b -> b = true.
Proof. intros b H. destruct H as [H]. exact H. Qed.

(* dtd_Qmem carries membership of [a] in [l]: the membership boolean   *)
(* is [existsb (fun y => Qeq_bool a y) l] and the carrier wraps its    *)
(* truth. *)
Definition dtd_Qmem (a : Q) (l : list Q) : Set :=
  dtd_bid (existsb (fun y => Qeq_bool a y) l).

(* dtd_Qnodup is the boolean kernel of duplicate-freedom: the head     *)
(* differs from every tail element by [Qeq_bool], checked by           *)
(* [existsb], and the tail is recursively duplicate-free. *)
Fixpoint dtd_Qnodup (l : list Q) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (fun y => Qeq_bool x y) xs) && dtd_Qnodup xs
  end.

Fixpoint dtd_remove (x : Q) (n : list Q) : list Q :=
  match n with
  | [] => []
  | y :: ys => if Qeq_bool x y then ys else y :: dtd_remove x ys
  end.

(* ============================================================ *)
(* 2. Supply theorems: premises 1-17 (statements 1-12).                *)
(* ============================================================ *)

(* premise 1 (DTPT.v:129) *)
Theorem dtd_Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> y <= x.
Proof.
  intros x y H. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

(* premises 2-3 (DTPT.v:144) *)
Theorem dtd_qadd_le : forall a b c d : Q, a <= b -> c <= d -> (a + c <= b + d)%Q.
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

(* premise 4 (DTPT.v:157) *)
Theorem dtd_qopp_le : forall a b : Q, a <= b -> (- b <= - a)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* premises 5-6 (DTPT.v:163) *)
Theorem dtd_qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> (n * p <= m * p)%Q.
Proof.
  intros [nn nd] [mn md] [pn pd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

(* premise 7 (DTPT.v:179) *)
Theorem dtd_qsub_le_r : forall a b c : Q, a <= b -> (a - c <= b - c)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos cd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos cd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

(* premise 8 (DTPT.v:195) *)
Theorem dtd_abs_eq : forall a : Q, 0 <= a -> Qabs a == a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

(* premise 9 (DTPT.v:204) *)
Theorem dtd_abs_neg : forall a : Q, a <= 0 -> Qabs a == - a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Qed.

(* premise 10 (DTPT.v:218) *)
Theorem dtd_Qeqb_true_of : forall x y : Q, x == y -> Qeq_bool x y = true.
Proof.
  intros x y H. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

(* auxiliary H1: symmetry of [Qeq_bool]; not a premise position, but   *)
(* the premises 11-35 rest on it in their proofs. *)
Lemma dtd_Qeqb_sym : forall x y : Q, Qeq_bool x y = Qeq_bool y x.
Proof.
  intros x y. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    apply dtd_Qeqb_true_of in E1'. congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    apply dtd_Qeqb_true_of in E2'. congruence.
Qed.

(* premises 11-12 (DTPT.v:236) *)
Theorem dtd_Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Qeq_bool a c = true.
Proof.
  intros a b c H1 H2. apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  apply dtd_Qeqb_true_of. transitivity b; assumption.
Qed.

(* premises 13-14 (DTPT.v:257) *)
Theorem dtd_Qmem_weaken : forall a b (l : list Q),
  dtd_Qmem a l -> Qeq_bool a b = true -> dtd_Qmem b l.
Proof.
  intros a b l H Hab. destruct H as [Hm]. apply dtd_bid_intro.
  apply existsb_exists in Hm. destruct Hm as [w [Hw Hq]].
  apply existsb_exists. exists w. split; [exact Hw|].
  apply (dtd_Qeqb_trans b a w). rewrite (dtd_Qeqb_sym b a). exact Hab. exact Hq.
Qed.

(* premise 15 (DTPT.v:266) *)
Theorem dtd_Qmem_dedup_aux_keep : forall a x (l : list Q),
  dtd_Qmem a (dtd_dedup_aux x l) -> dtd_Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H. destruct H as [Hd]. discriminate Hd.
  - intros H. destruct (Qeq_bool x y).
    + destruct (IH H) as [He].
      apply dtd_bid_intro. simpl. apply orb_true_iff. right. exact He.
    + destruct H as [Hm]. simpl in Hm. apply orb_true_iff in Hm.
      apply dtd_bid_intro. simpl. apply orb_true_iff.
      destruct Hm as [Hy | Hm'].
      * left. exact Hy.
      * apply dtd_bid_intro in Hm'.
        right. apply dtd_bid_to_eq. exact (IH Hm').
Qed.

(* premises 16-17 (DTPT.v:278) *)
Theorem dtd_Qmem_dedup_aux_drop : forall a x (l : list Q),
  dtd_Qmem a l -> Qeq_bool a x = false -> dtd_Qmem a (dtd_dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H _. destruct H as [Hd]. discriminate Hd.
  - intros H Hax. destruct H as [Hm]. simpl in Hm. apply orb_true_iff in Hm.
    destruct (Qeq_bool x y) eqn:Hxy.
    + apply dtd_bid_intro. simpl.
      destruct Hm as [Hy | Hm'].
      * exfalso.
        assert (Hya : Qeq_bool y a = true) by (rewrite (dtd_Qeqb_sym y a); exact Hy).
        assert (Hxa : Qeq_bool x a = true) by (apply (dtd_Qeqb_trans x y a); assumption).
        rewrite (dtd_Qeqb_sym x a) in Hxa. rewrite Hxa in Hax. discriminate.
      * apply dtd_bid_intro in Hm'. apply dtd_bid_to_eq. exact (IH Hm' Hax).
    + apply dtd_bid_intro. simpl. apply orb_true_iff.
      destruct Hm as [Hy | Hm'].
      * left. exact Hy.
      * apply dtd_bid_intro in Hm'.
        right. apply dtd_bid_to_eq. exact (IH Hm' Hax).
Qed.

(* ============================================================ *)
(* Premise 18 (dedup_aux_duck, DTPT.v:296) is recorded without direct  *)
(* supply: its conclusion embeds an implication to False, a shape the  *)
(* supplied statements avoid.  Its contradiction core is replayed for  *)
(* real inside the proof of dtd_dedup_Qnodup as an internal assert,    *)
(* which extraction erases together with the proof body. *)
(* ============================================================ *)

(* premise 19 (DTPT.v:314) *)
Theorem dtd_dedup_aux_Qnodup : forall x (l : list Q),
  dtd_bid (dtd_Qnodup l) -> dtd_bid (dtd_Qnodup (dtd_dedup_aux x l)).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - intros _. apply dtd_bid_intro. reflexivity.
  - intros H. apply dtd_bid_intro. destruct H as [Heq]. simpl in Heq.
    apply andb_true_iff in Heq. destruct Heq as [Hny Hys].
    destruct (Qeq_bool x y).
    + apply dtd_bid_to_eq. apply IH. exact (dtd_bid_intro _ Hys).
    + simpl. apply andb_true_iff. split.
      * apply negb_true_iff in Hny. apply negb_true_iff.
        destruct (existsb (fun z => Qeq_bool y z) (dtd_dedup_aux x ys)) eqn:E;
          [| reflexivity].
        exfalso. apply existsb_exists in E. destruct E as [w [Hw Hq]].
        assert (Hk : dtd_Qmem y (dtd_dedup_aux x ys))
          by (apply dtd_bid_intro; apply existsb_exists;
              exists w; split; [exact Hw | exact Hq]).
        destruct (dtd_Qmem_dedup_aux_keep y x _ Hk) as [Ht].
        rewrite Hny in Ht. discriminate.
      * destruct (IH (dtd_bid_intro _ Hys)) as [Heq2]. apply dtd_bid_to_eq. exact (dtd_bid_intro _ Heq2).
Qed.

(* premise 20 (DTPT.v:333) *)
Theorem dtd_dedup_Qmem_l : forall (l : list Q) a,
  dtd_Qmem a (dtd_dedup l) -> dtd_Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. destruct H as [Hd]. discriminate Hd.
  - intros H. destruct H as [Hm]. simpl in Hm. apply orb_true_iff in Hm.
    apply dtd_bid_intro. simpl. apply orb_true_iff.
    destruct Hm as [Hx | Hs].
    + left. exact Hx.
    + right. apply dtd_bid_to_eq.
      exact (IH a (dtd_Qmem_dedup_aux_keep a x _ (dtd_bid_intro _ Hs))).
Qed.

(* premise 21 (DTPT.v:343) *)
Theorem dtd_dedup_Qmem_r : forall (l : list Q) a,
  dtd_Qmem a l -> dtd_Qmem a (dtd_dedup l).
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. destruct H as [Hd]. discriminate Hd.
  - intros H. destruct H as [Hm]. simpl in Hm. apply orb_true_iff in Hm.
    apply dtd_bid_intro. simpl. apply orb_true_iff.
    destruct Hm as [Hx | Hs].
    + left. exact Hx.
    + destruct (Qeq_bool a x) eqn:Hax.
      * left. reflexivity.
      * right. apply dtd_bid_to_eq.
        exact (dtd_Qmem_dedup_aux_drop a x (dtd_dedup xs)
                 (IH a (dtd_bid_intro _ Hs)) Hax).
Qed.

(* ============================================================ *)
(* Four premises with mixed statement shapes are recorded without      *)
(* direct supply:                                                      *)
(*   premise 22 = Qmem_perm (DTPT.v:357), an iff conclusion;           *)
(*   premise 23 = Qmem_cons_nodup (DTPT.v:364), negation and iff;      *)
(*   premises 24-25 = remove_one (DTPT.v:378), iff and an exists       *)
(*     witness;                                                        *)
(*   premises 26-28 = same_set_length (DTPT.v:434), an iff over the Q  *)
(*     order.                                                          *)
(* Their content is carried by the atomic decompositions of section 3: *)
(* the computational removal function dtd_remove with the four removal *)
(* lemmas, and dtd_len_eq_of_mem2 phrased as two one-way forall        *)
(* implications. *)
(* ============================================================ *)

(* ============================================================ *)
(* 3. Auxiliary lemmas (infrastructure, not premise positions).  Their *)
(*    statements use the same atomic discrete carriers as the supply   *)
(*    theorems. *)
(* ============================================================ *)

(* auxiliary H2: membership passes from a sublist to the full list. *)
Lemma dtd_remove_sub_mem : forall a x (n : list Q),
  dtd_Qmem a (dtd_remove x n) -> dtd_Qmem a n.
Proof.
  intros a x n. induction n as [| y ys IH]; simpl.
  - intros H. destruct H as [Hd]. discriminate Hd.
  - destruct (Qeq_bool x y).
    + intros H. destruct H as [He].
      apply dtd_bid_intro. simpl. apply orb_true_iff. right. exact He.
    + intros H. destruct H as [Hm]. simpl in Hm. apply orb_true_iff in Hm.
      apply dtd_bid_intro. simpl. apply orb_true_iff.
      destruct Hm as [Hy | Hm'].
      * left. exact Hy.
      * right. apply dtd_bid_to_eq. exact (IH (dtd_bid_intro _ Hm')).
Qed.

(* auxiliary H3: membership survives removal of an element distinct    *)
(* from the member. *)
Lemma dtd_remove_mem_in : forall a x (n : list Q),
  dtd_Qmem a n -> Qeq_bool a x = false -> dtd_Qmem a (dtd_remove x n).
Proof.
  intros a x n. induction n as [| y ys IH]; simpl.
  - intros H _. destruct H as [Hd]. discriminate Hd.
  - intros H Hax. destruct H as [Hm]. simpl in Hm. apply orb_true_iff in Hm.
    destruct (Qeq_bool x y) eqn:Hxy.
    + apply dtd_bid_intro. simpl.
      destruct Hm as [Hy | Hm'].
      * exfalso.
        assert (Hyx : Qeq_bool y x = true)
          by (rewrite <- (dtd_Qeqb_sym x y); exact Hxy).
        assert (Hayx : Qeq_bool a x = true)
          by (apply (dtd_Qeqb_trans a y x); assumption).
        rewrite Hayx in Hax. discriminate.
      * exact Hm'.
    + apply dtd_bid_intro. simpl. apply orb_true_iff.
      destruct Hm as [Hy | Hm'].
      * left. exact Hy.
      * right. apply dtd_bid_to_eq. exact (IH (dtd_bid_intro _ Hm') Hax).
Qed.

(* auxiliary H4: removal preserves duplicate-freedom. *)
Lemma dtd_remove_nd : forall x (n : list Q),
  dtd_bid (dtd_Qnodup n) -> dtd_Qmem x n -> dtd_bid (dtd_Qnodup (dtd_remove x n)).
Proof.
  intros x n. induction n as [| y ys IH]; simpl.
  - intros _ _. apply dtd_bid_intro. reflexivity.
  - intros Hnd Hx. apply dtd_bid_intro. destruct Hnd as [Heq]. simpl in Heq.
    apply andb_true_iff in Heq. destruct Heq as [Hny Hndy].
    apply negb_true_iff in Hny.
    destruct (Qeq_bool x y) eqn:Hxy.
    + exact Hndy.
    + assert (Hxys : dtd_Qmem x ys).
      { apply dtd_bid_intro. apply dtd_bid_to_eq in Hx. apply orb_true_iff in Hx.
        destruct Hx as [Hc | Hc].
        - rewrite Hxy in Hc. discriminate.
        - exact Hc. }
      apply dtd_bid_intro. apply andb_true_iff. split.
      * apply negb_true_iff.
        destruct (existsb (fun z => Qeq_bool y z) (dtd_remove x ys)) eqn:E;
          [| reflexivity].
        exfalso. apply existsb_exists in E. destruct E as [w [Hw Hq]].
        assert (Hk : dtd_Qmem y (dtd_remove x ys))
          by (apply dtd_bid_intro; apply existsb_exists;
              exists w; split; [exact Hw | exact Hq]).
        destruct (dtd_remove_sub_mem y x ys Hk) as [Ht].
        rewrite Hny in Ht. discriminate.
      * apply dtd_bid_to_eq.
        apply IH; [exact (dtd_bid_intro _ Hndy) | exact Hxys].
Qed.

(* auxiliary H5: removal of a member shortens the list by exactly one. *)
Lemma dtd_remove_len : forall x (n : list Q),
  dtd_Qmem x n -> length n = S (length (dtd_remove x n)).
Proof.
  intros x n. induction n as [| y ys IH]; simpl.
  - intros H. destruct H as [Hd]. discriminate Hd.
  - intros H. destruct (Qeq_bool x y) eqn:Hxy.
    + reflexivity.
    + destruct H as [Hm]. simpl in Hm. apply orb_true_iff in Hm.
      destruct Hm as [Hc | Hc].
      * rewrite Hxy in Hc. discriminate.
      * apply dtd_bid_intro in Hc.
        specialize (IH Hc). simpl. rewrite <- IH. reflexivity.
Qed.

(* auxiliary H6: the head of a list is a member of it. *)
Lemma dtd_Qmem_refl_cons : forall x (l : list Q), dtd_Qmem x (x :: l).
Proof.
  intros x l. apply dtd_bid_intro. simpl. apply orb_true_iff. left.
  apply Qeq_bool_refl.
Qed.

(* auxiliary H7: two lists with equal membership in both directions    *)
(* and duplicate-freedom on both sides have equal length.  This        *)
(* decomposes the recorded same_set_length content into two one-way    *)
(* forall implications; removal goes through the computational          *)
(* dtd_remove and H2-H5.  The fact that the removed element leaves no  *)
(* survivor of its Qeq_bool class is proved as the internal assert     *)
(* Hkill below, matching the -> False shape of premise 18; it stays    *)
(* inside the proof and is erased by extraction. *)
Lemma dtd_len_eq_of_mem2 : forall m n : list Q,
  dtd_bid (dtd_Qnodup m) -> dtd_bid (dtd_Qnodup n) ->
  (forall a, dtd_Qmem a m -> dtd_Qmem a n) ->
  (forall a, dtd_Qmem a n -> dtd_Qmem a m) ->
  length m = length n.
Proof.
  intros m. induction m as [| x xs IH]; intros n Hm Hn Hmn Hnm.
  - destruct n as [| y ys].
    + reflexivity.
    + exfalso.
      pose proof (Hnm y (dtd_Qmem_refl_cons y ys)) as Hc.
      destruct Hc as [Hc0]. discriminate Hc0.
  - destruct n as [| y ys].
    + exfalso.
      pose proof (Hmn x (dtd_Qmem_refl_cons x xs)) as Hc.
      destruct Hc as [Hc0]. discriminate Hc0.
    + destruct Hm as [Hm1]. simpl in Hm1.
      apply andb_true_iff in Hm1. destruct Hm1 as [Hnx Hmxs].
      apply negb_true_iff in Hnx.
      assert (Hmx : dtd_Qmem x xs -> False).
      { intros Hcq. destruct Hcq as [Hcq0].
        rewrite Hnx in Hcq0. discriminate. }
      assert (Hx : dtd_Qmem x (y :: ys)) by (apply Hmn, dtd_Qmem_refl_cons).
      assert (Hkill : forall (u v : Q) (m0 : list Q),
                   dtd_bid (dtd_Qnodup m0) -> Qeq_bool u v = true ->
                   dtd_Qmem u (dtd_remove v m0) -> False).
      { intros u v m0. induction m0 as [| y0 ys0 IHk]; simpl.
        - intros _ _ H0. destruct H0 as [H00]. discriminate H00.
        - intros Hnd Huv H0. destruct Hnd as [Heq0]. simpl in Heq0.
          apply andb_true_iff in Heq0. destruct Heq0 as [Hny0 Hndy0].
          apply negb_true_iff in Hny0.
          destruct (Qeq_bool v y0) eqn:Hvy.
          + assert (Huy : Qeq_bool u y0 = true)
              by (apply (dtd_Qeqb_trans u v y0); assumption).
            simpl in H0.
            assert (Hwy : dtd_Qmem y0 ys0)
              by (apply (dtd_Qmem_weaken u y0 ys0 H0 Huy)).
            apply dtd_bid_to_eq in Hwy. rewrite Hny0 in Hwy. discriminate.
          + simpl in H0.
            destruct H0 as [Hb1]. simpl in Hb1.
            apply orb_true_iff in Hb1. destruct Hb1 as [Hb | Hb].
            * assert (Hyu : Qeq_bool y0 u = true)
                by (rewrite (dtd_Qeqb_sym y0 u); exact Hb).
              assert (Hyv : Qeq_bool y0 v = true)
                by (apply (dtd_Qeqb_trans y0 u v); assumption).
              rewrite (dtd_Qeqb_sym v y0) in Hvy.
              rewrite Hyv in Hvy. discriminate.
            * apply dtd_bid_intro in Hb.
              exact (IHk (dtd_bid_intro _ Hndy0) Huv Hb). }
      assert (Hnd' : dtd_bid (dtd_Qnodup (dtd_remove x (y :: ys))))
        by (apply dtd_remove_nd; [exact Hn | exact Hx]).
      assert (Hlen' : length (y :: ys) = S (length (dtd_remove x (y :: ys))))
        by (apply dtd_remove_len; exact Hx).
      assert (Hlen : length xs = length (dtd_remove x (y :: ys))).
      { apply (IH (dtd_remove x (y :: ys)) (dtd_bid_intro _ Hmxs) Hnd').
        - intros a Ha.
          assert (Ham : dtd_Qmem a (x :: xs)).
          { apply dtd_bid_intro. simpl. apply orb_true_iff. right.
            destruct Ha as [Hae]. exact Hae. }
          pose proof (Hmn a Ham) as Han.
          assert (Haxf : Qeq_bool a x = false).
          { destruct (Qeq_bool a x) eqn:E.
            - exfalso. exact (Hmx (dtd_Qmem_weaken a x xs Ha E)).
            - reflexivity. }
          exact (dtd_remove_mem_in a x (y :: ys) Han Haxf).
        - intros a Ha.
          pose proof (dtd_remove_sub_mem a x (y :: ys) Ha) as Han.
          destruct (Hnm a Han) as [Ham'].
          destruct (Qeq_bool a x) eqn:E2.
          + exfalso. exact (Hkill a x (y :: ys) Hn E2 Ha).
          + simpl in Ham'.
            apply orb_true_iff in Ham'.
            apply dtd_bid_intro.
            destruct Ham' as [Hc1 | Hc1].
            * rewrite E2 in Hc1. discriminate.
            * exact Hc1. }
      rewrite Hlen'. rewrite <- Hlen. reflexivity.
Qed.

(* auxiliary H8: dedup is duplicate-free (same content as the zero-    *)
(* premise host statement at DTPT.v:351; not a premise position).  The *)
(* premise 18 contradiction core is replayed as the internal assert    *)
(* Hduck inside the proof. *)
Lemma dtd_dedup_Qnodup : forall l : list Q, dtd_bid (dtd_Qnodup (dtd_dedup l)).
Proof.
  intros l. induction l as [| x xs IH]; simpl.
  - apply dtd_bid_intro. reflexivity.
  - assert (Hduck : forall (a : Q) (m : list Q),
               negb (existsb (fun z => Qeq_bool a z) (dtd_dedup_aux a m)) = true).
    { intros a m. induction m as [| y ys IHd]; simpl.
      - reflexivity.
      - destruct (Qeq_bool a y) eqn:Eay; simpl.
        + exact IHd.
        + rewrite Eay. exact IHd. }
    apply dtd_bid_intro. apply andb_true_iff. split.
    + exact (Hduck x (dtd_dedup xs)).
    + apply dtd_bid_to_eq.
      exact (dtd_dedup_aux_Qnodup x (dtd_dedup xs) IH).
Qed.

(* ============================================================ *)
(* 4. Supply theorems continued: premises 29-35 (statements 21-26). *)
(* ============================================================ *)

(* premise 29 (DTPT.v:465) *)
Theorem dtd_N9_ms_perm_inv : forall (l p : list Q),
  Permutation l p -> dtd_H_ms l = dtd_H_ms p.
Proof.
  intros l p Hp. unfold dtd_H_ms. f_equal. f_equal.
  apply dtd_len_eq_of_mem2.
  - apply dtd_dedup_Qnodup.
  - apply dtd_dedup_Qnodup.
  - intros a Ha.
    apply dtd_bid_intro.
    assert (Hpeq : existsb (fun y => Qeq_bool a y) p = true).
    { pose proof (dtd_dedup_Qmem_l l a Ha) as Hal.
      apply dtd_bid_to_eq in Hal.
      apply existsb_exists in Hal. destruct Hal as [w [Hw Hq]].
      apply existsb_exists. exists w. split.
      + apply (Permutation_in _ Hp). exact Hw.
      + exact Hq. }
    apply dtd_bid_to_eq.
    exact (dtd_dedup_Qmem_r p a (dtd_bid_intro _ Hpeq)).
  - intros a Ha.
    apply dtd_bid_intro.
    assert (Hleq : existsb (fun y => Qeq_bool a y) l = true).
    { pose proof (dtd_dedup_Qmem_l p a Ha) as Hap.
      apply dtd_bid_to_eq in Hap.
      apply existsb_exists in Hap. destruct Hap as [w [Hw Hq]].
      apply existsb_exists. exists w. split.
      + apply (Permutation_in _ (Permutation_sym Hp)). exact Hw.
      + exact Hq. }
    apply dtd_bid_to_eq.
    exact (dtd_dedup_Qmem_r l a (dtd_bid_intro _ Hleq)).
Qed.

(* premises 30-31 (DTPT.v:491) *)
Theorem dtd_qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* premise 32 (DTPT.v:499) *)
Theorem dtd_xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  apply Z.leb_le. exact H.
Qed.

(* premise 33 (DTPT.v:506) *)
Theorem dtd_xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

(* premise 34 (DTPT.v:514) *)
Theorem dtd_xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

(* premise 35 (DTPT.v:532) *)
Theorem dtd_xq_abs_eq : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros [n1 d1] [n2 d2] Hxy.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

(* ============================================================ *)
(* 5. Assumption audit at the end of the file: each supplied theorem   *)
(*    and each auxiliary lemma prints its global assumptions; the      *)
(*    expected report for all 29 names is Closed under the global      *)
(*    context. *)
(* ============================================================ *)

Print Assumptions dtd_Qle_bool_false_le.
Print Assumptions dtd_qadd_le.
Print Assumptions dtd_qopp_le.
Print Assumptions dtd_qmul_le_r.
Print Assumptions dtd_qsub_le_r.
Print Assumptions dtd_abs_eq.
Print Assumptions dtd_abs_neg.
Print Assumptions dtd_Qeqb_true_of.
Print Assumptions dtd_Qeqb_trans.
Print Assumptions dtd_Qmem_weaken.
Print Assumptions dtd_Qmem_dedup_aux_keep.
Print Assumptions dtd_Qmem_dedup_aux_drop.
Print Assumptions dtd_dedup_aux_Qnodup.
Print Assumptions dtd_dedup_Qmem_l.
Print Assumptions dtd_dedup_Qmem_r.
Print Assumptions dtd_N9_ms_perm_inv.
Print Assumptions dtd_qadd_nonneg.
Print Assumptions dtd_xq_Qle_bool_le.
Print Assumptions dtd_xq_abs_id.
Print Assumptions dtd_xq_abs_eq0.
Print Assumptions dtd_xq_abs_eq.
Print Assumptions dtd_Qeqb_sym.
Print Assumptions dtd_remove_sub_mem.
Print Assumptions dtd_remove_mem_in.
Print Assumptions dtd_remove_nd.
Print Assumptions dtd_remove_len.
Print Assumptions dtd_Qmem_refl_cons.
Print Assumptions dtd_len_eq_of_mem2.
Print Assumptions dtd_dedup_Qnodup.

(* ============================================================ *)
(* 6. Extraction check.  First the data layer (the duplicate-removal   *)
(*    family and the Qeq_bool-driven removal function) extracts as     *)
(*    real programs.  Then each of the 29 theorems is extracted        *)
(*    separately; proof-only content, including the boolean evidence   *)
(*    wrapped by dtd_bid, is erased by extraction. *)
(* ============================================================ *)

Separate Extraction dtd_dedup_aux dtd_dedup dtd_H_ms dtd_remove dtd_Qmem dtd_Qnodup.

Separate Extraction dtd_Qle_bool_false_le dtd_qadd_le dtd_qopp_le dtd_qmul_le_r
  dtd_qsub_le_r dtd_abs_eq dtd_abs_neg dtd_Qeqb_true_of dtd_Qeqb_trans
  dtd_Qmem_weaken dtd_Qmem_dedup_aux_keep dtd_Qmem_dedup_aux_drop
  dtd_dedup_aux_Qnodup dtd_dedup_Qmem_l dtd_dedup_Qmem_r dtd_N9_ms_perm_inv
  dtd_qadd_nonneg dtd_xq_Qle_bool_le dtd_xq_abs_id dtd_xq_abs_eq0 dtd_xq_abs_eq
  dtd_Qeqb_sym dtd_remove_sub_mem dtd_remove_mem_in
  dtd_remove_nd dtd_remove_len dtd_Qmem_refl_cons dtd_len_eq_of_mem2
  dtd_dedup_Qnodup.
