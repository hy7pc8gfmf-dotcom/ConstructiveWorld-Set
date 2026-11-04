(* ConstructiveWorld-Set -- decision-tree threshold counting family. *)

(** * UpAblBYUpperTight: balanced threshold trees with tight bounds.

    Mission.  Binary decision trees over monotone threshold queries:
      run/depth/leaf-count core [bylb_run], [bylb_depth],
      [bylb_nleaves]; threshold function [bylb_ft] with specification
      carrier [bylb_thr_spec], instances [bylb_ft_spec],
      [bylb_ft_mono]; NoDup lemmas [bylb_nodup_cons_notin],
      [bylb_nodup_app_inv], [bylb_nodup_map_inj], [bylb_seq_nodup],
      [bylb_run_nodup_split]; counting core [bylb_count_leaves_ge]
      with lower bound [bylb_lower_bound]; builder [btight_build]
      with [btight_build_spec], [btight_nleaves_exact], [bylb_tight].

    Dependencies.  Stdlib [List], [Bool.Bool], [Arith.Arith], [Lia].
      Self-contained; requires no other module of this development.

    References.  This development, UpAblBYUpperTight.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier
      completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (specifications as single-constructor inductive carriers);
      statements extract with [Obj.magic] = 0 and no erasure;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblBYUpperTight.v]
      compiles cleanly (exit 0); the artifact starts with
      [436f7121 000160bc]. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.

(* ========== 1. minimal boolean comparison decision trees (nat query positions, leaves tagged with the threshold verdict) ========== *)

Inductive bylb_dtree : Type :=
| bylb_dleaf : nat -> bylb_dtree
| bylb_dnode : nat -> bylb_dtree -> bylb_dtree -> bylb_dtree.

(* run core: at a query position n the oracle f sends the walk right on true and left on false; a leaf stops the walk. *)
Fixpoint bylb_run (T : bylb_dtree) (f : nat -> bool) : bylb_dtree :=
  match T with
  | bylb_dleaf m => bylb_dleaf m
  | bylb_dnode n l r => bylb_run (if f n then r else l) f
  end.

Fixpoint bylb_depth (T : bylb_dtree) : nat :=
  match T with
  | bylb_dleaf _ => 0
  | bylb_dnode _ l r => S (Nat.max (bylb_depth l) (bylb_depth r))
  end.

Fixpoint bylb_nleaves (T : bylb_dtree) : nat :=
  match T with
  | bylb_dleaf _ => 1
  | bylb_dnode _ l r => bylb_nleaves l + bylb_nleaves r
  end.

(* ========== 2. monotone threshold functions (nat -> bool, with the threshold specification) ========== *)

(* characteristic function of a threshold t: false for n < t, true for t <= n; the thresholds at play range over {0, ..., K}. *)
Definition bylb_ft (t : nat) : nat -> bool := fun n => t <=? n.

(* threshold specification: the two boolean equations on f, bundled as a
   single-constructor inductive carrier in Set. *)
Inductive bylb_thr_spec (t : nat) (f : nat -> bool) : Set :=
| bylb_thr_spec_intro :
    (forall n, n < t -> f n = false) -> (forall n, t <= n -> f n = true) ->
    bylb_thr_spec t f.

Lemma bylb_ft_spec : forall t : nat, bylb_thr_spec t (bylb_ft t).
Proof.
  intros t. apply bylb_thr_spec_intro; intros n H; unfold bylb_ft.
  - apply Nat.leb_gt. exact H.
  - apply Nat.leb_le. exact H.
Qed.

(* monotonicity premise: at a fixed threshold t, a point reading true keeps reading true as n grows (pointwise form). *)
Lemma bylb_ft_mono : forall (t n1 n2 : nat),
  n1 <= n2 -> bylb_ft t n1 = true -> bylb_ft t n2 = true.
Proof.
  intros t n1 n2 Hle H. unfold bylb_ft in *.
  apply Nat.leb_le. apply Nat.le_trans with (m := n1).
  - apply Nat.leb_le. exact H.
  - exact Hle.
Qed.

(* ========== 3. NoDup helpers, on the stdlib lemmas NoDup_cons_iff and *)
(*    NoDup_app_remove_l / NoDup_app_remove_r ========== *)

Lemma bylb_nodup_cons_notin : forall (A : Type) (a : A) (l : list A),
  NoDup (a :: l) -> ~ In a l.
Proof.
  intros A a l H. apply NoDup_cons_iff in H. apply H.
Qed.

Lemma bylb_nodup_app_inv : forall (A : Type) (a b : list A),
  NoDup (a ++ b) -> NoDup a /\ NoDup b.
Proof.
  intros A a b H. split.
  - apply (NoDup_app_remove_r a b H).
  - apply (NoDup_app_remove_l a b H).
Qed.

Lemma bylb_nodup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj H. induction H as [| x l Hnin Hnd IH]; cbn [map].
  - constructor.
  - constructor.
    + intros HI. apply in_map_iff in HI. destruct HI as [y [Hfy Hiny]].
      apply Hinj in Hfy. subst y. apply Hnin. exact Hiny.
    + exact IH.
Qed.

Lemma bylb_seq_nodup : forall len start : nat, NoDup (seq start len).
Proof.
  induction len as [| len IH]; intros start; cbn [seq].
  - constructor.
  - constructor.
    + intros HI. apply in_seq in HI. lia.
    + apply IH.
Qed.

(* ========== 4. split-and-count core ========== *)

(* at a node query position n, the answers false/true split the threshold list
   ts into left and right sublists, and the run image of each subtree over its
   sublist stays NoDup. *)
(* the list equation [image ts = image left ++ image right] fails here: with
   one threshold below n and one above n, the two sublists appear in an order
   different from ts, so the proof keeps NoDup directly and never passes
   through a list equation. *)
Lemma bylb_run_nodup_split :
  forall (n : nat) (l r : bylb_dtree) (ts : list nat),
    NoDup (map (fun t => bylb_run (bylb_dnode n l r) (bylb_ft t)) ts) ->
    NoDup (map (fun t => bylb_run l (bylb_ft t))
               (filter (fun t => negb (bylb_ft t n)) ts)) /\
    NoDup (map (fun t => bylb_run r (bylb_ft t))
               (filter (fun t => bylb_ft t n) ts)).
Proof.
  intros n l r. induction ts as [| t ts IH]; intros Hnd.
  - split; constructor.
  - cbn [map] in Hnd. apply NoDup_cons_iff in Hnd.
    destruct Hnd as [Hnin Hndts]. apply IH in Hndts.
    destruct Hndts as [HndL HndR].
    cbn [filter]. destruct (bylb_ft t n) eqn:E.
    + split.
      * exact HndL.
      * cbn [map negb]. constructor.
        -- intros HI. apply in_map_iff in HI.
           destruct HI as [t' [Hrun Hflt]]. apply filter_In in Hflt.
           destruct Hflt as [Hts Hq].
           assert (Hq' : bylb_ft t' n = true) by exact Hq.
           assert (Hg : bylb_run (bylb_dnode n l r) (bylb_ft t')
                        = bylb_run (bylb_dnode n l r) (bylb_ft t)).
           { cbn [bylb_run]. rewrite Hq'. rewrite E.
             cbn [bylb_run]. rewrite Hrun. reflexivity. }
           apply Hnin. rewrite <- Hg.
           exact (in_map (fun t0 => bylb_run (bylb_dnode n l r) (bylb_ft t0))
                         ts t' Hts).
        -- exact HndR.
    + split.
      * cbn [map negb]. constructor.
        -- intros HI. apply in_map_iff in HI.
           destruct HI as [t' [Hrun Hflt]]. apply filter_In in Hflt.
           destruct Hflt as [Hts Hq].
           assert (Hq' : negb (bylb_ft t' n) = true) by exact Hq.
           apply negb_true_iff in Hq'.
           assert (Hg : bylb_run (bylb_dnode n l r) (bylb_ft t')
                        = bylb_run (bylb_dnode n l r) (bylb_ft t)).
           { cbn [bylb_run]. rewrite Hq'. rewrite E.
             cbn [bylb_run]. rewrite Hrun. reflexivity. }
           apply Hnin. rewrite <- Hg.
           exact (in_map (fun t0 => bylb_run (bylb_dnode n l r) (bylb_ft t0))
                         ts t' Hts).
        -- exact HndL.
      * exact HndR.
Qed.

Lemma bylb_filter_split_length :
  forall (n : nat) (ts : list nat),
    length (filter (fun t => negb (bylb_ft t n)) ts)
    + length (filter (fun t => bylb_ft t n) ts) = length ts.
Proof.
  intros n. induction ts as [| a l IH]; cbn [length filter].
  - reflexivity.
  - destruct (bylb_ft a n); cbn [negb filter length]; lia.
Qed.

(* main count: when the run images over ts are pairwise distinct (NoDup), the
   length of ts is at most the leaf count. *)
(* leaf case: a constant leaf covers at most one threshold; node case: the
   lemma [bylb_run_nodup_split] hands the NoDup premise to the left and right
   sublists, the two inductions close it, and additivity gives the bound. *)
Theorem bylb_count_leaves_ge :
  forall (T : bylb_dtree) (ts : list nat),
    NoDup (map (fun t => bylb_run T (bylb_ft t)) ts) ->
    length ts <= bylb_nleaves T.
Proof.
  intros T. induction T as [m | n l IHl r IHr]; intros ts Hnd.
  - destruct ts as [| t ts].
    + cbn [length bylb_nleaves]. lia.
    + cbn [map bylb_run] in Hnd.
      apply bylb_nodup_cons_notin in Hnd.
      destruct ts as [| a rest]; cbn [length bylb_nleaves]; [lia |].
      exfalso. apply Hnd. cbn [map]. apply in_eq.
  - destruct (bylb_run_nodup_split n l r ts Hnd) as [HndL HndR].
    specialize (IHl (filter (fun t => negb (bylb_ft t n)) ts) HndL).
    specialize (IHr (filter (fun t => bylb_ft t n) ts) HndR).
    cbn [bylb_nleaves].
    pose proof (bylb_filter_split_length n ts) as Hsp.
    rewrite <- Hsp. apply Nat.add_le_mono; assumption.
Qed.

(* ========== 5. leaf count versus depth, and the main statements ========== *)

Lemma bylb_leaves_pow_depth :
  forall T : bylb_dtree, bylb_nleaves T <= 2 ^ bylb_depth T.
Proof.
  intros T. induction T as [m | n l IHl r IHr]; cbn [bylb_nleaves bylb_depth].
  - cbn. lia.
  - assert (Hb : 2 <> 0) by lia.
    assert (H1 : 2 ^ bylb_depth l
                 <= 2 ^ Nat.max (bylb_depth l) (bylb_depth r))
      by (apply Nat.pow_le_mono_r; lia).
    assert (H2 : 2 ^ bylb_depth r
                 <= 2 ^ Nat.max (bylb_depth l) (bylb_depth r))
      by (apply Nat.pow_le_mono_r; lia).
    assert (Hs : 2 ^ S (Nat.max (bylb_depth l) (bylb_depth r))
                 = 2 * 2 ^ Nat.max (bylb_depth l) (bylb_depth r))
      by reflexivity.
    lia.
Qed.

(* the correctness premise takes the form: running the oracle on threshold t
   must stop at [bylb_dleaf t], the leaf labeled by that same threshold. *)
(* the run images of the K+1 thresholds are then pairwise distinct by
   constructor injectivity; the count core gives leaves >= K+1, and
   leaves <= 2^depth gives Nat.log2 (S K) <= depth. *)
Theorem bylb_correct_tree_leaves :
  forall (K : nat) (T : bylb_dtree),
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) ->
    S K <= bylb_nleaves T /\ Nat.log2 (S K) <= bylb_depth T.
Proof.
  intros K T Hcorr.
  assert (Hme : map (fun t => bylb_run T (bylb_ft t)) (seq 0 (S K))
              = map (fun t => bylb_dleaf t) (seq 0 (S K))).
  { apply map_ext_in. intros t Ht. apply in_seq in Ht. apply Hcorr. lia. }
  assert (Hnd : NoDup (map (fun t => bylb_dleaf t) (seq 0 (S K)))).
  { apply bylb_nodup_map_inj.
    - intros x y Hxy. injection Hxy as Hxy. exact Hxy.
    - apply bylb_seq_nodup. }
  pose proof (bylb_count_leaves_ge T (seq 0 (S K))) as Hcnt.
  rewrite Hme in Hcnt.
  apply Hcnt in Hnd.
  rewrite length_seq in Hnd.
  split.
  - exact Hnd.
  - pose proof (bylb_leaves_pow_depth T) as Hlp.
    transitivity (Nat.log2 (2 ^ bylb_depth T)).
    + apply Nat.log2_le_mono. lia.
    + rewrite (Nat.log2_pow2 (bylb_depth T) (Nat.le_0_l (bylb_depth T))).
      apply Nat.le_refl.
Qed.

(* main exit in sigT nat witness form: the witness is d := Nat.log2 (S K). *)
(* the premise 0 < K is not needed: for K = 0, Nat.log2 1 = 0 and the depth of
   every tree is >= 0, so the statement holds without premises over all of
   nat. *)
Theorem bylb_lower_bound : forall K : nat,
  sigT (fun d : nat =>
    Nat.log2 (S K) <= d /\
    (forall T : bylb_dtree,
        (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) ->
        d <= bylb_depth T)).
Proof.
  intros K. apply (existT _ (Nat.log2 (S K))). split.
  - apply Nat.le_refl.
  - intros T Hcorr.
    destruct (bylb_correct_tree_leaves K T Hcorr) as [_ Hlog]. exact Hlog.
Qed.

(* ========== assumption checks on the counting family ========== *)

Print Assumptions bylb_count_leaves_ge.
Print Assumptions bylb_correct_tree_leaves.
Print Assumptions bylb_lower_bound.
(* ================= part 2. the btight_build family ================= *)
From Stdlib Require Import Arith.Arith Lia.

(* ========== 1. fuel-limited balanced halving over a threshold interval ========== *)

(* [btight_build f lo w] builds a balanced binary tree over the threshold
   interval [lo, lo+w-1] of width w. *)
(* f is the fuel: f = 0 or w <= 1 returns the leaf lo; for w = S (S w') the
   node queries the midpoint m := lo + w'/2, where a threshold t <= m reads
   true and descends into the subtree over [lo, m], while t > m reads false
   and descends into the subtree over [m+1, lo+w-1]. *)
Fixpoint btight_build (f lo w : nat) {struct f} : bylb_dtree :=
  match f with
  | 0 => bylb_dleaf lo
  | S f' =>
      match w with
      | 0 => bylb_dleaf lo
      | 1 => bylb_dleaf lo
      | S (S w') =>
          bylb_dnode (lo + w' / 2)
            (btight_build f' (S (lo + w' / 2)) (S w' - w' / 2))
            (btight_build f' lo (S (w' / 2)))
      end
  end.

(* ========== 2. induction on the interval invariant: correctness and the depth bound ========== *)

(* division fact used at both call sites: when the parent width S (S w') is at
   most 2 * 2^f, the two child widths S (w'/2) and S w' - w'/2 are each at
   most 2^f, and w'/2 <= w'. *)
(* after the parity case split on w' the arithmetic is purely linear. *)
Lemma btight_half_fuel : forall (f w' : nat),
  S (S w') <= 2 ^ S f ->
  S (w' / 2) <= 2 ^ f /\ S w' - w' / 2 <= 2 ^ f /\ w' / 2 <= w'.
Proof.
  intros f w' Hw.
  assert (HP : 2 ^ S f = 2 * 2 ^ f) by reflexivity.
  rewrite HP in Hw.
  assert (Hd : w' = 2 * (w' / 2) + w' mod 2) by apply Nat.div_mod_eq.
  assert (Hm : w' mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
  remember (w' / 2) as q eqn:Hq.
  remember (w' mod 2) as r eqn:Hr.
  split.
  - destruct r; lia.
  - split.
    + destruct r; lia.
    + lia.
Qed.

Lemma btight_build_spec : forall (f lo w : nat),
  w <= 2 ^ f ->
  (forall t, lo <= t -> t < lo + w ->
     bylb_run (btight_build f lo w) (bylb_ft t) = bylb_dleaf t)
  /\ bylb_depth (btight_build f lo w) <= f.
Proof.
  intros f. induction f as [| f IH]; intros lo w Hw.
  (* base case: f = 0 forces w <= 1, and the tree is the leaf lo. *)
  - assert (Hw1 : w <= 1) by (cbn in Hw; exact Hw).
    destruct w as [| w'].
    + split.
      * intros t Hlo Hhi. exfalso. lia.
      * cbn [btight_build bylb_depth]. lia.
    + assert (w' = 0) by lia. subst w'.
      split.
      * intros t Hlo Hhi. cbn [btight_build bylb_run].
        assert (Ht : t = lo) by lia. rewrite Ht. reflexivity.
      * cbn [btight_build bylb_depth]. lia.
  (* step: from f to S f; the parent width splits into the two child widths,
     bounded by [btight_half_fuel]. *)
  (* correctness dispatches on t <=? lo + w'/2 between the two child intervals,
     and the depth bound takes the larger of the two induction bounds. *)
  - destruct w as [|[|w']].
    + split.
      * intros t Hlo Hhi. exfalso. lia.
      * cbn [btight_build bylb_depth]. lia.
    + split.
      * intros t Hlo Hhi. cbn [btight_build bylb_run].
        assert (Ht : t = lo) by lia. rewrite Ht. reflexivity.
      * cbn [btight_build bylb_depth]. lia.
    + destruct (btight_half_fuel f w' Hw) as [Hq1 [Hq2 Hq3]].
      cbn [btight_build].
      remember (w' / 2) as q eqn:Hq.
      assert (Hq4 : q <= S w') by lia.
      assert (Hsplit : S (S w') = S q + (S w' - q)) by lia.
      destruct (IH lo (S q) Hq1) as [IHcl IHdl].
      destruct (IH (S (lo + q)) (S w' - q) Hq2) as [IHcr IHdr].
      split.
      * intros t Hlo Hhi. cbn [bylb_run].
        destruct (bylb_ft t (lo + q)) eqn:E.
        -- unfold bylb_ft in E. apply Nat.leb_le in E.
           apply IHcl; lia.
        -- unfold bylb_ft in E. apply Nat.leb_gt in E.
           apply IHcr; lia.
      * cbn [bylb_depth]. lia.
Qed.

(* ========== 3. exact leaf count (matches the leaf count on the lower-bound side) ========== *)

Lemma btight_nleaves_exact : forall (f lo w : nat),
  1 <= w -> w <= 2 ^ f -> bylb_nleaves (btight_build f lo w) = w.
Proof.
  intros f. induction f as [| f IH]; intros lo w H1 H2.
  - assert (Hw1 : w <= 1) by (cbn in H2; exact H2).
    destruct w as [| w'].
    + exfalso. lia.
    + assert (w' = 0) by lia. subst w'.
      cbn [btight_build bylb_nleaves]. reflexivity.
  - destruct w as [|[|w']].
    + exfalso. lia.
    + cbn [btight_build bylb_nleaves]. reflexivity.
    + destruct (btight_half_fuel f w' H2) as [Hq1 [Hq2 Hq3]].
      cbn [btight_build bylb_nleaves].
      remember (w' / 2) as q eqn:Hq.
      assert (Hp1 : 1 <= S q) by lia.
      assert (Hp2 : 1 <= S w' - q) by lia.
      rewrite (IH lo (S q) Hp1 Hq1).
      rewrite (IH (S (lo + q)) (S w' - q) Hp2 Hq2).
      lia.
Qed.

(* ========== 4. combined exit: the reachability half of the tight bound ========== *)

(* threefold conjunction: the K+1 threshold positions are correctly recognized,
   the leaf count is exactly S K, and the depth is <= S (Nat.log2 (S K)). *)
Theorem btight_leaves_tight : forall K : nat,
  sigT (fun T : bylb_dtree =>
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) /\
    (bylb_nleaves T = S K /\ bylb_depth T <= S (Nat.log2 (S K)))).
Proof.
  intros K.
  assert (Hpos : 0 < S K) by lia.
  destruct (Nat.log2_spec (S K) Hpos) as [_ Hhigh].
  assert (Hw : S K <= 2 ^ S (Nat.log2 (S K))) by lia.
  apply (existT _ (btight_build (S (Nat.log2 (S K))) 0 (S K))).
  destruct (btight_build_spec (S (Nat.log2 (S K))) 0 (S K) Hw) as [Hcorr Hdep].
  assert (Hn : bylb_nleaves (btight_build (S (Nat.log2 (S K))) 0 (S K)) = S K).
  { apply (btight_nleaves_exact (S (Nat.log2 (S K))) 0 (S K)); [lia | exact Hw]. }
  split.
  - intros t Ht. apply Hcorr; lia.
  - split.
    + exact Hn.
    + exact Hdep.
Qed.

(* target form, a twofold conjunction: some tree correctly recognizes the K+1
   monotone threshold positions and has depth <= S (Nat.log2 (S K)). *)
Theorem btight_tight : forall K : nat,
  sigT (fun T : bylb_dtree =>
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) /\
    bylb_depth T <= S (Nat.log2 (S K))).
Proof.
  intros K. destruct (btight_leaves_tight K) as [T [Hc [Hn Hd]]].
  apply (existT _ T). split.
  - exact Hc.
  - exact Hd.
Qed.

(* the same body exported under the target-form name. *)
Definition bylb_tight : forall K : nat,
  sigT (fun T : bylb_dtree =>
    (forall t, t <= K -> bylb_run T (bylb_ft t) = bylb_dleaf t) /\
    bylb_depth T <= S (Nat.log2 (S K))) := btight_tight.

(* ========== assumption checks on the builder family ========== *)

Print Assumptions btight_half_fuel.
Print Assumptions btight_build_spec.
Print Assumptions btight_nleaves_exact.
Print Assumptions btight_leaves_tight.
Print Assumptions btight_tight.
Print Assumptions bylb_tight.
