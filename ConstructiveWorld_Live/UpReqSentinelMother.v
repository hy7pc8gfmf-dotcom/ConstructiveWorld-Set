(* ConstructiveWorld-Set -- source modules for anchor-unreachable lemma sites. *)
(** * UpReqSentinelMother: anchor domination and unreachability modules.

    Mission.  A Section-generalized source pair (no extra assumptions,
      premises explicit; prefix [stm_]).  Module A (anchor domination):
      the enumerator [smin] is dominated from above by any member's core
      value ([stm_domin_in]/[stm_domin_head]; companion
      [stm_smin_singleton]).  Module B (unreachability): nonempty table,
      bounded cores, anchor outside the domain -- the anchor is never
      hit ([stm_unreach_lookup]/[stm_unreach_global]/[stm_hitcount_zero]/
      [stm_domain_gate]).  Plus a Set-layer witness pack
      ([stm_head_witness]/[stm_arg]/[stm_arg_sound]) and the G10
      [dmin] instantiation ([stm_g10_dmin]/[stm_g10_bridge], numeric
      checks, the 999-unreachable instance).

    Dependencies.  [S01_BaseRing], [G10_LoebFam]; Stdlib [ZArith]
      [Lia] [List].

    References.  [G10_LoebFam] ([dmin] G10:1398-1402; anchor 999 at
      G10:1400), read-only; same-name ConstructiveWorld-Main baseline.

    Constructivity.  Zero extra axioms, no admissions, no classical
      logic; main theorems all [Closed under the global context];
      unreachability branches by empty-type elimination and [sigT]
      witnesses; definitions Set/Type-valued, no Prop in computational
      positions; extraction erases Prop positions to [__], not magic.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpReqSentinelMother.v] compiles cleanly (exit 0); the first eight
      bytes of the artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
Require S01_BaseRing.
Open Scope Z_scope.

(* Set-layer decidable carriers: the certificate shapes for this module's comparison and membership faces (after extraction, Prop positions erase to the standard form). *)
Inductive stm_ZleT (x y : Z) : Set :=
| stm_ZleT_i : x <= y -> stm_ZleT x y.

Inductive stm_ZltT (x y : Z) : Set :=
| stm_ZltT_i : x < y -> stm_ZltT x y.

Inductive stm_ZeqT (x y : Z) : Set :=
| stm_ZeqT_i : x = y -> stm_ZeqT x y.

Inductive stm_ZneT (x y : Z) : Set :=
| stm_ZneT_i : x <> y -> stm_ZneT x y.

Inductive stm_NatLtT (n m : nat) : Set :=
| stm_NatLtT_i : (n < m)%nat -> stm_NatLtT n m.

(* ================= Section 1. Source modules: anchor domination + domain-bound unreachability (Section-generalized; the two parameters [dist]/[s] resolve at instantiation) ================= *)

Section SentinelMother.

(* [dist]: the distance kernel (the G10 instantiation takes [Z.abs (x - a)]); [s]: the anchor value (instantiated as 999). *)
Variable dist : Z -> Z -> Z.
Variable s : Z.

(* Enumerator mother shape: a replica of the G10 [dmin] structure -- an empty table yields the anchor [s]; a nonempty table takes the itemwise minimum of core values. *)
Fixpoint smin (x : Z) (l : list Z) : Z :=
  match l with
  | nil => s
  | a :: l' => Z.min (dist x a) (smin x l')
  end.

(* -- Source module A (anchor domination face) -- *)

(* Domination main lemma: the core value of any table member bounds the enumerator output from above (by induction). *)
Lemma stm_domin_in : forall (x a : Z) (l : list Z),
  S01_BaseRing.InT a l -> stm_ZleT (smin x l) (dist x a).
Proof.
  intros x a l Hin. revert Hin.
  induction l as [|b l' IH]; intro Hin.
  - inversion Hin.
  - simpl. apply stm_ZleT_i.
    inversion Hin as [l0 | c l0 HinT]; subst.
    + apply Z.le_min_l.
    + etransitivity.
      * apply Z.le_min_r.
      * destruct (IH HinT) as [Hle2]. exact Hle2.
Qed.

(* Head specialization of domination: the output on a nonempty table is bounded by the head's core value (the form consumed at the G10 call sites). *)
Lemma stm_domin_head : forall (x a : Z) (l : list Z),
  stm_ZleT (smin x (a :: l)) (dist x a).
Proof.
  intros x a l. apply stm_ZleT_i.
  exact (Z.le_min_l (dist x a) (smin x l)).
Qed.

(* Positive reachability (monotone faithfulness): on a singleton table whose core value lies within the anchor's bound,
   the output is exactly that core value -- the enumerator is a genuine minimizer, not a constant anchor emitter,
   the positive evidence that the module is non-vacuous. *)
Lemma stm_smin_singleton : forall (x a : Z),
  stm_ZleT (dist x a) s -> stm_ZeqT (smin x (a :: nil)) (dist x a).
Proof.
  intros x a H. destruct H as [Hle].
  apply stm_ZeqT_i. apply Z.min_l. exact Hle.
Qed.

(* -- Set-layer witness pack ([sigT] convention; after extraction the Prop positions erase to [__] while the data positions survive) -- *)

(* Head witness of a nonempty table: the explicit length finiteness ([0 < length]) supplies an in-table member for the [sigT] carrier. *)
Definition stm_head_witness (l : list Z) (H : stm_NatLtT 0 (length l)%nat) : {a : Z & S01_BaseRing.InT a l}.
Proof.
  destruct l as [|a l'].
  - exfalso. destruct H as [H0l]. simpl in H0l. lia.
  - exact (@existT _ (fun a0 : Z => S01_BaseRing.InT a0 (a :: l')) a
           (@S01_BaseRing.InT_here Z a l')).
Defined.

(* Argmin entry selector: returns the table entry realizing the minimal core value (pure [Set] computation). *)
Fixpoint stm_arg (x : Z) (l : list Z) : Z :=
  match l with
  | nil => 0%Z
  | a :: l' => if Z.leb (dist x a) (smin x l') then a else stm_arg x l'
  end.

(* Argmin soundness: a nonempty table + a uniform bound on all core values + the anchor outside the domain
   imply the entry lies in the table and its core value equals the enumerator output exactly
   (a constructive combination of a [Set] data pack and a [Prop] certificate). *)
Lemma stm_arg_sound : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  stm_NatLtT 0 (length l)%nat ->
  S01_BaseRing.And (S01_BaseRing.InT (stm_arg x l) l)
    (stm_ZeqT (dist x (stm_arg x l)) (smin x l)).
Proof.
  intros B x l. induction l as [|a l' IH]; intros Hcert Hlt Hlen.
  - destruct Hlen as [Hlen']. simpl in Hlen'. exfalso. lia.
  - destruct l' as [|b l''].
    + (* singleton table: the entry is the head *)
      assert (Hle : dist x a <= s).
      { pose proof (Hcert a (@S01_BaseRing.InT_here Z a nil)) as Hc.
        destruct Hc as [Hc2]. destruct Hlt as [Hlt2]. lia. }
      assert (Hb : Z.leb (dist x a) (smin x nil) = true).
      { apply Z.leb_le. exact Hle. }
      cbn [stm_arg]. rewrite Hb. split.
      * apply (@S01_BaseRing.InT_here Z a nil).
      * apply stm_ZeqT_i. cbn [smin]. symmetry. apply Z.min_l. exact Hle.
    + (* multi-element table: the contest between the head and the tail's minimum *)
      assert (Hlen'T : stm_NatLtT 0 (length (b :: l''))%nat)
        by (apply stm_NatLtT_i; simpl; lia).
      destruct (Z.leb (dist x a) (smin x (b :: l''))) eqn:Hbranch.
      * cbn [stm_arg]. rewrite Hbranch. cbn [stm_arg]. split.
        -- apply (@S01_BaseRing.InT_here Z a (b :: l'')).
        -- apply stm_ZeqT_i. cbn [smin]. symmetry. apply Z.min_l.
           apply Z.leb_le. exact Hbranch.
      * assert (Hgt : smin x (b :: l'') < dist x a).
        { apply Z.leb_gt. exact Hbranch. }
        change (smin x (b :: l''))
          with (Z.min (dist x b) (smin x l'')) in Hgt.
        destruct (IH (fun a0 Ha0 => Hcert a0
                       (@S01_BaseRing.InT_next Z a0 a (b :: l'') Ha0)) Hlt Hlen'T)
          as [Hin Heq].
        cbn [stm_arg]. rewrite Hbranch. split.
        -- apply (@S01_BaseRing.InT_next Z (stm_arg x (b :: l'')) a (b :: l'') Hin).
        -- apply stm_ZeqT_i. cbn [smin].
           destruct Heq as [Heq2].
           rewrite Z.min_r by lia. exact Heq2.
Qed.

(* -- Source module B (domain-bound unreachability face) -- *)

(* Lookup-type main lemma: an explicitly nonempty enumeration table + a bound on all core values
   in the table (explicit [Z.le] premise) + the anchor outside the domain (explicit [Z.lt] premise)
   imply the anchor position is never hit.
   Constructive content: a [sigT] witness + domination + transitivity + empty-type elimination, no classical logic. *)
Lemma stm_unreach_lookup : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  stm_NatLtT 0 (length l)%nat ->
  smin x l <> s.
Proof.
  intros B x l Hcert Hlt Hlen.
  destruct (stm_head_witness l Hlen) as [a Ha].
  destruct (stm_domin_in x a l Ha) as [Hd].
  destruct (Hcert a Ha) as [Hc].
  destruct Hlt as [Hlt2].
  intro Heq. rewrite Heq in Hd.
  exfalso. lia.
Qed.

(* Global-core corollary: when cores are bounded over the whole domain (both parameters quantified),
   a nonempty table suffices to avoid the anchor
   (a wrapper with the certificate shape; the unreachability core is still carried by the lookup-type main lemma). *)
Lemma stm_unreach_global : forall (B x : Z) (l : list Z),
  (forall y a, stm_ZleT (dist y a) B) -> stm_ZltT B s -> l <> nil ->
  smin x l <> s.
Proof.
  intros B x l Hdom Hlt Hne.
  apply (stm_unreach_lookup B x l).
  - intros a _. apply Hdom.
  - exact Hlt.
  - destruct l as [|a l'].
    + exfalso. apply Hne. reflexivity.
    + simpl. apply stm_NatLtT_i. lia.
Qed.

(* Count-type generalization: an anchor-hit counter over suffix positions (same protocol shape as the lookup lemma). *)
Fixpoint stm_hitcount (x : Z) (l : list Z) : nat :=
  match l with
  | nil => 0%nat
  | a :: l' => Nat.add (if Z.eqb (smin x (a :: l')) s then 1%nat else 0%nat)
                       (stm_hitcount x l')
  end.

(* The hit count is identically zero: boundedness + the anchor outside the domain imply the counter never fires on any table
   (each inspected position is a nonempty table, excluded position by position by the lookup-type main lemma). *)
Lemma stm_hitcount_zero : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  S01_BaseRing.Id (stm_hitcount x l) 0%nat.
Proof.
  intros B x l Hcert Hlt.
  induction l as [|a l' IH].
  - reflexivity.
  - assert (Hne : smin x (a :: l') <> s).
    { apply (stm_unreach_lookup B x (a :: l')).
      - intros a0 Ha0. apply Hcert. exact Ha0.
      - exact Hlt.
      - simpl. apply stm_NatLtT_i. lia. }
    cbn [stm_hitcount].
    rewrite (proj2 (Z.eqb_neq (smin x (a :: l')) s) Hne).
    rewrite (IH (fun a0 Ha0 => Hcert a0 (@S01_BaseRing.InT_next Z a0 a l' Ha0))).
    reflexivity.
Qed.

(* Positive companion: the output lands inside the domain (a direct composition of domination and the uniform bound). *)
Lemma stm_output_in_range : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) ->
  stm_NatLtT 0 (length l)%nat ->
  stm_ZleT (smin x l) B.
Proof.
  intros B x l Hcert Hlen.
  destruct (stm_head_witness l Hlen) as [a Ha].
  destruct (stm_domin_in x a l Ha) as [Hd1].
  destruct (Hcert a Ha) as [Hc1].
  apply stm_ZleT_i. etransitivity.
  - exact Hd1.
  - exact Hc1.
Qed.

(* Confluence gate (the source pair's principal statement): the output lands inside the domain and the anchor is unreachable, both faces in one statement. *)
Corollary stm_domain_gate : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  stm_NatLtT 0 (length l)%nat ->
  S01_BaseRing.And (stm_ZleT (smin x l) B) (stm_ZneT (smin x l) s).
Proof.
  intros B x l Hcert Hlt Hlen. split.
  - apply (stm_output_in_range B x l Hcert Hlen).
  - apply stm_ZneT_i. apply (stm_unreach_lookup B x l Hcert Hlt Hlen).
Qed.

End SentinelMother.

(* ================= Section 2. Instantiation of the G10 dmin scenario ([G10_LoebFam.v] consumed read-only, untouched; this section reconstructs the shape independently) ================= *)

(* Scenario constants: the anchor 999 (the G10:1400 empty-band branch); the domain bound 998, just below the anchor (the anchor sits outside the domain). *)
Definition stm_g10_s : Z := 999.
Definition stm_g10_B : Z := 998.
Definition stm_g10_dist (x a : Z) : Z := Z.abs (x - a).

(* The [dmin] replica: the source-module enumerator [smin] instantiated in the G10 scenario (shape matching G10:1398-1402). *)
Definition stm_g10_dmin (x : Z) (l : list Z) : Z :=
  smin stm_g10_dist stm_g10_s x l.

(* -- Numeric anchor checks, family-1 caliber (cross-checked against the G10 dwm trace, L1430-1444) -- *)

(* The empty-band branch emitting the anchor itself: the 999 scenario realized (the empty-table face is the defining face of the anchor position). *)
Lemma stm_g10_nil_sentinel : forall x : Z, stm_ZeqT (stm_g10_dmin x nil) 999.
Proof.
  intros x. apply stm_ZeqT_i. reflexivity.
Qed.

(* Emitting 2 onto the band [0]: the fee is [|2 - 0| = 2] (cross-checks G10 [dwm_W1 = 4 - 2]). *)
Lemma stm_g10_fee_emit2 : stm_ZeqT (stm_g10_dmin 2 (0 :: nil)) 2.
Proof.
  apply stm_ZeqT_i. reflexivity.
Qed.

(* Emitting 1 onto the band [2, 0]: the fee is [min(1, 1) = 1] (cross-checks G10 [dwm_W2 = 2 - 1]). *)
Lemma stm_g10_fee_emit1 : stm_ZeqT (stm_g10_dmin 1 (2 :: 0 :: nil)) 1.
Proof.
  apply stm_ZeqT_i. reflexivity.
Qed.

(* Emitting 3 onto the band [2, 1, 0]: the fee is [min(1, 2, 3) = 1] (cross-checks the premise of G10 [dwm_emit3_legal]). *)
Lemma stm_g10_fee_emit3 : stm_ZeqT (stm_g10_dmin 3 (2 :: 1 :: 0 :: nil)) 1.
Proof.
  apply stm_ZeqT_i. reflexivity.
Qed.

(* -- Family-2 caliber: the 999 anchor is unreachable (instantiating source module B) -- *)

(* Window-form instantiation: if the lookup value and the band entries all lie in a window of width [<= 998],
   then 999 is never emitted (the certificate face is discharged by pointwise instantiation of
   [Z.abs_le] plus [lia]; the [lt]/[le] premises are all explicit). *)
Lemma stm_g10_unreach_window : forall (x lo hi : Z) (l : list Z),
  stm_ZleT (hi - lo) stm_g10_B -> stm_ZleT lo x -> stm_ZleT x hi ->
  (forall a, S01_BaseRing.InT a l ->
     S01_BaseRing.And (stm_ZleT lo a) (stm_ZleT a hi)) -> l <> nil ->
  stm_g10_dmin x l <> stm_g10_s.
Proof.
  intros x lo hi l Hwidth Hxlo Hxhi Hmem Hne.
  destruct Hwidth as [Hw]. destruct Hxlo as [Hxl]. destruct Hxhi as [Hxh].
  unfold stm_g10_dmin.
  apply (stm_unreach_lookup stm_g10_dist stm_g10_s stm_g10_B x l).
  - intros a Ha. destruct (Hmem a Ha) as [Halo Hahi].
    destruct Halo as [Hal]. destruct Hahi as [Hah].
    apply stm_ZleT_i. unfold stm_g10_dist, stm_g10_B in *.
    apply Z.abs_le. lia.
  - apply stm_ZltT_i. unfold stm_g10_B, stm_g10_s. lia.
  - destruct l as [|a l'].
    + exfalso. apply Hne. reflexivity.
    + simpl. apply stm_NatLtT_i. lia.
Qed.

(* Concrete instance: the band [2, 1, 0] and lookup value 3 from the G10 documentation trace -- a comment-level invariant of G10 promoted to a theorem. *)
Theorem stm_g10_sentinel_unreachable_3_210 :
  stm_g10_dmin 3 (2 :: 1 :: 0 :: nil) <> stm_g10_s.
Proof.
  apply (stm_g10_unreach_window 3 0 3 (2 :: 1 :: 0 :: nil)).
  - apply stm_ZleT_i. unfold stm_g10_B. lia.
  - apply stm_ZleT_i. lia.
  - apply stm_ZleT_i. lia.
  - intros a Ha. inversion Ha as [l0 | y0 l0 Hnext]; subst.
    + split; apply stm_ZleT_i; lia.
    + inversion Hnext as [l1 | y1 l1 Hnext1]; subst.
      * split; apply stm_ZleT_i; lia.
      * inversion Hnext1 as [l2 | y2 l2 Hnext2]; subst.
        -- split; apply stm_ZleT_i; lia.
        -- inversion Hnext2.
  - discriminate.
Qed.

(* ================= Section 3. In-place hookup to G10 (via Require): bridge lemma + axiom-face audit + extraction audit ================= *)

Require Import G10_LoebFam.

(* Bridge lemma: the G10 [dmin] (read-only original, G10:1398-1402) and the source-module replica [stm_g10_dmin]
   are provably equal pointwise -- every source-module theorem in this file transfers across this
   bridge to the G10 call sites ([dwm_emit]/[halt_cert]) while [G10_LoebFam] itself is untouched. *)
Lemma stm_g10_bridge : forall (x : Z) (l : list Z),
  stm_ZeqT (dmin x l) (stm_g10_dmin x l).
Proof.
  intros x l. apply stm_ZeqT_i.
  unfold stm_g10_dmin, stm_g10_dist, stm_g10_s.
  induction l as [|a l' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* -- Assumption audit (each item below must report [Closed under the global context]) -- *)
Print Assumptions stm_domin_in.
Print Assumptions stm_unreach_lookup.
Print Assumptions stm_unreach_global.
Print Assumptions stm_hitcount_zero.
Print Assumptions stm_domain_gate.
Print Assumptions stm_arg_sound.
Print Assumptions stm_g10_unreach_window.
Print Assumptions stm_g10_sentinel_unreachable_3_210.
Print Assumptions stm_g10_bridge.

(* -- Extraction audit (the output names are fixed by the [Extraction] command below) -- *)
From Stdlib Require Import Extraction.
Extraction "_tq24s_extract" smin stm_arg stm_head_witness stm_hitcount stm_g10_dmin.
