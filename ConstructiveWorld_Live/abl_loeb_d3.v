(* ========================================================================= *)
(* abl_loeb_d3.v -- Loeb theorem D3, first segment: Set-level (Prop-free statement *)
(*   surface) constructive formalization of the HBL derived conditions (lbd_ items). *)
(* Mission. Land the G10_LoebFam :870 D3 waypoint, first segment: lift provability   *)
(*   into a first-class bool predicate lbd_Box (the Formula2 fsig Sigma-atom value   *)
(*   under the trivial valuation) and prove the three HBL derived conditions clause  *)
(*   by clause: decoder fuel insensitivity, pairing code order, the HBL1/HBL3/HBL2   *)
(*   bounded-witness conditions, and the D3' encoded self-reference exhibit (names   *)
(*   as declared below).                                                             *)
(* Dependencies. Stdlib Arith, Lia, Wf_nat, Wellfounded; pool G10_LoebFam (same-name  *)
(*   source copy archived in the pool, canonical source md5 51bb7b3e477f7c9ba776311a  *)
(*   a94f5dcf) and S01_BaseRing (Id / id_cong / NatLe / NatLe_drop / NatLe_lift;      *)
(*   lbd_lt_wf_set replaces the Prop-only lt_wf_ind).                                 *)
(* Constructivity. Set-carrier discipline, zero Prop on the statement surface:        *)
(*   existence via sigT, conjunction via prod, equations via Id for decoder data and  *)
(*   loeb_tid bool for box/verPf, order via NatLe with NatLe_drop as the sanctioned   *)
(*   extraction bridge; (…) <= (…)%nat premises are fuel-parameterized proof-layer    *)
(*   interfaces. Zero axioms, zero admissions, zero placeholders, zero classical      *)
(*   logic.                                                                           *)
(* Honesty boundary. Full-shape Loeb does NOT close in this slice: (i) no []          *)
(*   constructor in the object language (a [] sentence must be an fsig atom of        *)
(*   Formula2, coding round trip at G10_LoebFam :3633); (ii) unguarded [] needs       *)
(*   unbounded bsearch (rLPO lineage, classical); the guarded shape closed here       *)
(*   migrates the bound in closed form and fabricates nothing. Washed by              *)
(*   seat_abl6w2: bare = on data to Id, = true on bools to loeb_tid bool, all         *)
(*   comments English.                                                                *)
(* Build. rocq c -native-compiler no -Q <pool> "" abl_loeb_d3.v (Rocq 9.1.0,           *)
(*   toolchain Live/toolchain/opam/live; 9.0.1 live901 incompatible, vo 90100!=90001). *)
(* ========================================================================= *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Wellfounded.

Require Import G10_LoebFam.
Require Import S01_BaseRing.

(* ── Born-clean local bridges (definitional, zero axioms) ── *)

(* Id inversion: the only constructor is id_refl, so Id x y carries x = y.
   Proof-internal extraction bridge (the Prop equation is used inside
   proofs only), mirroring G10_LoebFam's tidQ discipline. *)
Definition id_eq_inv {A : Set} {x y : A} (H : Id x y) : x = y :=
  match H with id_refl => eq_refl end.

Ltac tidI H E := pose proof (id_eq_inv H) as E.

(* eq -> Id lift (the construction half of the inversion bridge) *)
Lemma lbd_id_of_eq {A : Set} (x y : A) (p : x = y) : Id x y.
Proof. rewrite p. apply id_refl. Qed.

(* Strong induction into Set: lt_wf_ind is Prop-only and every washed
   conclusion below is Set-carried, so the Type-valued combinator supplies
   the bridge (same induction shape as the source's lt_wf_ind uses). *)
Lemma lbd_lt_wf_set : forall P : nat -> Set,
  (forall n, (forall m, (m < n)%nat -> P m) -> P n) -> forall n, P n.
Proof.
  intros P H n. apply (well_founded_induction_type lt_wf). exact H.
Qed.

(* ===================================================================== *)
(* Segment A: decoder fuel insensitivity -- what is decoded is the code,   *)
(*   the fuel is only a recursion guardrail.                               *)
(*   D1's gnT_fuel/gnF_fuel and D2's gnPrf_replay give the one-way         *)
(*   "sufficient fuel on the code side" (gnX <= k -> dX2 k (gnX) = Some …);*)
(*   this segment adds the two-way invariance for arbitrary codes -- the   *)
(*   load-bearing piece that promotes verPf bool certificates into         *)
(*   uniform-fuel replay ledgers.                                          *)
(* ===================================================================== *)

(* Component bounds of the unp2 self-fuel split: first component <= code,
   second component strictly < code. Hypothesis equation carried by Id;
   conclusion conjunction carried by prod of NatLe (strictness by the
   successor shift NatLe (S b) x). *)
Lemma lbd_unp2_self_bounds : forall x a b : nat,
  Id (unp2 x x) (Some (a, b)) ->
  (NatLe a x * (NatLe b x * NatLe (Datatypes.S b) x))%type.
Proof.
  intros x. induction x as [x IH] using lbd_lt_wf_set. intros a b H.
  tidI H E0.
  destruct x as [|x'].
  - discriminate E0.
  - rewrite (unp2_S x' (Datatypes.S x')) in E0. cbv iota in E0.
    destruct (Nat.even (Datatypes.S x')) eqn:Ev.
    + destruct (unp2 x' (Nat.div2 (Datatypes.S x'))) as [[a0 b0]|] eqn:Eq.
      * injection E0 as Ea Eb.
        pose proof (Nat.le_div2 x') as Hd.
        pose proof (unp2_fuel (Nat.div2 (Datatypes.S x')) x' Hd) as Hfuel.
        rewrite Hfuel in Eq.
        assert (Hlt : (Nat.div2 (Datatypes.S x') < Datatypes.S x')%nat) by lia.
        assert (HIdq : Id (unp2 (Nat.div2 (Datatypes.S x'))
                                (Nat.div2 (Datatypes.S x')))
                           (Some (a0, b0)))
          by (rewrite Eq; apply id_refl).
        destruct (IH (Nat.div2 (Datatypes.S x')) Hlt a0 b0 HIdq)
          as [Ha1 [Hb1 Hb2]].
        apply NatLe_drop in Ha1. apply NatLe_drop in Hb1. apply NatLe_drop in Hb2.
        split; [apply NatLe_lift; lia | split; apply NatLe_lift; lia].
      * discriminate E0.
    + injection E0 as Ea Eb.
      pose proof (div2_le x') as Hd.
      split; [apply NatLe_lift; lia | split; apply NatLe_lift; lia].
Qed.

(* dT2 fuel insensitivity (conclusion carried by Id) *)
Lemma lbd_dT2_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> Id (dT2 k1 c) (dT2 k2 c).
Proof.
  intros c. induction c as [c IH] using lbd_lt_wf_set. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [dT2].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota. destruct l as [|[|[|[|l3]]]]; cbv iota; try reflexivity.
      * (* label 2: tsucc -- sub-code q is the second component, strictly below the code *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S O)) q
                     (lbd_id_of_eq (unp2 (Datatypes.S c') (Datatypes.S c'))
                                   (Some (Datatypes.S (Datatypes.S O), q)) Epc)) as Hb.
        destruct Hb as [_ [Hq Hlt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hlt.
        assert (Ha1 : (q <= k1')%nat) by lia.
        assert (Ha2 : (q <= k2')%nat) by lia.
        tidI (IH q Hlt k1' k2' Ha1 Ha2) Eql.
        rewrite Eql. apply id_refl.
      * (* label 3: tsub -- both sub-codes a b below q < code *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S O))) q
                     (lbd_id_of_eq (unp2 (Datatypes.S c') (Datatypes.S c'))
                                   (Some (Datatypes.S (Datatypes.S (Datatypes.S O)), q)) Epc)) as Hb1.
        destruct Hb1 as [_ [Hq Hqslt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqslt.
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b (lbd_id_of_eq (unp2 q q) (Some (a, b)) Epq)) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        apply NatLe_drop in Hqa. apply NatLe_drop in Hqb.
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hb1 : (b <= k1')%nat) by lia.
        assert (Hb2 : (b <= k2')%nat) by lia.
        assert (Hla : (a < Datatypes.S c')%nat) by lia.
        assert (Hlb : (b < Datatypes.S c')%nat) by lia.
        tidI (IH a Hla k1' k2' Ha1 Ha2) Ewa. rewrite Ewa.
        tidI (IH b Hlb k1' k2' Hb1 Hb2) Ewb. rewrite Ewb.
        apply id_refl.
    + reflexivity.
Qed.

(* dF2 fuel insensitivity (uses the dT2 invariance; strong induction along
   the code on itself; conclusion carried by Id) *)
Lemma lbd_dF2_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> Id (dF2 k1 c) (dF2 k2 c).
Proof.
  intros c. induction c as [c IH] using lbd_lt_wf_set. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [dF2].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota. destruct l as [|[|[|[|[|[|l3]]]]]]; cbv iota; try reflexivity.
      * (* label 4: teq -- the two dT2 routes *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))) q
                     (lbd_id_of_eq (unp2 (Datatypes.S c') (Datatypes.S c'))
                                   (Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))), q)) Epc))
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqslt.
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b (lbd_id_of_eq (unp2 q q) (Some (a, b)) Epq)) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        apply NatLe_drop in Hqa. apply NatLe_drop in Hqb.
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hta : Id (dT2 k1' a) (dT2 k2' a))
          by (apply lbd_dT2_fuel_inv; lia).
        assert (Htb : Id (dT2 k1' b) (dT2 k2' b))
          by (apply lbd_dT2_fuel_inv; lia).
        tidI Hta Eta. tidI Htb Etb.
        rewrite Eta, Etb. apply id_refl.
      * (* label 5: fimp -- the two dF2 routes (own IH) *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))) q
                     (lbd_id_of_eq (unp2 (Datatypes.S c') (Datatypes.S c'))
                                   (Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))), q)) Epc))
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqslt.
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b (lbd_id_of_eq (unp2 q q) (Some (a, b)) Epq)) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        apply NatLe_drop in Hqa. apply NatLe_drop in Hqb.
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hb1 : (b <= k1')%nat) by lia.
        assert (Hb2 : (b <= k2')%nat) by lia.
        assert (Hla : (a < Datatypes.S c')%nat) by lia.
        assert (Hlb : (b < Datatypes.S c')%nat) by lia.
        tidI (IH a Hla k1' k2' Ha1 Ha2) Ewa. rewrite Ewa.
        tidI (IH b Hlb k1' k2' Hb1 Hb2) Ewb. rewrite Ewb.
        apply id_refl.
    + reflexivity.
Qed.

(* dP2 fuel insensitivity (uses the dT2/dF2 invariances; strong induction
   along the code on itself; conclusion carried by Id) *)
Lemma lbd_dP2_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> Id (dP2 k1 c) (dP2 k2 c).
Proof.
  intros c. induction c as [c IH] using lbd_lt_wf_set. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [dP2].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota.
      destruct l as [|[|[|[|[|[|[|[|[|l3]]]]]]]]]; cbv iota; try reflexivity.
      * (* label 6: ax_eqT -- the two dT2 routes *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))) q
                     (lbd_id_of_eq (unp2 (Datatypes.S c') (Datatypes.S c'))
                                   (Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))), q)) Epc))
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqslt.
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b (lbd_id_of_eq (unp2 q q) (Some (a, b)) Epq)) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        apply NatLe_drop in Hqa. apply NatLe_drop in Hqb.
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hta : Id (dT2 k1' a) (dT2 k2' a))
          by (apply lbd_dT2_fuel_inv; lia).
        assert (Htb : Id (dT2 k1' b) (dT2 k2' b))
          by (apply lbd_dT2_fuel_inv; lia).
        tidI Hta Eta. tidI Htb Etb.
        rewrite Eta, Etb. apply id_refl.
      * (* label 7: mpF -- both sub-witness codes along the dP2 own invariance *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))) q
                     (lbd_id_of_eq (unp2 (Datatypes.S c') (Datatypes.S c'))
                                   (Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))), q)) Epc))
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqslt.
        destruct (unp2 q q) as [[w1 w2]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q w1 w2 (lbd_id_of_eq (unp2 q q) (Some (w1, w2)) Epq)) as Hb2.
        destruct Hb2 as [Hw1 [Hw2 Hw2lt]].
        apply NatLe_drop in Hw1. apply NatLe_drop in Hw2. apply NatLe_drop in Hw2lt.
        assert (Hu1 : (w1 <= k1')%nat) by lia.
        assert (Hu2 : (w1 <= k2')%nat) by lia.
        assert (Hv1 : (w2 <= k1')%nat) by lia.
        assert (Hv2 : (w2 <= k2')%nat) by lia.
        assert (Hl1 : (w1 < Datatypes.S c')%nat) by lia.
        assert (Hl2 : (w2 < Datatypes.S c')%nat) by lia.
        tidI (IH w1 Hl1 k1' k2' Hu1 Hu2) Ew1. rewrite Ew1.
        tidI (IH w2 Hl2 k1' k2' Hv1 Hv2) Ew2. rewrite Ew2.
        apply id_refl.
      * (* label 8: repl -- one dF2 route and two dT2 routes *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))))) q
                     (lbd_id_of_eq (unp2 (Datatypes.S c') (Datatypes.S c'))
                                   (Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))), q)) Epc))
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqslt.
        destruct (unp2 q q) as [[p0 r]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q p0 r (lbd_id_of_eq (unp2 q q) (Some (p0, r)) Epq)) as Hb2.
        destruct Hb2 as [Hp [Hr Hrlt]].
        apply NatLe_drop in Hp. apply NatLe_drop in Hr. apply NatLe_drop in Hrlt.
        destruct (unp2 p0 p0) as [[a b]|] eqn:Epp; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds p0 a b
                      (lbd_id_of_eq (unp2 p0 p0) (Some (a, b)) Epp)) as Hb3.
        destruct Hb3 as [Hpa [Hpb _]].
        apply NatLe_drop in Hpa. apply NatLe_drop in Hpb.
        assert (Hfa1 : (a <= k1')%nat) by lia.
        assert (Hfa2 : (a <= k2')%nat) by lia.
        assert (Hfa : Id (dF2 k1' a) (dF2 k2' a))
          by (apply lbd_dF2_fuel_inv; lia).
        assert (Htb : Id (dT2 k1' b) (dT2 k2' b))
          by (apply lbd_dT2_fuel_inv; lia).
        assert (Htr : Id (dT2 k1' r) (dT2 k2' r))
          by (apply lbd_dT2_fuel_inv; lia).
        tidI Hfa Efa. tidI Htb Etb. tidI Htr Etr.
        rewrite Efa, Etb, Etr. apply id_refl.
    + reflexivity.
Qed.

(* Self-fuel normalization corollary: with sufficient fuel the run agrees
   with the self-fuel run (the dP2 version of D1's unp2_fuel). Interface
   note for the downstream prf2 slice: the conclusion is now carried by Id;
   consumers extract the defining equation with tidI before rewriting. *)
Corollary lbd_dP2_norm : forall c k : nat, (c <= k)%nat -> Id (dP2 k c) (dP2 c c).
Proof.
  intros c k H. apply (lbd_dP2_fuel_inv c k c); [exact H | apply Nat.le_refl].
Qed.

(* ===================================================================== *)
(* Segment B: three code-order items -- monotonicity of the pairing        *)
(*   function (the arithmetic backbone of bound migration), carried by     *)
(*   NatLe with strictness via the successor shift.                        *)
(* ===================================================================== *)

Lemma lbd_pairp_gt_snd : forall a b : nat, NatLe (Datatypes.S b) (pairp a b).
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - apply NatLe_lift. lia.
  - apply NatLe_lift. specialize (IHa b). apply NatLe_drop in IHa. lia.
Qed.

Lemma lbd_pairp_mono : forall a a' b b' : nat,
  NatLe a a' -> NatLe b b' -> NatLe (pairp a b) (pairp a' b').
Proof.
  intros a. induction a as [|a IHa]; intros a' b b' Ha Hb.
  - destruct a' as [|a''].
    + apply NatLe_lift. cbn [pairp]. apply NatLe_drop in Hb. lia.
    + apply NatLe_lift. cbn [pairp].
      pose proof (lbd_pairp_gt_snd a'' b') as Hgt.
      apply NatLe_drop in Hgt. apply NatLe_drop in Hb. lia.
  - destruct a' as [|a''].
    + apply NatLe_lift. apply NatLe_drop in Ha. lia.
    + apply NatLe_lift. cbn [pairp].
      apply NatLe_drop in Ha.
      assert (Ha2 : NatLe a a'') by (apply NatLe_lift; lia).
      specialize (IHa a'' b b' Ha2 Hb).
      pose proof (pairp_pos a'' b').
      apply NatLe_drop in IHa. apply NatLe_drop in Hb. lia.
Qed.

Lemma lbd_pairp_mono_snd_lt : forall b b' a : nat,
  NatLe (Datatypes.S b) b' -> NatLe (Datatypes.S (pairp a b)) (pairp a b').
Proof.
  intros b b' a. induction a as [|a IHa]; cbn [pairp].
  - intros H. apply NatLe_lift. apply NatLe_drop in H. lia.
  - intros H. apply NatLe_lift.
    specialize (IHa H). apply NatLe_drop in H. apply NatLe_drop in IHa. lia.
Qed.

(* ===================================================================== *)
(* Segment C: the three HBL derived conditions (layer-1 main targets).     *)
(*   lbd_Box: the bounded provability predicate -- there is a witness code *)
(*   w below the bound B whose self-fuel replay is exactly |target|.       *)
(*   It IS the value of D2's Sigma-atom (fsig) under the trivial           *)
(*   valuation, hence a genuine in-language formula.                      *)
(*   The box surface is carried by loeb_tid bool equations, matching the   *)
(*   bsearch_witness / bsearch_character interface family of G10_LoebFam.  *)
(* ===================================================================== *)

Definition lbd_Box (B c : nat) : bool := bsearch B (fun w : nat => verPf w c).

(* MP code-level transfer: witness code of the conclusion composed from the
   codes of the major and minor premises *)
Definition lbd_mpT (ci cf : nat) : nat := MPc ci cf.

(* Bound-closure map: the cost upper bound after MP-composing two witness
   codes inside the bound B *)
Definition lbd_boxup (B : nat) : nat := MPc B B.

(* In-language identity pinned: lbd_Box IS the value of the Formula2 fsig
   Sigma-atom under the trivial valuation (loeb_tid bool carrier) *)
Lemma lbd_Box_lang_internal : forall B c : nat,
  loeb_tid bool (lbd_Box B c)
            (evalF2 (fsig (numT B) (numT c)) (fun _ : nat => 0)).
Proof.
  intros B c. unfold lbd_Box. cbn [evalF2].
  rewrite valt_numT. rewrite valt_numT. apply loeb_tid_refl.
Qed.

(* Constructive completion of the Sigma-reflection half: bool certificate
   promoted into a replay ledger --
   verPf w c = true (loeb_tid) yields an explicit formula g:
   dP2 w w = Some g and |g| = c *)
Theorem lbd_replay_upgrade : forall (w c : nat),
  loeb_tid bool (verPf w c) true ->
  sigT (fun g : Formula =>
    (loeb_tid (option Formula) (dP2 w w) (Some g) *
     loeb_tid nat (gnF g) c)%type).
Proof.
  intros w c Hv. unfold verPf in Hv. tidQ Hv Heq.
  destruct (dP2 w w) as [gg|] eqn:Ed.
  - cbv iota in Heq.
    apply (proj1 (Nat.eqb_eq (gnF gg) c)) in Heq.
    exists gg. split.
    + apply loeb_tid_refl.
    + apply loeb_tid_eq. exact Heq.
  - cbv iota in Heq. discriminate Heq.
Qed.

(* Uniform-fuel replay after promotion (fuel-parameterized theorem shape,
   same interface shape as gnPrf_replay) *)
Theorem lbd_replay_uniform : forall (w c : nat) (g : Formula) (k : nat),
  loeb_tid bool (verPf w c) true -> loeb_tid nat (gnF g) c -> (w <= k)%nat ->
  loeb_tid (option Formula) (dP2 k w) (Some g).
Proof.
  intros w c g k Hv Hc Hk.
  destruct (lbd_replay_upgrade w c Hv) as [gg [Ed Hcg]].
  tidQ Hcg Ecg. tidQ Hc Ech.
  (* |gg| = c = |g| implies gg = g (coding injectivity); the uniform-fuel
     replay then reaches g *)
  assert (Hgg : gg = g).
  { apply (gnF_inj gg g). rewrite Ecg. symmetry. exact Ech. }
  tidI (lbd_dP2_norm w k Hk) Edn.
  apply loeb_tid_eq. rewrite Edn. rewrite <- Hgg. tidQ Ed Ee. exact Ee.
Qed.

(* -- HBL1: necessitation --
   If |- f (with a Prf witness) then []_B|f| holds; the bound only needs to
   cover the witness code. Conclusion carried by loeb_tid bool. *)
Theorem lbd_HBL1 : forall (f : Formula) (pf : Prf f) (B : nat),
  (Datatypes.S (gnPrf f pf) <= B)%nat -> loeb_tid bool (lbd_Box B (gnF f)) true.
Proof.
  intros f pf B HB. unfold lbd_Box.
  apply (bsearch_witness B (fun w : nat => verPf w (gnF f)) (gnPrf f pf)).
  - apply loeb_tid_eq. apply (proj2 (Nat.ltb_lt (gnPrf f pf) B)). lia.
  - exact (verPf_ledger_sound (gnPrf f pf) f pf
             (@loeb_tid_refl nat (gnPrf f pf))).
Qed.

(* -- HBL3: K shape --
   []_B|f->g| -> []_B|f| -> []_{boxup B}|g|: two witness codes below the
   bound compose through lbd_mpT, and the composed code lands below the
   bound closure boxup B. *)
Theorem lbd_HBL3 : forall (a b : Formula) (B : nat),
  loeb_tid bool (lbd_Box B (gnF (fimp a b))) true ->
  loeb_tid bool (lbd_Box B (gnF a)) true ->
  loeb_tid bool (lbd_Box (lbd_boxup B) (gnF b)) true.
Proof.
  intros a b B Heq1 Heq2. unfold lbd_Box in *.
  destruct (bsearch_character B (fun w : nat => verPf w (gnF (fimp a b)))
              Heq1) as [w1 [Hlt1 Hv1]].
  destruct (bsearch_character B (fun w : nat => verPf w (gnF a))
              Heq2) as [w2 [Hlt2 Hv2]].
  tidQ Hlt1 E1. pose proof (proj1 (Nat.ltb_lt w1 B) E1) as L1.
  tidQ Hlt2 E2. pose proof (proj1 (Nat.ltb_lt w2 B) E2) as L2.
  cbv beta in Hv1. cbv beta in Hv2.
  (* promote both certificates into the forall-k uniform replay shape
     (the premise shape of MPc_code_closed) *)
  assert (Hmp1 : forall k : nat, (w1 <= k)%nat ->
                  loeb_tid (option Formula) (dP2 k w1) (Some (fimp a b))).
  { intros k Hk.
    exact (lbd_replay_uniform w1 (gnF (fimp a b)) (fimp a b) k
             Hv1 (@loeb_tid_refl nat (gnF (fimp a b))) Hk). }
  assert (Hmp2 : forall k : nat, (w2 <= k)%nat ->
                  loeb_tid (option Formula) (dP2 k w2) (Some a)).
  { intros k Hk.
    exact (lbd_replay_uniform w2 (gnF a) a k
             Hv2 (@loeb_tid_refl nat (gnF a)) Hk). }
  unfold lbd_mpT.
  pose proof (MPc_code_closed w1 w2 a b Hmp1 Hmp2 (MPc w1 w2)
                (Nat.le_refl (MPc w1 w2))) as Hmp.
  (* bound migration: MPc w1 w2 < boxup B = pairp 7 (pairp B B)
     (both w1 and w2 strictly below B: strict second-component lift +
     non-strict monotone chain, extracted through NatLe_drop) *)
  assert (Hbnd : (MPc w1 w2 < lbd_boxup B)%nat).
  { unfold lbd_boxup, MPc.
    assert (Hm1 : (pairp w1 w2 < pairp w1 B)%nat).
    { apply (NatLe_drop (Datatypes.S (pairp w1 w2)) (pairp w1 B)).
      apply (lbd_pairp_mono_snd_lt w2 B w1).
      apply NatLe_lift. lia. }
    assert (Hm2 : (pairp w1 B <= pairp B B)%nat).
    { apply (NatLe_drop (pairp w1 B) (pairp B B)).
      apply (lbd_pairp_mono w1 B B B).
      - apply NatLe_lift. lia.
      - apply NatLe_lift. lia. }
    assert (Hinner : (pairp w1 w2 < pairp B B)%nat).
    { apply Nat.lt_le_trans with (pairp w1 B).
      - exact Hm1.
      - exact Hm2. }
    apply (NatLe_drop (Datatypes.S (pairp 7 (pairp w1 w2)))
                      (pairp 7 (pairp B B))).
    apply (lbd_pairp_mono_snd_lt (pairp w1 w2) (pairp B B) 7).
    apply NatLe_lift. exact Hinner. }
  assert (Hver : loeb_tid bool (verPf (MPc w1 w2) (gnF b)) true).
  { unfold verPf. tidQ Hmp Emp. rewrite Emp. cbv iota.
    apply loeb_tid_eq. apply Nat.eqb_refl. }
  apply (bsearch_witness (lbd_boxup B) (fun w : nat => verPf w (gnF b))
           (MPc w1 w2)).
  - apply loeb_tid_eq.
    apply (proj2 (Nat.ltb_lt (MPc w1 w2) (lbd_boxup B))). exact Hbnd.
  - exact Hver.
Qed.

(* -- HBL2: rule shape --
   If |- f->g (with a Prf witness of code cB) then []_B|f| ->
   []_{boxup(pairp (S cB) B)}|g|: the witness code supplies the ledger via
   the gnPrf_replay uniform replay, and the bound closure covers both codes. *)
Theorem lbd_HBL2 : forall (a b : Formula) (pf : Prf (fimp a b)) (B cB : nat),
  (gnPrf (fimp a b) pf <= cB)%nat ->
  loeb_tid bool (lbd_Box B (gnF a)) true ->
  loeb_tid bool
    (lbd_Box (lbd_boxup (pairp (Datatypes.S cB) B)) (gnF b)) true.
Proof.
  intros a b pf B cB HcB Heq. unfold lbd_Box in *.
  destruct (bsearch_character B (fun w : nat => verPf w (gnF a))
              Heq) as [w2 [Hlt2 Hv2]].
  tidQ Hlt2 E2. pose proof (proj1 (Nat.ltb_lt w2 B) E2) as L2.
  cbv beta in Hv2.
  (* minor-premise certificate promoted into the forall-k uniform shape *)
  assert (Hmp2 : forall k : nat, (w2 <= k)%nat ->
                  loeb_tid (option Formula) (dP2 k w2) (Some a)).
  { intros k Hk.
    exact (lbd_replay_uniform w2 (gnF a) a k
             Hv2 (@loeb_tid_refl nat (gnF a)) Hk). }
  unfold lbd_mpT.
  (* the major-premise witness code supplies the ledger through the
     gnPrf_replay uniform replay (the direct use of D1') *)
  assert (Hb1 : forall k : nat, (gnPrf (fimp a b) pf <= k)%nat ->
                 loeb_tid (option Formula) (dP2 k (gnPrf (fimp a b) pf))
                            (Some (fimp a b)))
    by exact (gnPrf_replay (fimp a b) pf).
  pose proof (MPc_code_closed (gnPrf (fimp a b) pf) w2 a b Hb1 Hmp2
                (MPc (gnPrf (fimp a b) pf) w2)
                (Nat.le_refl (MPc (gnPrf (fimp a b) pf) w2))) as Hmp.
  (* bound migration: pairp (S cB) B covers both the witness code and the
     bound; boxup M = pairp 7 (pairp M M) *)
  assert (HM1 : (gnPrf (fimp a b) pf <= pairp (Datatypes.S cB) B)%nat).
  { pose proof (pairp_ge1 (Datatypes.S cB) B) as Hp. lia. }
  assert (HBM : (B <= pairp (Datatypes.S cB) B)%nat)
    by exact (pairp_ge (Datatypes.S cB) B).
  assert (HM2 : (w2 <= pairp (Datatypes.S cB) B)%nat) by lia.
  assert (Hbnd : (MPc (gnPrf (fimp a b) pf) w2
                   < lbd_boxup (pairp (Datatypes.S cB) B))%nat).
  { unfold lbd_boxup, MPc.
    assert (HM3 : (w2 < pairp (Datatypes.S cB) B)%nat) by lia.
    assert (Hm1 : (pairp (gnPrf (fimp a b) pf) w2
                    < pairp (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B))%nat).
    { apply (NatLe_drop (Datatypes.S (pairp (gnPrf (fimp a b) pf) w2))
                        (pairp (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B))).
      apply (lbd_pairp_mono_snd_lt w2 (pairp (Datatypes.S cB) B)
                  (gnPrf (fimp a b) pf)).
      apply NatLe_lift. lia. }
    assert (Hm2 : (pairp (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B)
                    <= pairp (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B))%nat).
    { apply (NatLe_drop (pairp (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B))
                        (pairp (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B))).
      apply (lbd_pairp_mono (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B)
                  (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B)).
      - apply NatLe_lift. lia.
      - apply NatLe_lift. lia. }
    assert (Hinner : (pairp (gnPrf (fimp a b) pf) w2
                      < pairp (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B))%nat).
    { apply Nat.lt_le_trans with (pairp (gnPrf (fimp a b) pf)
                                        (pairp (Datatypes.S cB) B)).
      - exact Hm1.
      - exact Hm2. }
    apply (NatLe_drop (Datatypes.S (pairp 7 (pairp (gnPrf (fimp a b) pf) w2)))
                      (pairp 7 (pairp (pairp (Datatypes.S cB) B)
                                      (pairp (Datatypes.S cB) B)))).
    apply (lbd_pairp_mono_snd_lt (pairp (gnPrf (fimp a b) pf) w2)
             (pairp (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B)) 7).
    apply NatLe_lift. exact Hinner. }
  assert (Hver : loeb_tid bool
                   (verPf (MPc (gnPrf (fimp a b) pf) w2) (gnF b)) true).
  { unfold verPf. tidQ Hmp Emp. rewrite Emp. cbv iota.
    apply loeb_tid_eq. apply Nat.eqb_refl. }
  apply (bsearch_witness (lbd_boxup (pairp (Datatypes.S cB) B))
           (fun w : nat => verPf w (gnF b)) (MPc (gnPrf (fimp a b) pf) w2)).
  - apply loeb_tid_eq.
    apply (proj2 (Nat.ltb_lt (MPc (gnPrf (fimp a b) pf) w2)
                             (lbd_boxup (pairp (Datatypes.S cB) B)))).
    exact Hbnd.
  - exact Hver.
Qed.

(* ===================================================================== *)
(* Segment D: the D3' encoded self-reference exhibit (layer 2): the box    *)
(*   of the Loeb implication of the diagonal sentence has a closed-form    *)
(*   computable bound. Uses D1's diagonal lemma (Defined, extractable) +   *)
(*   this slice's HBL1: for any unary th, the diagonal sentence            *)
(*   d = diagF th has |- th(|d|)->d (a Prf witness), whose proof code c*   *)
(*   directly gives the bound of the true box.                             *)
(*   "The guard is constructive": the bound is not an existential           *)
(*   assumption but the closed-form computation lbd_boxup c*.              *)
(*   Premise shape aligned with diagonal_lemma's live interface            *)
(*   (loeb_tid bool (unaryF th) true) -- no bridge shim needed.            *)
(* ===================================================================== *)

Theorem lbd_diag_necessitation : forall th : Formula,
  loeb_tid bool (unaryF th) true ->
  sigT (fun d : Formula =>
    sigT (fun pf : Prf (fimp (appN th (gnF d)) d) =>
      loeb_tid bool
        (lbd_Box (lbd_boxup (gnPrf (fimp (appN th (gnF d)) d) pf))
                 (gnF (fimp (appN th (gnF d)) d))) true)).
Proof.
  intros th Hun.
  destruct (diagonal_lemma th Hun) as [d [Hcl [_ pfx]]].
  exists d. exists pfx.
  apply (lbd_HBL1 (fimp (appN th (gnF d)) d) pfx
           (lbd_boxup (gnPrf (fimp (appN th (gnF d)) d) pfx))).
  unfold lbd_boxup, MPc.
  assert (H1 : (gnPrf (fimp (appN th (gnF d)) d) pfx
                < pairp (gnPrf (fimp (appN th (gnF d)) d) pfx)
                        (gnPrf (fimp (appN th (gnF d)) d) pfx))%nat).
  { apply (NatLe_drop (Datatypes.S (gnPrf (fimp (appN th (gnF d)) d) pfx))
                      (pairp (gnPrf (fimp (appN th (gnF d)) d) pfx)
                             (gnPrf (fimp (appN th (gnF d)) d) pfx))).
    apply lbd_pairp_gt_snd. }
  pose proof (pairp_ge 7 (pairp (gnPrf (fimp (appN th (gnF d)) d) pfx)
                          (gnPrf (fimp (appN th (gnF d)) d) pfx))) as H2.
  lia.
Qed.

(* ===================================================================== *)
(* Honesty boundary (explicit declaration, no special-cased constructs):   *)
(*   1. The object theory of the three HBL clauses in this slice is G10's  *)
(*      Prf (true closed equations + MP + repl); [] is realized with the   *)
(*      bounded bsearch semantics (lbd_Box = the fsig value), and the      *)
(*      truth value of [] is genuinely decided by the bound and the code   *)
(*      ledger (the semantics reused from D2's Sigma_fires /               *)
(*      Sigma_bound_tight smoke tests).                                    *)
(*   2. Full-shape Loeb is not in this slice (see the header fail-loud     *)
(*      record: the Formula2 coding round trip + the unbounded-search      *)
(*      wall); the downgraded shape is guarded: lbd_diag_necessitation     *)
(*      gives the closed-form computation of the guard.                    *)
(*   3. The dP2 decode-uniqueness direction (pairp decode injectivity)     *)
(*      remains unexpanded (D2 honesty boundary 2 carried over); this      *)
(*      slice does not depend on that direction.                           *)
(* ===================================================================== *)

(* -- Assumption-surface self-audit (all items should be Closed under the
      global context) -- *)
Print Assumptions lbd_dP2_fuel_inv.
Print Assumptions lbd_replay_upgrade.
Print Assumptions lbd_HBL1.
Print Assumptions lbd_HBL3.
Print Assumptions lbd_HBL2.
Print Assumptions lbd_diag_necessitation.
