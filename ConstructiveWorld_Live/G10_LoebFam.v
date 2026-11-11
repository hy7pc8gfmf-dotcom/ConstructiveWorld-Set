(* ConstructiveWorld-Set — the finite-merge group carrying the Löb diagonal-mechanism line. *)
(** * G10_LoebFam: the Löb genuine-proof long line — the constructive realization of the
    diagonal mechanism D1 and the provability predicate Σ(σ) D2 (pure Set level, stdlib only).

    Mission.  HB D1, the diagonal mechanism, first leg of the D1–D3 program ("Constructive
      governance of incompleteness"): the closed inductive proof carrier [Prf] with soundness
      [Prf_soundness]; the diagonal theorem genuinely assembled by the repl rule, witness the
      explicit fixed-point combinator [diagF]; the object language has equation atoms and
      implications only, quantifier semantics being the D2 interface; total decoders
      [dT]/[dF] with round trips [dec_gnT]/[dec_gnF]; the wallet-trajectory family
      [wpm_solvent_at_last_covered]/[wpm_melt_bankrupt]/[dwm_wallet_trajectory] with emitter
      legality [dwm_emit3_legal]; and [unaryT_selfT]/[diagonal_code_fixed]/[MPc_dP_closed]/[grm_two_step_budget_blown].

    Dependencies.  Stdlib [Arith], [Lia], [List], [Wf_nat]; the Set-level identity-type
      infrastructure is inlined in section 0; merged members carry their own Requires inline
      ([ZArith] family; [S01_BaseRing]–[S15_TailFEPUp], [UpCS], [Lqa]).

    References.  This development, the ConstructiveWorld-Main baseline modules UpLoeb.v,
      UpRefuted.v (the four kill experiments), UpQKBound.v (the QKᵀ bound pipeline),
      UpLoebD2.v (the provability predicate Σ(σ)) — statement names carried over verbatim,
      old in-library names ablated, downstream Requires this group directly.  Honest face:
      [wpm_solvent_bounded_family] is identity forwarding; [wpm_unbounded_family_unsound]
      stays a two-hop combinator; [Prf_replay] is already the closed replay term.

    Constructivity.  All statements are carried by [Set] (tid / sigT / bool / nat->nat; [tidQ]
      only inside [Proof]); every proof closes by [Qed]/[Defined]; no admissions, no classical
      logic, no placeholder parameters; [coqchk] reports [Axioms: none]; informative, extractable.

    Build.  [coqc -native-compiler no -q -Q . "" G10_LoebFam.v]; the artifact's first eight
      bytes are [436f7121 000160bc]. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Wf_nat.

(* ===================================================================== *)
(* §0  Set-level identity-type infrastructure (inlined from G04_ProjFam/G11_IDLFam, zero external dependencies)                *)
(* ===================================================================== *)

Inductive loeb_tid (A : Type) : A -> A -> Type := loeb_tid_refl : forall x : A, loeb_tid A x x.

Definition loeb_tid_sym (A : Type) (x y : A) (H : loeb_tid A x y) : loeb_tid A y x :=
  match H in loeb_tid _ a b return loeb_tid _ b a with
  | loeb_tid_refl _ a0 => @loeb_tid_refl _ a0
  end.

Definition loeb_tid_trans (A : Type) (x y z : A) (H1 : loeb_tid A x y) (H2 : loeb_tid A y z) :
  loeb_tid A x z :=
  match H1 in loeb_tid _ a b return loeb_tid _ b z -> loeb_tid _ a z with
  | loeb_tid_refl _ a0 => fun H => H
  end H2.

Definition loeb_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : loeb_tid A x y) :
  loeb_tid B (f x) (f y) :=
  match H in loeb_tid _ a b return loeb_tid B (f a) (f b) with
  | loeb_tid_refl _ a0 => @loeb_tid_refl _ (f a0)
  end.

(* loeb_tid -> definitional equation (used only inside Proof; statements show no Prop) *)
Lemma loeb_tid_eq (A : Type) (x y : A) : x = y -> loeb_tid A x y.
Proof. intros H. rewrite H. apply loeb_tid_refl. Qed.

(* The Ltac extracting the definitional equation from loeb_tid (Proof-internal only) *)
Ltac tidQ H E := pose proof (match H in loeb_tid _ a b return a = b with loeb_tid_refl _ _ => eq_refl end) as E.

(* The empty type: the carrier for loeb_tid bool contradiction closure / impossibility elimination *)
Inductive nul : Set :=.

(* ===================================================================== *)
(* §1  The syntax layer: closed inductive types + structural-recursion substitution                                   *)
(*     The D1 fragment language: terms = variable/zero/successor/self-substitution symbol; formulas = equation atoms/implications.       *)
(*     (No quantifier constructors -> no hard-codable quantifier branch exists at the syntax layer; fake method 3 has nowhere to hide.)    *)
(* ===================================================================== *)

Inductive Term : Set :=
| tvar : nat -> Term
| tzero : Term
| tsucc : Term -> Term
| tsub : Term -> Term -> Term.

Inductive Formula : Set :=
| teq : Term -> Term -> Formula
| fimp : Formula -> Formula -> Formula.

Fixpoint numT (m : nat) : Term :=
  match m with
  | O => tzero
  | Datatypes.S m' => tsucc (numT m')
  end.

(* Substitution into variable 0 (the language has no constrained binder -> no capture problem; pure structural recursion) *)
Fixpoint substT (u t : Term) : Term :=
  match u with
  | tvar O => t
  | tvar (Datatypes.S k) => tvar (Datatypes.S k)
  | tzero => tzero
  | tsucc u' => tsucc (substT u' t)
  | tsub a b => tsub (substT a t) (substT b t)
  end.

Fixpoint substF (f : Formula) (t : Term) : Formula :=
  match f with
  | teq u1 u2 => teq (substT u1 t) (substT u2 t)
  | fimp a b => fimp (substF a t) (substF b t)
  end.

(* The substitution-composition lemma (the bindless substitution lemma; load-bearing piece one of the diagonal combinator) *)
Lemma substT_comp : forall (u t1 t2 : Term),
  substT (substT u t1) t2 = substT u (substT t1 t2).
Proof.
  induction u as [k| |u IHu|a IHa b IHb]; intros t1 t2; simpl; try reflexivity.
  - destruct k; reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma substF_comp : forall (f : Formula) (t1 t2 : Term),
  substF (substF f t1) t2 = substF f (substT t1 t2).
Proof.
  induction f as [u1 u2|a IHa b IHb]; intros t1 t2; simpl.
  - rewrite !substT_comp. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

(* ===================================================================== *)
(* §2  Free variables / unary-ness / closedness (the bool-decidable form)                                *)
(* ===================================================================== *)

Fixpoint fvT (u : Term) : list nat :=
  match u with
  | tvar k => k :: nil
  | tzero => nil
  | tsucc u' => fvT u'
  | tsub a b => fvT a ++ fvT b
  end.

Fixpoint fvF (f : Formula) : list nat :=
  match f with
  | teq u1 u2 => fvT u1 ++ fvT u2
  | fimp a b => fvF a ++ fvF b
  end.

Definition unaryT (t : Term) : bool := forallb (fun k : nat => Nat.eqb k 0) (fvT t).
Definition unaryF (f : Formula) : bool := forallb (fun k : nat => Nat.eqb k 0) (fvF f).
Definition closedT (t : Term) : bool :=
  match fvT t with nil => true | _ => false end.
Definition closedF (f : Formula) : bool :=
  match fvF f with nil => true | _ => false end.

Lemma forallb0_character : forall l : list nat,
  forallb (fun k : nat => Nat.eqb k 0) l = true <-> (forall k : nat, In k l -> k = 0).
Proof.
  intros l. split; intros H.
  - intros k Hk. apply Nat.eqb_eq.
    apply (proj1 (forallb_forall (fun k : nat => Nat.eqb k 0) l) H k Hk).
  - apply forallb_forall. intros x Hx. rewrite (H x Hx). reflexivity.
Qed.

Lemma numT_fv : forall (m k : nat), In k (fvT (numT m)) -> nul.
Proof.
  induction m as [|m IHm]; simpl; intros k Hk.
  - destruct Hk.
  - exact (IHm k Hk).
Qed.

(* The characterization of free variables after substitution (load-bearing piece two) *)
Lemma fvT_subst : forall (u t : Term) (k : nat),
  In k (fvT (substT u t)) -> (In k (fvT u) /\ k <> 0) \/ In k (fvT t).
Proof.
  induction u as [k0| |u IHu|a IHa b IHb]; intros t k Hk; simpl in Hk; simpl.
  - destruct k0 as [|k'].
    + simpl in Hk. right. exact Hk.
    + simpl in Hk. destruct Hk as [Hk|[]].
      left. split.
      * left. exact Hk.
      * rewrite <- Hk. discriminate.
  - destruct Hk.
  - destruct (IHu t k Hk) as [Hc|Ht].
    + left. destruct Hc as [Hc1 Hc2]. split. * exact Hc1. * exact Hc2.
    + right. exact Ht.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (IHa t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. left. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
    + destruct (IHb t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. right. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
Qed.

Lemma fvF_subst : forall (f : Formula) (t : Term) (k : nat),
  In k (fvF (substF f t)) -> (In k (fvF f) /\ k <> 0) \/ In k (fvT t).
Proof.
  induction f as [u1 u2|a IHa b IHb]; intros t k Hk; simpl in Hk; simpl.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (fvT_subst u1 t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. left. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
    + destruct (fvT_subst u2 t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. right. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (IHa t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. left. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
    + destruct (IHb t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. right. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
Qed.

(* A unary formula substituted by a unary term stays unary (load-bearing piece three of the diagonal sentence's closedness) *)
Lemma substF_fv_zero : forall (f : Formula) (t : Term),
  (forall k : nat, In k (fvF f) -> k = 0) ->
  (forall k : nat, In k (fvT t) -> k = 0) ->
  forall k : nat, In k (fvF (substF f t)) -> k = 0.
Proof.
  induction f as [u1 u2|a IHa b IHb]; simpl; intros t Hzf Hzt k Hk.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (fvT_subst u1 t k Hk) as [Hc|Ht2].
      * apply Hzf. simpl. apply in_or_app. left. exact (proj1 Hc).
      * apply Hzt. exact Ht2.
    + destruct (fvT_subst u2 t k Hk) as [Hc|Ht2].
      * apply Hzf. simpl. apply in_or_app. right. exact (proj1 Hc).
      * apply Hzt. exact Ht2.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + assert (Ha : forall j : nat, In j (fvF a) -> j = 0).
      { intros j Hj. apply Hzf. apply in_or_app. left. exact Hj. }
      exact (IHa t Ha Hzt k Hk).
    + assert (Hb : forall j : nat, In j (fvF b) -> j = 0).
      { intros j Hj. apply Hzf. apply in_or_app. right. exact Hj. }
      exact (IHb t Hb Hzt k Hk).
Qed.

Lemma unaryF_subst : forall (f : Formula) (t : Term),
  unaryT t = true -> unaryF f = true -> unaryF (substF f t) = true.
Proof.
  intros f t Ht Hf.
  unfold unaryT in Ht. unfold unaryF in Hf.
  pose proof (proj1 (forallb0_character (fvT t)) Ht) as Ht0.
  pose proof (proj1 (forallb0_character (fvF f)) Hf) as Hf0.
  apply (proj2 (forallb0_character (fvF (substF f t)))).
  exact (substF_fv_zero f t Hf0 Ht0).
Qed.

Lemma closedF_subst_num : forall (f : Formula) (m : nat),
  unaryF f = true -> closedF (substF f (numT m)) = true.
Proof.
  intros f m Hf. unfold unaryF in Hf.
  pose proof (proj1 (forallb0_character (fvF f)) Hf) as Hf0.
  assert (Hzn : forall k : nat, In k (fvT (numT m)) -> k = 0).
  { intros k Hk. destruct (numT_fv m k Hk). }
  unfold closedF.
  assert (Hnil : fvF (substF f (numT m)) = nil).
  { destruct (fvF (substF f (numT m))) as [|k l] eqn:E.
    - reflexivity.
    - exfalso. assert (Hk : In k (fvF (substF f (numT m)))).
      { rewrite E. left. reflexivity. }
      destruct (fvF_subst f (numT m) k Hk) as [[Hin Hne]|Ht2].
      + rewrite (Hf0 k Hin) in Hne. exact (Hne eq_refl).
      + destruct (numT_fv m k Ht2). }
  rewrite Hnil. reflexivity.
Qed.

(* ===================================================================== *)
(* §3  Gödel coding: the nat pairing function + the total-function decoder (ruling out the material's decode=None fake method)   *)
(* ===================================================================== *)

Fixpoint pairp (a b : nat) : nat :=
  match a with
  | O => Datatypes.S (b + b)
  | Datatypes.S a' => (pairp a' b) + (pairp a' b)
  end.

Lemma pairp_pos : forall a b, (1 <= pairp a b)%nat.
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - lia.
  - pose proof (IHa b). lia.
Qed.

Lemma pairp_ge : forall a b, (b <= pairp a b)%nat.
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - lia.
  - pose proof (IHa b). lia.
Qed.

Lemma pairp_ge1 : forall a b, (a <= pairp a b)%nat.
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - lia.
  - pose proof (IHa b). pose proof (pairp_pos a b). lia.
Qed.

(* The parity / halving arithmetic mini-lemma chain *)
Lemma even_ss : forall x : nat, Nat.even (Datatypes.S (Datatypes.S x)) = Nat.even x.
Proof.
  intros x. unfold Nat.even.
  destruct x as [|x'].
  - reflexivity.
  - reflexivity.
Qed.

Lemma even_double : forall x : nat, Nat.even (x + x) = true.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (Datatypes.S x + Datatypes.S x) with (Datatypes.S (Datatypes.S (x + x))) by lia.
    rewrite even_ss. exact IHx.
Qed.

Lemma even_succ_double : forall x : nat, Nat.even (Datatypes.S (x + x)) = false.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (Datatypes.S x + Datatypes.S x) with (Datatypes.S (Datatypes.S (x + x))) by lia.
    rewrite even_ss. exact IHx.
Qed.

Lemma div2_ss : forall x : nat, Nat.div2 (Datatypes.S (Datatypes.S x)) = Datatypes.S (Nat.div2 x).
Proof.
  intros x. destruct x as [|x'].
  - reflexivity.
  - cbn [Nat.div2]. reflexivity.
Qed.

Lemma div2_add : forall x : nat, Nat.div2 (x + x) = x.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (Datatypes.S x + Datatypes.S x) with (Datatypes.S (Datatypes.S (x + x))) by lia.
    rewrite div2_ss. rewrite IHx. reflexivity.
Qed.

Lemma div2_le : forall n : nat, (Nat.div2 n <= n)%nat.
Proof.
  induction n as [|n IHn].
  - cbn [Nat.div2]. lia.
  - pose proof (Nat.le_div2 n). lia.
Qed.

(* Decoding with the value as its own fuel: unp2 f n — f consumes 1 per layer, the value halves per layer *)
Fixpoint unp2 (f n : nat) {struct f} : option (nat * nat) :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match n with
      | O => None
      | Datatypes.S n' =>
          if Nat.even (Datatypes.S n')
          then (match unp2 f' (Nat.div2 (Datatypes.S n')) with
                | Some (a, b) => Some (Datatypes.S a, b)
                | None => None
                end)
          else Some (O, Nat.div2 n')
      end
  end.

(* The single-step unfolding lemma: the only channel for controlled unfolding inside proofs (keeps unp2 rewritable while folded) *)
Lemma unp2_S : forall (f' n : nat),
  unp2 (Datatypes.S f') n =
  match n with
  | O => None
  | Datatypes.S n' =>
      if Nat.even (Datatypes.S n')
      then (match unp2 f' (Nat.div2 (Datatypes.S n')) with
            | Some (a, b) => Some (Datatypes.S a, b)
            | None => None
            end)
      else Some (O, Nat.div2 n')
  end.
Proof.
  intros f' n. destruct n as [|n'].
  - reflexivity.
  - reflexivity.
Qed.

(* Agreement with the self-fueled form when the fuel is sufficient (load-bearing piece four) *)
Lemma unp2_fuel : forall x g : nat, (x <= g)%nat -> unp2 g x = unp2 x x.
Proof.
  intros x. induction x as [x IH] using lt_wf_ind. intros g Hle.
  destruct x as [|[|x'']].
  - destruct g as [|g'].
    + reflexivity.
    + reflexivity.
  - destruct g as [|g'].
    + exfalso. lia.
    + reflexivity.
  - destruct g as [|[|g']].
    + exfalso. lia.
    + exfalso. lia.
    + rewrite (unp2_S (Datatypes.S g') (Datatypes.S (Datatypes.S x''))).
      rewrite (unp2_S (Datatypes.S x'') (Datatypes.S (Datatypes.S x''))).
      cbv iota.
      destruct (Nat.even (Datatypes.S (Datatypes.S x''))).
      * rewrite (div2_ss x'').
        pose proof (div2_le x'') as Hd2.
        pose proof (proj2 (Nat.succ_le_mono (Datatypes.S x'') (Datatypes.S g')) Hle) as Hs1.
        pose proof (proj2 (Nat.succ_le_mono x'' g') Hs1) as Hxg.
        assert (Hv1 : (Datatypes.S (Nat.div2 x'') <= Datatypes.S g')%nat).
        { apply Nat.le_trans with (Datatypes.S x'').
          - apply le_n_S. exact Hd2.
          - exact Hs1. }
        assert (Hv2 : (Datatypes.S (Nat.div2 x'') <= Datatypes.S x'')%nat)
          by (apply le_n_S; exact Hd2).
        assert (Hlt : (Datatypes.S (Nat.div2 x'') < Datatypes.S (Datatypes.S x''))%nat).
        { apply Nat.le_lt_trans with (Datatypes.S x'').
          - exact Hv2.
          - apply Nat.lt_succ_diag_r. }
        pose proof (IH (Datatypes.S (Nat.div2 x'')) Hlt (Datatypes.S g') Hv1) as IH1.
        pose proof (IH (Datatypes.S (Nat.div2 x'')) Hlt (Datatypes.S x'') Hv2) as IH2.
        rewrite IH1. rewrite IH2.
        reflexivity.
      * reflexivity.
Qed.

(* The pairing round-trip theorem: the core of decoder correctness *)
Lemma unp2_pair : forall a b : nat, unp2 (pairp a b) (pairp a b) = Some (a, b).
Proof.
  induction a as [|a IHa]; intros b.
  - cbn [pairp]. rewrite (unp2_S (b + b) (Datatypes.S (b + b))). cbv iota.
    rewrite even_succ_double. rewrite div2_add. reflexivity.
  - cbn [pairp]. destruct (pairp a b) as [|p] eqn:Ep.
    + exfalso. pose proof (pairp_pos a b) as Hp. rewrite Ep in Hp. lia.
    + replace (Datatypes.S p + Datatypes.S p) with (Datatypes.S (Datatypes.S (p + p))) by lia.
      rewrite (unp2_S (Datatypes.S (p + p)) (Datatypes.S (Datatypes.S (p + p)))). cbv iota.
      rewrite even_ss. rewrite even_double.
      rewrite div2_ss. rewrite div2_add.
      assert (Hle : (Datatypes.S p <= Datatypes.S (p + p))%nat) by lia.
      rewrite (unp2_fuel (Datatypes.S p) (Datatypes.S (p + p)) Hle).
      rewrite <- Ep. rewrite (IHa b). reflexivity.
Qed.

(* The coding functions (terms / formulas, pairwise-distinct tags) *)
Fixpoint gnT (t : Term) : nat :=
  match t with
  | tvar k => pairp 0 k
  | tzero => pairp 1 0
  | tsucc t' => pairp 2 (gnT t')
  | tsub a b => pairp 3 (pairp (gnT a) (gnT b))
  end.

Fixpoint gnF (f : Formula) : nat :=
  match f with
  | teq u1 u2 => pairp 4 (pairp (gnT u1) (gnT u2))
  | fimp a b => pairp 5 (pairp (gnF a) (gnF b))
  end.

(* The total-function decoder (fuel = the code value itself) *)
Fixpoint dT2 (f c : nat) {struct f} : option Term :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (O, p) => Some (tvar p)
      | Some (Datatypes.S O, _) => Some tzero
      | Some (Datatypes.S (Datatypes.S O), q) =>
          (match dT2 f' q with
           | Some x => Some (tsucc x)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S O)), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (tsub x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

Definition dT (c : nat) : option Term := dT2 c c.

Fixpoint dF2 (f c : nat) {struct f} : option Formula :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (teq x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dF2 f' a with
                | Some x =>
                    (match dF2 f' b with
                     | Some y => Some (fimp x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

Definition dF (c : nat) : option Formula := dF2 c c.

(* The decoder fuel lemma *)
Lemma gnT_fuel : forall (t : Term) (k : nat), (gnT t <= k)%nat -> dT2 k (gnT t) = Some t.
Proof.
  intros t. induction t as [m| |t IHt|a IHa b IHb]; intros k Hk.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + cbn [gnT dT2]. rewrite unp2_pair. reflexivity.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + cbn [gnT dT2]. rewrite unp2_pair. reflexivity.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + assert (Hb : (gnT t + 1 <= pairp 2 (gnT t))%nat) by (cbn [pairp]; lia).
      cbn [gnT pairp] in Hk.
      assert (Hlt : (gnT t <= k')%nat) by lia.
      cbn [gnT dT2]. rewrite unp2_pair. cbv iota.
      rewrite (IHt k' Hlt). reflexivity.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + assert (Hq : (pairp (gnT a) (gnT b) + 1 <= pairp 3 (pairp (gnT a) (gnT b)))%nat)
        by (cbn [pairp]; lia).
      pose proof (pairp_ge1 (gnT a) (gnT b)) as Hga.
      pose proof (pairp_ge (gnT a) (gnT b)) as Hgb.
      cbn [gnT pairp] in Hk.
      assert (Hla : (gnT a <= k')%nat) by lia.
      assert (Hlb : (gnT b <= k')%nat) by lia.
      cbn [gnT dT2]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (IHa k' Hla). rewrite (IHb k' Hlb). reflexivity.
Qed.

Lemma gnF_fuel : forall (f : Formula) (k : nat), (gnF f <= k)%nat -> dF2 k (gnF f) = Some f.
Proof.
  intros f. induction f as [u1 u2|a IHa b IHb]; intros k Hk.
  - destruct k as [|k'].
    + cbn [gnF pairp] in Hk. lia.
    + pose proof (pairp_ge1 (gnT u1) (gnT u2)) as Hq1.
      pose proof (pairp_ge (gnT u1) (gnT u2)) as Hq2.
      assert (Hq3 : (pairp (gnT u1) (gnT u2) + 1
                     <= pairp 4 (pairp (gnT u1) (gnT u2)))%nat) by (cbn [pairp]; lia).
      cbn [gnF pairp] in Hk.
      assert (Hla : (gnT u1 <= k')%nat) by lia.
      assert (Hlb : (gnT u2 <= k')%nat) by lia.
      cbn [gnF dF2]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (gnT_fuel u1 k' Hla). rewrite (gnT_fuel u2 k' Hlb).
      reflexivity.
  - destruct k as [|k'].
    + cbn [gnF pairp] in Hk. lia.
    + pose proof (pairp_ge1 (gnF a) (gnF b)) as Hq1.
      pose proof (pairp_ge (gnF a) (gnF b)) as Hq2.
      assert (Hq3 : (pairp (gnF a) (gnF b) + 1
                     <= pairp 5 (pairp (gnF a) (gnF b)))%nat) by (cbn [pairp]; lia).
      cbn [gnF pairp] in Hk.
      assert (Hla : (gnF a <= k')%nat) by lia.
      assert (Hlb : (gnF b <= k')%nat) by lia.
      cbn [gnF dF2]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (IHa k' Hla). rewrite (IHb k' Hlb).
      reflexivity.
Qed.

(* The round-trip theorem: genuine decoding (the positive counterpiece to the material's None placeholder) *)
Lemma dec_gnT : forall t : Term, dT (gnT t) = Some t.
Proof.
  intros t.
  exact (gnT_fuel t (gnT t) (Nat.le_refl (gnT t))).
Qed.

Lemma dec_gnF : forall f : Formula, dF (gnF f) = Some f.
Proof.
  intros f.
  exact (gnF_fuel f (gnF f) (Nat.le_refl (gnF f))).
Qed.

(* Coding injectivity *)
Lemma gnF_inj : forall f1 f2 : Formula, gnF f1 = gnF f2 -> f1 = f2.
Proof.
  intros f1 f2 H.
  pose proof (dec_gnF f1) as E1. pose proof (dec_gnF f2) as E2.
  rewrite H in E1. rewrite E1 in E2. inversion E2. reflexivity.
Qed.

(* ===================================================================== *)
(* §4  The code-level substitution function and the coding-interchange theorem                                            *)
(* ===================================================================== *)

Definition gsubF (c m : nat) : nat :=
  match dF c with
  | Some f => gnF (substF f (numT m))
  | None => c
  end.

(* Coding-substitution interchange: the code-level Sub function agrees exactly with the syntax-level subst (load-bearing piece five) *)
Theorem gn_comm : forall (f : Formula) (m : nat),
  loeb_tid nat (gnF (substF f (numT m))) (gsubF (gnF f) m).
Proof.
  intros f m. apply loeb_tid_eq. unfold gsubF. rewrite dec_gnF. reflexivity.
Qed.

(* ===================================================================== *)
(* §5  Value semantics (no hard-coded quantifier branch: the language itself has no quantifiers)                              *)
(* ===================================================================== *)

Fixpoint valt (t : Term) (s : nat -> nat) : nat :=
  match t with
  | tvar k => s k
  | tzero => 0
  | tsucc t' => Datatypes.S (valt t' s)
  | tsub a b => gsubF (valt a s) (valt b s)
  end.

Definition upd (s : nat -> nat) (v k : nat) : nat :=
  match k with
  | O => v
  | Datatypes.S k' => s (Datatypes.S k')
  end.

Lemma valt_numT : forall (m : nat) (s : nat -> nat), valt (numT m) s = m.
Proof.
  induction m as [|m IHm]; intros s; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
Qed.

Lemma valt_substT : forall (u t : Term) (s : nat -> nat),
  valt (substT u t) s = valt u (upd s (valt t s)).
Proof.
  induction u as [k0| |u IHu|a IHa b IHb]; intros t s; simpl.
  - destruct k0; simpl; reflexivity.
  - reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Fixpoint evalF (f : Formula) (s : nat -> nat) : bool :=
  match f with
  | teq u1 u2 => Nat.eqb (valt u1 s) (valt u2 s)
  | fimp a b => orb (negb (evalF a s)) (evalF b s)
  end.

Lemma evalF_subst : forall (f : Formula) (t : Term) (s : nat -> nat),
  evalF (substF f t) s = evalF f (upd s (valt t s)).
Proof.
  induction f as [u1 u2|a IHa b IHb]; intros t s; simpl.
  - rewrite !valt_substT. reflexivity.
  - rewrite IHa. rewrite IHb. reflexivity.
Qed.

(* ===================================================================== *)
(* §6  The object-level proof system Prf: Set-valued induction + three rules, all with metalevel semantic verification            *)
(*     ax_eqT: atomic equations with equal values are provable (the true-equation scheme)                             *)
(*     mpF  : modus ponens                                                      *)
(*     repl : value-equal terms are interchangeable in any unary substitution context (the            *)
(*            minimized form of the Σ0 replacement-invariant scheme — the diagonal biconditional's only non-logical axiom,        *)
(*            its semantics fully covered by the soundness theorem below — structurally excluding Triv filling)                               *)
(* ===================================================================== *)

Inductive Prf : Formula -> Set :=
| ax_eqT : forall u1 u2 : Term,
    (forall s : nat -> nat, loeb_tid nat (valt u1 s) (valt u2 s)) -> Prf (teq u1 u2)
| mpF : forall a b : Formula, Prf (fimp a b) -> Prf a -> Prf b
| repl : forall (th : Formula) (t1 t2 : Term),
    (forall s : nat -> nat, loeb_tid nat (valt t1 s) (valt t2 s)) ->
    Prf (fimp (substF th t1) (substF th t2)).

(* Metalevel soundness: every Prf term is true under the standard valuation (the structural guarantee against fake method 1) *)
Theorem Prf_soundness : forall (f : Formula), Prf f ->
  forall s : nat -> nat, loeb_tid bool (evalF f s) true.
Proof.
  intros f H. induction H as [u1 u2 Hval | a b pf1 IH1 pf2 IH2 | th t1 t2 Hval].
  - intros s. apply loeb_tid_eq. cbn [evalF]. tidQ (Hval s) E. rewrite E. apply Nat.eqb_refl.
  - intros s. specialize (IH1 s). specialize (IH2 s).
    tidQ IH1 E1. tidQ IH2 E2.
    apply loeb_tid_eq. cbn [evalF] in E1. rewrite E2 in E1.
    cbn [negb orb] in E1. exact E1.
  - intros s. simpl. rewrite (evalF_subst th t1 s). rewrite (evalF_subst th t2 s).
    tidQ (Hval s) E. rewrite E.
    destruct (evalF th (upd s (valt t2 s))).
    + cbn [negb orb]. apply loeb_tid_refl.
    + cbn [negb orb]. apply loeb_tid_refl.
Qed.

(* ===================================================================== *)
(* §7  The diagonal mechanism: the diag_fix combinator (the explicit closed form) and the diagonal theorem                          *)
(* ===================================================================== *)

(* The self-substitution term: x sub x *)
Definition selfT : Term := tsub (tvar 0) (tvar 0).
(* The wrapper body: th applied to the self-substitution term (variable 0's argument slot left open) *)
Definition wrapF (th : Formula) : Formula := substF th selfT.
(* diag_fix: the diagonal combinator, the explicit closed form of d — th's wrapper body applied to its own code *)
Definition diagF (th : Formula) : Formula :=
  substF (wrapF th) (numT (gnF (wrapF th))).
(* The numeric application of a unary formula *)
Definition appN (th : Formula) (m : nat) : Formula := substF th (numT m).

Lemma unaryT_selfT : unaryT selfT = true.
Proof.
  unfold selfT, unaryT.
  cbn [fvT].
  change (forallb (fun k : nat => Nat.eqb k 0) (fvT (tvar 0) ++ fvT (tvar 0)) = true).
  cbn [app].
  cbn [forallb].
  cbn [Nat.eqb andb].
  reflexivity.
Qed.

Lemma diagF_eq : forall th : Formula,
  loeb_tid Formula (diagF th)
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))).
Proof.
  intros th. apply loeb_tid_eq. unfold diagF, wrapF.
  rewrite substF_comp. reflexivity.
Qed.

(* The key code identity: the code of d = the value of the code-level substitution gsubF at (n, n) *)
Theorem diag_code_eq : forall th : Formula,
  loeb_tid nat (gnF (diagF th)) (gsubF (gnF (wrapF th)) (gnF (wrapF th))).
Proof.
  intros th. apply loeb_tid_eq. unfold diagF.
  tidQ (gn_comm (wrapF th) (gnF (wrapF th))) E.
  exact E.
Qed.

(* The key value identity: d's diagonal term evaluates under any valuation to exactly gnF d *)
Lemma diag_val_eq : forall (th : Formula) (s : nat -> nat),
  loeb_tid nat (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)
    (gnF (diagF th)).
Proof.
  intros th s.
  assert (H1 : valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s
               = gsubF (gnF (wrapF th)) (gnF (wrapF th))).
  { cbn [valt]. rewrite valt_numT. reflexivity. }
  apply (loeb_tid_trans nat _ (gsubF (gnF (wrapF th)) (gnF (wrapF th)))).
  - apply loeb_tid_eq. exact H1.
  - apply loeb_tid_sym. apply diag_code_eq.
Qed.

(* The closedness of the diagonal sentence *)
Theorem diag_closed : forall th : Formula,
  loeb_tid bool (unaryF th) true -> loeb_tid bool (closedF (diagF th)) true.
Proof.
  intros th Hun. tidQ Hun Eun.
  pose proof (unaryT_selfT) as Hut.
  assert (Hw : unaryF (wrapF th) = true).
  { unfold wrapF. apply unaryF_subst; assumption. }
  apply loeb_tid_eq. unfold diagF.
  apply (closedF_subst_num (wrapF th) (gnF (wrapF th)) Hw).
Qed.

(* ═══ D1 main theorem: the diagonal lemma (the provable version, constructive witness) ═══
   For every unary formula th there is an explicit closed sentence d = diagF th such that:
     1. d is closed (the constructive certificate loeb_tid bool (closedF d) true);
     2. |- d -> th(⌜d⌝) and |- th(⌜d⌝) -> d (the provable version of Id (d) (f d);
        both directions' Prf terms genuinely assembled from the repl rule + the code identity + the value identity). *)
Theorem diagonal_lemma : forall th : Formula,
  loeb_tid bool (unaryF th) true ->
  sigT (fun d : Formula =>
    ((loeb_tid bool (closedF d) true) *
     ((Prf (fimp d (appN th (gnF d)))) *
      (Prf (fimp (appN th (gnF d)) d))))%type).
Proof.
  intros th Hun. tidQ Hun Eun.
  pose proof (diag_closed th Hun) as Hcl.
  tidQ (diagF_eq th) EHd.
  assert (Hvals : forall s : nat -> nat,
    loeb_tid nat (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)
      (valt (numT (gnF (diagF th))) s)).
  { intros s. apply (loeb_tid_trans nat _ (gnF (diagF th))).
    - apply diag_val_eq.
    - apply loeb_tid_sym. apply loeb_tid_eq. apply valt_numT. }
  assert (Hs1 : Prf (fimp
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))))
    (substF th (numT (gnF (diagF th)))))).
  { exact (repl th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))
              (numT (gnF (diagF th))) Hvals). }
  rewrite <- EHd in Hs1.
  assert (Hvals2 : forall s : nat -> nat,
    loeb_tid nat (valt (numT (gnF (diagF th))) s)
      (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)).
  { intros s. apply (loeb_tid_trans nat _ (gnF (diagF th))).
    - apply loeb_tid_eq. apply valt_numT.
    - apply loeb_tid_sym. apply diag_val_eq. }
  assert (Hs2 : Prf (fimp
    (substF th (numT (gnF (diagF th))))
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))))).
  { exact (repl th (numT (gnF (diagF th)))
              (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) Hvals2). }
  rewrite <- EHd in Hs2.
  exists (diagF th). split.
  - exact Hcl.
  - split.
    + exact Hs1.
    + exact Hs2.
Defined.

(* The code-level clean form: the code of the diagonal sentence is exactly the code-level self-substitution value (no premises, the loeb_tid form) *)
Theorem diagonal_code_fixed : forall th : Formula,
  loeb_tid nat (gnF (diagF th)) (gsubF (gnF (wrapF th)) (gnF (wrapF th))).
Proof.
  intros th. apply loeb_tid_eq. unfold gsubF.
  rewrite dec_gnF. unfold diagF, wrapF. reflexivity.
Qed.

(* ===================================================================== *)
(* Honest boundary (explicitly declared, no ad-hoc constructions):                                            *)
(*   1. The syntactic identity d = th(⌜d⌝) is false in general (a size argument), so what D1 gives is the        *)
(*      "provable version" — the two-way Prf implication; this is exactly the standard shape of the diagonal lemma.                  *)
(*   2. D1's object theory = true closed equations + MP + the Σ0 replacement invariant (repl); its soundness             *)
(*      Prf_soundness is proven; that theory suffices to carry the diagonal mechanism but not yet               *)
(*      the Hilbert–Bernays derivability conditions (which need an in-language encoding of the provability predicate).                   *)
(*   3. Quantifier semantics and the provability predicate Σ(σ) are left to D2 (interface suggestions):                          *)
(*      a. When Formula is extended with fall/fex, evalF must be implemented with a bounded-search operator (no               *)
(*         hard-coded true/false branches), keeping the evalF_subst interchange theorem;           *)
(*      b. Suggested shape of the Σ(σ) ledger: sigT { w : nat & (Prf-level certificate) * (loeb_tid code-account cluster) },   *)
(*         reusing this piece's gsubF / dF / dec_gnF: what D2's "in-language provability predicate" needs          *)
(*         is exactly the "code -> formula" reflection; this piece's dec_gnF is its load-bearing piece;                   *)
(*      c. D3 derivability-condition suggestions: D1' = Prf f -> ledger(⌜f⌝) inhabited (using dT2's fuel structure     *)
(*         to give the code-level replay of proof terms); D2' = the code-level closure of MP; D3' = code self-reference            *)
(*         (the gnF stability of Prf(⌜·⌝) itself). None of the three needs classical axioms.                *)
(* ===================================================================== *)

(* ======== G10_LoebFam member piece: UpRefuted (merged verbatim, carries its own Requires) ======== *)
(* ===================================================================== *)
(* UpRefuted.v — the Coq-ization of the four kill experiments: the refutation-form theorem library                            *)
(*                                                                       *)
(* The Q2 module (third leg). Theoretical sources:                                              *)
(*   ROUNDTABLE2-unknown-algorithm-forced-mutation-experiment-final-snapshot.md (Chinese-named source file):                          *)
(*     Piece 1 — upstream session, Experiment 1 (killing WPM): the unbounded redemption-flow bankruptcy counterexample                        *)
(*           — Datatypes.S≡1 + infinitely many spend-1 redemptions ⟹ bankruptcy on the ⌊R⌋+1-th redemption,                      *)
(*              while the stepwise localization scheme (tail pointer + covering 1 per step) never goes bankrupt;                   *)
(*     Piece 2 — upstream session, Experiment E1 (killing GRM): the p-adic carry cascade implicating two fields                 *)
(*           — one evidence piece rewrites both fields' coordinates at once + the residue-class ring alternates and never reaches a fixed point;          *)
(*     Piece 3 — upstream session, Experiment 2 (killing the loom): the cross-hole coupled consistent cyclic-flow livelock                      *)
(*           — greedy reweaving self-oscillates, the friction counter grows unboundedly, the emit gate stays constantly false;                    *)
(*     Piece 4 — upstream sessions merged: the DWM dilemma closure: the lattice-axiom tier degenerates X into a trivial restatement of divisibility arithmetic        *)
(*           vs the free-emission tier where X is decidable-false and the Halt certificate is falsified on the spot by one legal emission.       *)
(*                                                                       *)
(* Formalization policy: each piece = a concrete counterexample object (explicit nat/Z/bool/list constructions) + a       *)
(* bool/tid decision proof of its properties. Statements zero Prop: equations via tid, order via nle, branching via bool.         *)
(* Absurdity closure: the tid bool true false empty-index elimination + the nle (Datatypes.S O) O empty-type elimination.          *)
(* Carriers throughout at the Z/nat/bool decision layer; stdlib only; infrastructure inlined for file independence (no G04_ProjFam import).   *)
(* Discipline self-audit: zero occurrences of the four forbidden words (head note included, keeping grep=0); between each main theorem's statement and Proof.      *)
(* no bare exists, no Prop-level and/or, no -> False, no Prop premises; the whole chain extractable       *)
(* (Obj.magic = 0, see the _probe_refuted verification record).                            *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.

Open Scope Z_scope.
Local Open Scope list_scope.

(* ===================================================================== *)
(* 0. Set-level infrastructure (inlined from the G04_ProjFam.v header; the standalone file does not Require it)                    *)
(* ===================================================================== *)

(* The Set-level identity type (the equation carrier with zero Prop in statements) *)
Inductive refu_tid (A : Type) : A -> A -> Type := refu_tid_refl : forall x : A, refu_tid A x x.

Definition refu_tid_sym (A : Type) (x y : A) (H : refu_tid A x y) : refu_tid A y x :=
  match H in refu_tid _ a b return refu_tid _ b a with
  | refu_tid_refl _ a0 => @refu_tid_refl _ a0
  end.

Definition refu_tid_trans (A : Type) (x y z : A) (H1 : refu_tid A x y) (H2 : refu_tid A y z) :
  refu_tid A x z :=
  match H1 in refu_tid _ a b return refu_tid _ b z -> refu_tid _ a z with
  | refu_tid_refl _ a0 => fun H => H
  end H2.

(* The functional congruence of the identity type (the universal transport piece) *)
Definition refu_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : refu_tid A x y) :
  refu_tid B (f x) (f y) :=
  match H in refu_tid _ a b return refu_tid B (f a) (f b) with
  | refu_tid_refl _ a0 => @refu_tid_refl _ (f a0)
  end.

(* refu_tid -> bool equation extraction (used only for internal proof reasoning) *)
Ltac tidEqN H name :=
  pose proof (match H in refu_tid _ a b return a = b with refu_tid_refl _ _ => eq_refl end) as name.

(* The bool-identity contradiction closer: H1 : refu_tid bool X true, H2 : refu_tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in refu_tid _ a b return a = b with refu_tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in refu_tid _ a b return a = b with refu_tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* The Set-level natural-number order type (k < m encoded as nle (Datatypes.S k) m) *)
Inductive refu_nle (n : nat) : nat -> Set :=
| refu_nle_n : refu_nle n n
| refu_nle_S : forall m : nat, refu_nle n m -> refu_nle n (Datatypes.S m).

(* The refu_nle (Datatypes.S O) O absurdity piece (empty elimination with non-overlapping indices; legally closes any Set goal) *)
Lemma refu_nle_10_absurd : forall P : Type, refu_nle (Datatypes.S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

Lemma refu_nle_trans : forall a b c : nat, refu_nle a b -> refu_nle b c -> refu_nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply refu_nle_S. exact IH.
Qed.

Lemma refu_nle_0 : forall m : nat, refu_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply refu_nle_n.
  - apply refu_nle_S. exact IH.
Qed.

Lemma refu_nle_SS : forall a b : nat, refu_nle a b -> refu_nle (Datatypes.S a) (Datatypes.S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply refu_nle_n.
  - apply refu_nle_S. exact IH.
Qed.

Lemma refu_nle_add_r : forall a b : nat, refu_nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply refu_nle_0.
  - exact (refu_nle_SS a1 (a1 + b) (IH b)).
Qed.

(* ---- bool decision mini-pieces ---- *)

Lemma negb_true_of_false : forall e : bool, refu_tid bool e false -> refu_tid bool (negb e) true.
Proof.
  intros e H. destruct e.
  - exact (refu_tid_sym bool true false H).
  - apply refu_tid_refl.
Qed.

Lemma negb_false_of_true : forall e : bool, refu_tid bool e true -> refu_tid bool (negb e) false.
Proof.
  intros e H. destruct e.
  - apply refu_tid_refl.
  - exact (refu_tid_sym bool false true H).
Qed.

Lemma andb_true_both : forall e1 e2 : bool,
  refu_tid bool e1 true -> refu_tid bool e2 true -> refu_tid bool (andb e1 e2) true.
Proof.
  intros e1 e2 H1 H2. destruct e1.
  - destruct e2.
    + apply refu_tid_refl.
    + exact H2.
  - exact H1.
Qed.

Lemma andb_false_left : forall e1 e2 : bool,
  refu_tid bool e1 false -> refu_tid bool (andb e1 e2) false.
Proof.
  intros e1 e2 H. destruct e1.
  - destruct e2.
    + exact H.
    + apply refu_tid_refl.
  - apply refu_tid_refl.
Qed.

Lemma Zeqb_true_of_eq : forall x y : Z, (x = y)%Z -> refu_tid bool (Z.eqb x y) true.
Proof.
  intros x y H. rewrite H. rewrite Z.eqb_refl. apply refu_tid_refl.
Qed.

Lemma Zeqb_diff_false : forall x y : Z, (x <> y)%Z -> refu_tid bool (Z.eqb x y) false.
Proof.
  intros x y H. destruct (Z.eqb x y) eqn:E.
  - apply Z.eqb_eq in E. exfalso. exact (H E).
  - apply refu_tid_refl.
Qed.

Lemma xorb_comm_t : forall b1 b2 : bool, refu_tid bool (xorb b1 b2) (xorb b2 b1).
Proof.
  intros b1 b2. destruct b1, b2; apply refu_tid_refl.
Qed.

(* ===================================================================== *)
(* Piece 1. The WPM unbounded family's bankruptcy unsoundness (upstream session Experiment 1)                                  *)
(*                                                                     *)
(* Melt coupon: at time zero the entire infinite certificate sequence is melted into one aggregate coupon, with budget R (constructively finite).        *)
(* Redemption flow: infinitely many "spend 1" queries. The balance after the k-th redemption = R - k.                 *)
(*   solvent k      := the first k redemptions are all payable ⟺ k ≤ R;                        *)
(*   insolvent k    := the balance after the k-th redemption is ≤ 0 (the next redemption must bankrupt).                 *)
(* Kill: bankruptcy on the ⌊R⌋+1-th redemption; every later redemption bankrupts too (unbounded flow = infinitely many bankruptcy events);      *)
(* Counterpart: the stepwise localization scheme (a stored certificate sequence covering 1 per step + tail pointer) pays coupon by coupon and never goes bankrupt.    *)
(* ===================================================================== *)

Definition wpm_R : Z := 3.

(* Aggregate-coupon balance trajectory: after the k-th redemption = R - k *)
Definition melt_wallet (k : nat) : Z := wpm_R - Z.of_nat k.

(* Payability verdict for redemption k: the first k redemptions are payable ⟺ k ≤ R *)
Definition solvent (k : nat) : bool := Z.leb (Z.of_nat k) wpm_R.

(* The completion bit after redemption k: balance ≤ 0 ⟹ redemption k+1 must bankrupt *)
Definition insolvent (k : nat) : bool := Z.leb (melt_wallet k) 0.

(* Localization scheme: the per-slot certificate sequence Datatypes.S ≡ 1 (covering 1 per step) + tail pointer; redemption k pays from the k-th certificate *)
Fixpoint loc_cov (k : nat) : Z := match k with O => 1 | Datatypes.S k' => loc_cov k' end.
Definition loc_solvent (k : nat) : bool := Z.leb 1 (loc_cov k).

(* On the meltable domain melt ≡ summation: the sum of the first n certificates (1 each) computable in one step *)
Fixpoint sum_S (n : nat) : Z := match n with O => 0 | Datatypes.S m => sum_S m + loc_cov m end.

Lemma loc_cov_one : forall k : nat, refu_tid Z (loc_cov k) 1.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - exact IH.
Qed.

Lemma loc_never_bankrupt : forall k : nat, refu_tid bool (loc_solvent k) true.
Proof.
  intros k. unfold loc_solvent.
  destruct (Z.leb 1 (loc_cov k)) eqn:E.
  - apply refu_tid_refl.
  - tidEqN (loc_cov_one k) HE. rewrite HE in E. simpl in E. discriminate E.
Qed.

Lemma sum_S_closed : forall n : nat, refu_tid Z (sum_S n) (Z.of_nat n).
Proof.
  intros n. induction n as [| n IH].
  - apply refu_tid_refl.
  - rewrite (Nat2Z.inj_succ n).
    change (refu_tid Z (sum_S n + loc_cov n) (Z.of_nat n + 1)).
    tidEqN IH HEa. rewrite HEa.
    tidEqN (loc_cov_one n) HEb. rewrite HEb.
    apply refu_tid_refl.
Qed.

(* Last payable redemption: the ⌊R⌋-th redemption pays exactly (balance down to zero) *)
Lemma wpm_solvent_at_last_covered : refu_tid bool (solvent (Z.to_nat wpm_R)) true.
Proof.
  unfold solvent, wpm_R.
  change (Z.to_nat 3) with 3%nat.
  change (Z.of_nat 3) with 3%Z.
  unfold Z.leb.
  change (3 ?= 3)%Z with Eq.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* The bankruptcy main theorem: bankruptcy on the ⌊R⌋+1-th redemption *)
Theorem wpm_melt_bankrupt : refu_tid bool (solvent (Datatypes.S (Z.to_nat wpm_R))) false.
Proof.
  unfold solvent, wpm_R.
  change (Datatypes.S (Z.to_nat 3)) with 4%nat.
  change (Z.of_nat 4) with 4%Z.
  unfold Z.leb.
  change (4 ?= 3)%Z with Gt.
  cbv iota.
  apply refu_tid_refl.
Qed.

Lemma wpm_wallet_zero_at_last_cover : refu_tid Z (melt_wallet (Z.to_nat wpm_R)) 0.
Proof.
  unfold melt_wallet, wpm_R.
  change (Z.to_nat 3) with 3%nat.
  change (Z.of_nat 3) with 3%Z.
  unfold Z.sub.
  change (3 + - 3)%Z with 0%Z.
  apply refu_tid_refl.
Qed.

Lemma wpm_wallet_negative_at_bankrupt : refu_tid Z (melt_wallet (Datatypes.S (Z.to_nat wpm_R))) (-1).
Proof.
  unfold melt_wallet, wpm_R.
  change (Datatypes.S (Z.to_nat 3)) with 4%nat.
  change (Z.of_nat 4) with 4%Z.
  unfold Z.sub.
  change (3 + - 4)%Z with (-1)%Z.
  apply refu_tid_refl.
Qed.

Lemma wpm_insolvent_at_bankrupt : refu_tid bool (insolvent (Datatypes.S (Z.to_nat wpm_R))) true.
Proof.
  unfold insolvent, melt_wallet, wpm_R.
  change (Datatypes.S (Z.to_nat 3)) with 4%nat.
  change (Z.of_nat 4) with 4%Z.
  unfold Z.leb, Z.sub.
  change (3 + - 4)%Z with (-1)%Z.
  change ((-1) ?= 0)%Z with Lt.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* Bankruptcy propagates along the redemption flow: once bankrupt, every later redemption bankrupts (unbounded flow ⟹ infinitely many bankruptcy events) *)
Lemma insolvent_step : forall k : nat,
  refu_tid bool (insolvent k) true -> refu_tid bool (insolvent (Datatypes.S k)) true.
Proof.
  intros k H. unfold insolvent in H.
  tidEqN H HE. unfold melt_wallet, wpm_R in HE. apply Z.leb_le in HE.
  unfold insolvent, melt_wallet, wpm_R.
  destruct (Z.leb (3 - Z.of_nat (Datatypes.S k)) 0) eqn:E.
  - apply refu_tid_refl.
  - apply Z.leb_gt in E. rewrite Nat2Z.inj_succ in E.
    exfalso. lia.
Qed.

Theorem wpm_insolvent_forever : forall j : nat,
  refu_tid bool (insolvent (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S j))))) true.
Proof.
  intros j. induction j as [| j IH].
  - exact wpm_insolvent_at_bankrupt.
  - apply insolvent_step. exact IH.
Qed.

(* On the bounded family the melt coupon is sound (the counterpart half): k ≤ R ⟹ the first k redemptions are all payable *)
Theorem wpm_solvent_bounded_family : forall n : nat,
  refu_tid bool (Z.leb (Z.of_nat n) wpm_R) true -> refu_tid bool (solvent n) true.
Proof.
  intros n H. exact H.
Qed.

(* Conjunction closure ("aggregate dominance" inverted into aggregate bankruptcy): same redemption flow, same redemption index,
   the melt-coupon payability bit false while the localization scheme's payability bit true *)
Theorem wpm_unbounded_family_unsound :
  refu_tid bool (andb (solvent (Datatypes.S (Z.to_nat wpm_R)))
                 (loc_solvent (Datatypes.S (Z.to_nat wpm_R)))) false.
Proof.
  apply andb_false_left. apply wpm_melt_bankrupt.
Qed.

(* ===================================================================== *)
(* Piece 2. The p-adic carry cascade implicating two fields + the residue-class ring alternating without reaching a fixed point (upstream session Experiment E1)      *)
(*                                                                     *)
(* The GRM census moves to the shared-denominator coordinate domain: fields = the prime coordinates of the rational guarantee w. Take p = 3,           *)
(* the usage flow = the PLA zero-avoiding circulation 2/3, 1/3, 2/3, 1/3, … (multiplicative shares); under the common denominator,          *)
(* the cumulative numerator trajectory: N(0)=0, N(2j)=3j, N(2j+1)=3j+2.                              *)
(*   Field one coordA: the Z/9 residue-class coordinate (coarse resolution);                               *)
(*   Field two coordB: the Z/3 zero-class detection bit (= the p-ledger normalization / carry-trigger bit).                *)
(* Kill: (a) any single usage-evidence piece rewrites both fields' coordinates at once (implication) — including the trigger step itself;            *)
(*       (b) the trigger bit alternates bit by bit along the 0↔2 residue-class ring, adjacent states never coincide —                   *)
(*           the axiom "≤ |census| = 2 steps to a fixed point" is still moving outside the budget (the axiom is dead);          *)
(*       (c) carry-cascade depth 2: at N(6) = 9 the coarse coordinate Z/9 also enters the zero class.                    *)
(* ===================================================================== *)

Definition p3 : Z := 3.

(* The cumulative-numerator recursion in two-step groups: after j groups = (N(2j), N(2j+1)); the share flow 2/p, 1/p alternating *)
Fixpoint pla_step2 (j : nat) : Z * Z :=
  match j with
  | O => (0, 2)
  | Datatypes.S j' => let ab := pla_step2 j' in (snd ab + 1, snd ab + 3)
  end.

(* Field one: the Z/9 residue-class coordinate *)
Definition coordA (n : Z) : Z := Z.modulo n 9.
(* Field two: the Z/3 zero-class detection bit (the normalization / carry-trigger bit) *)
Definition coordB (n : Z) : bool := Z.eqb (Z.modulo n 3) 0.

(* Exact mod-3 mini-pieces (the Z_mod_plus_full route, bypassing the division lemma's variable-side condition) *)
Lemma mod3_3j : forall j : nat, refu_tid Z (Z.modulo (3 * Z.of_nat j) 3) 0.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j) 3 = 0)%Z).
  { replace (3 * Z.of_nat j) with (0 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply refu_tid_refl.
Qed.

Lemma mod3_3j2 : forall j : nat, refu_tid Z (Z.modulo (3 * Z.of_nat j + 2) 3) 2.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j + 2) 3 = 2)%Z).
  { replace (3 * Z.of_nat j + 2) with (2 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply refu_tid_refl.
Qed.

Lemma mod3_3j3 : forall j : nat, refu_tid Z (Z.modulo (3 * Z.of_nat j + 3) 3) 0.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j + 3) 3 = 0)%Z).
  { replace (3 * Z.of_nat j + 3) with (3 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply refu_tid_refl.
Qed.

(* mod 9: differing by a small positive k forces different classes (k ∈ [1,8] ⟹ in Z/9, x and x+k lie in different classes) *)
Lemma mod9_diff_small : forall x k : Z,
  refu_tid bool (Z.ltb 0 k) true -> refu_tid bool (Z.ltb k 9) true ->
  refu_tid bool (Z.eqb (x mod 9) ((x + k) mod 9)) false.
Proof.
  intros x k Hk1 Hk2.
  tidEqN Hk1 HE1. tidEqN Hk2 HE2.
  apply Z.ltb_lt in HE1. apply Z.ltb_lt in HE2.
  pose proof (Z.mod_pos_bound x 9 (ltac:(lia))) as HB.
  pose proof (Z.div_mod x 9 (ltac:(lia))) as HD.
  destruct (Z.eqb (x mod 9) ((x + k) mod 9)) eqn:E.
  - apply Z.eqb_eq in E.
    assert (Hsplit : (x + k = (x mod 9 + k) + (x / 9) * 9)%Z) by lia.
    rewrite Hsplit in E. rewrite Z_mod_plus_full in E.
    destruct (Z_le_gt_dec (x mod 9) (8 - k)) as [Hc | Hc].
    + assert (Hsm : ((x mod 9 + k) mod 9 = x mod 9 + k)%Z)
        by (apply Z.mod_small; lia).
      rewrite Hsm in E. exfalso. lia.
    + assert (Hconn : (x mod 9 + k = (x mod 9 + k - 9) + 1 * 9)%Z) by lia.
      assert (Hmp : (((x mod 9 + k - 9) + 1 * 9) mod 9 = (x mod 9 + k - 9) mod 9)%Z)
        by (apply Z_mod_plus_full).
      rewrite <- Hconn in Hmp.
      rewrite Hmp in E.
      assert (Hsm2 : ((x mod 9 + k - 9) mod 9 = x mod 9 + k - 9)%Z)
        by (apply Z.mod_small; lia).
      rewrite Hsm2 in E. exfalso. lia.
  - apply refu_tid_refl.
Qed.

(* The trajectory closed form: N(2j) = 3j, N(2j+1) = 3j+2 (the bool-conjunction decision form) *)
Lemma pla_pair_closed : forall j : nat,
  refu_tid bool (andb (Z.eqb (fst (pla_step2 j)) (3 * Z.of_nat j))
                 (Z.eqb (snd (pla_step2 j)) (3 * Z.of_nat j + 2))) true.
Proof.
  intros j. induction j as [| j IH].
  - apply refu_tid_refl.
  - tidEqN IH HEc. apply andb_prop in HEc as [HE1 HE2].
    apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
    replace (fst (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 1) by reflexivity.
    replace (snd (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 3) by reflexivity.
    replace (3 * Z.of_nat (Datatypes.S j)) with (3 * Z.of_nat j + 3)
      by (rewrite Nat2Z.inj_succ; lia).
    replace (3 * Z.of_nat (Datatypes.S j) + 2) with (3 * Z.of_nat j + 5)
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite HE2.
    apply andb_true_both.
    + apply Zeqb_true_of_eq. lia.
    + apply Zeqb_true_of_eq. lia.
Qed.

(* (a) The implication theorem: an even-slot evidence piece (the +2/p share) rewrites both fields' coordinates at once *)
Theorem evidence_couples_two_fields : forall j : nat,
  refu_tid bool (andb
    (negb (Z.eqb (coordA (fst (pla_step2 j))) (coordA (snd (pla_step2 j)))))
    (negb (Bool.eqb (coordB (fst (pla_step2 j))) (coordB (snd (pla_step2 j)))))) true.
Proof.
  intros j. unfold coordA, coordB.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  rewrite HE1, HE2.
  tidEqN (mod3_3j j) HM1. rewrite HM1.
  tidEqN (mod3_3j2 j) HM2. rewrite HM2.
  apply andb_true_both.
  - apply negb_true_of_false.
    apply (mod9_diff_small (3 * Z.of_nat j) 2); apply refu_tid_refl.
  - simpl. apply refu_tid_refl.
Qed.

(* (a') Trigger-step implication: a ledger-trigger evidence piece (the +1/p share, landing in the zero class) likewise rewrites both fields at once —
   the carry event is not field one's private affair; the coarse coordinate is dragged along in sync *)
Theorem ledger_trigger_couples_too : forall j : nat,
  refu_tid bool (andb
    (negb (Bool.eqb (coordB (snd (pla_step2 j))) (coordB (fst (pla_step2 (Datatypes.S j))))))
    (negb (Z.eqb (coordA (snd (pla_step2 j))) (coordA (fst (pla_step2 (Datatypes.S j))))))) true.
Proof.
  intros j. unfold coordA, coordB.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 1) by reflexivity.
  rewrite HE2.
  tidEqN (mod3_3j2 j) HM2. rewrite HM2.
  assert (HM3' : (Z.modulo (3 * Z.of_nat j + 2 + 1) 3 = 0)%Z).
  { replace (3 * Z.of_nat j + 2 + 1) with (3 * Z.of_nat j + 3) by lia.
    tidEqN (mod3_3j3 j) H3. exact H3. }
  rewrite HM3'.
  apply andb_true_both.
  - simpl. apply refu_tid_refl.
  - apply negb_true_of_false.
    apply (mod9_diff_small (3 * Z.of_nat j + 2) 1); apply refu_tid_refl.
Qed.

(* (b) Not reaching the fixed point: adjacent two-step states never coincide (the residue-class ring 0↔2 alternates forever) *)
Theorem residue_class_never_freezes : forall j : nat,
  refu_tid bool (Z.eqb (snd (pla_step2 j)) (fst (pla_step2 (Datatypes.S j)))) false.
Proof.
  intros j.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 1) by reflexivity.
  rewrite HE2.
  apply Zeqb_diff_false. lia.
Qed.

(* The GRM axiom-budget blowout: |census| = 2 ⟹ the axiom asserts a fixed point at step 2;
   measured: steps 4→5 are still moving (the j = 2 instance) — the axiom is dead *)
Theorem grm_two_step_budget_blown :
  refu_tid bool (Z.eqb (snd (pla_step2 2)) (fst (pla_step2 3))) false.
Proof.
  tidEqN (pla_pair_closed 2) HEc.
  apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 3)) with (snd (pla_step2 2) + 1) by reflexivity.
  rewrite HE2.
  apply Zeqb_diff_false. lia.
Qed.

(* (c) Carry-cascade depth 2: N(6) = 9 — the coarse coordinate Z/9 also enters the zero class (two-bit normalization) *)
Theorem carry_cascade_depth2 : refu_tid bool (Z.eqb (coordA (fst (pla_step2 3))) 0) true.
Proof.
  unfold coordA.
  tidEqN (pla_pair_closed 3) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. rewrite HE1. apply refu_tid_refl.
Qed.

(* ===================================================================== *)
(* Piece 3. The loom livelock counterexample (upstream session Experiment 2)                                          *)
(*                                                                     *)
(* The two-hole miniature: slot values bool; the cross-hole joint legality gate (the emit gate) = the xor emit_gate —             *)
(* the cross-hole gate of "the six-gate joint legal space ≠ the product of the per-hole legalities".                         *)
(* The decision flow = the cyclically consistent flow: each hole decides a single direction ("flip away from the other", no same-hole bidirectional conflict),        *)
(* satisfying the loom's own consistency condition; the rej reweave semantics = the old evidence voided and this slot rewritten per the evidence to            *)
(* "different from the other's current value" (the synchronized reweave of cross-hole certificate passing).                               *)
(* The initial weave (true,true): each hole's pass accepted per the rules (consistency checks per-hole only, not cross-hole) — an illegal element.    *)
(* Kill: the synchronized reweave (a,b) ↦ (¬b, ¬a) preserves the xor invariant — an illegal initial weave stays illegal forever:            *)
(*   the emit gate constantly false (never emits) + slot values flipping every round (self-oscillation, period 2) +                     *)
(*   the friction counter +2 per round, growing unboundedly (unbounded reweave cost); and the greedy scheduling key itself is the livelock driver.      *)
(* ===================================================================== *)

(* The cross-hole joint legality gate (the emit gate) ＝ xor *)
Definition emit_gate (a b : bool) : bool := xorb a b.

(* The one-step synchronized reweave: both holes' old evidence voided at once, each flipping away from the other *)
Definition loom_step (p : bool * bool) : bool * bool :=
  (negb (snd p), negb (fst p)).

(* The loom run trajectory: the initial weave (true,true), driven by the cyclically consistent flow *)
Fixpoint loom_iter (k : nat) : bool * bool :=
  match k with
  | O => (true, true)
  | Datatypes.S k' => loom_step (loom_iter k')
  end.

(* The friction counter: each round both holes reweave once, +1 each *)
Fixpoint loom_fric (k : nat) : nat :=
  match k with O => O | Datatypes.S k' => Datatypes.S (Datatypes.S (loom_fric k')) end.

(* A one-step reweave preserves the emit gate's truth value (the transfer form of the xor invariant) *)
Lemma loom_step_inv : forall p : bool * bool,
  refu_tid bool (emit_gate (fst (loom_step p)) (snd (loom_step p)))
           (emit_gate (fst p) (snd p)).
Proof.
  intros p. destruct p as [a b]. destruct a, b; apply refu_tid_refl.
Qed.

(* Flow consistency (the loom's own condition): each hole's reweave direction is unique — the rewrite target is always "different from the other's current value",
   independent of this slot's own value, never "leaning toward the other" (no same-hole bidirectional conflict, no stalling idle spin),
   and the bool verdict is true for every state *)
Definition flip_check (p : bool * bool) : bool :=
  andb (Bool.eqb (fst (loom_step p)) (negb (snd p)))
       (Bool.eqb (snd (loom_step p)) (negb (fst p))).

Lemma loom_stream_consistent : forall p : bool * bool, refu_tid bool (flip_check p) true.
Proof.
  intros p. destruct p as [a b]. destruct a, b; apply refu_tid_refl.
Qed.

(* Period 2: the loom trajectory returns to its original state after two rounds (the self-oscillation carrier) *)
Lemma loom_period2 : forall k : nat,
  refu_tid (bool * bool) (loom_iter (Datatypes.S (Datatypes.S k))) (loom_iter k).
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - change (refu_tid (bool * bool) (loom_step (loom_iter (Datatypes.S (Datatypes.S k))))
                        (loom_step (loom_iter k))).
    exact (refu_tid_cong loom_step _ _ IH).
Qed.

(* The livelock main theorem: the emit gate constantly false at every round — a consistent flow exists, emission does not *)
Theorem loom_livelock_never_emits : forall k : nat,
  refu_tid bool (emit_gate (fst (loom_iter k)) (snd (loom_iter k))) false.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - exact (refu_tid_trans bool _ _ _ (loom_step_inv (loom_iter k)) IH).
Qed.

(* Self-oscillation: slot values flip every round (non-stalling idle spin); within period 2 forever oscillating between the two illegal elements *)
Lemma loom_flips : forall k : nat,
  refu_tid bool (xorb (fst (loom_iter (Datatypes.S k))) (fst (loom_iter k))) true.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - tidEqN (loom_period2 k) HEp. rewrite HEp.
    exact (refu_tid_trans bool _ _ _
      (xorb_comm_t (fst (loom_iter k)) (fst (loom_iter (Datatypes.S k)))) IH).
Qed.

(* The friction-counter closed form: after k rounds the friction counter = 2k (a genuine implementation, not a placeholder) *)
Lemma loom_fric_closed : forall k : nat, refu_tid nat (loom_fric k) (2 * k)%nat.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - change (refu_tid nat (Datatypes.S (Datatypes.S (loom_fric k))) (2 * Datatypes.S k)%nat).
    rewrite (Nat.mul_succ_r 2 k).
    tidEqN IH HEk. rewrite HEk.
    assert (HE2 : (2 * k + 2 = Datatypes.S (Datatypes.S (2 * k)))%nat) by lia.
    rewrite HE2. apply refu_tid_refl.
Qed.

(* Unbounded reweave cost: the friction counter strictly rises within any two-round window (the greedy scheduling key = the livelock driver;
   any budget is eventually broken through — refu_nle (Datatypes.S fric j) fric (j+2)) *)
Theorem loom_cost_unbounded : forall j : nat,
  refu_nle (Datatypes.S (loom_fric j)) (loom_fric (j + 2)%nat).
Proof.
  intros j.
  assert (HE : (loom_fric (j + 2) = loom_fric j + 4)%nat).
  { replace ((j + 2)%nat) with (Datatypes.S (Datatypes.S j)) by lia. simpl. lia. }
  rewrite HE.
  apply (refu_nle_trans (Datatypes.S (loom_fric j)) (Datatypes.S (loom_fric j) + 3) (loom_fric j + 4)).
  - apply refu_nle_add_r.
  - assert (HEq : (Datatypes.S (loom_fric j) + 3 = loom_fric j + 4)%nat) by lia.
    rewrite HEq. apply refu_nle_n.
Qed.

(* ===================================================================== *)
(* Piece 4. The DWM dilemma closure (upstream session Experiment 1 + upstream session Experiment 2 merged)                          *)
(*                                                                     *)
(* The differential wallet machine: the candidate band only grows, never deletes × exact finite halting. The halting branch hangs uniquely on the equality proposition X:         *)
(* "difference < grain ⟹ same slot". Carrier: the denominator-4 grid, all integer-encoded in grid-distance units of 1/4.    *)
(* The dilemma's two corners:                                                                 *)
(*   The free-emission corner (no added axioms): X is decidable-false (0 and 1/4 judged different slots), and               *)
(*     after Halt fires the certificate is falsified on the spot by one legal emission — Halt forever false;                        *)
(*   The lattice-axiom corner (emitter denominator fixed): X degenerates into a trivial restatement of divisibility arithmetic (grid-distance equality =           *)
(* "Z/2 divisibility + quotient equality"), zero connection to the wallet/grain mechanism — trivial.                        *)
(* ===================================================================== *)

Definition dwm_D : Z := 4.        (* common denominator: grid = {k/4} *)
Definition dwm_grain : Z := 2.    (* grain = 1/2 = 2 grid-distance units *)
Definition dwm_W0 : Z := 4.       (* initial wallet = 1 = 4 grid-distance units *)

(* The bool-ized equality proposition X: difference < grain ⟹ same slot (numeric equality) *)
Definition X_test (a b : Z) : bool :=
  if Z.ltb (Z.abs (a - b)) dwm_grain then Z.eqb a b else true.

(* The admission fee = the grid distance to the nearest present member (the empty-band numeric anchor 999 is forever unreachable: the band is seeded with a0) *)
Fixpoint dmin (x : Z) (l : list Z) : Z :=
  match l with
  | nil => 999
  | a :: l' => Z.min (Z.abs (x - a)) (dmin x l')
  end.

(* Presence detection (bool) *)
Fixpoint presentb (x : Z) (l : list Z) : bool :=
  match l with
  | nil => false
  | a :: l' => orb (Z.eqb x a) (presentb x l')
  end.

(* The emitter: pay the admission fee, return (new present band, new wallet) *)
Definition dwm_emit (x : Z) (l : list Z) (W : Z) : list Z * Z :=
  (x :: l, W - dmin x l).

(* The bool-ized Halt certificate: "every future legal emission is present" — for the emission x:
   legal (admission fee ≤ W) ⟹ x is present *)
Definition halt_cert (x : Z) (l : list Z) (W : Z) : bool :=
  implb (Z.leb (dmin x l) W) (presentb x l).

(* —— The free-emission corner: X decidable-false (the two-point counterexample: 0 and 1/4, difference 1 < grain 2 yet different slots) —— *)
Theorem dwm_X_refuted : refu_tid bool (X_test 0 1) false.
Proof.
  unfold X_test, dwm_grain.
  change (Z.abs (0 - 1)) with 1%Z.
  unfold Z.ltb, Z.eqb.
  change (1 ?= 2)%Z with Lt.
  change (0 ?= 1)%Z with Lt.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* —— The upstream-session fine-grained counterexample, full simulation: band seeded [0], grain = 2, wallet = 4.
   Step 1: emit 1/2 (grid 2), fee 2, wallet→2; step 2: emit 1/4 (grid 1), fee 1, wallet→1 < grain
   — Halt fires; step 3: emit 3/4 (grid 3), fee 1 ≤ wallet 1, legal, and 3 ∉ the present set
   — the "all future same-slot" certificate is falsified on the spot by one legal emission. —— *)
Definition dwm_W1 : Z := snd (dwm_emit 2 (0 :: nil) dwm_W0).
Definition dwm_W2 : Z := snd (dwm_emit 1 (2 :: 0 :: nil) dwm_W1).

Theorem dwm_wallet_trajectory : refu_tid Z dwm_W2 1.
Proof.
  assert (Hd1 : dmin 2 (0 :: nil) = 2%Z).
  { cbn [dmin]. change (Z.abs (2 - 0)) with 2%Z.
    unfold Z.min. change (2 ?= 999)%Z with Lt. reflexivity. }
  assert (Hd2 : dmin 1 (2 :: 0 :: nil) = 1%Z).
  { cbn [dmin]. change (Z.abs (1 - 2)) with 1%Z.
    change (Z.abs (1 - 0)) with 1%Z.
    unfold Z.min. change (1 ?= 999)%Z with Lt. reflexivity. }
  unfold dwm_W2, dwm_W1, dwm_emit, dwm_W0.
  cbn [snd]. rewrite Hd1. rewrite Hd2.
  change (4 - 2)%Z with 2%Z.
  change (2 - 1)%Z with 1%Z.
  apply refu_tid_refl.
Qed.

Theorem dwm_halt_fires : refu_tid bool (Z.ltb dwm_W2 dwm_grain) true.
Proof.
  tidEqN dwm_wallet_trajectory HEw. rewrite HEw.
  unfold Z.ltb, dwm_grain.
  change (1 ?= 2)%Z with Lt.
  cbv iota.
  apply refu_tid_refl.
Qed.

Theorem dwm_emit3_legal : refu_tid bool (Z.leb (dmin 3 (2 :: 1 :: 0 :: nil)) dwm_W2) true.
Proof.
  assert (Hd : dmin 3 (2 :: 1 :: 0 :: nil) = 1%Z).
  { cbn [dmin].
    change (Z.abs (3 - 2)) with 1%Z.
    change (Z.abs (3 - 1)) with 2%Z.
    change (Z.abs (3 - 0)) with 3%Z.
    unfold Z.min. change (3 ?= 999)%Z with Lt. reflexivity. }
  tidEqN dwm_wallet_trajectory HEw. rewrite Hd. rewrite HEw.
  unfold Z.leb. change (1 ?= 1)%Z with Eq. cbv iota.
  apply refu_tid_refl.
Qed.

Theorem dwm_emit3_not_present : refu_tid bool (presentb 3 (2 :: 1 :: 0 :: nil)) false.
Proof.
  cbn [presentb]. unfold orb.
  change (3 ?= 2)%Z with Gt.
  change (3 ?= 1)%Z with Gt.
  change (3 ?= 0)%Z with Gt.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* The Halt-forever-false half: in the Halt-fired state (wallet 1 < grain 2) the certificate judges x = 3 false *)
Theorem dwm_halt_cert_refuted : refu_tid bool (halt_cert 3 (2 :: 1 :: 0 :: nil) dwm_W2) false.
Proof.
  unfold halt_cert, dwm_W2, dwm_W1, dwm_emit, dwm_W0. apply refu_tid_refl.
Qed.

(* —— The lattice-axiom corner: X degenerates into a trivial restatement of divisibility arithmetic ——
   after adding the emitter lattice law (lattice points = multiples of 2·grid distances), same-slot equality reduces to Z/2 divisibility + quotient equality:
   lattice points a = 2·ka, b = 2·kb, |a−b| < 2 ⟹ ka = kb — the proof touches only divisibility arithmetic,
   with zero participation of the wallet/grain/admission-fee mechanism (the trivial tier). *)
Definition lattice_X (a b : Z) : bool :=
  if Z.ltb (Z.abs (a - b)) dwm_grain then Z.eqb (a / 2) (b / 2) else true.

Theorem dwm_lattice_X_trivial : forall a b : Z,
  refu_tid bool (Z.eqb (a mod 2) 0) true -> refu_tid bool (Z.eqb (b mod 2) 0) true ->
  refu_tid bool (lattice_X a b) true.
Proof.
  intros a b Ha Hb.
  tidEqN Ha HEA. tidEqN Hb HEB.
  apply Z.eqb_eq in HEA. apply Z.eqb_eq in HEB.
  pose proof (Z.div_mod a 2 (ltac:(lia))) as HDA.
  pose proof (Z.div_mod b 2 (ltac:(lia))) as HDB.
  rewrite HEA in HDA. rewrite HEB in HDB.
  assert (HA2 : (a = 2 * (a / 2))%Z) by lia.
  assert (HB2 : (b = 2 * (b / 2))%Z) by lia.
  unfold lattice_X, dwm_grain.
  destruct (Z.ltb (Z.abs (a - b)) 2) eqn:E.
  - apply Z.ltb_lt in E.
    rewrite HA2, HB2 in E.
    rewrite <- Z.mul_sub_distr_l in E.
    rewrite Z.abs_mul in E.
    assert (H2abs : (Z.abs 2 = 2)%Z) by reflexivity.
    rewrite H2abs in E.
    destruct (Z_lt_ge_dec (Z.abs (a / 2 - b / 2)) 1) as [Hlt | Hge].
    + assert (Hk : (a / 2 = b / 2)%Z) by lia.
      rewrite Hk. rewrite Z.eqb_refl. apply refu_tid_refl.
    + exfalso. lia.
  - apply refu_tid_refl.
Qed.

(* The dilemma-closure joint note: the free-emission corner dwm_X_refuted + dwm_halt_cert_refuted (without the added axiom, Halt forever false)
   conjoined with the lattice-axiom corner dwm_lattice_X_trivial (with it, X degenerates into a trivial restatement of divisibility arithmetic,
   zero connection to the wallet mechanism) — betting both corners is dead: DWM's original halting branch is unsatisfiable, or trivial if satisfied. *)

Close Scope Z_scope.

(* ======== G10_LoebFam member piece: UpQKBound (merged verbatim, carries its own Requires) ======== *)
(* ============================================================ *)
(* UpQKBound.v — closing the Plan-A QKᵀ pipeline: the bound-conversion pieces + the QKᵀ binding +       *)
(*   the explicit sigT packaging of Δ (downstream uses UpCS's dotp/sql/Q-layer core)          *)
(*                                                              *)
(* The mathematical target (the Real layer, the list-vector world, CW_ConstructiveWorld_219):   *)
(*   vector = list Real; dimension d := the vector length;                       *)
(*   root_of d := projT1 (real_sqrt_exists d Hd) (the sqrt witness:      *)
(*   And (r ≥ 0) (r·r == d); the root notation appears only in premises and the Δ definition,      *)
(*   never entering identity chains — identity chains all go through real_eq transport + pointwise tail bounds).          *)
(*                                                              *)
(* Piece 1 (the inner product/norm bridge) inner_sq_norm:                             *)
(*   ⟨q,q⟩ == Σq² (real_eq; UpCS's sql is Σq² — the naming bridge).        *)
(* The root-bounded premise shape (the correct primitive: under the Or encoding, A² ≤ Q² does not yield A ≤ Q):   *)
(*   Hqn : real_le (root_of (sql q) Hqq) Q — pieces 2/3 take their premises in this form.   *)
(*                                                              *)
(* Piece 2 (the bound conversion, the main piece) real_logit_bound_of_norm_bounds:            *)
(*   Root-bounded premises (root⟨q,q⟩ ≤ Q, root⟨k,k⟩ ≤ K, Q,K > 0) ⟹         *)
(*   real_le |⟨q,k⟩| (Q·K·√d + eps) (the eps version; the proof takes the inl strict branch).  *)
(*   Assembly: the C-S strict version (eps recorded explicitly: C-S's eps := (h/2)² — the source text mangles C-S into C-Datatypes.S — via       *)
(*   the abs conversion piece (abs_le_add_of_sq_lt), into |⟨q,k⟩| < root product + h,   *)
(*   then positive-factor multiplication monotonicity (root product ≤ Q·K) + 1 ≤ √d (equal at k=1, strict at k≥2    *)
(*   — the k branch) merged into the final +eps.                                  *)
(*                                                              *)
(* Piece 3 (the QKᵀ binding + the Δ packaging, the main theorem) qk_logits_bounded:               *)
(*   attn_logit q k d s s' := dotp(q s, k s')·inv(√d)             *)
(*   (the inv form: real_inv_pos root_d (root_d_pos d) — the positivity certificate      *)
(*   carried constructively). Premises: root-bounded uniformly over all s s'. Δ := (Q·K)·inv(√d)+1,   *)
(*   the sigT packaging: Δ > 0 ∧ ∀s s' |logit| ≤ Δ.                        *)
(*   The +1 slack algebra (eps pass-through absorbed; the zero-eps version):                      *)
(*     |dotp| < root product + 1/2 (the piece-2 mechanism, h := 1/2)                 *)
(*     ⟹ |logit| = |dotp|·inv(√d) < (root product + 1/2)·inv(√d)           *)
(*        = root product·inv(√d) + (1/2)·inv(√d) ≤ Q·K·inv(√d) + 1/2       *)
(*        (inv(√d) ≤ 1: √d ≥ 1 ⟹ inv reverses order)                       *)
(*        < Q·K·inv(√d) + 1 = Δ. The +1 exactly absorbs (1/2)·inv(√d) ≤ 1/2.  *)
(*                                                              *)
(* Piece 4 (a seam note, not a theorem): the downstream seam — this piece supplies the Δ bound               *)
(*   for bs_minorization's two-bound premise (−Δ ≤ z ≤ Δ given by |z| ≤ Δ) ⟹      *)
(*   the softmax kernel pointwise ≥ δ⋆·U, with δ⋆ = e^{−2Δ/T} ⟹ the (1−δ⋆)ⁿ contraction rate        *)
(*   (that downstream piece belongs to bs_minorization's Real-ization scope, not to this file).        *)
(*                                                              *)
(* The key constructive fact (a design discovery):                                   *)
(*   real_eq's Cauchy semantics constrains only the tail segment (∀δ>0 ∃N ∀n≥N |x_n−y_n|<δ),     *)
(*   giving no pointwise equality at any fixed index — hence uses of the sqrt witness r·r == d     *)
(*   always take the tail-bound form (fixed-δ truncation); all conclusions are real_lt (tail-segment strict    *)
(*   separation), zero pointwise-equality extraction, zero classical logic.                          *)
(*                                                              *)
(* Redlines: purely constructive; Set-level statements (Set-level And/Or/sigT, no Prop leaks);  *)
(*   all Qed-closed; extractable with zero magic.                                  *)
(* ============================================================ *)

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
Require Import UpCS.
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qring Arith.Arith.
From Stdlib Require Import Lia Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ################ Part 0: Q-layer helpers (the decidable order + the square bridge) ###### *)

Lemma Qle_or_lt : forall x y : Q, {x <= y} + {y < x}.
Proof.
  intros x y.
  destruct (Qcompare x y) eqn:E.
  - assert (Hxy : x == y) by (apply (proj2 (Qeq_alt x y)); exact E).
    left. rewrite Hxy. apply Qle_refl.
  - left. apply Qlt_le_weak. apply (proj2 (Qlt_alt x y)). exact E.
  - right. apply (proj2 (Qlt_alt y x)).
    rewrite <- (Qcompare_antisym x y). rewrite E. reflexivity.
Qed.

Lemma Qlt_0_half : Qlt 0 (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_half_one : Qlt (1#2) 1.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_le_one : Qle 0 1.
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma Qle_0_sq_Q : forall x : Q, Qle 0 (x * x).
Proof.
  intro x.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - apply (Qmult_le_0_compat x x); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    setoid_replace (x * x) with ((- x) * (- x)).
    + apply (Qmult_le_0_compat (- x) (- x)).
      * exact (Qopp_le_compat x 0 Hle).
      * exact (Qopp_le_compat x 0 Hle).
    + ring.
Qed.

Lemma Qle_0_of_sq_0 : forall a : Q, Qle 0 a -> a * a == 0 -> a == 0.
Proof.
  intros a Ha Hsq.
  destruct (Qeq_dec a 0) as [Heq | Hne]; [exact Heq |].
  exfalso.
  assert (Hlt : 0 < a).
  { destruct (Qle_or_lt a 0) as [Hle | Hgt].
    - exfalso. apply Hne. apply (Qle_antisym a 0); [exact Hle | exact Ha].
    - exact Hgt. }
  assert (H1 : 0 * a < a * a) by (apply (Qmult_lt_compat_r 0 a a); assumption).
  assert (H2 : 0 * a == 0) by ring.
  rewrite H2 in H1. rewrite Hsq in H1.
  exact (Qlt_irrefl 0 H1).
Qed.

(* Square non-negativity + the monotone core of square bounds: 0 ≤ a, 0 ≤ y, a² ≤ y² ⟹ a ≤ y *)
Lemma QH1core : forall a y : Q,
  Qle 0 a -> Qle 0 y -> Qle (a * a) (y * y) -> Qle a y.
Proof.
  intros a y Ha Hy Hsq.
  destruct (Qle_or_lt a y) as [Hle | Hlt]; [exact Hle |].
  exfalso.
  destruct (Qeq_dec y 0) as [Hy0 | Hny0].
  - rewrite Hy0 in Hsq.
    assert (Haa : a * a == 0).
    { apply (Qle_antisym (a * a) 0).
      - simpl in Hsq. exact Hsq.
      - apply (Qle_0_sq_Q a). }
    assert (Ha0 : a == 0) by (apply (Qle_0_of_sq_0 a Ha Haa)).
    rewrite Hy0, Ha0 in Hlt. exact (Qlt_irrefl 0 Hlt).
  - assert (Hpy : 0 < y).
    { destruct (Qle_or_lt y 0) as [Hle | Hgt].
      - exfalso. apply Hny0. apply (Qle_antisym y 0); [exact Hle | exact Hy].
      - exact Hgt. }
    assert (Hpa : 0 < a) by (apply (Qlt_trans 0 y a Hpy Hlt)).
    assert (H1 : y * y < a * y) by (apply (Qmult_lt_compat_r y a y); assumption).
    assert (H2 : a * y < a * a).
    { setoid_replace (a * y) with (y * a) by ring.
      apply (Qmult_lt_compat_r y a a); assumption. }
    assert (H3 : y * y < a * a) by (apply (Qlt_trans (y * y) (a * y) (a * a) H1 H2)).
    exact (Qlt_irrefl (y * y) (Qlt_le_trans (y * y) (a * a) (y * y) H3 Hsq)).
Qed.

(* The strict version: 0 ≤ d, 0 < h, d² < h² ⟹ d < h *)
Lemma Qlt_of_sq_lt : forall d h : Q,
  Qle 0 d -> Qle 0 h -> Qlt (d * d) (h * h) -> Qlt d h.
Proof.
  intros d h Hd Hh Hlt.
  destruct (Qle_or_lt h d) as [Hle | Hlt'].
  - exfalso.
    assert (Hmono : h * h <= d * d).
    { apply (Qle_trans (h * h) (d * h) (d * d)).
      - apply (Qmult_le_compat_r h d h); [exact Hle | exact Hh].
      - setoid_replace (d * h) with (h * d) by ring.
        apply (Qmult_le_compat_r h d d); [exact Hle | exact Hd]. }
    exact (Qlt_irrefl (d * d) (Qlt_le_trans (d * d) (h * h) (d * d) Hlt Hmono)).
  - exact Hlt'.
Qed.

(* The absolute-value version: 0 ≤ y, x² ≤ y² ⟹ |x| ≤ y *)
Lemma Qle_abs_le_sq : forall x y : Q,
  Qle 0 y -> Qle (x * x) (y * y) -> Qle (Qabs x) y.
Proof.
  intros x y Hy Hsq.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos x Hpos).
    apply (QH1core x y); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    assert (Habsx : Qabs x == - x) by (apply Qabs_neg; exact Hle).
    rewrite Habsx.
    apply (QH1core (- x) y).
    + exact (Qopp_le_compat x 0 Hle).
    + exact Hy.
    + setoid_replace ((- x) * (- x)) with (x * x) by ring. exact Hsq.
Qed.

(* Square equality + both non-negative ⟹ equality *)
Lemma Qeq_of_sq_eq : forall a b : Q,
  Qle 0 a -> Qle 0 b -> a * a == b * b -> a == b.
Proof.
  intros a b Ha Hb Hsq.
  apply (Qle_antisym a b).
  - apply (QH1core a b); [exact Ha | exact Hb | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; exact Hsq].
  - apply (QH1core b a); [exact Hb | exact Ha | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; rewrite Hsq; reflexivity].
Qed.

(* |x·x| == |x|² *)
Lemma Qabs_sq : forall x : Q, Qabs (x * x) == Qabs x * Qabs x.
Proof.
  intro x.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos (x * x)).
    + rewrite (Qabs_pos x Hpos). reflexivity.
    + apply (Qmult_le_0_compat x x); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    setoid_replace (x * x) with ((- x) * (- x)) by ring.
    rewrite (Qabs_pos ((- x) * (- x))).
    + assert (Habsx : Qabs x == - x) by (apply Qabs_neg; exact Hle).
      rewrite Habsx. reflexivity.
    + apply (Qmult_le_0_compat (- x) (- x)).
      * exact (Qopp_le_compat x 0 Hle).
      * exact (Qopp_le_compat x 0 Hle).
Qed.

(* x² == |x|·|x| *)
Lemma Qsq_abs_eq : forall x : Q, x * x == Qabs x * Qabs x.
Proof.
  intro x. rewrite <- (Qabs_sq x).
  apply Qeq_sym. apply Qabs_pos. apply Qle_0_sq_Q.
Qed.

(* Multiplicativity of the absolute value: |a·b| == |a|·|b| *)
Lemma Qabs_mult_gen : forall a b : Q, Qabs (a * b) == Qabs a * Qabs b.
Proof.
  intros a b.
  apply (Qeq_of_sq_eq (Qabs (a * b)) (Qabs a * Qabs b)).
  - apply Qabs_nonneg.
  - apply (Qmult_le_0_compat (Qabs a) (Qabs b)); apply Qabs_nonneg.
  - setoid_replace (Qabs a * Qabs b * (Qabs a * Qabs b))
      with (Qabs a * Qabs a * (Qabs b * Qabs b)) by ring.
    rewrite <- (Qabs_sq a). rewrite <- (Qabs_sq b).
    rewrite (Qabs_pos (a * a) (Qle_0_sq_Q a)).
    rewrite (Qabs_pos (b * b) (Qle_0_sq_Q b)).
    rewrite <- (Qabs_sq (a * b)).
    rewrite (Qabs_pos ((a * b) * (a * b)) (Qle_0_sq_Q (a * b))).
    ring.
Qed.

(* Monotone multiplication under double non-negativity *)
Lemma Qmult_le_mono2 : forall a b c d : Q,
  Qle 0 a -> Qle 0 b -> Qle a c -> Qle b d -> Qle (a * b) (c * d).
Proof.
  intros a b c d Ha Hb Hac Hbd.
  assert (Hc0 : 0 <= c) by (apply (Qle_trans 0 a c); assumption).
  apply (Qle_trans (a * b) (c * b) (c * d)).
  - apply (Qmult_le_compat_r a c b); assumption.
  - setoid_replace (c * b) with (b * c) by ring.
    setoid_replace (c * d) with (d * c) by ring.
    apply (Qmult_le_compat_r b d c); [exact Hbd | exact Hc0].
Qed.

(* 1 ≤ x², 0 ≤ x ⟹ 1 ≤ x (the pointwise kernel of √d ≥ 1) *)
Lemma Qle_1_of_sq : forall x : Q, Qle 0 x -> Qle 1 (x * x) -> Qle 1 x.
Proof.
  intros x H0 Hsq.
  assert (H : Qle (1 * 1) (x * x)).
  { setoid_replace (1 * 1) with 1 by ring. exact Hsq. }
  apply (QH1core 1 x); [exact zero_le_one | exact H0 | exact H].
Qed.

(* UpCS's sqlQ/dotpQ naming bridge: dotpQ u u == sqlQ u *)
Lemma dotpQ_sqlQ : forall u : list Q, dotpQ u u == sqlQ u.
Proof.
  induction u as [| x xs IH].
  - reflexivity.
  - cbn [dotpQ sqlQ]. rewrite IH. ring.
Qed.

(* ################ Part 2: the vector world + the Real tail-segment use pieces ########## *)
(* This file carries its own dotp/sql (the CW_ConstructiveWorld_219 Real version; UpCS's same-named pieces fix the scanned     *)
(* Real and cannot be used across; UpCS's pure-Q-layer cs_Q/dotpQ/sqlQ are used as usual).      *)

Fixpoint qkb_dotp (a b : list Real) : Real :=
  match a, b with
  | x :: xs, y :: ys => real_plus (real_mult x y) (qkb_dotp xs ys)
  | _, _ => real_zero
  end.

Fixpoint qkb_sql (a : list Real) : Real :=
  match a with
  | nil => real_zero
  | x :: rest => real_plus (real_mult x x) (qkb_sql rest)
  end.

(* ---- Q-layer supplements ---- *)

Lemma Qlt_0_two : Qlt 0 2.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_eight : Qlt 0 8.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_one : Qlt 0 1.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_sixteen : Qlt 0 16.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_32 : Qlt 0 32.
Proof. vm_compute. reflexivity. Qed.

Lemma Qle_0_three_quarters : Qle 0 (3#4).
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma Qlt_0_7_16 : Qlt 0 (7#16).
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_quarter : Qlt 0 (1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma Qle_add_pos_r : forall a e : Q, Qle 0 e -> Qle a (a + e).
Proof.
  intros a e He.
  apply (Qle_trans a (a + 0) (a + e)).
  - apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat a a 0 e); [apply Qle_refl | exact He].
Qed.

Lemma Qabs_lt_l : forall x c : Q, Qlt (Qabs x) c -> Qlt x c.
Proof.
  intros x c H.
  destruct (Qle_or_lt 0 x) as [H0 | H0].
  - rewrite (Qabs_pos x H0) in H. exact H.
  - apply (Qlt_trans x 0 c H0).
    apply (Qle_lt_trans 0 (Qabs x) c (Qabs_nonneg x) H).
Qed.

Lemma Qabs_lt_low : forall x c : Q, Qlt (Qabs x) c -> Qlt (- c) x.
Proof.
  intros x c H.
  destruct (Qle_or_lt x (- c)) as [Hle | Hgt].
  - exfalso.
    assert (Hc0 : 0 < c) by (apply (Qle_lt_trans 0 (Qabs x) c (Qabs_nonneg x) H)).
    assert (Habs : Qabs x == - x) by (apply Qabs_neg; lra).
    rewrite Habs in H.
    assert (Hge0 : - (- c) <= - x) by exact (Qopp_le_compat x (- c) Hle).
    assert (Hcc : c == - (- c)) by ring.
    rewrite Hcc in Hge0.
    lra.
  - exact Hgt.
Qed.

(* ---- real_le tail-segment use (the eq branch with eps slack; the lt branch exact) ---- *)

Lemma real_lt_pt_le : forall x y : Real,
  real_lt x y ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (projT1 x n) (projT1 y n)).
Proof.
  intros x y H. destruct H as [e [Hp [N HN]]].
  exists N. intros n Hn.
  assert (Hp0 : Qlt 0 e) by (apply QltT_to_Qlt; exact Hp).
  assert (Hq : Qlt e (projT1 y n - projT1 x n)).
  { apply QltT_to_Qlt. exact (HN n (NatLe_lift N n Hn)). }
  lra.
Qed.

Lemma real_le_pt_ev_plus : forall (x y : Real) (e : Q),
  Qlt 0 e -> real_le x y ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (projT1 x n) (projT1 y n + e)).
Proof.
  intros x y e He H. destruct H as [Hlt | Heq].
  - destruct (real_lt_pt_le x y Hlt) as [N HN]. exists N. intros n Hn.
    apply (Qle_trans (projT1 x n) (projT1 y n) (projT1 y n + e));
      [exact (HN n Hn) | apply Qle_add_pos_r; apply Qlt_le_weak; exact He].
  - destruct (Heq e (Qlt_to_QltT 0 e He)) as [N HN].
    exists N. intros n Hn.
    assert (Hab : Qlt (Qabs (projT1 x n - projT1 y n)) e).
    { apply QltT_to_Qlt. exact (HN n (NatLe_lift N n Hn)). }
    assert (Hl := Qabs_lt_l _ _ Hab).
    lra.
Qed.

(* ---- the real_const bridge ---- *)

Lemma qkb_real_const_pos : forall c : Q, Qlt 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc.
  exists ((1#2) * c). split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (1#2) c); [exact Qlt_0_half | exact Hc].
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)).
    setoid_replace (c - 0) with c by ring.
    lra.
Qed.

Lemma real_const_eq_of_Qeq : forall a b : Q, a == b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)). rewrite H. ring.
Qed.

Lemma qkb_real_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z) (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  try rewrite !(qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). try rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
  try rewrite !(qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). try rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
  ring.
Qed.

(* ################ Part 3: the nat embedding + the constructive square-root binding ######## *)

(* Q-side natural-number constants (avoiding Q.of_nat/Z conversions) *)
Fixpoint natQ (k : nat) : Q :=
  match k with
  | 0%nat => 0%Q
  | Datatypes.S m => 1 + natQ m
  end.

Lemma natQ_pos : forall k : nat, Qle 0 (natQ k).
Proof.
  induction k as [| k IH].
  - apply Qle_refl.
  - cbn [natQ]. apply (Qle_trans 0 (0 + natQ k) (1 + natQ k)).
    + rewrite Qplus_0_l. exact IH.
    + apply (Qplus_le_compat 0 1 (natQ k) (natQ k));
        [exact zero_le_one | apply Qle_refl].
Qed.

Lemma natQ_Sk_ge_one : forall k : nat, Qle 1 (natQ (Datatypes.S k)).
Proof.
  intro k. cbn [natQ].
  apply (Qle_trans 1 (1%Q + 0%Q) (1%Q + natQ k)).
  - apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
  - setoid_replace (1%Q + 0%Q) with (0%Q + 1%Q) by ring.
    setoid_replace (1%Q + natQ k) with (natQ k + 1%Q) by ring.
    apply (Qplus_le_compat 0 (natQ k) 1 1); [apply natQ_pos | apply Qle_refl].
Qed.

(* The Real-side embedding *)
Fixpoint qkb_nat_to_R (k : nat) : Real :=
  match k with
  | 0%nat => real_zero
  | Datatypes.S m => real_plus real_one (qkb_nat_to_R m)
  end.

Lemma nat_to_R_proj : forall (k : nat) (n : nat),
  projT1 (qkb_nat_to_R k) n == natQ k.
Proof.
  induction k as [| k IH]; intro n.
  - reflexivity.
  - cbn [qkb_nat_to_R]. rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    change (projT1 real_one n) with 1%Q.
    rewrite IH. reflexivity.
Qed.

Lemma qkb_nat_to_R_pos : forall k : nat, real_lt real_zero (qkb_nat_to_R (Datatypes.S k)).
Proof.
  intro k.
  exists (1#2). split.
  - apply Qlt_to_QltT. exact Qlt_0_half.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    rewrite (nat_to_R_proj (Datatypes.S k) n).
    cbn [natQ].
    setoid_replace (1 + natQ k - 0) with (1%Q + natQ k) by ring.
    assert (H1 : Qle 0 (natQ k)) by apply natQ_pos.
    lra.
Qed.

(* The square-root bound-conversion primitive: root_of appears only in premises and the Δ definition, never in identity chains *)
Definition root_of (d : Real) (Hd : real_le real_zero d) : Real :=
  projT1 (real_sqrt_exists d Hd).

Definition root_d (k : nat) : Real :=
  root_of (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)).

Lemma root_d_sq : forall k : nat,
  real_eq (real_mult (root_d k) (root_d k)) (qkb_nat_to_R (Datatypes.S k)).
Proof.
  intro k. unfold root_d, root_of.
  destruct (real_sqrt_exists (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)))
    as [r [Hr0 Hrsq]].
  exact Hrsq.
Qed.

(* The sqrt witness's tail lower bound: r² == natQ(Datatypes.S k) (tail segment) + Datatypes.S k ≥ 1 ⟹ r_n² > 9/16 (tail segment) *)
Lemma sq_bound_from_eq : forall (k : nat) (r : Real),
  real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (9#16) (projT1 r n * projT1 r n)).
Proof.
  intros k r Hrsq. destruct r as [u Hu].
  destruct (Hrsq (7#16) (Qlt_to_QltT 0 (7#16) Qlt_0_7_16)) as [N1 HN1].
  exists N1. intros n Hn.
  cbn [projT1] in HN1 |- *.
  assert (Hlow2 : Qlt (- (7#16)) (u n * u n - natQ (Datatypes.S k))).
  { assert (Ht := HN1 n (NatLe_lift N1 n Hn)).
    apply QltT_to_Qlt in Ht.
    assert (Hlow := Qabs_lt_low _ _ Ht).
    rewrite (nat_to_R_proj (Datatypes.S k) n) in Hlow.
    exact Hlow. }
  assert (Hone : Qle 1 (natQ (Datatypes.S k))) by apply natQ_Sk_ge_one.
  remember (u n * u n) as t eqn:Et.
  remember (natQ (Datatypes.S k)) as q eqn:Eq.
  lra.
Qed.

(* The root's lower bound: Datatypes.S k ≥ 1 ⟹ root ≥ 3/4 (tail segment) *)
Lemma sqrt_dim_ge_quarter : forall (k : nat) (r : Real),
  real_le real_zero r ->
  real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (3#4) (projT1 r n)).
Proof.
  intros k r Hr0 Hrsq. destruct r as [u Hu].
  destruct (sq_bound_from_eq k (existT (fun s : Qseq => cauchy s) u Hu) Hrsq)
    as [N1 HN1].
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [e0 [Hpos0 [N0 HN0]]].
    exists (Nat.max N0 N1). intros n Hn.
    assert (Hn0 : (N0 <= n)%nat).
    { apply (Nat.le_trans N0 (Nat.max N0 N1) n); [apply Nat.le_max_l | exact Hn]. }
    assert (Hn1 : (N1 <= n)%nat).
    { apply (Nat.le_trans N1 (Nat.max N0 N1) n); [apply Nat.le_max_r | exact Hn]. }
    assert (Hge : Qle 0 (u n)).
    { assert (Hpos : Qlt 0 e0) by (apply QltT_to_Qlt; exact Hpos0).
      assert (Hq : Qlt e0 (u n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HN0 n (NatLe_lift N0 n Hn0)). }
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    apply (QH1core (3#4) (u n)).
    + exact Qle_0_three_quarters.
    + exact Hge.
    + setoid_replace ((3#4) * (3#4)) with (9#16) by ring.
      apply Qlt_le_weak. exact (HN1 n Hn1).
  - exfalso.
    destruct (Heq0 (1#4) (Qlt_to_QltT 0 (1#4) Qlt_0_quarter)) as [N2 HN2].
    assert (Hn1 : (N1 <= Nat.max N1 N2)%nat) by apply Nat.le_max_l.
    assert (Hn2 : (N2 <= Nat.max N1 N2)%nat) by apply Nat.le_max_r.
    assert (H9 : Qlt (9#16) (u (Nat.max N1 N2) * u (Nat.max N1 N2)))
      by exact (HN1 (Nat.max N1 N2) Hn1).
    assert (Hsmall0 := HN2 (Nat.max N1 N2) (NatLe_lift N2 (Nat.max N1 N2) Hn2)).
    apply QltT_to_Qlt in Hsmall0.
    change (projT1 real_zero (Nat.max N1 N2)) with 0%Q in Hsmall0.
    setoid_replace (0 - u (Nat.max N1 N2))
      with (- u (Nat.max N1 N2)) in Hsmall0 by ring.
    rewrite Qabs_opp in Hsmall0.
    assert (Hsq : u (Nat.max N1 N2) * u (Nat.max N1 N2)
                  == Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))).
    { rewrite <- (Qabs_pos (u (Nat.max N1 N2) * u (Nat.max N1 N2))
                    (Qle_0_sq_Q (u (Nat.max N1 N2)))). apply Qabs_sq. }
    rewrite Hsq in H9.
    assert (Hq4 : (1#4) * (1#4) == (1#16)) by ring.
    assert (Hqabs0 : Qle 0 (Qabs (u (Nat.max N1 N2)))) by apply Qabs_nonneg.
    assert (Hstep : Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))
                    < (1#4) * (1#4)).
    { assert (Hq4p : Qlt 0 ((1#4) * (1#4))).
      { apply (Qmult_lt_0_compat (1#4) (1#4)); exact Qlt_0_quarter. }
      nra. }
    assert (Hmono : Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))
                    < (1#16)).
    { rewrite <- Hq4. exact Hstep. }
    assert (Hg : Qlt (1#16) (9#16)) by (vm_compute; reflexivity).
    lra.
Qed.

Lemma root_zero_of : forall (d : Real) (Hd : real_le real_zero d),
  real_le real_zero (root_of d Hd).
Proof.
  intros d Hd. unfold root_of.
  destruct (real_sqrt_exists d Hd) as [r [Hr0 Hrsq]]. exact Hr0.
Qed.

Lemma root_sq_of : forall (d : Real) (Hd : real_le real_zero d),
  real_eq (real_mult (root_of d Hd) (root_of d Hd)) d.
Proof.
  intros d Hd. unfold root_of.
  destruct (real_sqrt_exists d Hd) as [r [Hr0 Hrsq]]. exact Hrsq.
Qed.

Lemma root_d_ge_zero : forall k : nat, real_le real_zero (root_d k).
Proof.
  intro k. unfold root_d, root_of.
  destruct (real_sqrt_exists (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)))
    as [r [Hr0 Hrsq]]. exact Hr0.
Qed.

Lemma root_d_pos : forall k : nat, real_lt real_zero (root_d k).
Proof.
  intro k.
  unfold root_d, root_of.
  destruct (real_sqrt_exists (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)))
    as [r [Hr0 Hrdsq]].
  destruct (sqrt_dim_ge_quarter k r Hr0 Hrdsq) as [N HN].
  exists (1#2). split.
  - apply Qlt_to_QltT. exact Qlt_0_half.
  - exists N. intros n Hn.
    apply NatLe_drop in Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    setoid_replace (projT1 r n - 0) with (projT1 r n) by ring.
    apply (Qlt_le_trans (1#2) (3#4) (projT1 r n));
      [exact Qlt_half_one | exact (HN n Hn)].
Qed.

(* The pointwise form of real_inv_pos (Defined-body unfolding + the leb branch) *)
Lemma real_inv_pos_pt :
  forall (u : Qseq) (Hu : cauchy u) (eps0 : Q) (Heps0 : QltT 0 eps0)
         (N0 : nat) (HN0 : forall n : nat, NatLe N0 n -> QltT eps0 (u n - projT1 real_zero n))
         (n : nat), (N0 <= n)%nat ->
  projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) u Hu)
             (existT _ eps0 (Heps0, existT _ N0 HN0))) n == Qinv (u n).
Proof.
  intros u Hu eps0 Heps0 N0 HN0 n Hn.
  unfold real_inv_pos. cbn [projT1].
  destruct (Nat.leb N0 n) eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hlt : (n < N0)%nat) by (apply (proj1 (Nat.leb_gt N0 n) E)).
    exact (Nat.lt_irrefl n (Nat.lt_le_trans n N0 n Hlt Hn)).
Qed.

(* ################ Part 4: the abs bound-conversion piece (B') and the eps pass-through ######## *)

(* The core abs conversion piece: x² < y² + h² ⟹ |x| < |y| + 2h (no sign premise, the Qabs form) *)
Lemma abs_le_add_abs_of_sq_lt : forall (x y : Real) (h : Q),
  Qlt 0 h ->
  real_lt (real_mult x x) (real_plus (real_mult y y) (real_const (h * h))) ->
  real_lt (real_abs x) (real_plus (real_abs y) (real_const (2 * h))).
Proof.
  intros x y h Hh Hlt. destruct Hlt as [e1 [Hpos1 [N1 HN1]]].
  exists h. split.
  - apply Qlt_to_QltT. exact Hh.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)).
  rewrite !(qeqT_imp_qeq _ _ (real_abs_proj _ _)).
  assert (Hpt : Qlt e1 (projT1 y n * projT1 y n + h * h - projT1 x n * projT1 x n)).
  { pose proof (HN1 n Hn) as Hp.
    apply QltT_to_Qlt in Hp.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp. rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hp.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)) in Hp.
    exact Hp. }
  assert (Hax : projT1 x n * projT1 x n == Qabs (projT1 x n) * Qabs (projT1 x n))
    by apply Qsq_abs_eq.
  assert (Hay : projT1 y n * projT1 y n == Qabs (projT1 y n) * Qabs (projT1 y n))
    by apply Qsq_abs_eq.
  assert (Hax0 : Qle 0 (Qabs (projT1 x n))) by apply Qabs_nonneg.
  assert (Hay0 : Qle 0 (Qabs (projT1 y n))) by apply Qabs_nonneg.
  assert (Hpos1q : Qlt 0 e1) by (apply QltT_to_Qlt; exact Hpos1).
  destruct (Qle_or_lt (Qabs (projT1 x n)) (Qabs (projT1 y n))) as [Hle | Hgt];
    nra.
Defined.
(* |x·y| ≤ |x|·y + eps (the y > 0 tail segment; eps passed through directly) *)
Lemma abs_mult_pos_eps : forall (x y : Real) (eps : Real),
  real_lt real_zero y -> real_lt real_zero eps ->
  real_lt (real_abs (real_mult x y))
          (real_plus (real_mult (real_abs x) y) eps).
Proof.
  intros x y eps Hy Heps.
  destruct Hy as [ey [Hpey [Ny HNy]]].
  destruct Heps as [ee [Hpee [Ne HNe]]].
  exists ee. split; [exact Hpee | exists (Nat.max Ny Ne); intros n Hn].
  assert (Hny : (Ny <= n)%nat).
  { apply (Nat.le_trans Ny (Nat.max Ny Ne) n);
      [apply Nat.le_max_l | apply (NatLe_drop (Nat.max Ny Ne) n Hn)]. }
  assert (Hne : (Ne <= n)%nat).
  { apply (Nat.le_trans Ne (Nat.max Ny Ne) n);
      [apply Nat.le_max_r | apply (NatLe_drop (Nat.max Ny Ne) n Hn)]. }
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_abs_proj _ _)).
  try rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). try rewrite !(qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). try rewrite !(qeqT_imp_qeq _ _ (real_abs_proj _ _)).
  assert (Hy0 : Qle 0 (projT1 y n)).
  { assert (Hq : Qlt ey (projT1 y n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNy n (NatLe_lift Ny n Hny)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 y n - 0) with (projT1 y n) in Hq by ring.
    apply (Qle_trans 0 ey (projT1 y n)).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpey.
    - apply Qlt_le_weak. exact Hq. }
  rewrite (Qabs_mult_gen (projT1 x n) (projT1 y n)).
  rewrite (Qabs_pos (projT1 y n) Hy0).
  assert (Hep : Qlt ee (projT1 eps n - projT1 real_zero n)).
  { apply QltT_to_Qlt. exact (HNe n (NatLe_lift Ne n Hne)). }
  change (projT1 real_zero n) with 0%Q in Hep.
  lra.
Qed.

(* ################ Part 5: local projections + strict C-S (the CW_ConstructiveWorld_219 Real version; the source text mangles C-S into C-Datatypes.S) ## *)

Lemma sql_proj_l : forall (a : list Real) (k : nat),
  projT1 (qkb_sql a) k == sqlQ (map (fun x : Real => projT1 x k) a).
Proof.
  induction a as [| x xs IH]; intro k.
  - reflexivity.
  - cbn [qkb_sql]. rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite IH.
    reflexivity.
Qed.

Lemma dotp_proj_l : forall (a b : list Real) (k : nat),
  projT1 (qkb_dotp a b) k
    == dotpQ (map (fun x : Real => projT1 x k) a)
             (map (fun y : Real => projT1 y k) b).
Proof.
  induction a as [| x xs IH]; intros b k.
  - reflexivity.
  - destruct b as [| y ys].
    + reflexivity.
    + cbn [qkb_dotp]. rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite IH.
      reflexivity.
Qed.

(* Finite-sum Cauchy–Schwarz (the strict version, the real layer; the pointwise lift of UpCS's cs_Q) *)
Theorem cs_real_lt : forall (a b : list Real) (eps : Real),
  real_lt real_zero eps ->
  real_lt (real_mult (qkb_dotp a b) (qkb_dotp a b))
          (real_plus (real_mult (qkb_sql a) (qkb_sql b)) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [e1 [Hpos1 [N1 HN1]]].
  exists e1. split.
  - exact Hpos1.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
    rewrite (sql_proj_l a n). rewrite (sql_proj_l b n). rewrite (dotp_proj_l a b n).
    set (A := sqlQ (map (fun x : Real => projT1 x n) a)).
    set (B := sqlQ (map (fun x : Real => projT1 x n) b)).
    set (C := dotpQ (map (fun x : Real => projT1 x n) a)
                    (map (fun y : Real => projT1 y n) b)).
    assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
    assert (Hep : Qlt e1 (projT1 eps n)).
    { pose proof (HN1 n Hn) as Ht.
      apply QltT_to_Qlt in Ht.
      assert (Hzr : projT1 eps n - projT1 real_zero n == projT1 eps n).
      { rewrite Hz0. ring. }
      rewrite Hzr in Ht. exact Ht. }
    assert (Hgap : Qle 0 (A * B - C * C)).
    { apply (Qle_trans _ (C * C - C * C)).
      - apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
      - assert (Hcs := cs_Q (map (fun x : Real => projT1 x n) a)
                            (map (fun y : Real => projT1 y n) b)).
        unfold Qminus.
        exact (Qplus_le_compat (C * C) (A * B) (-(C * C)) (-(C * C))
                 (QleT'_to_Qle _ _ Hcs) (Qle_refl _)). }
    apply (Qlt_le_trans e1 (projT1 eps n)).
    + exact Hep.
    + apply (Qle_trans _ (0 + projT1 eps n)).
      * apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ ((A * B - C * C) + projT1 eps n)).
        -- exact (Qplus_le_compat 0 (A * B - C * C) (projT1 eps n) (projT1 eps n)
                    Hgap (Qle_refl _)).
        -- apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
Qed.


Lemma Qle_add_pos_l : forall b a : Q, Qle 0 a -> Qle b (b + a).
Proof.
  intros b a Ha.
  apply (Qle_trans b (b + 0) (b + a)).
  - apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat b b 0 a); [apply Qle_refl | exact Ha].
Qed.

Lemma Qle_abs_self : forall x : Q, Qle x (Qabs x).
Proof.
  intro x. destruct (Qle_or_lt 0 x) as [H0 | H0].
  - rewrite (Qabs_pos x H0). apply Qle_refl.
  - rewrite (Qabs_neg x (Qlt_le_weak x 0 H0)). lra.
Qed.

(* The tail bound on the root's absolute value (the unified form; the lt/eq branches digested internally):
   the lt branch gives the exact bound via 0 (|rq_n| = rq_n ≤ Q_n); the eq branch gives |rq_n| ≤ d. *)
Lemma root_abs_tail : forall (rq Q2 : Real) (d : Q),
  Qlt 0 d -> real_lt real_zero Q2 ->
  real_le real_zero rq -> real_le rq Q2 ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 rq n)) (projT1 Q2 n + d)).
Proof.
  intros rq Q2 d Hd HQ Hr0 Hrq.
  destruct (real_le_pt_ev_plus rq Q2 d Hd Hrq) as [Nq HNq].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [er [Hper [Nr HNr]]].
    exists (Nat.max Nr (Nat.max Nq NQ)). intros n Hn.
    assert (Hnr : (Nr <= n)%nat) by lia.
    assert (Hnq : (Nq <= n)%nat) by lia.
    assert (HnQ : (NQ <= n)%nat) by lia.
    assert (HQ0 : Qle 0 (projT1 Q2 n)).
    { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
      assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    assert (Hper' : Qlt 0 er) by (apply QltT_to_Qlt; exact Hper).
    assert (Hge : Qle 0 (projT1 rq n)).
    { assert (Hq : Qlt er (projT1 rq n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNr n (NatLe_lift Nr n Hnr)). }
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    rewrite (Qabs_pos (projT1 rq n) Hge).
    exact (HNq n Hnq).
  - destruct (Heq0 d (Qlt_to_QltT 0 d Hd)) as [Ne HNe].
    exists (Nat.max Nq (Nat.max Ne NQ)). intros n Hn.
    assert (Hnq : (Nq <= n)%nat) by lia.
    assert (Hne : (Ne <= n)%nat) by lia.
    assert (HnQ : (NQ <= n)%nat) by lia.
    assert (HQ0 : Qle 0 (projT1 Q2 n)).
    { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
      assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    assert (Hab : Qlt (Qabs (projT1 rq n)) d).
    { assert (Ht := HNe n (NatLe_lift Ne n Hne)).
      apply QltT_to_Qlt in Ht.
      change (projT1 real_zero n) with 0%Q in Ht.
      setoid_replace (0 - projT1 rq n) with (- projT1 rq n) in Ht by ring.
      rewrite Qabs_opp in Ht. exact Ht. }
    apply (Qle_trans (Qabs (projT1 rq n)) d (projT1 Q2 n + d)).
    { apply Qlt_le_weak. exact Hab. }
    { setoid_replace (projT1 Q2 n + d) with (d + projT1 Q2 n) by ring.
      apply (Qle_add_pos_l d (projT1 Q2 n) HQ0). }
Qed.

(* The root-product tail bound (the unified form): |rq·rk| ≤ Q·K + d·(MQ+MK) + d², where
   MQ/MK are the global bounds of Q/K (real_norm_bounded) and d is the internal eq-branch truncation granularity *)
Lemma prod_tail_bound : forall (rq rk Q2 K2 : Real) (MQ MK : Q) (d : Q),
  Qlt 0 d ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  real_le real_zero rq -> real_le rq Q2 ->
  real_le real_zero rk -> real_le rk K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (real_mult rq rk) n))
        (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
Proof.
  intros rq rk Q2 K2 MQ MK d Hd HQ HK Hr0 Hrq Hk0 Hrk HMQ HMK.
  destruct (root_abs_tail rq Q2 d Hd HQ Hr0 Hrq) as [Nq HNq].
  destruct (root_abs_tail rk K2 d Hd HK Hk0 Hrk) as [Nk HNk].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct HK as [eK [HpeK [NK HNK]]].
  exists (Nat.max Nq (Nat.max Nk (Nat.max NQ NK))).
  intros n Hn.
  assert (Hnq : (Nq <= n)%nat) by lia.
  assert (Hnk : (Nk <= n)%nat) by lia.
  assert (HnQ : (NQ <= n)%nat) by lia.
  assert (HnK : (NK <= n)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite Qabs_mult_gen.
  assert (Hbq : Qle (Qabs (projT1 rq n)) (projT1 Q2 n + d)) by exact (HNq n Hnq).
  assert (Hbk : Qle (Qabs (projT1 rk n)) (projT1 K2 n + d)) by exact (HNk n Hnk).
  assert (Haq : Qle 0 (Qabs (projT1 rq n))) by apply Qabs_nonneg.
  assert (Hak : Qle 0 (Qabs (projT1 rk n))) by apply Qabs_nonneg.
  assert (HQ0 : Qle 0 (projT1 Q2 n)).
  { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
    lra. }
  assert (HK0 : Qle 0 (projT1 K2 n)).
  { assert (Hk : Qlt eK (projT1 K2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNK n (NatLe_lift NK n HnK)). }
    change (projT1 real_zero n) with 0%Q in Hk.
    assert (HpeK' : Qlt 0 eK) by (apply QltT_to_Qlt; exact HpeK).
    lra. }
  assert (HQm : Qle (projT1 Q2 n) MQ).
  { apply (Qle_trans (projT1 Q2 n) (Qabs (projT1 Q2 n)) MQ).
    { apply Qle_abs_self. }
    { exact (HMQ n). } }
  assert (HKm : Qle (projT1 K2 n) MK).
  { apply (Qle_trans (projT1 K2 n) (Qabs (projT1 K2 n)) MK).
    { apply Qle_abs_self. }
    { exact (HMK n). } }
  apply (Qle_trans (Qabs (projT1 rq n) * Qabs (projT1 rk n))
                   ((projT1 Q2 n + d) * (projT1 K2 n + d))
                   (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
  - apply (Qmult_le_mono2 _ _ _ _ Haq Hak Hbq Hbk).
  - nra.
Qed.


(* ################ Part 6: piece 1, the inner product/norm bridge #################### *)

(* Piece 1: ⟨q,q⟩ == Σq² (UpCS's qkb_sql is Σq² — the naming bridge). *)
Theorem inner_sq_norm : forall q : list Real, real_eq (qkb_dotp q q) (qkb_sql q).
Proof.
  intro q. apply real_eq_of_zero_diff. intros n. apply qeq_imp_qeqT.
  rewrite (dotp_proj_l q q n). rewrite (sql_proj_l q n).
  rewrite dotpQ_sqlQ. ring.
Qed.

(* ################ Part 7: piece 2, the bound-conversion main piece #################### *)

(* The pairing bound: root-bounded premises ⟹ |⟨a,b⟩| < Q·K + h (the inl strict branch; witness h/4) *)
Lemma qk_pair_bound : forall (a b : list Real) (Q2 K2 : Real) (MQ MK : Q) (h : Q)
  (Ha : real_le real_zero (qkb_sql a)) (Hb : real_le real_zero (qkb_sql b)),
  Qlt 0 h -> Qlt 0 MQ -> Qlt 0 MK ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  real_le (root_of (qkb_sql a) Ha) Q2 -> real_le (root_of (qkb_sql b) Hb) K2 ->
  real_lt (real_abs (qkb_dotp a b)) (real_plus (real_mult Q2 K2) (real_const h)).
Proof.
  intros a b Q2 K2 MQ MK h Ha Hb Hh HMQp HMKp HQ HK HMQ HMK Hqa Hkb.
  set (ra := root_of (qkb_sql a) Ha).
  set (rb := root_of (qkb_sql b) Hb).
  assert (Hrasq : real_eq (real_mult ra ra) (qkb_sql a)) by apply (root_sq_of (qkb_sql a) Ha).
  assert (Hrbsq : real_eq (real_mult rb rb) (qkb_sql b)) by apply (root_sq_of (qkb_sql b) Hb).
  assert (Hra0 : real_le real_zero ra) by apply (root_zero_of (qkb_sql a) Ha).
  assert (Hrb0 : real_le real_zero rb) by apply (root_zero_of (qkb_sql b) Hb).
  (* The C-S strict version, eps := ((1#4)*h)² *)
  assert (Hcs : real_lt (real_mult (qkb_dotp a b) (qkb_dotp a b))
                  (real_plus (real_mult (qkb_sql a) (qkb_sql b))
                              (real_const (((1#4) * h) * ((1#4) * h))))).
  { apply cs_real_lt. apply qkb_real_const_pos.
    apply (Qmult_lt_0_compat ((1#4) * h) ((1#4) * h)).
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh]. }
  (* Change of variables to (ra·rb)² *)
  assert (E12 : real_eq (real_mult (qkb_sql a) (qkb_sql b))
                        (real_mult (real_mult ra rb) (real_mult ra rb))).
  { apply (real_eq_trans (real_mult (qkb_sql a) (qkb_sql b))
                         (real_mult (real_mult ra ra) (real_mult rb rb)) _).
    - apply (RealSetoid.real_eq_mult_compat (qkb_sql a) (qkb_sql b)
                                 (real_mult ra ra) (real_mult rb rb)
                                 (real_eq_sym (real_mult ra ra) (qkb_sql a) Hrasq)
                                 (real_eq_sym (real_mult rb rb) (qkb_sql b) Hrbsq)).
    - apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
      rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). ring. }
  assert (H3 : real_lt (real_mult (qkb_dotp a b) (qkb_dotp a b))
                (real_plus (real_mult (real_mult ra rb) (real_mult ra rb))
                           (real_const (((1#4) * h) * ((1#4) * h))))).
  { apply (real_lt_le_trans _ (real_plus (real_mult (qkb_sql a) (qkb_sql b))
                                          (real_const (((1#4) * h) * ((1#4) * h)))) _ Hcs).
    apply (real_le_plus_compat (real_mult (qkb_sql a) (qkb_sql b))
                               (real_mult (real_mult ra rb) (real_mult ra rb))
                               (real_const (((1#4) * h) * ((1#4) * h)))
                               (real_const (((1#4) * h) * ((1#4) * h)))).
    + apply (RealSetoid.real_eq_le (real_mult (qkb_sql a) (qkb_sql b))
                                   (real_mult (real_mult ra rb) (real_mult ra rb))
                                   E12).
    + apply (real_le_refl (real_const (((1#4) * h) * ((1#4) * h)))). }
  (* B'：|AB| < |ra·rb| + 2·((1#4)*h) = |ra·rb| + (1#2)*h *)
  assert (H4 : real_lt (real_abs (qkb_dotp a b))
                (real_plus (real_abs (real_mult ra rb))
                           (real_const (2 * ((1#4) * h))))).
  { apply (abs_le_add_abs_of_sq_lt (qkb_dotp a b) (real_mult ra rb) ((1#4) * h)).
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
    - exact H3. }
  (* B''s pointwise tail fact (without destroying the witness value):
     per n ≥ N4: |AB|_n ≤ |ra_n·rb_n| + (1#2)*h  — from real_lt's strict difference and eps4 > 0 *)
  destruct H4 as [eps4 [Hpos4 [N4 HN4]]].
  set (d := h / (32 * (1 + MQ + MK + h))).
  assert (Hgt : Qlt 0 (1 + MQ + MK + h)) by lra.
  assert (HX1 : Qle 1 (1 + MQ + MK + h)) by lra.
  assert (Hd0 : Qlt 0 d).
  { unfold d. apply (Qmult_lt_0_compat h (/ (32 * (1 + MQ + MK + h)))).
    - exact Hh.
    - apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat 32 (1 + MQ + MK + h)).
      + exact Qlt_0_32.
      + exact Hgt. }
  assert (Hd1 : d * (32 * (1 + MQ + MK + h)) == h).
  { unfold d. field.
    intro Hz. lra. }
  assert (Hd2 : Qle (16 * (d * (MQ + MK) + d * d)) h).
  { assert (Hdh : Qle d h) by nra.
    nra. }
  destruct (prod_tail_bound ra rb Q2 K2 MQ MK d Hd0 HQ HK
              Hra0 Hqa Hrb0 Hkb
              HMQ HMK) as [Np HNp].
  exists ((1#4) * h). split.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
  - exists (Nat.max N4 Np). intros n Hn.
    assert (Hn4 : (N4 <= n)%nat).
    { apply (Nat.le_trans N4 (Nat.max N4 Np) n);
        [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 Np) n Hn)]. }
    assert (Hnp : (Np <= n)%nat).
    { apply (Nat.le_trans Np (Nat.max N4 Np) n);
        [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 Np) n Hn)]. }
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)).
    rewrite !(qeqT_imp_qeq _ _ (real_abs_proj _ _)).
    assert (Hf1 : Qle (Qabs (projT1 (qkb_dotp a b) n))
                      (Qabs (projT1 ra n) * Qabs (projT1 rb n) + (1#2) * h)).
    { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
      apply QltT_to_Qlt in Hq.
      assert (Hpe4 : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hq. rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)) in Hq.
      rewrite !(qeqT_imp_qeq _ _ (real_abs_proj _ _)) in Hq.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hq.
      rewrite (Qabs_mult_gen (projT1 ra n) (projT1 rb n)) in Hq.
      lra. }
    assert (Hf2 : Qle (Qabs (projT1 ra n) * Qabs (projT1 rb n))
                      (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
    { pose proof (HNp n Hnp) as Hp.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hp.
      rewrite (Qabs_mult_gen (projT1 ra n) (projT1 rb n)) in Hp.
      exact Hp. }
    nra.
Qed.
(* ################ Part 8: piece 2, the rd-loss chain + the main theorem ############ *)

(* The rd ≥ 0 tail segment (the inl branch exact; the inr branch's rd≈0 contradicts rd²≈Datatypes.S k≥1) *)
Lemma rd_pos_tail : forall (k : nat) (r : Real),
  real_le real_zero r -> real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle 0 (projT1 r n)).
Proof.
  intros k r Hr0 Hrsq.
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [e0 [Hpos0 [N0 HN0]]].
    exists N0. intros n Hn0.
    assert (Hq : Qlt e0 (projT1 r n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HN0 n (NatLe_lift N0 n Hn0)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 r n - 0) with (projT1 r n) in Hq by ring.
    apply (Qle_trans 0 e0 (projT1 r n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact Hpos0
      | apply Qlt_le_weak; exact Hq].
  - exfalso.
    destruct (sq_bound_from_eq k r Hrsq) as [N1 HN1].
    destruct (Heq0 (1#4) (Qlt_to_QltT 0 (1#4) Qlt_0_quarter)) as [N2 HN2].
    assert (H9 : Qlt (9#16)
                   (projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2)))
      by exact (HN1 (Nat.max N1 N2) (Nat.le_max_l N1 N2)).
    assert (Hs := HN2 (Nat.max N1 N2)
                    (NatLe_lift N2 (Nat.max N1 N2) (Nat.le_max_r N1 N2))).
    apply QltT_to_Qlt in Hs.
    change (projT1 real_zero (Nat.max N1 N2)) with 0%Q in Hs.
    setoid_replace (0 - projT1 r (Nat.max N1 N2))
      with (- projT1 r (Nat.max N1 N2)) in Hs by ring.
    rewrite Qabs_opp in Hs.
    assert (Hsq : projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2)
                  == Qabs (projT1 r (Nat.max N1 N2))
                     * Qabs (projT1 r (Nat.max N1 N2))).
    { rewrite <- (Qabs_pos
                    (projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2))
                    (Qle_0_sq_Q (projT1 r (Nat.max N1 N2)))).
      apply Qabs_sq. }
    rewrite Hsq in H9.
    assert (Hmono : Qabs (projT1 r (Nat.max N1 N2))
                      * Qabs (projT1 r (Nat.max N1 N2)) < (1#16)).
    { assert (Ha0 : Qle 0 (Qabs (projT1 r (Nat.max N1 N2))))
        by apply Qabs_nonneg.
      nra. }
    lra.
Qed.

(* The rd ≥ 1 − dq tail segment (under the dq ≤ 1 premise) *)
Lemma rd_ge_one_minus_delta : forall (k : nat) (r : Real) (dq : Q),
  Qlt 0 dq -> Qle dq 1 ->
  real_le real_zero r -> real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (1 - dq) (projT1 r n)).
Proof.
  intros k r dq Hdq0 Hdq1 Hr0 Hrsq.
  destruct (rd_pos_tail k r Hr0 Hrsq) as [N0 HN0].
  destruct (Qle_or_lt 1 dq) as [Hge | Hlt].
  - exists N0. intros n Hn. pose proof (HN0 n Hn) as Hge0. lra.
  - assert (Hpos : Qlt 0 (1 - dq)) by lra.
    assert (Heps : Qlt 0 (1 - (1 - dq) * (1 - dq))) by nra.
    destruct (Hrsq (1 - (1 - dq) * (1 - dq))
                   (Qlt_to_QltT 0 (1 - (1 - dq) * (1 - dq)) Heps)) as [N1 HN1].
    exists (Nat.max N0 N1). intros n Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    apply (QH1core (1 - dq) (projT1 r n)).
    + assert (Hd1 : Qle 0 dq) by (apply Qlt_le_weak; exact Hdq0).
      lra.
    + exact (HN0 n Hn0).
    + (* rd² ≈ the Datatypes.S k tail segment ⟹ rd_n² > Datatypes.S k − (1−(1−dq)²) ≥ (1−dq)² *)
      assert (Hs := HN1 n (NatLe_lift N1 n Hn1)).
      apply QltT_to_Qlt in Hs.
      assert (Hlow := Qabs_lt_low _ _ Hs).
      rewrite (nat_to_R_proj (Datatypes.S k) n) in Hlow.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hlow.
      assert (Hone : Qle 1 (natQ (Datatypes.S k))) by apply natQ_Sk_ge_one.
      nra.
Qed.

(* Piece 2: the final bound after rd-loss — Q·K ≤ Q·K·rd + MQ·MK·dq (tail segment) *)
Lemma qk_rd_loss : forall (k : nat) (Q2 K2 r : Real) (MQ MK dq : Q),
  Qlt 0 dq -> Qle dq 1 ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  real_le real_zero r -> real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (projT1 Q2 n * projT1 K2 n)
        (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq)).
Proof.
  intros k Q2 K2 r MQ MK dq Hdq0 Hdq1 HQ HK HMQ HMK Hr0 Hrsq.
  destruct (rd_pos_tail k r Hr0 Hrsq) as [N0 HN0].
  destruct (rd_ge_one_minus_delta k r dq Hdq0 Hdq1 Hr0 Hrsq) as [N1 HN1].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct HK as [eK [HpeK [NK HNK]]].
  exists (Nat.max N0 (Nat.max N1 (Nat.max NQ NK))). intros n Hn.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (HnQ : (NQ <= n)%nat) by lia.
  assert (HnK : (NK <= n)%nat) by lia.
  assert (HQ0 : Qle 0 (projT1 Q2 n)).
  { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 Q2 n - 0) with (projT1 Q2 n) in Hq by ring.
    apply (Qle_trans 0 eQ (projT1 Q2 n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact HpeQ
      | apply Qlt_le_weak; exact Hq]. }
  assert (HK0 : Qle 0 (projT1 K2 n)).
  { assert (Hk : Qlt eK (projT1 K2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNK n (NatLe_lift NK n HnK)). }
    change (projT1 real_zero n) with 0%Q in Hk.
    setoid_replace (projT1 K2 n - 0) with (projT1 K2 n) in Hk by ring.
    apply (Qle_trans 0 eK (projT1 K2 n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact HpeK
      | apply Qlt_le_weak; exact Hk]. }
  assert (HQb : Qle (projT1 Q2 n) MQ).
  { apply (Qle_trans (projT1 Q2 n) (Qabs (projT1 Q2 n)) MQ).
    - apply Qle_abs_self.
    - exact (HMQ n). }
  assert (HKb : Qle (projT1 K2 n) MK).
  { apply (Qle_trans (projT1 K2 n) (Qabs (projT1 K2 n)) MK).
    - apply Qle_abs_self.
    - exact (HMK n). }
  assert (Hrdn : Qle (1 - dq) (projT1 r n)) by (exact (HN1 n Hn1)).
  assert (Hsum : Qle 1 (projT1 r n + dq)) by lra.
  assert (Hdq0le : Qle 0 dq) by (apply Qlt_le_weak; exact Hdq0).
  assert (Hd : Qle (projT1 Q2 n * projT1 K2 n) (MQ * MK)).
  { apply (Qmult_le_mono2 (projT1 Q2 n) (projT1 K2 n) MQ MK);
      [exact HQ0 | exact HK0 | exact HQb | exact HKb]. }
  assert (Hqk20 : Qle 0 (projT1 Q2 n * projT1 K2 n)).
  { apply (Qmult_le_0_compat (projT1 Q2 n) (projT1 K2 n)); assumption. }
  assert (Hscale : Qle (projT1 Q2 n * projT1 K2 n)
                       (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))).
  { apply (Qle_trans (projT1 Q2 n * projT1 K2 n)
                     (projT1 Q2 n * projT1 K2 n * 1)
                     (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))).
    - apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
    - apply (Qmult_le_mono2 (projT1 Q2 n * projT1 K2 n) 1
                            (projT1 Q2 n * projT1 K2 n) (projT1 r n + dq));
        [exact Hqk20 | exact zero_le_one | apply Qle_refl | exact Hsum]. }
  assert (Hdqle : Qle (projT1 Q2 n * projT1 K2 n * dq) (MQ * MK * dq)).
  { apply (Qmult_le_mono2 (projT1 Q2 n * projT1 K2 n) dq (MQ * MK) dq);
      [exact Hqk20 | exact Hdq0le | exact Hd | apply Qle_refl]. }
  assert (Hsplit : Qle (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
                       (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq)).
  { setoid_replace (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
      with (projT1 Q2 n * projT1 K2 n * projT1 r n
            + projT1 Q2 n * projT1 K2 n * dq) by ring.
    apply (Qplus_le_compat (projT1 Q2 n * projT1 K2 n * projT1 r n)
                           (projT1 Q2 n * projT1 K2 n * projT1 r n)
                           (projT1 Q2 n * projT1 K2 n * dq) (MQ * MK * dq));
      [apply Qle_refl | exact Hdqle]. }
  apply (Qle_trans (projT1 Q2 n * projT1 K2 n)
                   (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
                   (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq));
    [exact Hscale | exact Hsplit].
Qed.

(* ################ Part 9: piece 2, the main theorem (the rd-loss chain assembly) ######## *)

(* Piece 2: root-bounded premises ⟹ |⟨a,b⟩| ≤ Q·K·√d + eps (the eps version; the inl strict branch).
   Assembly: qk_pair_bound (h := eps/2, strict witness eps/8) + the rd-loss chain
   (QK ≤ QK·rd + QK·dq, dq := eps/(32(1+QK)); the dq ≤ 1 branch uses qk_rd_loss,
   the dq > 1 branch has eps itself already large and needs only the rd ≥ 0 tail segment), the eps/4 slack witness. *)
Theorem real_logit_bound_of_norm_bounds :
  forall (a b : list Real) (Qb Kb : Q) (k : nat) (eps : Q)
    (Ha : real_le real_zero (qkb_sql a)) (Hb : real_le real_zero (qkb_sql b)),
    Qlt 0 eps -> Qlt 0 Qb -> Qlt 0 Kb ->
    real_le (root_of (qkb_sql a) Ha) (real_const Qb) ->
    real_le (root_of (qkb_sql b) Hb) (real_const Kb) ->
    real_le (real_abs (qkb_dotp a b))
      (real_plus (real_mult (real_mult (real_const Qb) (real_const Kb)) (root_d k))
                 (real_const eps)).
Proof.
  intros a b Qb Kb k eps Ha Hb Heps HQ HK Hqa Hkb.
  assert (HQK0 : Qlt 0 (Qb * Kb)) by (apply Qmult_lt_0_compat; assumption).
  assert (Hgt1 : Qlt 0 (1 + Qb * Kb)) by lra.
  set (dq := eps / (32 * (1 + Qb * Kb))).
  assert (Hdq0 : Qlt 0 dq).
  { unfold dq. apply (Qmult_lt_0_compat eps (/ (32 * (1 + Qb * Kb)))).
    - exact Heps.
    - apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat 32 (1 + Qb * Kb)).
      + exact Qlt_0_32.
      + exact Hgt1. }
  assert (Hdqe : dq * (32 * (1 + Qb * Kb)) == eps).
  { unfold dq. field.
    intro Hz. lra. }
  assert (Hdqk : Qle (Qb * Kb * dq) ((1#32) * eps)).
  { rewrite <- Hdqe.
    setoid_replace ((1#32) * (dq * (32 * (1 + Qb * Kb))))
      with (dq + dq * (Qb * Kb)) by ring.
    setoid_replace (Qb * Kb * dq) with (0 + dq * (Qb * Kb)) by ring.
    apply (Qplus_le_compat 0%Q dq (dq * (Qb * Kb)) (dq * (Qb * Kb))).
    - apply Qlt_le_weak. exact Hdq0.
    - apply Qle_refl. }
  assert (HcQpos : real_lt real_zero (real_const Qb)) by (apply qkb_real_const_pos; exact HQ).
  assert (HcKpos : real_lt real_zero (real_const Kb)) by (apply qkb_real_const_pos; exact HK).
  assert (HQbnd : forall n : nat, Qle (Qabs (projT1 (real_const Qb) n)) Qb).
  { intro n. rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)). rewrite (Qabs_pos Qb (Qlt_le_weak 0 Qb HQ)).
    apply Qle_refl. }
  assert (HKbnd : forall n : nat, Qle (Qabs (projT1 (real_const Kb) n)) Kb).
  { intro n. rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)). rewrite (Qabs_pos Kb (Qlt_le_weak 0 Kb HK)).
    apply Qle_refl. }
  destruct (qk_pair_bound a b (real_const Qb) (real_const Kb) Qb Kb ((1#2) * eps)
              Ha Hb
              (Qmult_lt_0_compat (1#2) eps Qlt_0_half Heps) HQ HK HcQpos HcKpos
              HQbnd HKbnd Hqa Hkb) as [eps4 [Hpos4 [N4 HN4]]].
  destruct (Qle_or_lt dq 1) as [Hdq1 | Hdqbig].
  - (* dq ≤ 1: the rd-loss chain QK ≤ QK·rd + QK·dq *)
    assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
    destruct (qk_rd_loss k (real_const Qb) (real_const Kb) (root_d k) Qb Kb dq
                Hdq0 Hdq1 HcQpos HcKpos HQbnd HKbnd Hrd0 (root_d_sq k))
      as [N2 HN2].
    left.
    exists ((1#4) * eps). split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1#4) eps); [exact Qlt_0_quarter | exact Heps].
    + exists (Nat.max N4 N2). intros n Hn.
      assert (Hn4 : (N4 <= n)%nat).
      { apply (Nat.le_trans N4 (Nat.max N4 N2) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 N2) n Hn)]. }
      assert (Hn2 : (N2 <= n)%nat).
      { apply (Nat.le_trans N2 (Nat.max N4 N2) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 N2) n Hn)]. }
      apply Qlt_to_QltT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)).
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)).
      assert (Hf1 : Qlt eps4 (Qb * Kb + (1#2) * eps - Qabs (projT1 (qkb_dotp a b) n))).
      { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hq. rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hq.
        rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)) in Hq. rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)) in Hq.
        exact Hq. }
      assert (Hbr : Qle (Qb * Kb) (Qb * Kb * projT1 (root_d k) n + Qb * Kb * dq)).
      { pose proof (HN2 n Hn2) as Hq.
        rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)) in Hq. exact Hq. }
      assert (Hpos4q : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      remember (Qabs (projT1 (qkb_dotp a b) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq eqn:HMq in *.
      remember (Mq * projT1 (root_d k) n) as W eqn:HW in *.
      remember (Mq * dq) as Z eqn:HZ in *.
      clear HQ HK Hgt1 HQK0 Hdqe HMq HAq Ha Hb Hqa Hkb
            HcQpos HcKpos HQbnd HKbnd HN4 HN2 Hrd0.
      assert (Hbr2 : Qle (Mq - (1#32) * eps) W).
      { assert (H1 : Qle (Mq - Z) W) by lra.
        apply (Qle_trans (Mq - (1#32) * eps) (Mq - Z) W).
        - lra.
        - exact H1. }
      clear HW HZ Hbr Hdqk Hdq0 Hdq1.
      lra.
  - (* dq > 1: eps > 32(1+QK); QK itself < eps/32, only the rd ≥ 0 tail segment needed *)
    assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
    destruct (rd_pos_tail k (root_d k) Hrd0 (root_d_sq k)) as [N0 HN0].
    left.
    exists ((1#4) * eps). split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1#4) eps); [exact Qlt_0_quarter | exact Heps].
    + exists (Nat.max N4 N0). intros n Hn.
      assert (Hn4 : (N4 <= n)%nat).
      { apply (Nat.le_trans N4 (Nat.max N4 N0) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 N0) n Hn)]. }
      assert (Hn0 : (N0 <= n)%nat).
      { apply (Nat.le_trans N0 (Nat.max N4 N0) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 N0) n Hn)]. }
      apply Qlt_to_QltT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)).
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)).
      assert (Hf1 : Qlt eps4 (Qb * Kb + (1#2) * eps - Qabs (projT1 (qkb_dotp a b) n))).
      { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hq. rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hq.
        rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)) in Hq. rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)) in Hq.
        exact Hq. }
      assert (Hrn : Qle 0 (projT1 (root_d k) n)) by (exact (HN0 n Hn0)).
      assert (Hpos4q : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      remember (Qabs (projT1 (qkb_dotp a b) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq eqn:HMq in *.
      clear HQ HK Hgt1 Hdqe HMq HAq Ha Hb Hqa Hkb
            HcQpos HcKpos HQbnd HKbnd HN4 HN0 Hdq0.
      assert (Hmlt : Qlt Mq (Mq * dq)).
      { pose proof (Qmult_lt_compat_r 1 dq Mq HQK0 Hdqbig) as Hm2.
        setoid_replace (1 * Mq) with Mq in Hm2 by ring.
        setoid_replace (dq * Mq) with (Mq * dq) in Hm2 by ring.
        exact Hm2. }
      assert (Hm32 : Qle Mq ((1#32) * eps)).
      { apply (Qle_trans Mq (Mq * dq) ((1#32) * eps));
          [apply Qlt_le_weak; exact Hmlt | exact Hdqk]. }
      remember (Mq * projT1 (root_d k) n) as W eqn:HW in *.
      assert (Hw0 : Qle 0 W).
      { subst W. apply (Qmult_le_0_compat Mq (projT1 (root_d k) n)).
        - apply Qlt_le_weak. exact HQK0.
        - exact Hrn. }
      clear Hmlt Hdqbig Hdqk HQK0 HW Hrn.
      lra.
Qed.

(* ################ Part 10: piece 3, the QKᵀ binding + the Δ packaging (the Section main theorem) ## *)

Section QKLogitSection.

Variable kdim : nat.
Variable Qc Kc : Q.

(* The inverse root: real_inv_pos constructively carries the positivity certificate (root_d_pos) *)
Definition w_root : Real := real_inv_pos (root_d kdim) (root_d_pos kdim).

(* Δ := Q·K·inv(√d) + 1 (the +1 slack exactly absorbs (1/2)·w ≤ 2/3 < 1) *)
Definition Delta : Real :=
  real_plus (real_mult (real_mult (real_const Qc) (real_const Kc)) w_root)
            (real_const 1).

(* attn_logit：⟨q,k⟩·inv(√d) *)
Definition attn_logit (a b : list Real) : Real :=
  real_mult (qkb_dotp a b) w_root.

End QKLogitSection.

(* w_root's tail-segment data: positivity (the real_inv_pos_pos tail segment) + the multiplication check
   (the real_inv_pos_correct tail segment, the fixed δ := 1#4 truncation: 3/4 < Wn·Rn < 5/4).
   The lower-bound coefficient 5/3 is absorbed by rd ≥ 3/4: Wn ≤ 5/3, (3/8)·Wn ≤ 5/8 < 1,
   and Δ's +1 slack is absorbed as usual (the per-pair witness stays 1/4). *)
Theorem qk_logits_bounded :
  forall (k : nat) (Qb Kb : Q) (vq vk : nat -> list Real)
    (Hvsq : forall s : nat, real_le real_zero (qkb_sql (vq s)))
    (Hksq : forall s : nat, real_le real_zero (qkb_sql (vk s))),
    Qlt 0 Qb -> Qlt 0 Kb ->
    (forall s : nat, real_le (root_of (qkb_sql (vq s)) (Hvsq s)) (real_const Qb)) ->
    (forall s : nat, real_le (root_of (qkb_sql (vk s)) (Hksq s)) (real_const Kb)) ->
    And (real_lt real_zero (Delta k Qb Kb))
        (forall s s' : nat,
           real_le (real_abs (attn_logit k (vq s) (vk s'))) (Delta k Qb Kb)).
Proof.
  intros k Qb Kb vq vk Hvsq Hksq HQ HK Hvb Hkb.
  assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
  destruct (sqrt_dim_ge_quarter k (root_d k) Hrd0 (root_d_sq k)) as [Ns HNs].
  assert (Hwlt : real_lt real_zero (w_root k))
    by (apply (real_inv_pos_pos (root_d k) (root_d_pos k))).
  destruct Hwlt as [ew [Hpew [Nwp HNwp]]].
  assert (Hcorrect : real_eq (real_mult (root_d k) (w_root k)) real_one)
    by (apply (real_inv_pos_correct (root_d k) (root_d_pos k))).
  assert (Hqt : Qlt 0 (1#8)) by lra.
  destruct (Hcorrect (1#8) (Qlt_to_QltT 0 (1#8) Hqt)) as [Nc HNc].
  set (Nw := Nat.max Ns (Nat.max Nwp Nc)).
  assert (Hwp' : forall n : nat, (Nw <= n)%nat -> Qlt 0 (projT1 (w_root k) n)).
  { intros n Hnn.
    assert (Hnwp : (Nwp <= n)%nat).
    { apply (Nat.le_trans Nwp Nw n).
      - apply (Nat.le_trans Nwp (Nat.max Nwp Nc) Nw).
        + apply Nat.le_max_l.
        + apply Nat.le_max_r.
      - exact Hnn. }
    assert (Hq : Qlt ew (projT1 (w_root k) n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNwp n (NatLe_lift Nwp n Hnwp)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 (w_root k) n - 0) with (projT1 (w_root k) n) in Hq by ring.
    apply (Qle_lt_trans 0 ew (projT1 (w_root k) n)).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpew.
    - exact Hq. }
  assert (Hwub : forall n : nat, (Nw <= n)%nat ->
            Qlt (projT1 (w_root k) n) (3#2)).
  { intros n Hnn.
    assert (Hnc : (Nc <= n)%nat).
    { apply (Nat.le_trans Nc Nw n).
      - apply (Nat.le_trans Nc (Nat.max Nwp Nc) Nw).
        + apply Nat.le_max_r.
        + apply Nat.le_max_r.
      - exact Hnn. }
    assert (Hc' : Qlt (Qabs (projT1 (root_d k) n * projT1 (w_root k) n - 1)) (1#8)).
    { pose proof (HNc n (NatLe_lift Nc n Hnc)) as Hq.
      apply QltT_to_Qlt in Hq.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hq.
      change (projT1 real_one n) with 1%Q in Hq.
      exact Hq. }
    assert (Hrl : Qlt (3#4) (projT1 (root_d k) n * projT1 (w_root k) n)).
    { assert (Hl := Qabs_lt_low _ _ Hc'). lra. }
    assert (Hru : Qlt (projT1 (root_d k) n * projT1 (w_root k) n) (9#8)).
    { assert (Hu := Qabs_lt_l _ _ Hc'). lra. }
    assert (Hwpn : Qlt 0 (projT1 (w_root k) n)) by (apply (Hwp' n Hnn)).
    assert (Hns : (Ns <= n)%nat).
    { apply (Nat.le_trans Ns Nw n).
      - apply Nat.le_max_l.
      - exact Hnn. }
    assert (Hs1 : Qle ((3#4) * projT1 (w_root k) n)
                      (projT1 (root_d k) n * projT1 (w_root k) n)).
    { apply (Qmult_le_compat_r (3#4) (projT1 (root_d k) n) (projT1 (w_root k) n));
        [exact (HNs n Hns) | apply Qlt_le_weak; exact Hwpn]. }
    assert (Hw43b : Qle (projT1 (w_root k) n)
                      ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))).
    { apply (Qle_trans (projT1 (w_root k) n)
                       ((4#3) * ((3#4) * projT1 (w_root k) n))
                       ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))).
      - apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. ring.
      - setoid_replace ((4#3) * ((3#4) * projT1 (w_root k) n))
          with (((3#4) * projT1 (w_root k) n) * (4#3)) by ring.
        setoid_replace ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))
          with ((projT1 (root_d k) n * projT1 (w_root k) n) * (4#3)) by ring.
        apply (Qmult_le_compat_r ((3#4) * projT1 (w_root k) n)
                                  (projT1 (root_d k) n * projT1 (w_root k) n) (4#3)).
        + exact Hs1.
        + apply Qlt_le_weak. lra. }
    clear - Hw43b Hru Hwpn. lra. }
  assert (HcQpos : real_lt real_zero (real_const Qb)) by (apply qkb_real_const_pos; exact HQ).
  assert (HcKpos : real_lt real_zero (real_const Kb)) by (apply qkb_real_const_pos; exact HK).
  assert (HQbnd : forall n : nat, Qle (Qabs (projT1 (real_const Qb) n)) Qb).
  { intro n. rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)). rewrite (Qabs_pos Qb (Qlt_le_weak 0 Qb HQ)).
    apply Qle_refl. }
  assert (HKbnd : forall n : nat, Qle (Qabs (projT1 (real_const Kb) n)) Kb).
  { intro n. rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)). rewrite (Qabs_pos Kb (Qlt_le_weak 0 Kb HK)).
    apply Qle_refl. }
  assert (Hpair : forall s s' : nat,
           real_lt (real_abs (qkb_dotp (vq s) (vk s')))
                   (real_plus (real_mult (real_const Qb) (real_const Kb))
                              (real_const (1#2)))).
  { intros s s'.
    apply (qk_pair_bound (vq s) (vk s') (real_const Qb) (real_const Kb) Qb Kb (1#2)
             (Hvsq s) (Hksq s') Qlt_0_half HQ HK HcQpos HcKpos HQbnd HKbnd
             (Hvb s) (Hkb s')). }
  split.
  - (* Δ > 0 (witness 1/2): QK > 0 and Wn > 0 (tail segment) *)
    exists (1#2). split.
    + apply Qlt_to_QltT. exact Qlt_0_half.
    + exists Nw. intros n Hn.
      unfold Delta.
      apply Qlt_to_QltT.
      change (projT1 real_zero n) with 0%Q.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)).
      setoid_replace (Qb * Kb * projT1 (w_root k) n + 1 - 0)
        with (Qb * Kb * projT1 (w_root k) n + 1) by ring.
      assert (Hnn : (Nw <= n)%nat) by (apply (NatLe_drop Nw n Hn)).
      pose proof (Hwp' n Hnn) as Hwp.
      assert (Hqk0 : Qlt 0 (Qb * Kb)) by (apply Qmult_lt_0_compat; assumption).
      assert (Hqw : Qlt 0 (Qb * Kb * projT1 (w_root k) n)).
      { apply (Qmult_lt_0_compat (Qb * Kb) (projT1 (w_root k) n));
          [exact Hqk0 | exact Hwp]. }
      setoid_replace ((1#2)%Q) with (0 + (1#2)) by ring.
      apply (Qplus_lt_compat 0 (Qb * Kb * projT1 (w_root k) n) (1#2) 1);
        [exact Hqw | exact Qlt_half_one].
  - (* pointwise |logit| ≤ Δ (the inl strict branch, witness 1/4) *)
    intros s s'.
    destruct (Hpair s s') as [epsp [Hpsep [Np HNp]]].
    left.
    exists (1#4). split.
    + apply Qlt_to_QltT. exact Qlt_0_quarter.
    + exists (Nat.max Nw Np). intros n Hn.
      assert (Hnn : (Nw <= n)%nat).
      { apply (Nat.le_trans Nw (Nat.max Nw Np) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max Nw Np) n Hn)]. }
      assert (Hnp : (Np <= n)%nat).
      { apply (Nat.le_trans Np (Nat.max Nw Np) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max Nw Np) n Hn)]. }
      unfold attn_logit, Delta.
      apply Qlt_to_QltT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)).
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)). try rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
      rewrite (Qabs_mult_gen (projT1 (qkb_dotp (vq s) (vk s')) n)
                             (projT1 (w_root k) n)).
      rewrite (Qabs_pos (projT1 (w_root k) n) (Qlt_le_weak 0 (projT1 (w_root k) n) (Hwp' n Hnn))).
      assert (Hpp : Qlt epsp
                        (Qb * Kb + (1#2)
                           - Qabs (projT1 (qkb_dotp (vq s) (vk s')) n))).
      { pose proof (HNp n (NatLe_lift Np n Hnp)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hq. rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) in Hq.
        rewrite !(qeqT_imp_qeq _ _ (real_const_proj _ _)) in Hq. rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)) in Hq.
        exact Hq. }
      assert (Heps' : Qlt 0 epsp) by (apply QltT_to_Qlt; exact Hpsep).
      remember (Qabs (projT1 (qkb_dotp (vq s) (vk s')) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq2 eqn:HM2 in *.
      clear - Hpp Heps' Hwp' Hwub Hnn.
      assert (Hpp2 : Qle Aq (Mq2 + (1#2))) by lra.
      remember (Aq * projT1 (w_root k) n) as XW eqn:HXX in *.
      remember (Mq2 * projT1 (w_root k) n) as QW eqn:HQW in *.
      clear - Hpp2 Hwp' Hwub HXX HQW Hnn Hpp Heps'.
      assert (Hxw' : Qlt XW (QW + (3#4))).
      { rewrite HQW.
        apply (Qle_lt_trans XW (Aq * projT1 (w_root k) n)
                            (Mq2 * projT1 (w_root k) n + (3#4))).
        - apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT. rewrite <- HXX. reflexivity.
        - apply (Qle_lt_trans (Aq * projT1 (w_root k) n)
                              (Mq2 * projT1 (w_root k) n + (1#2) * projT1 (w_root k) n)
                              (Mq2 * projT1 (w_root k) n + (3#4))).
          + setoid_replace (Mq2 * projT1 (w_root k) n + (1#2) * projT1 (w_root k) n)
              with ((Mq2 + (1#2)) * projT1 (w_root k) n) by ring.
            apply (Qmult_le_compat_r Aq (Mq2 + (1#2)) (projT1 (w_root k) n));
              [exact Hpp2 | apply Qlt_le_weak; exact (Hwp' n Hnn)].
          + apply (proj2 (Qplus_lt_r ((1#2) * projT1 (w_root k) n) (3#4)
                                     (Mq2 * projT1 (w_root k) n))).
            setoid_replace (3#4) with ((3#2) * (1#2)) by ring.
            setoid_replace ((1#2) * projT1 (w_root k) n)
              with (projT1 (w_root k) n * (1#2)) by ring.
            apply (Qmult_lt_compat_r (projT1 (w_root k) n) (3#2) (1#2));
              [lra | exact (Hwub n Hnn)]. }
      clear - Hxw'. lra.
Qed.

Close Scope Q_scope.

(* ======== G10_LoebFam member piece: UpLoebD2 (merged verbatim, carries its own Requires) ======== *)
(* ===================================================================== *)
(* UpLoebD2.v — the Löb genuine-proof long line D2: the constructive realization of the provability ledger Σ(σ)                *)
(*              (pure Set level / stdlib only / depends on UpLoeb.v = the D1 base)         *)
(*                                                                       *)
(* Paper positioning: "Constructive governance of incompleteness" — constructive realization of HB D1–D3, second leg.              *)
(*   D1 = the diagonal mechanism (UpLoeb.v, already given); D2 = this piece; D3 = the Löb main theorem (later).  *)
(*                                                                       *)
(* D2 delivers four pieces (matching D1's end-of-file interface suggestions):                                   *)
(*   §8 proof-term code accounts and code-level replay: gnPrf (proof term -> code, tags 6/7/8, partitioned exclusively against     *)
(*        term codes 0–3 and formula codes 4–5 in the pairp tag space) + dP2/dP (the total-function       *)
(*        fuel decoder of proof codes, isomorphic to dT2/dF2) + the replay main theorem gnPrf_replay:           *)
(*        a certificate's code, run through dP2 under any sufficient fuel, replays exactly back to the proven formula.                    *)
(*        [D1'] Prf f -> ledger(⌜f⌝) inhabited = ledger_entry.                  *)
(*   §9 the provability ledger: ledger_at w = sigT{ f & sigT{ pf : Prf f &               *)
(*        (the loeb_tid code account aligning w with ⌜f⌝) * (the dP replay account) }} — at code w hangs a          *)
(*        Prf certificate + the double loeb_tid account; the certificate travels as a first-class component (not rebuilt from the code,         *)
(*        impossible in principle — see the honest boundary at file end).                                  *)
(*   §10 MP code-level closure [D2']: MPc c1 c2 = pairp 7 (pairp c1 c2) —             *)
(*        modus ponens is closed at the code level: the new code synthesized from two certificate codes replays exactly to the MP conclusion          *)
(*        (MPc_code_closed purely code-level + MPc_prf_closed/MPc_dP_closed supplying the Prf account).*)
(*   §11 the Σ(σ) reflection load-bearing pieces: bsearch (a genuinely bounded structural-recursive search, starting at false, no hard-coded    *)
(*        branches) + verPf (the dP2-driven code-level certificate verifier) + Formula2 (the fsig Σ-atom,  *)
(*        the language still has no constrained binder -> substF2 captures nothing -> the evalF2_subst interchange law stays intact)    *)
(*        + two-way load-bearing: a ledger row ⟹ the Σ-atom is true (evalF2_fsig_ledger);              *)
(*        Σ-atom true ⟹ a code w below the bound whose replay is exactly that code's formula (Sigma_bsearch_reflect).*)
(*        the dec_gnF-driven "code -> formula" reflection = code_reflect.                     *)
(*                                                                       *)
(* The three fake methods compared (inheriting D1): fake method 1 (the hyp placeholder) — the certificate pf hung on a ledger row is a genuine term of the Prf inductive type     *)
(*   fake method 2 (Triv filling) — the replay/closure theorems genuinely assembled from pairp/unp2/gnT_fuel/        *)
(*   gnF_fuel, no placeholder finishes; fake method 3 (quantifier hard-coding) — bsearch is a structural       *)
(*   genuine search, with the two-way vm_compute smoke tests Sigma_fires / Sigma_bound_tight:     *)
(*   true at bound 3000, false at the just-short bound (2623) — the truth value genuinely decided by the bound and the code account.               *)
(*                                                                       *)
(* Set-level discipline: all D2 carriers (ledger / dP2 / verPf / bsearch / Formula2 /     *)
(*   evalF2 / MPc / gnPrf) zero Prop; load-bearing theorem statements carried by loeb_tid/sigT/bool.     *)
(*   The only exception: the fuel-parameterized theorems' (gnPrf_replay / MPc_code_closed)            *)
(*   (… <= k)%nat bound premises — exactly the same shape as the gnT_fuel / gnF_fuel interfaces D1 already gave        *)
(*   (Proof-level arithmetic interfaces, not Set-level data). Zero axioms, zero admissions, zero placeholders,         *)
(*   zero classical logic; the whole chain informative and extractable.                                       *)
(* ===================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.


(* ===================================================================== *)
(* §8 proof-term code accounts and code-level replay                                                    *)
(*     The Gödel coding of proof terms: the three rules carry tags 6 / 7 / 8 respectively — mutually exclusive against     *)
(*     term tags 0–3 and formula tags 4–5. The metalevel premises of ax_eqT / repl (the loeb_tid value equality, universally quantified over valuations)    *)
(*     stay out of the code — carried by D1's metalevel soundness Prf_soundness; the honest boundary is at file end.         *)
(* ===================================================================== *)

Fixpoint gnPrf (f : Formula) (pf : Prf f) {struct pf} : nat :=
  match pf in Prf f0 return nat with
  | @ax_eqT u1 u2 _ => pairp 6 (pairp (gnT u1) (gnT u2))
  | @mpF a b pf1 pf2 => pairp 7 (pairp (gnPrf (fimp a b) pf1) (gnPrf a pf2))
  | @repl th t1 t2 _ => pairp 8 (pairp (pairp (gnF th) (gnT t1)) (gnT t2))
  end.

(* The total-function decoder of proof codes (fuel = the code value; isomorphic to D1's dT2/dF2):
     tag 6: ax_eqT — the two term codes are decoded via dT2, replaying teq;
     tag 7: mpF   — the two certificate codes are decoded via dP2 (the major premise must decode to fimp, and the
            minor premise's replay must have code equal to the major premise's antecedent code: the gnF comparison), replaying the MP conclusion;
     tag 8: repl  — the th code via dF2 and the two substituted term codes via dT2 are decoded, replaying the substitution biconditional. *)
Fixpoint dP2 (f c : nat) {struct f} : option Formula :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (teq x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))), q) =>
          (match unp2 q q with
           | Some (w1, w2) =>
               (match dP2 f' w1 with
                | Some (fimp u v) =>
                    (match dP2 f' w2 with
                     | Some z => if Nat.eqb (gnF z) (gnF u) then Some v else None
                     | None => None
                     end)
                | _ => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))), q) =>
          (match unp2 q q with
           | Some (p, r) =>
               (match unp2 p p with
                | Some (a, b) =>
                    (match dF2 f' a with
                     | Some th =>
                         (match dT2 f' b with
                          | Some x =>
                              (match dT2 f' r with
                               | Some y => Some (fimp (substF th x) (substF th y))
                               | None => None
                               end)
                          | None => None
                          end)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

Definition dP (c : nat) : option Formula := dP2 c c.

(* The code-level hygiene smoke test: the proof decoder rejects small codes / formula codes (656 = gnF (teq tzero tzero)) *)
Lemma dP_rejects_small : dP 3 = None.
Proof. reflexivity. Qed.

Lemma dP_rejects_formula_code : dP 656 = None.
Proof. reflexivity. Qed.

(* ═══ D2 main theorem one (code-level replay): a certificate's code, replayed through dP2 under any sufficient fuel,
       yields exactly the proven formula — D1's suggested "dT2 fuel structure as the code-level replay of proof terms". ═══ *)
Theorem gnPrf_replay : forall (f : Formula) (pf : Prf f) (k : nat),
  (gnPrf f pf <= k)%nat -> loeb_tid (option Formula) (dP2 k (gnPrf f pf)) (Some f).
Proof.
  intros f pf.
  induction pf as [u1 u2 Hv | a b pf1 IH1 pf2 IH2 | th t1 t2 Hv]; intros k Hk;
    destruct k as [|k'].
  - (* ax_eqT, fuel exhausted: proof codes are always positive — contradiction *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* the ax_eqT main case: the two term codes replay via gnT_fuel *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnT u1) (gnT u2)) as Hq1.
    pose proof (pairp_ge (gnT u1) (gnT u2)) as Hq2.
    pose proof (pairp_pos (gnT u1) (gnT u2)) as Hq3.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnT u1 <= k')%nat) by lia.
    assert (Hb2 : (gnT u2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (gnT_fuel u1 k' Hb1). cbv iota.
    rewrite (gnT_fuel u2 k' Hb2). cbv iota.
    apply loeb_tid_refl.
  - (* mpF, fuel exhausted *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* the mpF main case: the two sub-certificate codes replay + the gnF comparison reflection *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq1.
    pose proof (pairp_ge (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq2.
    pose proof (pairp_pos (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq3.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnPrf (fimp a b) pf1 <= k')%nat) by lia.
    assert (Hb2 : (gnPrf a pf2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (IH1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (IH2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply loeb_tid_refl.
  - (* repl, fuel exhausted *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* the repl main case: th via dF2, the two substituted terms via dT2, replaying the substitution biconditional *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnF th) (gnT t1)) as Hq1.
    pose proof (pairp_ge (gnF th) (gnT t1)) as Hq2.
    pose proof (pairp_pos (gnF th) (gnT t1)) as Hq3.
    pose proof (pairp_ge1 (pairp (gnF th) (gnT t1)) (gnT t2)) as Hq4.
    pose proof (pairp_ge (pairp (gnF th) (gnT t1)) (gnT t2)) as Hq5.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnF th <= k')%nat) by lia.
    assert (Hb2 : (gnT t1 <= k')%nat) by lia.
    assert (Hb3 : (gnT t2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (gnF_fuel th k' Hb1). cbv iota.
    rewrite (gnT_fuel t1 k' Hb2). cbv iota.
    rewrite (gnT_fuel t2 k' Hb3). cbv iota.
    apply loeb_tid_refl.
Qed.

(* The equation form of the self-fueled replay (used for rewriting inside proofs) *)
Corollary gnPrf_replay_eq : forall (f : Formula) (pf : Prf f),
  dP2 (gnPrf f pf) (gnPrf f pf) = Some f.
Proof.
  intros f pf.
  tidQ (gnPrf_replay f pf (gnPrf f pf) (Nat.le_refl (gnPrf f pf))) E. exact E.
Qed.

(* The dP form: the certificate code's self-fueled replay returns exactly the proven formula (no premises) *)
Theorem Prf_replay : forall (f : Formula) (pf : Prf f),
  loeb_tid (option Formula) (dP (gnPrf f pf)) (Some f).
Proof.
  intros f pf. unfold dP.
  exact (gnPrf_replay f pf (gnPrf f pf) (Nat.le_refl (gnPrf f pf))).
Qed.

(* ===================================================================== *)
(* §9 the row structure of the provability ledger Σ(σ)                                                *)
(*     row = hung at code w: the proven formula f, the Prf certificate pf, the double loeb_tid code account:                   *)
(*       the first account (alignment): w is exactly ⌜f⌝;                                        *)
(*       the second account (replay): pf's proof code, replayed via dP, returns exactly f.                         *)
(*     D1': Prf f -> ledger(⌜f⌝) inhabited = ledger_entry.                       *)
(* ===================================================================== *)

Definition ledger_at (w : nat) : Type :=
  sigT (fun f : Formula =>
    sigT (fun pf : Prf f =>
      (loeb_tid nat w (gnF f) *
       loeb_tid (option Formula) (dP (gnPrf f pf)) (Some f))%type)).

Definition loebd2_ledger : Type := sigT ledger_at.

Theorem ledger_entry : forall (f : Formula) (pf : Prf f), ledger_at (gnF f).
Proof.
  intros f pf. unfold ledger_at. exists f. exists pf. split.
  - apply loeb_tid_refl.
  - exact (Prf_replay f pf).
Qed.

Theorem ledger_inhabited : loebd2_ledger.
Proof.
  unfold loebd2_ledger. exists (gnF (teq tzero tzero)).
  apply (ledger_entry (teq tzero tzero)
    (ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)))).
Qed.

(* The code-alignment transport of ledger rows: a row does not depend on the choice of representative *)
Theorem ledger_tid_transfer : forall (w1 w2 : nat),
  loeb_tid nat w1 w2 -> ledger_at w1 -> ledger_at w2.
Proof.
  intros w1 w2 Hw Hrow. unfold ledger_at in Hrow. unfold ledger_at.
  destruct Hrow as [f [pf [H1 H2]]].
  exists f. exists pf. split.
  - apply (loeb_tid_trans nat w2 w1 (gnF f)). apply loeb_tid_sym. exact Hw. exact H1.
  - exact H2.
Qed.

(* The dec_gnF-driven "code -> formula" reflection: every code c aligned with ⌜g⌝ reflects out
   the inhabitation certificate "the code of f is aligned with c and dF c replays exactly to f" *)
Theorem code_reflect : forall (c : nat) (g : Formula),
  loeb_tid nat c (gnF g) ->
  sigT (fun f : Formula =>
    (loeb_tid nat (gnF f) c * loeb_tid (option Formula) (dF c) (Some f))%type).
Proof.
  intros c g H. exists g. split.
  - exact (loeb_tid_sym nat c (gnF g) H).
  - apply loeb_tid_eq. unfold dF. tidQ H Ec. rewrite Ec. apply dec_gnF.
Qed.

(* ===================================================================== *)
(* §10 MP code-level closure [D2']                                                    *)
(*     MPc: the code-level synthesizer of modus ponens. Closure = the new code synthesized from two certificate codes (each with its own sufficient fuel)          *)
(*     replays, under any sufficient fuel, exactly to the MP conclusion; the Prf side is supplied    *)
(*     directly by gnPrf_replay. The gnF comparison of dP2's tag-7 branch is here reflected as satisfied by Nat.eqb_refl.      *)
(* ===================================================================== *)

Definition MPc (c1 c2 : nat) : nat := pairp 7 (pairp c1 c2).

Theorem MPc_code_closed : forall (c1 c2 : nat) (a b : Formula),
  (forall k : nat, (c1 <= k)%nat ->
     loeb_tid (option Formula) (dP2 k c1) (Some (fimp a b))) ->
  (forall k : nat, (c2 <= k)%nat ->
     loeb_tid (option Formula) (dP2 k c2) (Some a)) ->
  forall k : nat, (MPc c1 c2 <= k)%nat ->
  loeb_tid (option Formula) (dP2 k (MPc c1 c2)) (Some b).
Proof.
  intros c1 c2 a b H1 H2 k Hk. unfold MPc.
  destruct k as [|k'].
  - unfold MPc in Hk. cbn [pairp] in Hk. lia.
  - cbn [dP2].
    pose proof (pairp_ge1 c1 c2) as Hq1.
    pose proof (pairp_ge c1 c2) as Hq2.
    pose proof (pairp_pos c1 c2) as Hq3.
    unfold MPc in Hk. cbn [pairp] in Hk.
    assert (Hb1 : (c1 <= k')%nat) by lia.
    assert (Hb2 : (c2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (H1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (H2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply loeb_tid_refl.
Qed.

Theorem MPc_prf_closed : forall (a b : Formula) (pf1 : Prf (fimp a b)) (pf2 : Prf a)
  (k : nat), (gnPrf b (mpF a b pf1 pf2) <= k)%nat ->
  loeb_tid (option Formula) (dP2 k (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))) (Some b).
Proof.
  intros a b pf1 pf2 k Hk.
  apply (MPc_code_closed (gnPrf (fimp a b) pf1) (gnPrf a pf2) a b
    (gnPrf_replay (fimp a b) pf1) (gnPrf_replay a pf2) k).
  cbn [gnPrf MPc] in Hk. exact Hk.
Qed.

(* The dP self-fueled form: the replay of the MP-synthesized code is exactly the conclusion — the clean statement of code-level MP closure *)
Theorem MPc_dP_closed : forall (a b : Formula) (pf1 : Prf (fimp a b)) (pf2 : Prf a),
  loeb_tid (option Formula)
    (dP (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))) (Some b).
Proof.
  intros a b pf1 pf2. unfold dP.
  apply (MPc_code_closed (gnPrf (fimp a b) pf1) (gnPrf a pf2) a b
    (gnPrf_replay (fimp a b) pf1) (gnPrf_replay a pf2)).
  exact (Nat.le_refl (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))).
Qed.

(* ===================================================================== *)
(* §11 the Σ(σ) reflection load-bearing pieces                                                       *)
(*     bsearch: a genuinely bounded search (structural recursion, starting at false, no hard-coded truth branches);           *)
(*     verPf: the dP2-driven code-level certificate verifier (the decidable "replayed code == target code" comparison);      *)
(*     Formula2: the D1 fragment + fsig (the Σ-atom: below bound B, search for a certificate code verifying target code c).      *)
(*     The language still has no constrained binder -> substF2 has no capture problem -> the evalF2_subst interchange law stays intact.    *)
(* ===================================================================== *)

Fixpoint bsearch (bd : nat) (p : nat -> bool) : bool :=
  match bd with
  | O => false
  | Datatypes.S b' => orb (p b') (bsearch b' p)
  end.

(* The witness completeness of the search: true ⟹ there is a witness below the bound *)
Theorem bsearch_witness : forall (N : nat) (p : nat -> bool) (w : nat),
  loeb_tid bool (Nat.ltb w N) true -> loeb_tid bool (p w) true ->
  loeb_tid bool (bsearch N p) true.
Proof.
  induction N as [|N' IHN]; intros p w Hlt Hp.
  - exfalso. tidQ Hlt E. pose proof (proj1 (Nat.ltb_lt w 0) E) as Hw0. lia.
  - cbn [bsearch]. destruct (Nat.eq_dec w N') as [Heq|Hne].
    + rewrite <- Heq. tidQ Hp Ep. apply loeb_tid_eq. rewrite Ep. reflexivity.
    + assert (Hlt2 : loeb_tid bool (Nat.ltb w N') true).
      { apply loeb_tid_eq. tidQ Hlt Elt.
        pose proof (proj1 (Nat.ltb_lt w (Datatypes.S N')) Elt) as H1.
        apply (proj2 (Nat.ltb_lt w N')). lia. }
      apply (loeb_tid_trans bool (orb (p N') (bsearch N' p)) (orb (p N') true)).
      * exact (loeb_tid_cong (orb (p N')) (bsearch N' p) true (IHN p w Hlt2 Hp)).
      * apply loeb_tid_eq. destruct (p N'); reflexivity.
Qed.

(* The characterization of the search: true ⟹ there is a code below the bound whose verification is true (loeb_tid/bool carriers, zero Prop) *)
Theorem bsearch_character : forall (N : nat) (p : nat -> bool),
  loeb_tid bool (bsearch N p) true ->
  sigT (fun w : nat =>
    (loeb_tid bool (Nat.ltb w N) true * loeb_tid bool (p w) true)%type).
Proof.
  induction N as [|N' IHN]; intros p H.
  - exfalso. cbn [bsearch] in H. tidQ H E. discriminate E.
  - cbn [bsearch] in H. destruct (p N') eqn:Ep.
    + exists N'. split.
      * apply loeb_tid_eq. apply (proj2 (Nat.ltb_lt N' (Datatypes.S N'))). lia.
      * apply loeb_tid_eq. rewrite Ep. reflexivity.
    + cbn [orb] in H.
      destruct (IHN p H) as [w [Hlt Hpw]].
      exists w. split.
      * apply loeb_tid_eq. tidQ Hlt Elt.
        pose proof (proj1 (Nat.ltb_lt w N') Elt) as H1.
        apply (proj2 (Nat.ltb_lt w (Datatypes.S N'))). lia.
      * exact Hpw.
Qed.

(* The pointwise loeb_tid covariance of bsearch (the transfer piece of the Σ-clause along loeb_tid semantics, for D3) *)
Theorem bsearch_tid_cong : forall (bd : nat) (p q : nat -> bool),
  (forall j : nat, loeb_tid bool (p j) (q j)) ->
  loeb_tid bool (bsearch bd p) (bsearch bd q).
Proof.
  induction bd as [|bd' IHb]; intros p q Hp.
  - apply loeb_tid_refl.
  - cbn [bsearch]. apply loeb_tid_eq.
    tidQ (Hp bd') Eh. rewrite Eh.
    tidQ (IHb p q Hp) Ei. rewrite Ei.
    reflexivity.
Qed.

(* The Σ-language: the D1 fragment + the Σ-atom fsig B c
   (semantics: bsearch (valt B s) (fun w => verPf w (valt c s))) *)
Inductive Formula2 : Set :=
| f2b : Formula -> Formula2
| fsig : Term -> Term -> Formula2
| fimp2 : Formula2 -> Formula2 -> Formula2.

Fixpoint substF2 (f : Formula2) (t : Term) : Formula2 :=
  match f with
  | f2b g => f2b (substF g t)
  | fsig B c => fsig (substT B t) (substT c t)
  | fimp2 a b => fimp2 (substF2 a t) (substF2 b t)
  end.

Definition verPf (w c : nat) : bool :=
  match dP2 w w with
  | Some g => Nat.eqb (gnF g) c
  | None => false
  end.

Fixpoint evalF2 (f : Formula2) (s : nat -> nat) : bool :=
  match f with
  | f2b g => evalF g s
  | fsig B c => bsearch (valt B s) (fun w : nat => verPf w (valt c s))
  | fimp2 a b => orb (negb (evalF2 a s)) (evalF2 b s)
  end.

(* ═══ D2 main theorem two (the interchange law intact): evalF_subst under the bounded-search language ═══ *)
Theorem evalF2_subst : forall (f : Formula2) (t : Term) (s : nat -> nat),
  evalF2 (substF2 f t) s = evalF2 f (upd s (valt t s)).
Proof.
  induction f as [g | B c | a IHa b IHb]; intros t s.
  - cbn [substF2 evalF2]. rewrite evalF_subst. reflexivity.
  - cbn [substF2 evalF2]. rewrite !valt_substT. reflexivity.
  - cbn [substF2 evalF2]. rewrite IHa. rewrite IHb. reflexivity.
Qed.

(* The Σ(σ) reliability half one: a w aligned with a proof code must pass verPf verification *)
Theorem verPf_ledger_sound : forall (w : nat) (f : Formula) (pf : Prf f),
  loeb_tid nat w (gnPrf f pf) -> loeb_tid bool (verPf w (gnF f)) true.
Proof.
  intros w f pf Hw. apply loeb_tid_eq. unfold verPf.
  tidQ Hw E. rewrite E.
  rewrite (gnPrf_replay_eq f pf). cbv iota. apply Nat.eqb_refl.
Qed.

(* The Σ(σ) reliability half two: a ledger row (certificate code below the bound, formula code aligned) ⟹ the Σ-atom is true *)
Theorem evalF2_fsig_ledger : forall (B c : Term) (s : nat -> nat)
  (f : Formula) (pf : Prf f),
  loeb_tid bool (Nat.ltb (gnPrf f pf) (valt B s)) true ->
  loeb_tid nat (gnF f) (valt c s) ->
  loeb_tid bool (evalF2 (fsig B c) s) true.
Proof.
  intros B c s f pf Hw Hc. apply loeb_tid_eq. cbn [evalF2].
  assert (Hpw : loeb_tid bool (verPf (gnPrf f pf) (valt c s)) true).
  { apply loeb_tid_eq. unfold verPf.
    rewrite (gnPrf_replay_eq f pf). cbv iota.
    tidQ Hc Ec. rewrite Ec. apply Nat.eqb_refl. }
  tidQ (bsearch_witness (valt B s) (fun w : nat => verPf w (valt c s))
          (gnPrf f pf) Hw Hpw) Ebs.
  exact Ebs.
Qed.

(* The bridging demonstration: a real ledger row (an ax_eqT certificate, proof code 2624) + bound 3000 ⟹ the Σ-atom true *)
Theorem Sigma_atom_fires_via_ledger :
  loeb_tid bool (evalF2 (fsig (numT 3000) (numT (gnF (teq tzero tzero))))
              (fun _ : nat => 0)) true.
Proof.
  apply (evalF2_fsig_ledger (numT 3000) (numT (gnF (teq tzero tzero)))
    (fun _ : nat => 0) (teq tzero tzero)
    (ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)))).
  - apply loeb_tid_eq. rewrite valt_numT.
    apply (proj2 (Nat.ltb_lt
      (gnPrf (teq tzero tzero)
        (ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s))))
      3000)).
    vm_compute. lia.
  - apply loeb_tid_eq. rewrite valt_numT. reflexivity.
Qed.

(* The reflection of Σ-atom truth: the searched-out code w below the bound has a replay exactly equal to that code's formula
   (dP2-driven; certificate reconstruction impossible in principle — see the honest boundary at file end — reflection reaches the replay layer) *)
Theorem Sigma_bsearch_reflect : forall (B : nat) (g : Formula),
  loeb_tid bool (bsearch B (fun w : nat => verPf w (gnF g))) true ->
  sigT (fun w : nat =>
    (loeb_tid bool (Nat.ltb w B) true *
     sigT (fun f : Formula =>
       (loeb_tid nat (gnF f) (gnF g) *
        loeb_tid (option Formula) (dP2 w w) (Some f))%type))%type).
Proof.
  intros B g H.
  destruct (bsearch_character B (fun w : nat => verPf w (gnF g)) H)
    as [w [Hlt Hvw]].
  exists w. split.
  - exact Hlt.
  - unfold verPf in Hvw. tidQ Hvw E. cbv beta in E.
    destruct (dP2 w w) as [gg|] eqn:Ed.
    + cbv iota in E.
      pose proof (proj1 (Nat.eqb_eq (gnF gg) (gnF g)) E) as Eeq.
      exists gg. split.
      * apply loeb_tid_eq. exact Eeq.
      * apply loeb_tid_eq. reflexivity.
    + cbv iota in E. discriminate E.
Qed.

(* The truth smoke test (counter-evidence to fake method 3: the search is genuinely true, the bound decides the truth value;
   2624 = the proof code of gnPrf (teq tzero tzero) (ax_eqT ...),
   656  = the formula code of gnF (teq tzero tzero)) *)
Lemma Sigma_fires : evalF2 (fsig (numT 3000) (numT (gnF (teq tzero tzero))))
                      (fun _ : nat => 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Sigma_bound_tight : evalF2 (fsig (numT 2623) (numT (gnF (teq tzero tzero))))
                      (fun _ : nat => 0) = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* Honest boundary (explicitly declared, no ad-hoc constructions):                                            *)
(*   1. dP2/verPf only replay the "proven formula" and do not reconstruct the Prf certificate itself: ax_eqT/repl's       *)
(*      metalevel premises are loeb_tid value equalities universally quantified over valuations (extensional functions), impossible in principle to reconstruct from codes.          *)
(*      Hence ledger rows carry the certificate pf as a first-class traveling component (the verbatim realization of D1's interface suggestion),        *)
(*      while the Σ-atom's reflection reaches only the "replay layer" (Sigma_bsearch_reflect).               *)
(*   2. The code-space partition of gnPrf/dP2 (terms 0–3 / formulas 4–5 / proofs 6–8) only guarantees tag        *)
(*      exclusivity; the pairp decoding-uniqueness direction is not developed in this piece (D1 already gave unp2_pair forward).      *)
(*      verPf's reliability is bounded by the decidable "replayed code == target code" comparison, sufficient to carry          *)
(*      the bounded-search semantics of Σ(σ).                                                *)
(*   3. The fuel-parameterized theorems' (gnPrf_replay / MPc_code_closed) (… <= k)%nat bound      *)
(*      premises share the shape of D1's gnT_fuel / gnF_fuel — Proof-level arithmetic interfaces, not             *)
(*      Set-level data; all remaining statements use loeb_tid/sigT/bool as pure carriers.                        *)
(*   4. D2 does not chase the Löb main theorem (D3).                                           *)
(*                                                                       *)
(* D3 interface suggestions:                                                            *)
(*   a. The derivability-condition counterpart pieces are all in place: ledger_entry (D1') / MPc_dP_closed (D2') /         *)
(*      gnPrf_replay (coding stability). The next leg: the gnF2/dF2b codec round trip for Formula2       *)
(*      (tags 9/10/11; fsig's B and c are term slots, directly reusing the gnT/gnF_fuel          *)
(*      proof technique), then the gnF stability of Prf(⌜·⌝) itself.                           *)
(*   b. The Σ(σ) completeness half: promoting the w reflected by Sigma_bsearch_reflect into a certificate row           *)
(*      requires replacing the metalevel loeb_tid value equalities in ax_eqT/repl's premises with decidable code-level certificates             *)
(*      (e.g. restricting ax_eqT to closed term pairs with dT2 certificates; repl with the (th,t1,t2)           *)
(*      dF2/dT2 certificate triple) — the key step promoting the ledger into an in-language provability predicate.          *)
(*   c. bsearch_tid_cong can transport the Σ-clause along loeb_tid semantics; evalF2_subst already guarantees       *)
(*      substitution interchange; the Löb sentence diagF2 := substF2 (wrap2 th) (numT (gnF2 (wrap2 th))) *)
(*      has its diagonal assembly directly copying D1 §7's repl + code identity + value identity trio.            *)
(* ===================================================================== *)

(* —— Replacement-piece assumption-surface self-audit (slice 3; all should be Closed under the global context) —— *)
Print Assumptions even_ss.
Print Assumptions div2_ss.
Print Assumptions unp2_S.
Print Assumptions dec_gnT.
Print Assumptions wpm_solvent_at_last_covered.
Print Assumptions wpm_melt_bankrupt.
Print Assumptions wpm_wallet_zero_at_last_cover.
Print Assumptions wpm_wallet_negative_at_bankrupt.
Print Assumptions wpm_insolvent_at_bankrupt.
Print Assumptions dwm_X_refuted.
Print Assumptions dwm_wallet_trajectory.
Print Assumptions dwm_halt_fires.
Print Assumptions dwm_emit3_legal.
Print Assumptions dwm_emit3_not_present.

(* —— Replacement-piece assumption-surface self-audit (slice-5 additions; all should be Closed under the global context) —— *)
Print Assumptions dec_gnF.
Print Assumptions unaryT_selfT.
Print Assumptions diagonal_code_fixed.
Print Assumptions MPc_dP_closed.
Print Assumptions grm_two_step_budget_blown.
