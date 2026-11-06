(* ConstructiveWorld-Set -- certifiable stopping-time primitives and GuardedChain conservation-break chains. *)

(** * UpStopTime: certifiable stopping times and the GuardedChain conservation-break chain.

    Mission.  Stopping times for geometric decay over decidable rational
      orders and the GuardedChain conservation-break chain: the CoInductive
      chain type [GChain] with its productive generator [grun] carries a
      strictly decreasing budget, read out by [gchain_budget], [gbudget_at],
      [ghead_at] and the detector [gbottom_at].  Main statements:
      [guarded_breaks], [minimal_stoptime], [st_dominance], with the searcher
      [stsearch] and the negative contrast [unguarded_no_stoptime].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lia], [Arith.PeanoNat].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5],
      [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [UpBudgetReal], [UpConstitution] of this development.

    References.  This development, UpStopTime.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpStopTime.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
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
Require Import UpBudgetReal.
Require Import UpConstitution.

Local Open Scope Q_scope.

(* ================= Section 0. Local bridges: nat order, boolean reflection, Q reshaping ================= *)

(* Both directions of the [NatLt] bridge; [NatLt] is literally
   [Id (Nat.ltb n m) true], and the library elimination and introduction
   lemmas sit behind a section boundary, so both are rebuilt here. *)
Lemma st_natlt_drop : forall n m : nat, NatLt n m -> (n < m)%nat.
Proof.
intros n m H. apply (proj1 (Nat.ltb_lt n m)).
apply RealSetoid.Id_eq. exact H.
Qed.

Lemma st_natlt_lift : forall n m : nat, (n < m)%nat -> NatLt n m.
Proof.
intros n m H. apply RealSetoid.eq_Id. apply (proj2 (Nat.ltb_lt n m)).
exact H.
Qed.

(* The [false] shape of [QltT]: no crossing at [x] forces [y <= x]; this is
   the minimality half of the minimal stopping time. *)
Lemma st_qlt_false_ge : forall x y : Q, Id (Qlt_bool x y) false -> QleT' y x.
Proof.
intros x y Hf.
destruct (Q_dec x y) as [[H1 | H2] | H3].
- exfalso.
  assert (Ht : QltT x y) by (apply Qlt_to_QltT; exact H1).
  pose proof (id_trans (id_sym Hf) Ht) as Hc. inversion Hc.
- apply Qle_to_QleT'. apply Qlt_le_weak. exact H2.
- apply uc_qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact H3.
Qed.

(* Left reshaping along [st_QId], the [Qeq_bool] reflection: [x == y] and
   [y < z] give [x < z]. *)
Definition st_QId (x y : Q) : Set := Id (Qeq_bool x y) true.

Lemma st_qid_refl : forall x : Q, st_QId x x.
Proof. intro x. apply sf_qeq_id. apply Qeq_refl. Qed.

Lemma st_qid_trans : forall a b c : Q, st_QId a b -> st_QId b c -> st_QId a c.
Proof.
intros a b c H1 H2. apply sf_qeq_id.
apply (Qeq_trans a b c (qeqT_imp_qeq a b (sf_id_qeq a b H1))
         (qeqT_imp_qeq b c (sf_id_qeq b c H2))).
Qed.

Lemma st_qltT_qid_l : forall x y z : Q, st_QId x y -> QltT y z -> QltT x z.
Proof.
intros x y z Hq Hlt.
apply (uc_qeq_lt_l y x z
         (qeq_imp_qeqT y x (Qeq_sym x y (qeqT_imp_qeq x y (sf_id_qeq x y Hq))))).
exact Hlt.
Qed.

(* [QltT] implies the [Qle] order, for statement positions that carry an
   order premise. *)
Lemma st_qle_of_ltT : forall x y : Q, QltT x y -> Qle x y.
Proof. intros x y H. apply Qlt_le_weak. apply QltT_to_Qlt. exact H. Qed.

(* Subtracting keeps upper bounds within one: from [Qle 0 k] one gets
   [Qle (1 - k) 1], via [Qplus_le_compat] and the opposite shift. *)
Lemma st_qle_one_minus : forall k : Q, Qle 0 k -> Qle (1 - k) 1.
Proof.
intros k Hk.
apply QleT'_to_Qle.
apply (uc_qeq_le_l (1 + (- k)) (1 - k)%Q 1%Q).
- apply qeq_imp_qeqT. apply Qeq_refl.
- apply (uc_qeq_le_r (1 + 0)%Q 1%Q (1 + (- k))%Q).
  + apply qeq_imp_qeqT. apply Qplus_0_r.
  + apply Qle_to_QleT'.
    apply Qplus_le_compat.
    * apply Qle_refl.
    * apply QleT'_to_Qle. apply (uc_opp_le_shift k (Qle_to_QleT' 0%Q k Hk)).
Qed.

(* The minimum of two nats, decided by [Nat.leb] and extractable. *)
Definition stmin (a b : nat) : nat := if Nat.leb a b then a else b.

Lemma stmin_le_l : forall a b : nat, NatLe b a -> Id (stmin a b) b.
Proof.
intros a b H. apply NatLe_drop in H. unfold stmin.
destruct (Nat.leb a b) eqn:E.
- apply Nat.leb_le in E. assert (Heq : a = b) by lia.
  rewrite Heq. reflexivity.
- reflexivity.
Qed.

Lemma stmin_le_r : forall a b : nat, NatLe a b -> Id (stmin a b) a.
Proof.
intros a b H. apply NatLe_drop in H. unfold stmin.
destruct (Nat.leb a b) eqn:E.
- reflexivity.
- apply Nat.leb_gt in E. assert (Heq : a = b) by lia.
  rewrite Heq. reflexivity.
Qed.

(* Nat order along [Id]: equal nats are comparable. *)
Lemma st_natle_of_id : forall n m : nat, Id n m -> NatLe n m.
Proof.
intros n m H. apply NatLe_lift. apply Nat.leb_le.
assert (E : n = m) by (apply RealSetoid.Id_eq; exact H).
rewrite E. apply Nat.leb_refl.
Qed.

(* ================= Section 1. The GuardedChain conservation-break chain ================= *)

(* The CoInductive type [GChain] is non-well-founded: each [gstep] produces
   its successor constructor, so productivity coincides with conservation.
   The node [gstop] is the bottomed node carrying the remaining budget and
   the final value; past it the budget reads zero and the value stays.  The
   generator [grun] is a CoFixpoint whose recursive call sits under the
   [gstep] constructor, with the budget decreasing strictly by one per
   layer; the guard condition is enforced statically by the guard checker. *)

CoInductive GChain : Set :=
| gstop : nat -> Q -> GChain
| gstep : nat -> Q -> GChain -> GChain.

(* The conservation generator: a geometric decay chain with rate [k],
   remaining budget [b] and accumulated value [c]. *)
CoFixpoint grun (k : Q) (b : nat) (c : Q) : GChain :=
  match b with
  | O => gstop 0 c
  | Datatypes.S b' => gstep (Datatypes.S b') c (grun k b' (c * (1 - k)))
  end.

(* Projections: budget and accumulated value at the chain head. *)
Definition gchain_budget (ch : GChain) : nat :=
  match ch with gstop b _ => b | gstep b _ _ => b end.

Definition gchain_head (ch : GChain) : Q :=
  match ch with gstop _ c => c | gstep _ c _ => c end.

(* Observers at depth [n]: budget, accumulated value, bottoming detection. *)

Fixpoint gbudget_at (n : nat) (ch : GChain) : nat :=
  match n with
  | O => gchain_budget ch
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => 0
      | gstep _ _ tl => gbudget_at m tl
      end
  end.

(*   Head-value convention (freezing): past a [gstop] node the accumulated
    value stays frozen. *)
Fixpoint ghead_at (n : nat) (ch : GChain) : Q :=
  match n with
  | O => gchain_head ch
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => gchain_head ch
      | gstep _ _ tl => ghead_at m tl
      end
  end.

(*   Bottoming detection: a [gstop] occurs within [n] steps, or a [gstep]
    node whose budget is already exhausted. *)
Fixpoint gbottom_at (n : nat) (ch : GChain) : bool :=
  match n with
  | O =>
      match ch with
      | gstop _ _ => true
      | gstep b _ _ => Nat.leb b 0
      end
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => true
      | gstep b _ tl => if Nat.leb b 0 then true else gbottom_at m tl
      end
  end.

(* The reference value sequence, the iterate form of c*(1-k)^n, shrinking in
   lockstep with [grun]. *)
Fixpoint gval (k : Q) (c : Q) (n : nat) : Q :=
  match n with
  | O => c
  | Datatypes.S m => gval k (c * (1 - k)) m
  end.

(* ---- Part 1 lemma group: conservation, budget monotonicity, head values ----- *)

(* Head projections of the generator: the budget at the chain head is the
   generated budget; destructing makes the match force the cofix to unfold. *)
Lemma grun_budget : forall (k : Q) (b : nat) (c : Q),
  Id (gchain_budget (grun k b c)) b.
Proof.
intros k b c. destruct b; reflexivity.
Qed.

Lemma grun_head : forall (k : Q) (b : nat) (c : Q),
  Id (gchain_head (grun k b c)) c.
Proof.
intros k b c. destruct b; reflexivity.
Qed.

(* Budget monotonicity: at any depth [n <= b] the budget is [b - n], the
   pointwise form of the strictly decreasing step. *)
Lemma grun_budget_at : forall (k : Q) (n : nat) (b : nat) (c : Q),
  NatLe n b -> Id (gbudget_at n (grun k b c)) (b - n)%nat.
Proof.
intros k n. induction n as [| n IH]; intros b c Hn.
- destruct b as [| b']; reflexivity.
- destruct b as [| b'].
  + reflexivity.
  + change (gbudget_at (Datatypes.S n) (grun k (Datatypes.S b') c))
      with (gbudget_at n (grun k b' (c * (1 - k)))).
    replace (Datatypes.S b' - Datatypes.S n)%nat with (b' - n)%nat by lia.
    apply IH. apply NatLe_lift. apply NatLe_drop in Hn. lia.
Qed.

(* Head-value trajectory: at any depth [n <= b] the accumulated value is the
   [n]-th term of the reference sequence. *)
Lemma grun_head_at : forall (k : Q) (n : nat) (b : nat) (c : Q),
  NatLe n b -> Id (ghead_at n (grun k b c)) (gval k c n).
Proof.
intros k n. induction n as [| n IH]; intros b c Hn.
- destruct b as [| b']; reflexivity.
- destruct b as [| b'].
  + exfalso. apply NatLe_drop in Hn. lia.
  + change (ghead_at (Datatypes.S n) (grun k (Datatypes.S b') c))
      with (ghead_at n (grun k b' (c * (1 - k)))).
    change (gval k c (Datatypes.S n)) with (gval k (c * (1 - k)) n).
    apply IH. apply NatLe_lift. apply NatLe_drop in Hn. lia.
Qed.

(* Multiplicative associativity on atomic variables: the ring procedure
   rejects terms containing subtractions, so the variable form comes first. *)
Lemma st_mult_assoc_qeq : forall (a b p : Q), (a * b) * p == a * (b * p).
Proof. intros a b p. ring. Qed.

(* The reference sequence equals the power form: [gval k c n] agrees with
   [c * (1 - k)^n] through the [st_QId] reflection. *)
Lemma gval_pow_QId : forall (k : Q) (n : nat) (c : Q),
  st_QId (gval k c n) (c * q_pow (1 - k) n).
Proof.
intros k n. induction n as [| n IH]; intros c.
- replace (q_pow (1 - k) 0) with 1%Q by reflexivity.
  apply sf_qeq_id. apply Qeq_sym. apply Qmult_1_r.
- change (gval k c (Datatypes.S n)) with (gval k (c * (1 - k)) n).
  change (q_pow (1 - k) (Datatypes.S n)) with ((1 - k) * q_pow (1 - k) n).
  assert (H1 : Id (Qeq_bool (gval k (c * (1 - k)) n)
                     ((c * (1 - k)) * q_pow (1 - k) n)) true)
    by exact (IH (c * (1 - k))).
  assert (H2 : Id (Qeq_bool ((c * (1 - k)) * q_pow (1 - k) n)
                     (c * ((1 - k) * q_pow (1 - k) n))) true)
    by (apply sf_qeq_id;
        exact (st_mult_assoc_qeq c (1 - k) (q_pow (1 - k) n))).
  exact (st_qid_trans _ _ _ H1 H2).
Qed.

(* Monotonicity of bottoming detection: bottoming within [n] steps persists
   at the successor depth.  Observing the successor step leaves the test
   [Nat.leb b 0] on the node budget stuck, so [b] is destructed directly and
   [Nat.leb (Datatypes.S b') 0] reduces definitionally to [false]. *)
Lemma gbottom_mono : forall (n : nat) (ch : GChain),
  Id (gbottom_at n ch) true -> Id (gbottom_at (Datatypes.S n) ch) true.
Proof.
intros n. induction n as [| n IH]; intros ch H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbottom_at 0%nat (gstep (Datatypes.S b') c tl)) with false in H.
      inversion H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbottom_at (Datatypes.S (Datatypes.S n)) (gstep (Datatypes.S b') c tl))
        with (gbottom_at (Datatypes.S n) tl).
      apply IH.
      change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl) in H.
      exact H.
Qed.

(* Bottoming zeroes the budget at the successor depth (zeroing convention).
   The premise of a strict decrease at every step rules out hollow chains
   that keep stepping after the budget reaches zero; that premise is exactly
   the GuardedChain discipline.  With [b] destructed directly, a single
   application of the decreasing premise, and the [Id_eq] reshaping into nat
   order, the arithmetic closes by [lia]. *)
Lemma gbottom_true_spend : forall (n : nat) (ch : GChain),
  (forall m : nat, NatLt (gbudget_at (Datatypes.S m) ch) (gbudget_at m ch)) ->
  Id (gbottom_at n ch) true -> Id (gbudget_at (Datatypes.S n) ch) 0%nat.
Proof.
intros n. induction n as [| n IH]; intros ch Hdec H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * (* A bottomed [gstep 0] node: at [m = 0] the everywhere-decreasing
         premise would force the tail budget below zero, so hollow chains
         are excluded. *)
      exfalso.
      pose proof (Hdec 0%nat) as Hbad.
      change (gbudget_at 1%nat (gstep 0%nat c tl)) with (gbudget_at 0%nat tl)
        in Hbad.
      change (gbudget_at 0%nat (gstep 0%nat c tl)) with 0%nat in Hbad.
      pose proof (proj1 (Nat.ltb_lt (gbudget_at 0%nat tl) 0%nat)
                    (RealSetoid.Id_eq _ _ Hbad)) as Hlt.
      lia.
    * change (gbottom_at 0%nat (gstep (Datatypes.S b') c tl)) with false in H.
      inversion H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * (* A [gstep 0] head node: the same hollow-chain exclusion applies. *)
      exfalso.
      pose proof (Hdec 0%nat) as Hbad.
      change (gbudget_at 1%nat (gstep 0%nat c tl)) with (gbudget_at 0%nat tl)
        in Hbad.
      change (gbudget_at 0%nat (gstep 0%nat c tl)) with 0%nat in Hbad.
      pose proof (proj1 (Nat.ltb_lt (gbudget_at 0%nat tl) 0%nat)
                    (RealSetoid.Id_eq _ _ Hbad)) as Hlt.
      lia.
    * change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl) in H.
      change (gbudget_at (Datatypes.S (Datatypes.S n)) (gstep (Datatypes.S b') c tl))
        with (gbudget_at (Datatypes.S n) tl).
      apply IH.
      -- (* The decreasing premise transfers along the [gstep] tail: the
            universally quantified premise instantiates directly at the
            successor. *)
         intros m.
         pose proof (Hdec (Datatypes.S m)) as Hs.
         change (gbudget_at (Datatypes.S (Datatypes.S m)) (gstep (Datatypes.S b') c tl))
           with (gbudget_at (Datatypes.S m) tl) in Hs.
         change (gbudget_at (Datatypes.S m) (gstep (Datatypes.S b') c tl))
           with (gbudget_at m tl) in Hs.
         exact Hs.
      -- exact H.
Qed.

(* An exhausted budget implies bottoming, with no extra premise: the
   detector counts [gstep] nodes whose budget is spent. *)
Lemma gbottom_true_of_budget0 : forall (n : nat) (ch : GChain),
  Id (gbudget_at n ch) 0%nat -> Id (gbottom_at n ch) true.
Proof.
intros n. induction n as [| n IH]; intros ch H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + change (gbudget_at 0%nat (gstep b c tl)) with b in H.
    rewrite (RealSetoid.Id_eq b 0%nat H). reflexivity.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbudget_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbudget_at n tl) in H.
      change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl).
      apply IH. exact H.
Qed.

(* ---- Part 1 [vm_compute] spot checks ---- *)

(* For [grun (1#2) 4 (8#10)] the budget walks 4, 3, 2, 1, 0 and bottoms,
   while the value follows the decreasing sequence 0.8*(1/2)^n. *)
Eval vm_compute in gbudget_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in ghead_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in gbottom_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in gbottom_at 3 (grun (1#2) 4 (8#10)).

Lemma test_grun_budget0 : Id (gbudget_at 4 (grun (1#2) 4 (8#10))) 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_grun_bottom : Id (gbottom_at 4 (grun (1#2) 4 (8#10))) true.
Proof. vm_compute. reflexivity. Qed.

Lemma test_grun_running3 : Id (gbottom_at 3 (grun (1#2) 4 (8#10))) false.
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 2. Productivity implies soundness, via [UpConstitution.q_decay_breaks] ================= *)

(* Productivity: the CoFixpoint generator decreases its budget strictly at
   every step, so the chain bottoms within its own budget of [b] steps.
   Soundness: taking the break budget [N] solved out by [q_decay_breaks] as
   the chain budget, the chain bottoms at depth [N] with head value
   [c0 * (1 - k)^N < eps], so the stopping time carries its own certificate. *)


Corollary guarded_ledger_clears : forall (k : Q) (b : nat) (c : Q),
  Id (gbudget_at b (grun k b c)) 0%nat.
Proof.
intros k b c.
assert (Hzz : Id (b - b)%nat 0%nat)
  by (apply RealSetoid.eq_Id; apply Nat.sub_diag).
exact (id_trans (grun_budget_at k b b c (NatLe_lift b b (Nat.le_refl b))) Hzz).
Qed.

(* Productivity witness, pointwise: a strictly decreasing budget gives the
   smaller budget at depth [m+1] whenever [m < b]. *)
Lemma grun_budget_strict : forall (k : Q) (b : nat) (c : Q) (m : nat),
  NatLt m b ->
  NatLt (gbudget_at (Datatypes.S m) (grun k b c)) (gbudget_at m (grun k b c)).
Proof.
intros k b c m Hm. apply NatLe_drop in Hm.
assert (H1 : Id (gbudget_at (Datatypes.S m) (grun k b c)) (b - Datatypes.S m)%nat).
{ apply grun_budget_at. apply NatLe_lift. lia. }
assert (H2 : Id (gbudget_at m (grun k b c)) (b - m)%nat).
{ apply grun_budget_at. apply NatLe_lift. lia. }
apply st_natlt_lift.
rewrite (RealSetoid.Id_eq _ _ H1).
rewrite (RealSetoid.Id_eq _ _ H2).
lia.
Qed.

(* Productivity conclusion: a conservation chain of any budget [b] bottoms
   at depth [b]. *)
Theorem guarded_productive : forall (k : Q) (b : nat) (c : Q),
  Id (gbottom_at b (grun k b c)) true.
Proof.
intros k b c. apply gbottom_true_of_budget0. apply guarded_ledger_clears.
Qed.

(* Soundness: the break budget delivered by [q_decay_breaks] is an
   admissible stopping time for the conservation chain -- the chain bottoms
   at that depth, and the frozen head value lies strictly below the
   threshold [eps]. *)
Theorem guarded_breaks : forall (k c0 eps : Q),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => And (NatLe 1 N)
           (And (Id (gbottom_at N (grun k N c0)) true)
                (QltT (ghead_at N (grun k N c0)) eps))).
Proof.
intros k c0 eps Hk0 Hk1 Hc0 He.
destruct (q_decay_breaks k c0 eps Hk0 Hk1 Hc0 He) as [N [HN1 HN]].
exists N. split.
- exact HN1.
- split.
  + apply guarded_productive.
  + pose proof (grun_head_at k N N c0 (NatLe_lift N N (Nat.le_refl N))) as Hh.
    rewrite (RealSetoid.Id_eq (ghead_at N (grun k N c0)) (gval k c0 N) Hh).
    exact (st_qltT_qid_l (gval k c0 N) (c0 * q_pow (1 - k) N) eps
             (gval_pow_QId k N c0) HN).
Qed.

(* ================= Section 3. The minimal stopping time, by decidable linear search ================= *)

(* The crossing predicate [P n] tests [c0 * (1 - k)^n < eps] through
   [Qlt_bool] and is monotone under decay.  From a seed upper bound [U] the
   searcher [stsearch] scans downward linearly and returns the minimal
   crossing index together with its triple certificate: within the bound,
   crossed at the index, and not crossed at any smaller index.  The failure
   branch carries a witness that no index up to the bound crosses. *)

(* The crossing predicate, executable. *)
Definition st_pred_decay (k c0 eps : Q) : nat -> bool :=
  fun n => Qlt_bool (c0 * q_pow (1 - k) n) eps.

(* The search result, carried by [Set]: a hit packages the minimal-index
   triple certificate; a miss packages the everywhere-not-crossed witness. *)
Definition st_hit (P : nat -> bool) (U : nat) : Set :=
  sigT (fun N => And (NatLe N U)
           (And (Id (P N) true)
                (forall j : nat, NatLt j N -> Id (P j) false))).

Definition st_miss (P : nat -> bool) (U : nat) : Set :=
  forall j : nat, NatLe j U -> Id (P j) false.

Definition st_res (P : nat -> bool) (U : nat) : Set :=
  Or (st_hit P U) (st_miss P U).

(* The search steps stay [Defined]: [stsearch] is an executable decider and
   extraction must keep its body. *)
Lemma stsearch_step_0 (P : nat -> bool) : st_res P 0%nat.
Proof.
destruct (P 0%nat) eqn:E0.
- apply inl. exists 0%nat. split.
  + apply NatLe_lift. apply Nat.le_refl.
  + split.
    * apply RealSetoid.eq_Id. exact E0.
    * intros j Hj. exfalso.
      pose proof (proj1 (Nat.ltb_lt j 0%nat) (RealSetoid.Id_eq _ _ Hj)) as Hlt.
      lia.
- apply inr. intros j Hj. apply NatLe_drop in Hj. destruct j as [| j'].
  + apply RealSetoid.eq_Id. exact E0.
  + exfalso. lia.
Defined.

Lemma stsearch_step_S (P : nat -> bool) (U : nat) (r : st_res P U)
  : st_res P (Datatypes.S U).
Proof.
destruct r as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  apply inl. exists N. split.
  + apply NatLe_lift. apply NatLe_drop in HNle. lia.
  + split; assumption.
- destruct (P (Datatypes.S U)) eqn:E.
  + apply inl. exists (Datatypes.S U). split.
    * apply NatLe_lift. apply Nat.le_refl.
    * split.
      -- apply RealSetoid.eq_Id. exact E.
      -- intros j Hj. apply miss. apply NatLe_lift.
         apply NatLe_drop in Hj. lia.
  + apply inr. intros j Hj. apply NatLe_drop in Hj.
    destruct (Nat.eq_dec j (Datatypes.S U)) as [Heq | Hne].
    * rewrite Heq. apply RealSetoid.eq_Id. exact E.
    * apply miss. apply NatLe_lift. lia.
Defined.

(* The linear search itself: downward from the bound [U] to zero, keeping
   the minimal hit. *)
Fixpoint stsearch (P : nat -> bool) (U : nat) : st_res P U :=
  match U as u return st_res P u with
  | O => stsearch_step_0 P
  | Datatypes.S U' => stsearch_step_S P U' (stsearch P U')
  end.

(* Nonnegative powers: [Qle 0 x] gives [Qle 0 (x^n)], by induction with
   [Qmult_le_0_compat]. *)
Lemma st_qpow_nonneg : forall (x : Q) (n : nat), Qle 0 x -> Qle 0 (q_pow x n).
Proof.
intros x n Hx. induction n as [| n IH].
- (* The base case [Qle 0 1] goes through [uc_znat_pos 1], whose statement
     reduces definitionally to [1]. *)
  apply QleT'_to_Qle. exact (uc_znat_pos 1%nat).
- change (q_pow x (Datatypes.S n)) with (x * q_pow x n).
  apply Qmult_le_0_compat.
  + exact Hx.
  + exact IH.
Qed.

(* Decay monotonicity, the engine of the upper-bound direction: for
   [n <= m] a crossing at [n] persists at [m].  Since [0 <= 1 - k <= 1],
   raising to powers reverses nothing: [(1 - k)^m <= (1 - k)^n] through the
   exponent-addition law of [q_pow] and [uc_pow_le_drop]; the premise
   [Qle 0 c0] keeps the multiplicative premise [0 <= c0 * (1 - k)^n]
   available. *)
Lemma st_decay_mono : forall (k c0 eps : Q) (n m : nat),
  QltT 0 k -> QltT k 1 -> Qle 0 c0 ->
  NatLe n m -> QltT (c0 * q_pow (1 - k) n) eps ->
  QltT (c0 * q_pow (1 - k) m) eps.
Proof.
intros k c0 eps n m Hk0 Hk1 Hc0 Hle Hn.
apply NatLe_drop in Hle.
pose proof (QltT_to_Qlt _ _ Hn) as Hn'.
pose proof (st_qle_of_ltT 0 k Hk0) as H0k.
assert (H1kle : Qle 0 (1 - k))
  by (apply Qlt_le_weak; apply QltT_to_Qlt; exact (uc_lt_opp_shift k 1 Hk1)).
assert (Hle01 : Qle (1 - k) 1) by (apply st_qle_one_minus; exact H0k).
(* Exponent split: [q_pow (1 - k) m] equals [q_pow (1 - k) n] times
   [q_pow (1 - k) (m - n)]. *)
assert (Hdec : c0 * q_pow (1 - k) m
               == (c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat).
{ assert (Hm : (n + (m - n))%nat = m) by lia.
  assert (T2 : q_pow (1 - k) (n + (m - n))%nat == q_pow (1 - k) m)
    by (rewrite Hm; apply Qeq_refl).
  assert (Hpow : q_pow (1 - k) m
                 == q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat).
  { exact (Qeq_trans (q_pow (1 - k) m) (q_pow (1 - k) (n + (m - n))%nat)
             (q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat)
             (Qeq_sym (q_pow (1 - k) (n + (m - n))%nat) (q_pow (1 - k) m) T2)
             (qeqT_imp_qeq _ _ (uc_pow_add (1 - k) n (m - n)%nat))). }
  rewrite Hpow.
  exact (Qeq_sym ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                 (c0 * (q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat))
                 (st_mult_assoc_qeq c0 (q_pow (1 - k) n)
                    (q_pow (1 - k) (m - n)%nat))). }
(* A factor bounded by one makes the coefficient product contract. *)
assert (Hgap : Qle ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                   (c0 * q_pow (1 - k) n)).
{ pose proof (QleT'_to_Qle (q_pow (1 - k) (m - n)%nat) (q_pow (1 - k) 0%nat)
                (uc_pow_le_drop (1 - k) 0%nat (m - n)%nat
                   (Qle_to_QleT' 0%Q (1 - k)%Q H1kle)
                   (Qle_to_QleT' (1 - k)%Q 1%Q Hle01))) as Hq1.
  change (q_pow (1 - k) 0%nat) with 1%Q in Hq1.
  rewrite (Qmult_comm (c0 * q_pow (1 - k) n) (q_pow (1 - k) (m - n)%nat)).
  apply (Qle_trans (q_pow (1 - k) (m - n)%nat * (c0 * q_pow (1 - k) n))
                   (1%Q * (c0 * q_pow (1 - k) n))
                   (c0 * q_pow (1 - k) n)).
  - apply (Qmult_le_compat_r (q_pow (1 - k) (m - n)%nat) 1%Q
             (c0 * q_pow (1 - k) n)).
    + exact Hq1.
    + apply Qmult_le_0_compat.
      * exact Hc0.
      * exact (st_qpow_nonneg (1 - k) n H1kle).
  - apply QleT'_to_Qle.
    apply (uc_qeq_le_l (c0 * q_pow (1 - k) n) (1%Q * (c0 * q_pow (1 - k) n))
            (c0 * q_pow (1 - k) n)).
    + apply qeq_imp_qeqT. apply Qeq_sym. apply Qmult_1_l.
    + apply Qle_to_QleT'. apply Qle_refl. }
apply (uc_qeq_lt_l ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                   (c0 * q_pow (1 - k) m) eps
          (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hdec))).
apply Qlt_to_QltT.
apply (Qle_lt_trans ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                    (c0 * q_pow (1 - k) n) eps).
- exact Hgap.
- exact Hn'.
Qed.

(* The minimal stopping time: existence, together with the minimality
   certificate at all predecessors and the upper-bound monotonicity
   certificate at all successors. *)
Theorem minimal_stoptime : forall (k c0 eps : Q) (U : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun N => And (NatLe N U)
           (And (QltT (c0 * q_pow (1 - k) N) eps)
                (And (forall j : nat, NatLt j N -> QleT' eps (c0 * q_pow (1 - k) j))
                     (forall j : nat, NatLe N j -> QltT (c0 * q_pow (1 - k) j) eps)))).
Proof.
intros k c0 eps U Hk0 Hk1 Hc0 He HU.
destruct (stsearch (st_pred_decay k c0 eps) U) as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  exists N. split.
  + exact HNle.
  + split.
    * exact hP.
    * split.
      -- (* Minimality: the not-crossed certificates at all predecessors
            give [eps <=] each earlier value. *)
         intros j Hj. apply st_qlt_false_ge. exact (hmin j Hj).
      -- (* Upper bound: decay monotonicity carries the crossing from the
            minimum to every later index. *)
         intros j Hj.
         exact (st_decay_mono k c0 eps N j Hk0 Hk1
                  (Qlt_le_weak 0%Q c0 (QltT_to_Qlt 0%Q c0 Hc0)) Hj hP).
- exfalso.
  pose proof (miss U (NatLe_lift U U (Nat.le_refl U))) as Hf.
  pose proof (id_trans (id_sym HU) Hf) as Hcontra. inversion Hcontra.
Qed.

(* The search report, shaped for [vm_compute] inspection: certificates of
   function type are kept out of the printed value. *)
Definition stsearch_report (P : nat -> bool) (U : nat) : nat * bool :=
  match stsearch P U with
  | inl h => (projT1 h, true)
  | inr _ => (U, false)
  end.

(* ================= Section 4. Two-objective dominance of the threshold policy ================= *)

(* Discrete order-algebraic form.  A policy is a stopping index plus its
   crossing certificate there.  Objective one counts merges and equals the
   stopping time; objective two counts wasted service through [st_waste],
   the steps served while the predicate already holds but the stop has not
   come.  The minimum dominates on both objectives at once: its stopping
   time is at most the competitor's, and a competitor crossed on the whole
   stretch from the minimum up to its own stop wastes at least the entire
   gap between the two. *)

(* The wasted-service counter: the number of steps before the stop [N] at
   which the predicate already holds -- a step served after crossing is
   wasted. *)
Fixpoint st_waste (P : nat -> bool) (N : nat) : nat :=
  match N with
  | O => 0%nat
  | Datatypes.S m => (st_waste P m + (if P m then 1 else 0))%nat
  end.

(* The minimum wastes nothing: the not-crossed certificates at all
   predecessors accumulate layer by layer. *)
Lemma st_waste_zero : forall (P : nat -> bool) (N : nat),
  (forall j : nat, NatLt j N -> Id (P j) false) -> Id (st_waste P N) 0%nat.
Proof.
intros P N. induction N as [| N IH]; intros Hmin.
- reflexivity.
- change (st_waste P (Datatypes.S N))
    with (st_waste P N + (if P N then 1 else 0))%nat.
  rewrite (RealSetoid.Id_eq _ _
             (IH (fun j Hj => Hmin j (st_natlt_lift j (Datatypes.S N)
                       (Nat.lt_lt_succ_r j N (st_natlt_drop j N Hj)))))).
  rewrite (RealSetoid.Id_eq _ _
             (Hmin N (st_natlt_lift N (Datatypes.S N)
                        (Nat.lt_succ_diag_r N)))).
  reflexivity.
Qed.

(* Counting lower bound: crossing at every step of the stretch from [a] to
   [m] wastes at least [m - a] steps. *)
Lemma st_waste_lower : forall (P : nat -> bool) (a m : nat),
  NatLe a m ->
  (forall j : nat, NatLe a j -> NatLt j m -> Id (P j) true) ->
  NatLe (m - a)%nat (st_waste P m).
Proof.
intros P a m. induction m as [| m IH]; intros Hle Hge.
- apply NatLe_lift.
  change (st_waste P 0%nat) with 0%nat.
  apply NatLe_drop in Hle. lia.
- apply NatLe_lift.
  change (st_waste P (Datatypes.S m))
    with (st_waste P m + (if P m then 1 else 0))%nat.
  destruct (Nat.leb a m) eqn:Ea.
  + assert (H1 : NatLe (m - a)%nat (st_waste P m)).
    { apply IH.
      - exact (NatLe_lift a m (proj1 (Nat.leb_le a m) Ea)).
      - intros j Hj1 Hj2. apply Hge.
        * exact Hj1.
        * exact (st_natlt_lift j (Datatypes.S m)
                   (Nat.lt_lt_succ_r j m (st_natlt_drop j m Hj2))). }
    apply NatLe_drop in H1. apply NatLe_drop in Hle.
    assert (Ham : (a <= m)%nat) by exact (proj1 (Nat.leb_le a m) Ea).
    assert (Hs : ((Datatypes.S m) - a)%nat = (Datatypes.S (m - a))%nat) by lia.
    rewrite Hs.
    assert (HPm : (P m)%bool = true).
    { apply RealSetoid.Id_eq. apply Hge.
      - exact (NatLe_lift a m (proj1 (Nat.leb_le a m) Ea)).
      - exact (st_natlt_lift m (Datatypes.S m) (Nat.lt_succ_diag_r m)). }
    rewrite HPm.
    change (if true then 1 else 0)%nat with 1%nat.
    lia.
  + apply Nat.leb_gt in Ea. apply NatLe_drop in Hle.
    assert (Hz : ((Datatypes.S m) - a)%nat = 0%nat) by lia.
    rewrite Hz.
    destruct (P m); lia.
Qed.

(* The certificate-carrying policy class: a stopping index plus its
   crossing witness there. *)
Record st_policy (P : nat -> bool) : Set := mk_policy {
  pol_stop : nat;
  pol_break : Id (P pol_stop) true
}.

Arguments pol_stop {P} _.
Arguments pol_break {P} _.
Arguments mk_policy {P} _ _.

(* Two-objective dominance in pure order-algebraic form, against any
   certified competitor with stop [M]: the minimum does not increase the
   merge count, wastes nothing itself, and the competitor wastes at least
   the whole gap [M - Nstar]. *)
Theorem st_dominance : forall (P : nat -> bool) (Nstar : nat) (q : st_policy P),
  (forall j : nat, NatLt j Nstar -> Id (P j) false) ->
  Id (P Nstar) true ->
  (forall n m : nat, NatLe n m -> Id (P n) true -> Id (P m) true) ->
  And (NatLe Nstar (pol_stop q))
      (And (Id (st_waste P Nstar) 0%nat)
           (NatLe ((pol_stop q - Nstar)%nat)
                  (st_waste P (pol_stop q)))).
Proof.
intros P Nstar q Hmin hN Hmono. destruct q as [M hM].
split.
- (* Dominance one: [M < Nstar] contradicts the not-crossed certificates
     at the predecessors. *)
  destruct (Nat.leb Nstar M) eqn:E.
  + exact (NatLe_lift Nstar M (proj1 (Nat.leb_le Nstar M) E)).
  + exfalso.
    pose proof (Hmin M (st_natlt_lift M Nstar
                   (proj1 (Nat.leb_gt Nstar M) E))) as Hf.
    pose proof (id_trans (id_sym hM) Hf) as Hcontra. inversion Hcontra.
- split.
  + exact (st_waste_zero P Nstar Hmin).
  + assert (Hle : NatLe Nstar M).
    { destruct (Nat.leb Nstar M) eqn:E2.
      - exact (NatLe_lift Nstar M (proj1 (Nat.leb_le Nstar M) E2)).
      - exfalso.
        pose proof (Hmin M (st_natlt_lift M Nstar
                       (proj1 (Nat.leb_gt Nstar M) E2))) as Hf.
        pose proof (id_trans (id_sym hM) Hf) as Hcontra. inversion Hcontra. }
    apply st_waste_lower.
    * exact Hle.
    * intros j Hj1 Hj2. exact (Hmono Nstar j Hj1 hN).
Qed.

(* The geometric-decay instantiation of threshold dominance: the minimal
   stopping time of Section 3 supplies the abstract dominance statement of
   Section 4. *)
Theorem st_thresh_dominance : forall (k c0 eps : Q) (U : nat)
                                     (q : st_policy (st_pred_decay k c0 eps)),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun Nstar =>
          And (NatLe Nstar (pol_stop q))
              (And (QltT (c0 * q_pow (1 - k) Nstar) eps)
                   (And (Id (st_waste (st_pred_decay k c0 eps) Nstar) 0%nat)
                        (NatLe ((pol_stop q - Nstar)%nat)
                               (st_waste (st_pred_decay k c0 eps) (pol_stop q)))))).
Proof.
intros k c0 eps U q Hk0 Hk1 Hc0 He HU.
assert (Hmono : forall n m : nat,
          NatLe n m -> Id (st_pred_decay k c0 eps n) true ->
          Id (st_pred_decay k c0 eps m) true).
{ intros n m Hle Hn.
  exact (st_decay_mono k c0 eps n m Hk0 Hk1
           (Qlt_le_weak 0%Q c0 (QltT_to_Qlt 0%Q c0 Hc0)) Hle Hn). }
destruct (stsearch (st_pred_decay k c0 eps) U) as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  exists N.
  destruct (st_dominance (st_pred_decay k c0 eps) N q hmin hP Hmono)
    as [Hd1 [Hd2 Hd3]].
  split.
  + exact Hd1.
  + split.
    * exact hP.
    * split.
      -- exact Hd2.
      -- exact Hd3.
- exfalso.
  pose proof (miss U (NatLe_lift U U (Nat.le_refl U))) as Hf.
  pose proof (id_trans (id_sym HU) Hf) as Hcontra. inversion Hcontra.
Qed.

(* ================= Section 5. The negative contrast: a self-referential constant chain without budget witness ================= *)

(* The chain [uloop] keeps budget one and head value [c] at every step: the
   CoFixpoint guard accepts it, but no decreasing witness exists.  Three
   negative facts -- the budget never reaches zero, the detector never sees
   bottoming, and no stopping time exists -- separate it from the
   GuardedChain of Section 2, where a decreasing budget forces bottoming. *)

CoFixpoint uloop (c : Q) : GChain := gstep 1%nat c (uloop c).

(* Negative fact a: the budget is constantly one -- observing through a
   match forces the cofix to unfold, and the budget never zeroes. *)
Lemma unguarded_budget_const : forall (c : Q) (n : nat),
  Id (gbudget_at n (uloop c)) 1%nat.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (gbudget_at (Datatypes.S n) (uloop c)) with (gbudget_at n (uloop c)).
  exact IH.
Qed.

(* Negative fact b: the head value is constantly [c] -- a self-referential
   constant with no improving trajectory. *)
Lemma unguarded_head_const : forall (c : Q) (n : nat),
  Id (ghead_at n (uloop c)) c.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (ghead_at (Datatypes.S n) (uloop c)) with (ghead_at n (uloop c)).
  exact IH.
Qed.

(* Negative fact c: at every depth the detector reports no bottoming. *)
Lemma unguarded_never_bottoms : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) false.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (gbottom_at (Datatypes.S n) (uloop c)) with (gbottom_at n (uloop c)).
  exact IH.
Qed.

(* Negative theorem: the witness-free constant chain has no stopping time;
   a [true] bottoming detection contradicts it directly. *)
Theorem unguarded_no_stoptime : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) true -> Empty_set.
Proof.
intros c n H.
pose proof (unguarded_never_bottoms c n) as Hf.
pose proof (id_trans (id_sym H) Hf) as Hcontra. inversion Hcontra.
Qed.

(* Separation: the budget sequence of the constant chain never reaches the
   zeroing point, the exact opposite of a GuardedChain budget. *)
Theorem unguarded_vs_guarded : forall (c : Q) (n : nat),
  Id (gbudget_at n (uloop c)) 0%nat -> Empty_set.
Proof.
intros c n H0.
pose proof (unguarded_budget_const c n) as H1.
pose proof (id_trans (id_sym H0) H1) as Hcontra. inversion Hcontra.
Qed.

(* The negative facts assembled into one triple observation. *)
Theorem unguarded_trivial : forall (c : Q) (n : nat),
  And (Id (gbudget_at n (uloop c)) 1%nat)
      (And (Id (gbottom_at n (uloop c)) false)
           (Id (ghead_at n (uloop c)) c)).
Proof.
intros c n. split.
- apply unguarded_budget_const.
- split.
  + apply unguarded_never_bottoms.
  + apply unguarded_head_const.
Qed.

(* ---- Part 5 [vm_compute] spot checks ---- *)
Eval vm_compute in gbottom_at 7 (uloop (1#10)).
Eval vm_compute in gbudget_at 7 (uloop (1#10)).

Lemma test_uloop_never : Id (gbottom_at 7 (uloop (1#10))) false.
Proof. vm_compute. reflexivity. Qed.

Lemma test_uloop_budget : Id (gbudget_at 7 (uloop (1#10))) 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 6. Joint [vm_compute] spot checks for Sections 3 and 4 ================= *)

(* For c0 = 4/5, k = 1/2 and eps = 1/10 the crossing predicate first holds
   at n = 4, along the values 4/5, 2/5, 1/5, 1/10, 1/20; from the upper
   bound 5 the searcher reports the minimal stopping time 4. *)

Definition stpred_demo : nat -> bool := st_pred_decay (1#2) (8#10) (1#10).

Eval vm_compute in (stpred_demo 0, stpred_demo 1, stpred_demo 2,
                    stpred_demo 3, stpred_demo 4, stpred_demo 5).
Eval vm_compute in stsearch_report stpred_demo 5.
Eval vm_compute in st_waste stpred_demo 6.

Lemma test_stsearch_min : Id (stsearch_report stpred_demo 5) (4%nat, true).
Proof. vm_compute. reflexivity. Qed.

Lemma test_waste_star : Id (st_waste stpred_demo 4) 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_waste_gap : Id (st_waste stpred_demo 6) 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 7. Extraction check ================= *)

(* The whole stopping-time decider chain is extracted -- predicate, search,
   report, wasted-service counter and the power core -- with
   [Obj.magic] = 0. *)

From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upstoptime.ml" st_pred_decay stsearch stsearch_report st_waste q_pow.

(* ================= Section 8. Print Assumptions probe ================= *)

Print Assumptions guarded_breaks.
Print Assumptions minimal_stoptime.
Print Assumptions st_dominance.
Print Assumptions unguarded_no_stoptime.
