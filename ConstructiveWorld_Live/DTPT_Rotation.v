(* ===================================================================== *)
(* DTPT_Rotation -- true cyclic rotation theory over Q lists, born clean   *)
(* on a Set-carried statement face.                                        *)
(* Mission. The true rotation operator [rotc := skipn ++ firstn] with the  *)
(*   phase [Pinf_c]; the two-runs decomposition and the seam identity;     *)
(*   the exact three-term closed form of [H_adj (rotc k l)] on sorted      *)
(*   lists; the 3-spread and sharpened 2-spread bounds with sharpness      *)
(*   witness; the dynamic supremum [Hsup_cyc] (monotone, bounded,          *)
(*   attained, frozen at the full turn, spectrally finite); the guarded    *)
(*   addition law, the periodicity cluster, the affine lambda-interpola-   *)
(*   tion family ([H_lam_cyc], [H_lam_pmid], [H_lam_gen]) with endpoint    *)
(*   selectors and separation witnesses, the middle-phase sorted collapse, *)
(*   the [phase_dev] detector family, and the legacy disposal map.         *)
(* Dependencies. Stdlib QArith/Qabs/List/Arith/Lia/Permutation;           *)
(*   S01_BaseRing, S02_CauchyComplete ([Id]/[InT]/[NatLe]/[QeqT]/         *)
(*   [QleT']/[QltT]); DTPT and DTPT_Entropy (twin toolbox, landed).        *)
(* References. NsepBudgetVerify.v (header and audit-tail format);          *)
(*   S01_BaseRing.v, LW0LeibWindow.v (decidable-carrier bridge style);     *)
(*   the baseline rotation module whose theorem names are carried over.    *)
(* Constructivity. Every statement face is Set-carried ([QeqT],            *)
(*   [QleT'], [QltT], [NatLe], [InT], [NeT], [Id], [And], [Or], [sigT]);   *)
(*   no Prop enters a witness type.  Sorted carrier: the landed            *)
(*   [DTPT_Entropy] inductive [SortedQ : list Q -> Set] (constructors      *)
(*   carry a Prop-side [Forall] bound: the landed existing form, mirrored  *)
(*   and declared here).  All closures are [Defined]; no [Qed].  The only  *)
(*   Prop-faced declarations are the transport bridges [pb_InT_drop],      *)
(*   [pb_NeT_drop] (proof bodies only).                                    *)
(* Build. rocq c -native-compiler no -q -Q <Set Live world root> ""      *)
(*   DTPT_Rotation.v (this sandbox directory as workdir).                  *)
(* ===================================================================== *)
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import DTPT.
Require Import DTPT_Entropy.
Import DTPT_Entropy.
Import DTPT_Entropy.DTPT_Entropy.
Import ListNotations.
Open Scope Q_scope.

Module DTPT_Rotation.

(* ========== Section A: carrier toolkit ========== *)

(* Set-level nat dichotomy: either n <= m or m < n. *)
Definition nat_cases (n m : nat) : Set := NatLe n m + NatLe (S m) n.

Lemma cyc_nat_cases : forall n m : nat, nat_cases n m.
Proof.
  intro n. induction n as [| n IH]; intro m.
  - left. apply NatLe_lift. apply Nat.le_0_l.
  - destruct m as [| m'].
    + right. apply NatLe_lift. lia.
    + destruct (IH m') as [H | H].
      * left. apply NatLe_lift. pose proof (NatLe_drop n m' H). lia.
      * right. apply NatLe_lift. pose proof (NatLe_drop (S m') n H). lia.
Defined.

(* Set-level list nonemptiness carrier: [] goes to the empty Set. *)
Definition NeT (l : list Q) : Set :=
  match l with
  | [] => Empty_set
  | _ :: _ => unit
  end.

Lemma pb_NeT_drop : forall l : list Q, NeT l -> l <> [].
Proof.
  intros [| a rest] H.
  - destruct H.
  - intro Hc. discriminate Hc.
Defined.

(* Reflexivity of the [NatLe] carrier and the two-way transport between
   the S01 [NatLe]/[Id] faces and the twin [DTPT] faces, for consuming
   the landed DTPT laws of the [Pmid] endpoints. *)
Lemma natle_reflT : forall n : nat, NatLe n n.
Proof.
  intro n. apply NatLe_lift. apply Nat.le_refl.
Defined.

Lemma natle_to_dtpt : forall n m : nat, NatLe n m -> DTPT.DTPT.NatLe n m.
Proof.
  intros n m H. apply DTPT.DTPT.NatLe_lift. exact (NatLe_drop n m H).
Defined.

Lemma dtpt_id_eq : forall {A : Set} (x y : A),
  DTPT.DTPT.Id x y -> x = y.
Proof.
  intros A x y H. destruct H. apply eq_refl.
Defined.

Lemma id_eq : forall {A : Set} (x y : A), Id x y -> x = y.
Proof.
  intros A x y H. destruct H. apply eq_refl.
Defined.

Lemma pb_InT_drop : forall (A : Set) (x : A) (l : list A), InT x l -> In x l.
Proof.
  intros A x l H. induction H as [| y l0 H IH].
  - left. reflexivity.
  - right. exact IH.
Defined.

(* Set-level membership kit: the head and the last element of a nonempty  *)
(* list (as witnessed by [NeT], a Set carrier) are [InT] members; [P0]     *)
(* preserves [InT] membership; [rot n] transports it. *)
Fixpoint inT_hd (l : list Q) (n : NeT l) : InT (hd 0 l) l.
Proof.
  destruct l as [| a rest].
  - destruct n.
  - apply InT_here.
Defined.

Fixpoint inT_lastq (l : list Q) (n : NeT l) {struct l} : InT (lastq l) l :=
  (match l as l0 return NeT l0 -> InT (lastq l0) l0 with
   | [] =>
       fun n0 => (Empty_set_rect (fun _ => InT (lastq (@nil Q)) (@nil Q))) n0
   | a :: rest =>
       fun n0 =>
         (match rest as r0
               return NeT (a :: r0) ->
                      (NeT r0 -> InT (lastq r0) r0) ->
                      InT (lastq (a :: r0)) (a :: r0) with
          | [] => fun _ _ => InT_here (lastq [a]) []
          | b :: bs =>
              fun _ ih => InT_next (lastq (a :: b :: bs)) a (b :: bs) (ih tt)
          end) n0 (inT_lastq rest)
   end) n.

Lemma P0_neT : forall l : list Q, NeT l -> NeT (P0 l).
Proof.
  induction l as [| a rest IH]; intros n.
  - destruct n.
  - cbn [P0]. destruct (P0 rest) as [| y ys].
    + cbn [insert_q]. exact tt.
    + cbn [insert_q]. destruct (Qle_bool a y); exact tt.
Defined.

Lemma inT_insert_self : forall (a : Q) (l : list Q), InT a (insert_q a l).
Proof.
  intro a. induction l as [| y ys IH].
  - apply InT_here.
  - cbn [insert_q]. destruct (Qle_bool a y) eqn:E.
    + apply InT_here.
    + apply InT_next. exact IH.
Defined.

Lemma inT_insert_mono : forall (a x : Q) (l : list Q),
  InT x l -> InT x (insert_q a l).
Proof.
  intros a x. induction l as [| y ys IH]; intros Hx.
  - inversion Hx.
  - cbn [insert_q]. destruct (Qle_bool a y) eqn:E.
    + inversion Hx as [Hx1 | y0 l0 Hx2]; subst.
      * apply InT_next. apply InT_here.
      * apply InT_next. apply InT_next. exact Hx2.
    + inversion Hx as [Hx1 | y0 l0 Hx2]; subst.
      * apply InT_here.
      * apply InT_next. exact (IH Hx2).
Defined.

Lemma inT_P0_intro : forall (l : list Q) (x : Q),
  InT x l -> InT x (P0 l).
Proof.
  induction l as [| a rest IH]; intros x Hx.
  - inversion Hx.
  - cbn [P0]. inversion Hx as [Hx1 | y0 l0 Hx2]; subst.
    + exact (inT_insert_self a (P0 rest)).
    + exact (inT_insert_mono a x (P0 rest) (IH x Hx2)).
Defined.

Lemma inT_app_l : forall (l1 l2 : list Q) (x : Q),
  InT x l1 -> InT x (l1 ++ l2).
Proof.
  induction l1 as [| a rest IH]; intros l2 x H.
  - inversion H.
  - inversion H as [Hc1 | y0 l0 Hc2]; subst.
    + apply InT_here.
    + apply InT_next. exact (IH l2 x Hc2).
Defined.

Lemma inT_app_r : forall (l1 l2 : list Q) (x : Q),
  InT x l2 -> InT x (l1 ++ l2).
Proof.
  induction l1 as [| a rest IH]; intros l2 x H.
  - exact H.
  - apply InT_next. exact (IH l2 x H).
Defined.

Lemma inT_app_inv : forall (l1 l2 : list Q) (x : Q),
  InT x (l1 ++ l2) -> (InT x l1) + (InT x l2).
Proof.
  induction l1 as [| a rest IH]; intros l2 x H.
  - right. exact H.
  - inversion H as [Hc1 | y0 l0 Hc2]; subst.
    + left. apply InT_here.
    + destruct (IH l2 x Hc2) as [H3 | H3].
      * left. apply InT_next. exact H3.
      * right. exact H3.
Defined.

Lemma inT_rot_intro : forall (l : list Q) (n : nat) (x : Q),
  InT x l -> InT x (firstn n l ++ skipn n l).
Proof.
  induction l as [| a rest IH]; intros n x Hx.
  - inversion Hx.
  - destruct n as [| n'].
    + cbn [firstn skipn app]. exact Hx.
    + cbn [firstn skipn app]. inversion Hx as [Hx1 | y0 l0 Hx2]; subst.
      * apply InT_here.
      * apply InT_next.
        destruct (inT_app_inv (firstn n' rest) (skipn n' rest) x (IH n' x Hx2))
          as [H3 | H3].
        -- apply inT_app_l. exact H3.
        -- apply inT_app_r. exact H3.
Defined.

(* Numeric strict inequality as a decidable [Id] face of Qcompare. *)
Definition neqQb (a b : Q) : bool :=
  match Qcompare a b with
  | Eq => false
  | _ => true
  end.

Definition NeqT (a b : Q) : Set := Id (neqQb a b) true.

(* Structural boolean equality of Q lists; strict inequality face. *)
Fixpoint list_eqb (a b : list Q) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => andb (Qeq_bool x y) (list_eqb xs ys)
  | _, _ => false
  end.

Definition NeqL (a b : list Q) : Set := Id (list_eqb a b) false.

(* Transport of the right argument of [QleT'] along [QeqT]. *)
Lemma qleT_arg_eq : forall a b c : Q, QeqT b c -> QleT' a b -> QleT' a c.
Proof.
  intros a b c Heq Hle. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - apply QleT'_to_Qle. exact Hle.
  - apply QleT'_to_Qle. apply xq_Qeq_le.
    exact (qeqT_imp_qeq _ _ Heq).
Defined.

Lemma qleT_arg_eq_l : forall a b c : Q, QeqT a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c Heq Hle. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - apply QleT'_to_Qle. apply xq_Qeq_le. exact (qeqT_imp_qeq _ _ Heq).
  - apply QleT'_to_Qle. exact Hle.
Defined.

Lemma qeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof.
  intros a b H. apply qeq_imp_qeqT. apply Qeq_sym.
  exact (qeqT_imp_qeq _ _ H).
Defined.

Lemma qleT_trans : forall a b c : Q, QleT' a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c H1 H2. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - apply QleT'_to_Qle. exact H1.
  - apply QleT'_to_Qle. exact H2.
Defined.

Lemma qleT_of_qeqT : forall a b : Q, QeqT a b -> QleT' a b.
Proof.
  intros a b H.
  apply xq_Qeq_le. exact (qeqT_imp_qeq _ _ H).
Defined.

Lemma qmult_1_l_id : forall x : Q, Id ((1%Z # 1%positive) * x) x.
Proof.
  intros [nx dx].
  apply eq_imp_id. unfold Qmult. cbn [Qnum Qden]. f_equal.
  apply Z.mul_1_l.
Defined.

Lemma QleT'_refl : forall x : Q, QleT' x x.
Proof.
  intro x. apply Qle_to_QleT'.
  unfold Qle. apply Z.le_refl.
Defined.

Lemma qleT_mul_1_l : forall x : Q, QleT' x ((1%Z # 1%positive)%Q * x).
Proof.
  intro x.
  apply (qleT_arg_eq_l x ((1%Z # 1%positive)%Q * x) ((1%Z # 1%positive)%Q * x)).
  - apply qeq_imp_qeqT. symmetry. apply Qmult_1_l.
  - apply QleT'_refl.
Defined.

Lemma qleT_from_diff : forall u v n : Q,
  QeqT (v - u) n -> QleT' 0 n -> QleT' u v.
Proof.
  intros u v n Heq Hn.
  apply (snd (Qle_0_sub' u v)).
  apply (qleT_arg_eq 0 n (v - u)).
  - apply qeqT_sym. exact Heq.
  - exact Hn.
Defined.

Lemma cyc_le_triple : forall s : Q, QleT' 0 s -> QleT' s (3 * s).
Proof.
  intros s Hs.
  pose proof (QleT'_to_Qle _ _ Hs) as Hs'.
  assert (Hqq : QleT' 0 (s + s)) by exact (qadd_nonneg s s Hs' Hs').
  assert (Hr : (s + s + s - s == s + s)%Q) by ring.
  assert (H3 : (3 * s == s + s + s)%Q) by ring.
  assert (Hqq2 : QleT' 0 (s + s + s - s))
    by (apply (qleT_arg_eq 0 (s + s) (s + s + s - s));
        [ apply qeq_imp_qeqT; apply Qeq_sym; exact Hr | exact Hqq ]).
  apply Qle_to_QleT'. apply (Qle_trans s (s + s + s) (3 * s)).
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' s (s + s + s))). exact Hqq2.
  - apply QleT'_to_Qle. apply xq_Qeq_le. apply Qeq_sym. exact H3.
Defined.

Lemma rs_le_double : forall s : Q, QleT' 0 s -> QleT' s (2 * s).
Proof.
  intros s Hs.
  assert (H2 : (2 * s == s + s)%Q) by ring.
  assert (Hr : (s + s - s == s)%Q) by ring.
  apply Qle_to_QleT'. apply (Qle_trans s (s + s) (2 * s)).
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' s (s + s))).
    apply (qleT_arg_eq 0 s (s + s - s));
      [ apply qeq_imp_qeqT; apply Qeq_sym; exact Hr | exact Hs ].
  - apply QleT'_to_Qle. apply xq_Qeq_le. apply Qeq_sym. exact H2.
Defined.

(* ========== Section B: firstn/skipn preserve order ========== *)

Lemma firstn_incl : forall (l : list Q) (k : nat) (z : Q),
  InT z (firstn k l) -> InT z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; inversion Hin.
  - destruct k as [| k']; simpl in Hin.
    + inversion Hin.
    + inversion Hin as [Hin0 | y0 l0 HinT]; subst.
      * apply InT_here.
      * apply InT_next. exact (IH k' z HinT).
Defined.

Lemma skipn_incl : forall (l : list Q) (k : nat) (z : Q),
  InT z (skipn k l) -> InT z l.
Proof.
  induction l as [| a rest IH]; intros k z Hin.
  - destruct k; simpl in Hin; inversion Hin.
  - destruct k as [| k']; simpl in Hin.
    + exact Hin.
    + apply InT_next. exact (IH k' z Hin).
Defined.

Lemma firstn_SortedQ : forall (l : list Q) (k : nat),
  SortedQ l -> SortedQ (firstn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct k as [| k']; simpl.
    + apply sortQ_nil.
    + apply sortQ_cons.
      * apply IH. exact HSr.
      * apply Forall_forall. intros z Hz. apply HFa.
        assert (Hstep : forall (l0 : list Q) (kk : nat) (w : Q),
                  In w (firstn kk l0) -> In w l0).
        { induction l0 as [| a0 r0 IH0]; intros kk w Hw.
          - destruct kk; simpl in Hw; destruct Hw.
          - destruct kk as [| k'']; simpl in Hw.
            + destruct Hw.
            + destruct Hw as [Hw1 | Hw2].
              * left. exact Hw1.
              * right. exact (IH0 k'' w Hw2). }
        exact (Hstep rest k' z Hz).
Defined.

Lemma skipn_SortedQ : forall (l : list Q) (k : nat),
  SortedQ l -> SortedQ (skipn k l).
Proof.
  induction l as [| a rest IH]; intros k HS.
  - destruct k as [| k']; simpl; apply sortQ_nil.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    destruct k as [| k']; simpl.
    + apply sortQ_cons; [ exact HSr | exact HFa ].
    + apply IH. exact HSr.
Defined.

Theorem rotc_two_runs : forall (k : nat) (l : list Q),
  SortedQ l -> And (SortedQ (skipn k l)) (SortedQ (firstn k l)).
Proof.
  intros k l HS. split.
  - apply skipn_SortedQ. exact HS.
  - apply firstn_SortedQ. exact HS.
Defined.

(* ========== Section C: the seam identity ========== *)

Theorem H_adj_app_seam : forall (u v : list Q),
  NeT u -> NeT v ->
  QeqT (H_adj (u ++ v)) (H_adj u + H_adj v + Qabs (hd 0 v - lastq u)).
Proof.
  induction u as [| a rest IH]; intros v Hne Hne2.
  - destruct Hne.
  - destruct rest as [| b bs].
    + destruct v as [| c v'].
      * destruct Hne2.
      * apply qeq_imp_qeqT.
        change (H_adj ([a] ++ c :: v')) with (Qabs (c - a) + H_adj (c :: v'))%Q.
        change (H_adj [a]) with 0%Q.
        change (lastq [a]) with a.
        change (hd 0 (c :: v')) with c.
        ring.
    + apply qeq_imp_qeqT.
      change (H_adj ((a :: b :: bs) ++ v))
        with (Qabs (b - a) + H_adj (b :: bs ++ v))%Q.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      assert (Hne' : NeT (b :: bs)) by exact tt.
      replace (H_adj (b :: bs ++ v)) with (H_adj ((b :: bs) ++ v))
        by reflexivity.
      rewrite (qeqT_imp_qeq _ _ (IH v Hne' Hne2)).
      ring.
Defined.

(* ========== Section D: true rotation base ========== *)

Definition rotc (n : nat) (l : list Q) : list Q :=
  skipn n l ++ firstn n l.

Definition Pinf_c (l : list Q) (s : nat) : list Q := rotc (S s) l.

Theorem rotc_length : forall (n : nat) (l : list Q),
  Id (length (rotc n l)) (length l).
Proof.
  intros n l. apply eq_imp_id. unfold rotc.
  rewrite length_app, length_firstn, length_skipn.
  lia.
Defined.

Theorem rotc_in : forall (l : list Q) (n : nat) (x : Q),
  InT x l -> InT x (rotc n l).
Proof.
  induction l as [| a rest IH]; intros n x Hin.
  - inversion Hin.
  - destruct n as [| n'].
    + cbn [rotc skipn firstn app]. rewrite app_nil_r. exact Hin.
    + cbn [rotc skipn firstn app].
      inversion Hin as [Hc1 | y0 l0 Hc2]; subst.
      * apply inT_app_r. apply InT_here.
      * pose proof (IH n' x Hc2) as Hrot.
        cbn [rotc skipn firstn app] in Hrot.
        destruct (inT_app_inv (skipn n' rest) (firstn n' rest) x Hrot)
          as [H3 | H3].
        -- apply inT_app_l. exact H3.
        -- apply inT_app_r. apply InT_next. exact H3.
Defined.

Lemma rotc_0 : forall l : list Q, Id (rotc 0 l) l.
Proof.
  intro l. apply eq_imp_id. unfold rotc. simpl.
  induction l as [| a rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Defined.

Lemma skipn_all_app : forall (a b : list Q),
  Id (skipn (length a) (a ++ b)) b.
Proof.
  intros a b. apply eq_imp_id.
  induction a as [| x xs IH]; simpl.
  - reflexivity.
  - exact IH.
Defined.

Lemma firstn_all_app : forall (a b : list Q),
  Id (firstn (length a) (a ++ b)) a.
Proof.
  intros a b. apply eq_imp_id.
  induction a as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Defined.

Lemma rotc_rot_app : forall (a b : list Q),
  Id (rotc (length a) (a ++ b)) (b ++ a).
Proof.
  intros a b. apply eq_imp_id. unfold rotc.
  rewrite (id_eq _ _ (skipn_all_app a b)).
  rewrite (id_eq _ _ (firstn_all_app a b)).
  reflexivity.
Defined.

Theorem rotc_inv : forall (n : nat) (l : list Q),
  NatLe n (length l) -> Id (rotc (length l - n) (rotc n l)) l.
Proof.
  intros n l Hn.
  pose proof (NatLe_drop n (length l) Hn) as Hnle.
  apply eq_imp_id.
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat) by exact (firstn_length_le l Hnle).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hab : (length (a ++ b) - length a = length b)%nat)
    by (rewrite length_app; lia).
  rewrite Hsplit.
  rewrite <- Hla.
  rewrite Hab.
  rewrite (id_eq _ _ (rotc_rot_app a b)).
  rewrite (id_eq _ _ (rotc_rot_app b a)).
  reflexivity.
Defined.

Theorem Pinf_c_length : forall (l : list Q) (s : nat),
  Id (length (Pinf_c l s)) (length l).
Proof.
  intros l s. exact (rotc_length (S s) l).
Defined.

Theorem Pinf_c_in : forall (l : list Q) (s : nat) (x : Q),
  InT x l -> InT x (Pinf_c l s).
Proof.
  intros l s x Hx. exact (rotc_in l (S s) x Hx).
Defined.

Theorem Pinf_true_id : forall (l : list Q) (s : nat), Id (Pinf l s) l.
Proof.
  intros l s. exact (Pinf_eq_l l s).
Defined.

Theorem H_rotc_span_lb : forall (n : nat) (l : list Q) (x y : Q),
  InT x l -> InT y l -> QleT' (Qabs (x - y)) (H_adj (rotc n l)).
Proof.
  intros n l x y Hx Hy.
  apply (xq_pair_dist_le (rotc n l) x y).
  - apply pb_InT_drop. apply rotc_in. exact Hx.
  - apply pb_InT_drop. apply rotc_in. exact Hy.
Defined.

Theorem H_rotc_span_lb_wit : forall n : nat,
  QleT' 2 (H_adj (rotc n [0; 1; 2])).
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply (Qle_trans 2 (Qabs (0 - 2)) (H_adj (rotc n [0; 1; 2]))).
  - replace (Qabs (0 - 2)) with 2%Q by reflexivity.
    apply Qle_refl.
  - apply QleT'_to_Qle. apply H_rotc_span_lb.
    + apply InT_here.
    + apply InT_next. apply InT_next. apply InT_here.
Defined.

Theorem H_rotc_separates :
  sigT (fun l : list Q => sigT (fun n : nat => NeqT (H_adj (rotc n l)) (H_adj l))).
Proof.
  apply (existT _ [0; 1; 2]). apply (existT _ 1%nat).
  vm_compute. exact id_refl.
Defined.

Theorem rotc_Pinf_separates :
  sigT (fun l : list Q =>
        sigT (fun n : nat =>
              sigT (fun s : nat => NeqL (rotc n l) (Pinf l s)))).
Proof.
  apply (existT _ [0; 1; 2]). apply (existT _ 1%nat). apply (existT _ 0%nat).
  vm_compute. exact id_refl.
Defined.

(* ========== Section E: boundary discrimination ========== *)

Fixpoint skipn_neT (k : nat) (l : list Q) (h : NatLe (S k) (length l))
  {struct l} : NeT (skipn k l).
Proof.
  destruct l as [| a rest].
  - apply (False_rect (NeT (skipn k []))).
    pose proof (NatLe_drop (S k) 0 h). simpl in *. lia.
  - destruct k as [| k'].
    + exact tt.
    + cbn [skipn]. apply (skipn_neT k' rest).
      apply NatLe_lift.
      pose proof (NatLe_drop (S (S k')) (S (length rest)) h) as Hp.
      apply (proj2 (Nat.succ_le_mono (S k') (length rest))). exact Hp.
Defined.

Lemma firstn_neT : forall (k : nat) (l : list Q),
  NatLe 1 k -> NatLe k (length l) -> NeT (firstn k l).
Proof.
  intros k l H1 H2.
  pose proof (NatLe_drop 1 k H1) as Hp1.
  pose proof (NatLe_drop k (length l) H2) as Hp2.
  destruct l as [| a rest].
  - apply (False_rect (NeT (firstn k []))). simpl in *. lia.
  - destruct k as [| k'].
    + apply (False_rect (NeT (firstn 0 (a :: rest)))). simpl in *. lia.
    + cbn [firstn]. exact tt.
Defined.

Theorem rotc_skipn_all : forall (l : list Q) (k : nat),
  NatLe (length l) k -> Id (skipn k l) (@nil Q).
Proof.
  intro l. induction l as [| a rest IH]; intros k Hk.
  - destruct k as [| k']; apply eq_imp_id; reflexivity.
  - destruct k as [| k'].
    + apply (False_rect (Id (skipn 0 (a :: rest)) (@nil Q))).
      pose proof (NatLe_drop (length (a :: rest)) 0 Hk). simpl in *. lia.
    + cbn [skipn]. apply IH.
      apply NatLe_lift.
      pose proof (NatLe_drop (S (length rest)) (S k') Hk) as Hp.
      simpl in Hp. lia.
Defined.

Theorem rotc_firstn_all : forall (l : list Q) (k : nat),
  NatLe (length l) k -> Id (firstn k l) l.
Proof.
  intro l. induction l as [| a rest IH]; intros k Hk.
  - destruct k as [| k']; apply eq_imp_id; reflexivity.
  - destruct k as [| k'].
    + apply (False_rect (Id (firstn 0 (a :: rest)) (a :: rest))).
      pose proof (NatLe_drop (length (a :: rest)) 0 Hk). simpl in *. lia.
    + cbn [firstn]. apply eq_imp_id.
      assert (Hle : NatLe (length rest) k')
        by (apply NatLe_lift;
            pose proof (NatLe_drop (S (length rest)) (S k') Hk) as Hp;
            simpl in Hp; lia).
      rewrite (id_eq _ _ (IH k' Hle)). reflexivity.
Defined.

Theorem rotc_ge_len_id : forall (k : nat) (l : list Q),
  NatLe (length l) k -> Id (rotc k l) l.
Proof.
  intros k l Hk. apply eq_imp_id. unfold rotc.
  rewrite (id_eq _ _ (rotc_skipn_all l k Hk)).
  rewrite (id_eq _ _ (rotc_firstn_all l k Hk)).
  reflexivity.
Defined.

Theorem rotc_full : forall l : list Q, Id (rotc (length l) l) l.
Proof.
  intro l. apply eq_imp_id. unfold rotc.
  rewrite (id_eq _ _ (rotc_skipn_all l (length l) (natle_reflT (length l)))).
  rewrite (id_eq _ _ (rotc_firstn_all l (length l) (natle_reflT (length l)))).
  reflexivity.
Defined.

Theorem lastq_skipn_kept : forall (l : list Q) (k : nat),
  NatLe (S k) (length l) -> Id (lastq (skipn k l)) (lastq l).
Proof.
  intro l. induction l as [| a rest IH]; intros k Hlt.
  - apply (False_rect (Id (lastq (skipn k [])) (lastq []))).
    pose proof (NatLe_drop (S k) (length (@nil Q)) Hlt). simpl in *. lia.
  - destruct k as [| k'].
    + apply eq_imp_id. reflexivity.
    + cbn [skipn]. destruct rest as [| b bs].
      * apply (False_rect (Id (lastq (skipn (S k') [a])) (lastq [a]))).
        pose proof (NatLe_drop (S (S k')) 1 Hlt). simpl in *. lia.
      * cbn [lastq]. apply IH.
        apply NatLe_lift. simpl.
        pose proof (NatLe_drop (S (S k')) (length (a :: b :: bs)) Hlt) as Hp.
        simpl in Hp. lia.
Defined.

Theorem hd_firstn_kept : forall (k : nat) (l : list Q),
  NatLe 1 k -> Id (hd 0 (firstn k l)) (hd 0 l).
Proof.
  intros k l Hk. destruct l as [| a rest].
  - destruct k as [| k']; apply eq_imp_id; reflexivity.
  - destruct k as [| k'].
    + apply (False_rect (Id (hd 0 (firstn 0 (a :: rest))) (hd 0 (a :: rest)))).
      pose proof (NatLe_drop 1 0 Hk). simpl in *. lia.
    + cbn [firstn hd]. apply eq_imp_id. reflexivity.
Defined.

Lemma sorted_hd_min : forall (l : list Q), SortedQ l ->
  forall z : Q, InT z l -> QleT' (hd 0 l) z.
Proof.
  induction l as [| a rest IH]; intros HS z Hin.
  - inversion Hin.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    inversion Hin as [Heq | y0 l0 HinT]; subst.
    + apply Qle_to_QleT'. apply Qle_refl.
    + apply Qle_to_QleT'. apply HFa. apply pb_InT_drop. exact HinT.
Defined.

Lemma sorted_lastq_max : forall (l : list Q), SortedQ l ->
  forall z : Q, InT z l -> QleT' z (lastq l).
Proof.
  induction l as [| a rest IH]; intros HS z Hin.
  - inversion Hin.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    destruct rest as [| b bs].
    + inversion Hin as [Heq | y0 l0 HinT]; subst.
      * apply Qle_to_QleT'. apply Qle_refl.
      * inversion HinT.
    + inversion Hin as [Heq | y0 l0 HinT]; subst.
      * apply Qle_to_QleT'. apply HFa. apply pb_InT_drop.
        exact (inT_lastq (b :: bs) tt).
      * change (lastq (z :: b :: bs)) with (lastq (b :: bs)).
        exact (IH HSr z HinT).
Defined.

Lemma sorted_sub_le_spread : forall (l : list Q) (z w : Q),
  SortedQ l -> InT z l -> InT w l -> QleT' (z - w) (lastq l - hd 0 l).
Proof.
  intros l z w HS Hz Hw.
  assert (Hzm : QleT' z (lastq l)) by exact (sorted_lastq_max l HS z Hz).
  assert (Hwn : QleT' (hd 0 l) w) by exact (sorted_hd_min l HS w Hw).
  apply (snd (Qle_0_sub' (z - w) (lastq l - hd 0 l))).
  assert (Hr : (lastq l - hd 0 l - (z - w) == (lastq l - z) + (w - hd 0 l))%Q)
    by ring.
  apply (qleT_arg_eq 0 ((lastq l - z) + (w - hd 0 l))
                      (lastq l - hd 0 l - (z - w)));
    [ apply qeq_imp_qeqT; apply Qeq_sym; exact Hr | ].
  apply qadd_nonneg.
  - apply QleT'_to_Qle. apply (fst (Qle_0_sub' z (lastq l))). exact Hzm.
  - apply QleT'_to_Qle. apply (fst (Qle_0_sub' (hd 0 l) w)). exact Hwn.
Defined.

Lemma sorted_abs_le_spread : forall (l : list Q) (z w : Q),
  SortedQ l -> InT z l -> InT w l -> QleT' (Qabs (z - w)) (lastq l - hd 0 l).
Proof.
  intros l z w HS Hz Hw.
  apply (Qabs_case (z - w) (fun t => QleT' t (lastq l - hd 0 l))).
  - intro Hpos. exact (sorted_sub_le_spread l z w HS Hz Hw).
  - intro Hneg.
    assert (Hr2 : (- (z - w) == w - z)%Q) by ring.
    apply (qleT_arg_eq_l (- (z - w)) (w - z) (lastq l - hd 0 l));
      [ apply qeq_imp_qeqT; exact Hr2 | ].
    exact (sorted_sub_le_spread l w z HS Hw Hz).
Defined.

(* ========== Section F: exact closed forms on sorted lists ========== *)

Theorem H_adj_rotc_exact_mid : forall (k : nat) (l : list Q),
  SortedQ l -> NatLe 1 k -> NatLe (S k) (length l) ->
  QeqT (H_adj (rotc k l)) ((lastq l - hd 0 (skipn k l))
                           + (lastq l - hd 0 l)
                           + (lastq (firstn k l) - hd 0 l)).
Proof.
  intros k l HS H1 H2.
  assert (HSs : SortedQ (skipn k l)) by exact (skipn_SortedQ l k HS).
  assert (HSf : SortedQ (firstn k l)) by exact (firstn_SortedQ l k HS).
  assert (Hnes : NeT (skipn k l)) by exact (skipn_neT k l H2).
  assert (Hnef : NeT (firstn k l)).
  { destruct l as [| a rest].
    - apply (False_rect (NeT (firstn k []))).
      pose proof (NatLe_drop (S k) (length (@nil Q)) H2). simpl in *. lia.
    - destruct k as [| k'].
      + apply (False_rect (NeT (firstn 0 (a :: rest)))).
        pose proof (NatLe_drop 1 0 H1). simpl in *. lia.
      + cbn [firstn]. exact tt. }
  apply qeq_imp_qeqT.
  assert (HE : H_adj (rotc k l) == H_adj (skipn k l ++ firstn k l))
    by reflexivity.
  rewrite HE.
  rewrite (qeqT_imp_qeq _ _ (H_adj_app_seam (skipn k l) (firstn k l) Hnes Hnef)).
  rewrite (qeqT_imp_qeq _ _ (xq_telescope (skipn k l) HSs)).
  rewrite (qeqT_imp_qeq _ _ (xq_telescope (firstn k l) HSf)).
  rewrite (id_eq _ _ (lastq_skipn_kept l k H2)).
  rewrite (id_eq _ _ (hd_firstn_kept k l H1)).
  assert (Hab : Qabs (hd 0 l - lastq l) == lastq l - hd 0 l).
  { rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm (hd 0 l) (lastq l))).
    apply qeqT_imp_qeq. apply xq_abs_id.
    apply QleT'_to_Qle. apply (fst (Qle_0_sub' (hd 0 l) (lastq l))).
    apply xq_hd_le_lastq. exact HS. }
  rewrite Hab. ring.
Defined.

Theorem H_adj_rotc_exact_0 : forall l : list Q, SortedQ l ->
  QeqT (H_adj (rotc 0 l)) (lastq l - hd 0 l).
Proof.
  intros l HS.
  rewrite (id_eq _ _ (rotc_0 l)).
  exact (xq_telescope l HS).
Defined.

Theorem H_adj_rotc_exact_ge : forall (k : nat) (l : list Q), SortedQ l ->
  NatLe (length l) k -> QeqT (H_adj (rotc k l)) (lastq l - hd 0 l).
Proof.
  intros k l HS Hk.
  rewrite (id_eq _ _ (rotc_ge_len_id k l Hk)).
  exact (xq_telescope l HS).
Defined.

Theorem H_adj_rotc_exact_short : forall (k : nat) (l : list Q), SortedQ l ->
  NatLe (length l) 1 -> QeqT (H_adj (rotc k l)) (lastq l - hd 0 l).
Proof.
  intros k l HS Hn.
  destruct (cyc_nat_cases (length l) k) as [Hle | Hgt].
  - exact (H_adj_rotc_exact_ge k l HS Hle).
  - assert (H0 : (k = 0)%nat).
    { pose proof (NatLe_drop (S k) (length l) Hgt). pose proof (NatLe_drop (length l) 1 Hn). lia. }
    rewrite H0. exact (H_adj_rotc_exact_0 l HS).
Defined.

Theorem H_adj_rotc_sorted_exact : forall (k : nat) (l : list Q), SortedQ l ->
  Or (QeqT (H_adj (rotc k l)) ((lastq l - hd 0 (skipn k l))
                               + (lastq l - hd 0 l)
                               + (lastq (firstn k l) - hd 0 l)))
     (QeqT (H_adj (rotc k l)) (lastq l - hd 0 l)).
Proof.
  intros k l HS.
  destruct (cyc_nat_cases (length l) k) as [Hge | Hlt].
  - right. exact (H_adj_rotc_exact_ge k l HS Hge).
  - destruct k as [| k'].
    + right. exact (H_adj_rotc_exact_0 l HS).
    + left. apply (H_adj_rotc_exact_mid (S k') l HS).
      * apply NatLe_lift. lia.
      * exact Hlt.
Defined.

(* ========== Section G: the 3-spread upper bound ========== *)

Theorem H_adj_rotc_ub3 : forall (k : nat) (l : list Q),
  SortedQ l -> NeT l -> QleT' (H_adj (rotc k l)) (3 * (lastq l - hd 0 l)).
Proof.
  intros k l HS Hne.
  assert (Hsp : QleT' 0 (lastq l - hd 0 l)).
  { apply (fst (Qle_0_sub' (hd 0 l) (lastq l))). apply xq_hd_le_lastq. exact HS. }
  assert (Hmlast : InT (lastq l) l) by exact (inT_lastq l Hne).
  assert (Hmhd : InT (hd 0 l) l) by exact (inT_hd l Hne).
  destruct (cyc_nat_cases (length l) k) as [Hge | Hlt].
  - rewrite (id_eq _ _ (rotc_ge_len_id k l Hge)).
    apply Qle_to_QleT'. apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (3 * (lastq l - hd 0 l))).
    + rewrite (qeqT_imp_qeq _ _ (xq_telescope l HS)). apply Qle_refl.
    + apply QleT'_to_Qle. apply cyc_le_triple. exact Hsp.
  - destruct k as [| k'].
    + rewrite (id_eq _ _ (rotc_0 l)).
      apply Qle_to_QleT'. apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (3 * (lastq l - hd 0 l))).
      * rewrite (qeqT_imp_qeq _ _ (xq_telescope l HS)). apply Qle_refl.
      * apply QleT'_to_Qle. apply cyc_le_triple. exact Hsp.
    + assert (H1 : NatLe 1 (S k')) by (apply NatLe_lift; lia).
      assert (HEm : QeqT (H_adj (rotc (S k') l))
                    ((lastq l - hd 0 (skipn (S k') l))
                     + (lastq l - hd 0 l)
                     + (lastq (firstn (S k') l) - hd 0 l)))
        by exact (H_adj_rotc_exact_mid (S k') l HS H1 Hlt).
      assert (Hnes : NeT (skipn (S k') l)) by exact (skipn_neT (S k') l Hlt).
      assert (Hnef : NeT (firstn (S k') l))
        by (apply firstn_neT;
            [ apply NatLe_lift; lia
            | apply NatLe_lift;
              pose proof (NatLe_drop (S (S k')) (length l) Hlt) as Hp; lia ]).
      assert (Hmns : InT (hd 0 (skipn (S k') l)) l).
      { apply (skipn_incl l (S k')).
        exact (inT_hd (skipn (S k') l) Hnes). }
      assert (Hmfl : InT (lastq (firstn (S k') l)) l).
      { apply (firstn_incl l (S k')).
        exact (inT_lastq (firstn (S k') l) Hnef). }
      assert (HT1 : QleT' (lastq l - hd 0 (skipn (S k') l)) (lastq l - hd 0 l))
        by exact (sorted_sub_le_spread l (lastq l) (hd 0 (skipn (S k') l)) HS Hmlast Hmns).
      assert (HT3 : QleT' (lastq (firstn (S k') l) - hd 0 l) (lastq l - hd 0 l))
        by exact (sorted_sub_le_spread l (lastq (firstn (S k') l)) (hd 0 l) HS Hmfl Hmhd).
      assert (H3 : (3 * (lastq l - hd 0 l)
                    == (lastq l - hd 0 l) + (lastq l - hd 0 l)
                       + (lastq l - hd 0 l))%Q) by ring.
      apply Qle_to_QleT'.
      apply (Qle_trans _ ((lastq l - hd 0 (skipn (S k') l))
                        + (lastq l - hd 0 l)
                        + (lastq (firstn (S k') l) - hd 0 l))
                        (3 * (lastq l - hd 0 l))).
      * rewrite (qeqT_imp_qeq _ _ HEm). apply Qle_refl.
      * rewrite (qeqT_imp_qeq _ _ (qeq_imp_qeqT _ _ H3)).
        apply QleT'_to_Qle; apply qadd_le;
          [ apply QleT'_to_Qle; apply qadd_le;
              [ exact (QleT'_to_Qle _ _ HT1) | apply Qle_refl ]
          | exact (QleT'_to_Qle _ _ HT3) ].
Defined.

(* ========== Section H: the dynamic supremum [Hsup_cyc] ========== *)

Definition qmax2 (x y : Q) : Q := if Qle_bool x y then y else x.

Lemma qmax2_ub_l : forall x y : Q, QleT' x (qmax2 x y).
Proof.
  intros x y. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - apply xq_Qle_bool_le. exact E.
  - apply Qle_to_QleT'. apply Qle_refl.
Defined.

Lemma qmax2_ub_r : forall x y : Q, QleT' y (qmax2 x y).
Proof.
  intros x y. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_bool_false_le. exact E.
Defined.

Fixpoint Hsup_cyc (l : list Q) (n : nat) : Q :=
  match n with
  | O => H_adj (rotc 0 l)
  | S n' => qmax2 (Hsup_cyc l n') (H_adj (rotc (S n') l))
  end.

Theorem Hsup_cyc_mono : forall (l : list Q) (n : nat),
  QleT' (Hsup_cyc l n) (Hsup_cyc l (S n)).
Proof.
  intros l n. destruct n as [| n]; cbn [Hsup_cyc].
  - apply qmax2_ub_l.
  - apply qmax2_ub_l.
Defined.

Theorem Hsup_cyc_ub : forall (l : list Q) (n : nat), SortedQ l -> NeT l ->
  QleT' (Hsup_cyc l n) (3 * (lastq l - hd 0 l)).
Proof.
  intros l n HS Hne. induction n as [| n IH].
  - cbn [Hsup_cyc]. exact (H_adj_rotc_ub3 0 l HS Hne).
  - cbn [Hsup_cyc]. unfold qmax2.
    destruct (Qle_bool (Hsup_cyc l n) (H_adj (rotc (S n) l))) eqn:E.
    + exact (H_adj_rotc_ub3 (S n) l HS Hne).
    + exact IH.
Defined.

Theorem Hsup_cyc_attained : forall (l : list Q) (n : nat),
  sigT (fun i : nat => And (NatLe i n) (QeqT (Hsup_cyc l n) (H_adj (rotc i l)))).
Proof.
  intros l n. induction n as [| n IH].
  - apply (existT _ 0%nat). split.
    + apply NatLe_lift. apply Nat.le_0_l.
    + cbn [Hsup_cyc]. apply qeq_imp_qeqT. apply Qeq_refl.
  - destruct IH as [i [Hin Hval]].
    cbn [Hsup_cyc]. unfold qmax2.
    destruct (Qle_bool (Hsup_cyc l n) (H_adj (rotc (S n) l))) eqn:E.
    + apply (existT _ (S n)). split.
      * apply natle_reflT.
      * apply qeq_imp_qeqT. apply Qeq_refl.
    + apply (existT _ i). split.
      * apply NatLe_lift. pose proof (NatLe_drop i n Hin). lia.
      * exact Hval.
Defined.

Theorem rotc_H_wit_mid : QeqT (H_adj (rotc 1 [0; 1; 2])) 3%Q.
Proof. vm_compute. exact id_refl. Defined.

Theorem rotc_H_wit_min : QeqT (H_adj (rotc 0 [0; 1; 2])) 2%Q.
Proof. vm_compute. exact id_refl. Defined.

(* The middle-phase operator, the phase tag and the prefix supremum are
   redefined in place over the [DTPT_Entropy] data face ([P0]/[Pinf]/
   [H_adj]) so that every statement of this piece lives on one data face;
   the landed DTPT boundedness law [H_adj_bound] is consumed through its
   qualified name (its statement carries no [Id]/[NatLe] face). *)
Notation H_adj_bound := DTPT.DTPT.H_adj_bound.

Definition Pmid (l : list Q) (s lam : nat) : list Q :=
  firstn lam (P0 l) ++ skipn lam (Pinf l s).

Inductive PhaseTag : Set := PhP0 | PhMid | PhPinf.

Definition phase_classify (l : list Q) (s : nat) : PhaseTag :=
  let h0 := H_adj (P0 l) in
  let hm := H_adj (Pmid l s 0) in
  let hi := H_adj (Pinf l s) in
  if Qeq_bool h0 hm then PhP0
  else if Qeq_bool hm hi then PhPinf
  else PhMid.

Fixpoint Hsup (l : list Q) (n : nat) : Q :=
  match n with
  | O => H_adj (Pinf l 0)
  | S m => let prev := Hsup l m in
           let cur := H_adj (Pinf l (S m)) in
           if Qle_bool prev cur then cur else prev
  end.

Lemma Hsup_S_eq : forall (l : list Q) (n : nat),
  Hsup l (S n) =
  if Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))
  then H_adj (Pinf l (S n)) else Hsup l n.
Proof. reflexivity. Defined.

Theorem Hsup_mono : forall (l : list Q) (n : nat),
  (Hsup l n <= Hsup l (S n))%Q.
Proof.
  intros l n. rewrite Hsup_S_eq.
  destruct (Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))) eqn:E.
  - apply (proj1 (Qle_bool_iff _ _)). exact E.
  - apply Qle_refl.
Defined.

Lemma llm_P0_length_local : forall l : list Q, Id (length (P0 l)) (length l).
Proof.
  intro l. apply eq_imp_id.
  symmetry. apply (Permutation_length (D5_P0_perm l)).
Defined.

Lemma llm_Pmid_zero_local : forall (l : list Q) (s : nat),
  Id (Pmid l s 0) (Pinf l s).
Proof.
  intros l s. apply eq_imp_id. reflexivity.
Defined.

Lemma llm_Pmid_full_local : forall (l : list Q) (s : nat) (lam : nat),
  NatLe (length l) lam -> Id (Pmid l s lam) (P0 l).
Proof.
  intros l s lam H. apply eq_imp_id. unfold Pmid.
  pose proof (NatLe_drop (length l) lam H) as Hp.
  assert (Hlen : (length (P0 l) <= lam)%nat).
  { rewrite (id_eq _ _ (llm_P0_length_local l)). exact Hp. }
  rewrite (id_eq _ _ (rotc_firstn_all (P0 l) lam (NatLe_lift (length (P0 l)) lam Hlen))).
  assert (Hskip : NatLe (length (Pinf l s)) lam).
  { apply NatLe_lift. unfold Pinf, rot.
    rewrite length_app, length_firstn, length_skipn. lia. }
  rewrite (id_eq _ _ (rotc_skipn_all (Pinf l s) lam Hskip)).
  rewrite app_nil_r.
  reflexivity.
Defined.


(* ========== Section I: addition law, freezing, spectrum ========== *)

Lemma hs_skipn_app_le : forall (b : list Q) (m : nat) (c : list Q),
  NatLe m (length b) -> Id (skipn m (b ++ c)) (skipn m b ++ c).
Proof.
  intro b. induction b as [| x bs IH]; intros m c Hm.
  - destruct m as [| m'].
    + apply eq_imp_id. reflexivity.
    + apply (False_rect (Id (skipn (S m') ([] ++ c)) (skipn (S m') [] ++ c))).
      pose proof (NatLe_drop (S m') (length (@nil Q)) Hm). simpl in *. lia.
  - destruct m as [| m'].
    + apply eq_imp_id. reflexivity.
    + cbn [skipn app].
      assert (Hm' : NatLe m' (length bs)).
      { apply NatLe_lift.
        pose proof (NatLe_drop (S m') (S (length bs)) Hm) as Hp.
        apply (proj2 (Nat.succ_le_mono m' (length bs))). exact Hp. }
      exact (IH m' c Hm').
Defined.

Lemma hs_firstn_app_le : forall (b : list Q) (m : nat) (c : list Q),
  NatLe m (length b) -> Id (firstn m (b ++ c)) (firstn m b).
Proof.
  intro b. induction b as [| x bs IH]; intros m c Hm.
  - destruct m as [| m'].
    + apply eq_imp_id. reflexivity.
    + apply (False_rect (Id (firstn (S m') ([] ++ c)) (firstn (S m') []))).
      pose proof (NatLe_drop (S m') (length (@nil Q)) Hm). simpl in *. lia.
  - destruct m as [| m'].
    + apply eq_imp_id. reflexivity.
    + cbn [firstn app].
      assert (Hm' : NatLe m' (length bs)).
      { apply NatLe_lift.
        pose proof (NatLe_drop (S m') (S (length bs)) Hm) as Hp.
        apply (proj2 (Nat.succ_le_mono m' (length bs))). exact Hp. }
      exact (id_cong (fun w => x :: w) (IH m' c Hm')).
Defined.

Lemma hs_skipn_app_r : forall (a : list Q) (k : nat) (c : list Q),
  NatLe (length a) k -> Id (skipn k (a ++ c)) (skipn (k - length a) c).
Proof.
  intro a. induction a as [| x as' IH]; intros k c Hk.
  - destruct k as [| k']; apply eq_imp_id; reflexivity.
  - destruct k as [| k'].
    + apply (False_rect (Id (skipn 0 ((x :: as') ++ c)) (skipn (0 - length (x :: as')) c))).
      pose proof (NatLe_drop (S (length as')) 0 Hk). simpl in *. lia.
    + cbn [skipn app].
      assert (Hk' : NatLe (length as') k').
      { apply NatLe_lift.
        pose proof (NatLe_drop (S (length as')) (S k') Hk) as Hp.
        apply (proj2 (Nat.succ_le_mono (length as') k')). exact Hp. }
      exact (IH k' c Hk').
Defined.

Lemma hs_firstn_app_gen : forall (a : list Q) (k : nat) (c : list Q),
  Id (firstn k (a ++ c)) (firstn k a ++ firstn (k - length a) c).
Proof.
  intro a. induction a as [| x as' IH]; intros k c.
  - destruct k as [| k']; apply eq_imp_id; reflexivity.
  - destruct k as [| k'].
    + apply eq_imp_id. reflexivity.
    + cbn [firstn app].
      exact (id_cong (fun w => x :: w) (IH k' c)).
Defined.

Theorem rotc_add_local : forall (m n : nat) (l : list Q),
  NatLe (m + n) (length l) -> Id (rotc m (rotc n l)) (rotc (m + n) l).
Proof.
  intros m n l Hmn.
  pose proof (NatLe_drop (m + n) (length l) Hmn) as Hmnle.
  assert (Hnle : (n <= length l)%nat) by lia.
  apply eq_imp_id.
  pose (a := firstn n l).
  pose (b := skipn n l).
  assert (Hla : (length a = n)%nat) by exact (firstn_length_le l Hnle).
  assert (Hsplit : l = a ++ b)
    by (unfold a, b; symmetry; apply firstn_skipn).
  assert (Hrot : rotc n l = b ++ a).
  { rewrite <- Hla. rewrite Hsplit.
    exact (id_eq _ _ (rotc_rot_app a b)). }
  assert (Hll : (length l = length a + length b)%nat)
    by (rewrite Hsplit; rewrite length_app; lia).
  assert (Hmb : (m <= length b)%nat) by lia.
  assert (Hage : (length a <= m + n)%nat) by lia.
  rewrite Hrot. rewrite Hsplit.
  unfold rotc.
  rewrite (id_eq _ _ (hs_skipn_app_le b m a (NatLe_lift m (length b) Hmb))).
  rewrite (id_eq _ _ (hs_firstn_app_le b m a (NatLe_lift m (length b) Hmb))).
  rewrite (id_eq _ _ (hs_skipn_app_r a (m + n) b (NatLe_lift (length a) (m + n) Hage))).
  rewrite (id_eq _ _ (hs_firstn_app_gen a (m + n) b)).
  rewrite (id_eq _ _ (rotc_firstn_all a (m + n) (NatLe_lift (length a) (m + n) Hage))).
  assert (Hsub : (m + n - length a = m)%nat) by lia.
  rewrite Hsub.
  rewrite <- app_assoc.
  reflexivity.
Defined.

Theorem rotc_freeze_local : forall (k : nat) (l : list Q),
  Id (rotc (k + length l) l) (rotc (length l) l).
Proof.
  intros k l.
  assert (H1 : Id (rotc (k + length l) l) l).
  { apply (rotc_ge_len_id (k + length l) l).
    apply NatLe_lift. lia. }
  rewrite (id_eq _ _ H1).
  rewrite (id_eq _ _ (rotc_full l)).
  exact id_refl.
Defined.

Theorem rotc_periodic_naive_false :
  sigT (fun l : list Q =>
        sigT (fun k : nat => NeqL (rotc (k + length l) l) (rotc k l))).
Proof.
  apply (existT _ [0; 1; 2]). apply (existT _ 1%nat).
  vm_compute. exact id_refl.
Defined.

Theorem rotc_add_naive_false :
  sigT (fun l : list Q =>
        sigT (fun m : nat =>
              sigT (fun n : nat => NeqL (rotc m (rotc n l)) (rotc (m + n) l)))).
Proof.
  apply (existT _ [0; 1; 2]). apply (existT _ 3%nat). apply (existT _ 1%nat).
  vm_compute. exact id_refl.
Defined.

Lemma qmax2_le : forall x y : Q, QleT' y x -> QleT' (qmax2 x y) x.
Proof.
  intros x y Hy. unfold qmax2. destruct (Qle_bool x y) eqn:E.
  - exact Hy.
  - apply Qle_to_QleT'. apply Qle_refl.
Defined.

Theorem Hsup_cyc_mono_from : forall (l : list Q) (a b : nat),
  NatLe a b -> QleT' (Hsup_cyc l a) (Hsup_cyc l b).
Proof.
  intros l a b. induction b as [| b IH]; intros Ha.
  - assert (H0 : (a = 0)%nat) by (pose proof (NatLe_drop a 0 Ha); lia).
    rewrite H0. apply Qle_to_QleT'. apply Qle_refl.
  - destruct (cyc_nat_cases a b) as [Hle | Hgt].
    + apply Qle_to_QleT'.
      apply (Qle_trans (Hsup_cyc l a) (Hsup_cyc l b) (Hsup_cyc l (S b))).
      * apply QleT'_to_Qle. apply IH. exact Hle.
      * apply QleT'_to_Qle. apply Hsup_cyc_mono.
    + pose proof (NatLe_drop a (S b) Ha) as Hp1.
      assert (Ha' : (a = S b)%nat) by (pose proof (NatLe_drop (S b) a Hgt); lia).
      rewrite Ha'. apply Qle_to_QleT'. apply Qle_refl.
Defined.

Lemma H_adj_eq_Hsup0 : forall l : list Q, QeqT (H_adj l) (Hsup_cyc l 0).
Proof.
  intro l. cbn [Hsup_cyc].
  rewrite (id_eq _ _ (rotc_0 l)).
  apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem Hsup_cyc_step_frozen : forall (l : list Q) (n : nat),
  NatLe (length l) n -> QeqT (Hsup_cyc l (S n)) (Hsup_cyc l n).
Proof.
  intros l n Hn.
  assert (Hle : NatLe (length l) (S n))
    by (apply NatLe_lift;
        pose proof (NatLe_drop (length l) n Hn) as Hp; lia).
  cbn [Hsup_cyc].
  rewrite (id_eq _ _ (rotc_ge_len_id (S n) l Hle)).
  apply qeq_imp_qeqT. apply Qle_antisym.
  - apply QleT'_to_Qle. apply qmax2_le.
    apply Qle_to_QleT'.
    apply (Qle_trans (H_adj l) (Hsup_cyc l 0) (Hsup_cyc l n)).
    + apply QleT'_to_Qle. apply xq_Qeq_le.
      exact (qeqT_imp_qeq _ _ (H_adj_eq_Hsup0 l)).
    + apply QleT'_to_Qle.
      exact (Hsup_cyc_mono_from l 0 n (NatLe_lift 0 n (Nat.le_0_l n))).
  - apply QleT'_to_Qle. apply qmax2_ub_l.
Defined.

Theorem Hsup_cyc_stable : forall (l : list Q) (n : nat),
  NatLe (length l) n -> QeqT (Hsup_cyc l n) (Hsup_cyc l (length l)).
Proof.
  intros l n. induction n as [| n IH]; intros Hn.
  - destruct l as [| a rest].
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + apply (False_rect (QeqT (Hsup_cyc (a :: rest) 0)
                              (Hsup_cyc (a :: rest) (length (a :: rest))))).
      pose proof (NatLe_drop (length (a :: rest)) 0 Hn). simpl in *. lia.
  - destruct (cyc_nat_cases (length l) n) as [Hle | Hgt].
    + apply qeq_imp_qeqT.
      apply (Qeq_trans (Hsup_cyc l (S n)) (Hsup_cyc l n) (Hsup_cyc l (length l))).
      * exact (qeqT_imp_qeq _ _ (Hsup_cyc_step_frozen l n Hle)).
      * exact (qeqT_imp_qeq _ _ (IH Hle)).
    + assert (Heq : (length l = S n)%nat).
      { pose proof (NatLe_drop (S n) (length l) Hgt).
        pose proof (NatLe_drop (length l) (S n) Hn). lia. }
      rewrite Heq. apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem rotc_spectrum_bound : forall (k : nat) (l : list Q),
  sigT (fun k' : nat =>
        And (NatLe k' (length l - 1)) (Id (rotc k l) (rotc k' l))).
Proof.
  intros k l.
  destruct (cyc_nat_cases (S k) (length l)) as [Hlt | Hge].
  - apply (existT _ k). split.
    + apply NatLe_lift. pose proof (NatLe_drop (S k) (length l) Hlt). lia.
    + apply eq_imp_id. reflexivity.
  - apply (existT _ 0%nat). split.
    + apply NatLe_lift. apply Nat.le_0_l.
    + assert (Hge' : NatLe (length l) k).
      { apply NatLe_lift.
        pose proof (NatLe_drop (S (length l)) (S k) Hge) as Hp.
        apply (proj2 (Nat.succ_le_mono (length l) k)). exact Hp. }
      rewrite (id_eq _ _ (rotc_ge_len_id k l Hge')).
      rewrite (id_eq _ _ (rotc_0 l)).
      exact id_refl.
Defined.

Theorem H_adj_spectrum_bound : forall (k : nat) (l : list Q),
  sigT (fun k' : nat =>
        And (NatLe k' (length l - 1))
            (QeqT (H_adj (rotc k l)) (H_adj (rotc k' l)))).
Proof.
  intros k l. destruct (rotc_spectrum_bound k l) as [k' [Hle Heq]].
  apply (existT _ k'). split.
  - exact Hle.
  - rewrite (id_eq _ _ Heq). apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem Hsup_cyc_attained_range : forall (l : list Q) (n : nat),
  sigT (fun i : nat =>
        And (NatLe i (length l)) (QeqT (Hsup_cyc l n) (H_adj (rotc i l)))).
Proof.
  intros l n.
  destruct (Hsup_cyc_attained l n) as [i [Hin Hval]].
  destruct (cyc_nat_cases (S i) (length l)) as [Hlt | Hge].
  - apply (existT _ i). split.
    + apply NatLe_lift.
      pose proof (NatLe_drop (S i) (length l) Hlt). lia.
    + exact Hval.
  - pose proof (NatLe_drop (S (length l)) (S i) Hge) as Hp.
    assert (Hge' : NatLe (length l) i) by (apply NatLe_lift; lia).
    rewrite (id_eq _ _ (rotc_ge_len_id i l Hge')) in Hval.
    apply (existT _ (length l)). split.
    + apply natle_reflT.
    + rewrite (id_eq _ _ (rotc_full l)). exact Hval.
Defined.

Theorem Hsup_cyc_stable_wit : QeqT (Hsup_cyc [0; 1; 2] 5) (Hsup_cyc [0; 1; 2] 2).
Proof. vm_compute. exact id_refl. Defined.

Theorem Hsup_cyc_frozen_value_wit : QeqT (Hsup_cyc [0; 1; 2] 7) 3%Q.
Proof. vm_compute. exact id_refl. Defined.

(* ========== Section J: seam order and the sharpened bound ========== *)

Theorem rotc_periodic : forall (l : list Q) (k : nat),
  NatLe (length l) k -> Id (rotc (k + length l) l) (rotc k l).
Proof.
  intros l k Hk.
  assert (H1 : Id (rotc (k + length l) l) l).
  { apply (rotc_ge_len_id (k + length l) l).
    apply NatLe_lift. lia. }
  rewrite (id_eq _ _ H1).
  rewrite (id_eq _ _ (rotc_ge_len_id k l Hk)).
  exact id_refl.
Defined.

Theorem rotc_class_folds : forall (l : list Q) (k : nat),
  sigT (fun j : nat => And (NatLe j (length l)) (Id (rotc k l) (rotc j l))).
Proof.
  intros l k.
  destruct (cyc_nat_cases (length l) k) as [Hge | Hlt].
  - apply (existT _ 0%nat). split.
    + apply NatLe_lift. apply Nat.le_0_l.
    + rewrite (id_eq _ _ (rotc_ge_len_id k l Hge)).
      rewrite (id_eq _ _ (rotc_0 l)).
      exact id_refl.
  - apply (existT _ k). split.
    + apply NatLe_lift. pose proof (NatLe_drop (S k) (length l) Hlt). lia.
    + apply eq_imp_id. reflexivity.
Defined.

Lemma rs_lastq_cons_ne : forall (x : Q) (xs : list Q),
  NeT xs -> Id (lastq (x :: xs)) (lastq xs).
Proof.
  intros x xs Hne. destruct xs as [| y ys].
  - destruct Hne.
  - apply eq_imp_id. reflexivity.
Defined.

Theorem rs_lastq_firstn_hd_skipn : forall (l : list Q) (j : nat),
  NatLe (S j) (length l) -> Id (lastq (firstn (S j) l)) (hd 0 (skipn j l)).
Proof.
  intro l. induction l as [| a rest IH]; intros j Hj.
  - apply (False_rect (Id (lastq (firstn (S j) [])) (hd 0 (skipn j [])))).
    pose proof (NatLe_drop (S j) (length (@nil Q)) Hj). simpl in *. lia.
  - destruct j as [| j'].
    + apply eq_imp_id. reflexivity.
    + assert (Hj' : NatLe (S j') (length rest)).
      { apply NatLe_lift.
        pose proof (NatLe_drop (S (S j')) (S (length rest)) Hj) as Hp.
        apply (proj2 (Nat.succ_le_mono (S j') (length rest))). exact Hp. }
      assert (Hne : NeT (firstn (S j') rest)).
      { apply firstn_neT.
        - apply NatLe_lift. lia.
        - exact Hj'. }
      change (firstn (S (S j')) (a :: rest)) with (a :: firstn (S j') rest).
      change (skipn (S j') (a :: rest)) with (skipn j' rest).
      rewrite (id_eq _ _ (rs_lastq_cons_ne a (firstn (S j') rest) Hne)).
      exact (IH j' Hj').
Defined.

Theorem rs_skipn_S_incl : forall (l : list Q) (j : nat) (z : Q),
  InT z (skipn (S j) l) -> InT z (skipn j l).
Proof.
  intro l. induction l as [| a rest IH]; intros j z Hin.
  - destruct j; simpl in Hin; inversion Hin.
  - destruct j as [| j'].
    + simpl in Hin. apply InT_next. exact Hin.
    + simpl in Hin. simpl. exact (IH j' z Hin).
Defined.

Theorem rs_seam_order : forall (l : list Q) (k : nat),
  SortedQ l -> NatLe 1 k -> NatLe (S k) (length l) ->
  QleT' (lastq (firstn k l)) (hd 0 (skipn k l)).
Proof.
  intros l k HS H0 Hlt. destruct k as [| k'].
  - apply (False_rect (QleT' (lastq (firstn 0 l)) (hd 0 (skipn 0 l)))).
    pose proof (NatLe_drop 1 0 H0). lia.
  - assert (Hk' : NatLe (S k') (length l)).
    { apply NatLe_lift.
      pose proof (NatLe_drop (S (S k')) (length l) Hlt) as Hp. lia. }
    assert (E : Id (lastq (firstn (S k') l)) (hd 0 (skipn k' l)))
      by exact (rs_lastq_firstn_hd_skipn l k' Hk').
    rewrite (id_eq _ _ E).
    apply (sorted_hd_min (skipn k' l) (skipn_SortedQ l k' HS)
                         (hd 0 (skipn (S k') l))).
    apply (rs_skipn_S_incl l k').
    exact (inT_hd (skipn (S k') l) (skipn_neT (S k') l Hlt)).
Defined.

Theorem rotc_class_sharp_ub : forall (l : list Q) (k : nat),
  SortedQ l -> QleT' (H_adj (rotc k l)) (2 * (lastq l - hd 0 l)).
Proof.
  intros l k HS.
  assert (Hsp : QleT' 0 (lastq l - hd 0 l)).
  { apply (fst (Qle_0_sub' (hd 0 l) (lastq l))).
    apply xq_hd_le_lastq. exact HS. }
  destruct (cyc_nat_cases (length l) k) as [Hge | Hlt].
  - rewrite (id_eq _ _ (rotc_ge_len_id k l Hge)).
    apply Qle_to_QleT'.
    apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (2 * (lastq l - hd 0 l))).
    + rewrite (qeqT_imp_qeq _ _ (xq_telescope l HS)). apply Qle_refl.
    + apply QleT'_to_Qle. apply rs_le_double. exact Hsp.
  - destruct k as [| k'].
    + rewrite (id_eq _ _ (rotc_0 l)).
      apply Qle_to_QleT'.
      apply (Qle_trans (H_adj l) (lastq l - hd 0 l) (2 * (lastq l - hd 0 l))).
      * rewrite (qeqT_imp_qeq _ _ (xq_telescope l HS)). apply Qle_refl.
      * apply QleT'_to_Qle. apply rs_le_double. exact Hsp.
    + assert (H1 : NatLe 1 (S k')) by (apply NatLe_lift; lia).
      assert (HEm : QeqT (H_adj (rotc (S k') l))
                    ((lastq l - hd 0 (skipn (S k') l))
                     + (lastq l - hd 0 l)
                     + (lastq (firstn (S k') l) - hd 0 l)))
        by exact (H_adj_rotc_exact_mid (S k') l HS H1 Hlt).
      assert (Hseam : QleT' (lastq (firstn (S k') l)) (hd 0 (skipn (S k') l)))
        by exact (rs_seam_order l (S k') HS H1 Hlt).
      assert (Hsum : QleT' ((lastq l - hd 0 (skipn (S k') l))
                            + (lastq (firstn (S k') l) - hd 0 l))
                           (lastq l - hd 0 l)).
      { apply (snd (Qle_0_sub' _ _)).
        assert (Hr : (lastq l - hd 0 l
                      - ((lastq l - hd 0 (skipn (S k') l))
                         + (lastq (firstn (S k') l) - hd 0 l))
                      == hd 0 (skipn (S k') l) - lastq (firstn (S k') l))%Q)
          by ring.
        apply (qleT_arg_eq 0
                 (hd 0 (skipn (S k') l) - lastq (firstn (S k') l))
                 (lastq l - hd 0 l
                  - ((lastq l - hd 0 (skipn (S k') l))
                     + (lastq (firstn (S k') l) - hd 0 l)))).
        - apply qeq_imp_qeqT. apply Qeq_sym. exact Hr.
        - apply (fst (Qle_0_sub' (lastq (firstn (S k') l))
                                 (hd 0 (skipn (S k') l)))).
          exact Hseam. }
      apply Qle_to_QleT'.
      apply (Qle_trans _ ((lastq l - hd 0 (skipn (S k') l))
                        + (lastq l - hd 0 l)
                        + (lastq (firstn (S k') l) - hd 0 l))
                        (2 * (lastq l - hd 0 l))).
      * rewrite (qeqT_imp_qeq _ _ HEm). apply Qle_refl.
      * assert (H2s : (2 * (lastq l - hd 0 l)
                       == (lastq l - hd 0 l) + (lastq l - hd 0 l))%Q)
          by ring.
        rewrite (qeqT_imp_qeq _ _ (qeq_imp_qeqT _ _ H2s)).
        assert (Hrw : ((lastq l - hd 0 (skipn (S k') l))
                       + (lastq l - hd 0 l)
                       + (lastq (firstn (S k') l) - hd 0 l)
                       == (lastq l - hd 0 (skipn (S k') l)
                           + (lastq (firstn (S k') l) - hd 0 l))
                          + (lastq l - hd 0 l))%Q)
          by ring.
        rewrite Hrw.
        apply QleT'_to_Qle. apply qadd_le;
          [ exact (QleT'_to_Qle _ _ Hsum) | apply Qle_refl ].
Defined.

Lemma sorted_wit_002 : SortedQ [0; 0; 2].
Proof.
  apply sortQ_cons.
  - apply sortQ_cons.
    + apply sortQ_cons.
      * apply sortQ_nil.
      * apply Forall_nil.
    + apply Forall_forall. intros z Hz. simpl in Hz.
      destruct Hz as [E | []]; subst z.
      apply QleT'_to_Qle. apply xq_Qle_bool_le.
      vm_compute. reflexivity.
  - apply Forall_forall. intros z Hz. simpl in Hz.
    destruct Hz as [E | [E | []]]; subst z.
    + apply QleT'_to_Qle. apply xq_Qle_bool_le. vm_compute. reflexivity.
    + apply QleT'_to_Qle. apply xq_Qle_bool_le. vm_compute. reflexivity.
Defined.

Theorem rotc_class_sharp_attained :
  sigT (fun l : list Q =>
        sigT (fun k : nat =>
              And (SortedQ l)
                  (QeqT (H_adj (rotc k l)) (2 * (lastq l - hd 0 l))))).
Proof.
  apply (existT _ [0; 0; 2]). apply (existT _ 1%nat). split.
  - apply sorted_wit_002.
  - vm_compute. exact id_refl.
Defined.

(* ========== Section K: phase base faces ========== *)

Theorem rotc_P0_min : forall (l : list Q) (k : nat),
  QleT' (H_adj (P0 l)) (H_adj (rotc k l)).
Proof.
  intros l k. destruct l as [| a rest].
  - destruct k; apply Qle_to_QleT'; apply Qle_refl.
  - assert (HP : QeqT (H_adj (P0 (a :: rest)))
                 (lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : QeqT (Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest))))
                  (lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))).
    { apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _
                (xq_abs_sub_comm (hd 0 (P0 (a :: rest)))
                                 (lastq (P0 (a :: rest))))).
      apply qeqT_imp_qeq. apply xq_abs_id.
      apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) (rotc k (a :: rest))).
    { apply Permutation_in with (l := a :: rest).
      - apply Permutation_sym. etransitivity.
        + apply Permutation_app_comm.
        + rewrite firstn_skipn. apply Permutation_refl.
      - apply Permutation_in with (l := P0 (a :: rest)).
        + apply Permutation_sym. apply D5_P0_perm.
        + apply xq_hd_In_gen. apply xq_P0_cons_ne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) (rotc k (a :: rest))).
    { apply Permutation_in with (l := a :: rest).
      - apply Permutation_sym. etransitivity.
        + apply Permutation_app_comm.
        + rewrite firstn_skipn. apply Permutation_refl.
      - apply Permutation_in with (l := P0 (a :: rest)).
        + apply Permutation_sym. apply D5_P0_perm.
        + apply xq_lastq_In. apply xq_P0_cons_ne. }
    assert (HPd : QleT' (Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest))))
                        (H_adj (rotc k (a :: rest)))).
    { apply xq_pair_dist_le; assumption. }
    pose proof (qeqT_imp_qeq _ _ HP) as HPq.
    pose proof (qeqT_imp_qeq _ _ HP2) as HP2q.
    apply Qle_to_QleT'.
    rewrite HPq. rewrite <- HP2q.
    apply QleT'_to_Qle. exact HPd.
Defined.

Theorem rotc_0_H_adj : forall l : list Q, QeqT (H_adj (rotc 0 l)) (H_adj l).
Proof.
  intro l.
  rewrite (id_eq _ _ (rotc_0 l)).
  apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem phase_side_cyc_side_degenerate : forall (l : list Q) (k : nat),
  Id (Qle_bool (H_adj (P0 l)) (H_adj (rotc k l))) true.
Proof.
  intros l k. apply xq_Qle_bool_true.
  apply QleT'_to_Qle. apply rotc_P0_min.
Defined.

Theorem phase_side_cyc_side_zero : forall (l : list Q) (k : nat),
  Id ((if Qle_bool (H_adj (P0 l)) (H_adj (rotc k l)) then 0 else 1)%nat) 0%nat.
Proof.
  intros l k.
  rewrite (id_eq _ _ (phase_side_cyc_side_degenerate l k)).
  apply eq_imp_id. reflexivity.
Defined.

(* ========== Section L: the affine lambda-interpolation family ========== *)

Lemma lam_affine_diff_sub : forall h0 h1 lam1 lam2 : Q,
  QeqT (lam1 * h0 + (1 - lam1) * h1 - (lam2 * h0 + (1 - lam2) * h1))
       ((lam1 - lam2) * (h0 - h1)).
Proof.
  intros h0 h1 lam1 lam2. apply qeq_imp_qeqT.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  change (lam1 - lam2) with (lam1 + - lam2)%Q.
  change (h0 - h1) with (h0 + - h1)%Q.
  change ((lam1 * h0 + (1 + - lam1) * h1) - (lam2 * h0 + (1 + - lam2) * h1))
    with ((lam1 * h0 + (1 + - lam1) * h1)
          + - (lam2 * h0 + (1 + - lam2) * h1))%Q.
  ring.
Defined.

Theorem H_lam_diff_sub : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  QeqT (H_lam l s lam1 - H_lam l s lam2)
       ((lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s))).
Proof.
  intros l s lam1 lam2. unfold H_lam.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (Pinf l s)) lam1 lam2).
Defined.

Theorem H_lam_affine : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam l s lam)
       (H_adj (Pinf l s) + lam * (H_adj (P0 l) - H_adj (Pinf l s))).
Proof.
  intros l s lam. apply qeq_imp_qeqT. unfold H_lam.
  change (1 - lam) with (1 + - lam)%Q.
  change (H_adj (P0 l) - H_adj (Pinf l s))
    with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
  ring.
Defined.

Theorem H_lam_anti_mono : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  QleT' lam1 lam2 -> QleT' (H_lam l s lam2) (H_lam l s lam1).
Proof.
  intros l s lam1 lam2 Hlam.
  assert (Hs : QleT' 0 ((lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l)))).
  { apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply QleT'_to_Qle.
      apply (fst (Qle_0_sub' (H_adj (P0 l)) (H_adj (Pinf l s)))).
      apply H_adj_cross_phase_lb. }
  assert (Hsd : QeqT (H_lam l s lam1 - H_lam l s lam2)
                ((lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l)))).
  { apply qeq_imp_qeqT.
    apply (Qeq_trans _ ((lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s)))).
    - exact (qeqT_imp_qeq _ _ (H_lam_diff_sub l s lam1 lam2)).
    - change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (Pinf l s))
        with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
      change (H_adj (Pinf l s) - H_adj (P0 l))
        with (H_adj (Pinf l s) + - H_adj (P0 l))%Q.
      ring. }
  apply (qleT_from_diff (H_lam l s lam2) (H_lam l s lam1)
           ((lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l)))).
  - exact Hsd.
  - exact Hs.
Defined.

Theorem H_lam_mono_diff : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  QleT' (H_adj (Pinf l s)) (H_adj (P0 l)) -> QleT' lam1 lam2 ->
  QleT' (H_lam l s lam1) (H_lam l s lam2).
Proof.
  intros l s lam1 lam2 Hle Hlam.
  assert (Hs : QleT' 0 ((lam2 - lam1) * (H_adj (P0 l) - H_adj (Pinf l s)))).
  { apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply QleT'_to_Qle.
      apply (fst (Qle_0_sub' (H_adj (Pinf l s)) (H_adj (P0 l)))). exact Hle. }
  apply (qleT_from_diff (H_lam l s lam1) (H_lam l s lam2)
           ((lam2 - lam1) * (H_adj (P0 l) - H_adj (Pinf l s)))).
  - exact (H_lam_diff_sub l s lam2 lam1).
  - exact Hs.
Defined.

Theorem H_lam_const_when_eq : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_adj (P0 l)) (H_adj (Pinf l s)) -> QeqT (H_lam l s lam) (H_adj (P0 l)).
Proof.
  intros l s lam Heq. apply qeq_imp_qeqT. unfold H_lam.
  rewrite (qeqT_imp_qeq _ _ Heq).
  ring.
Defined.

Theorem H_lam_midpoint : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  QeqT (H_lam l s ((lam1 + lam2) / 2))
       ((H_lam l s lam1 + H_lam l s lam2) / 2).
Proof.
  intros l s lam1 lam2. apply qeq_imp_qeqT. unfold H_lam.
  change (1 - (lam1 + lam2) / 2) with (1 + - ((lam1 + lam2) / 2))%Q.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  field.
Defined.

Definition lam_opt (h0 h1 : Q) : Q := align_lambda_opt h0 h1.

Theorem lam_opt_values : forall h0 h1 : Q,
  Or (Id (lam_opt h0 h1) 1%Q) (Id (lam_opt h0 h1) 0%Q).
Proof. intros h0 h1. exact (align_lambda_opt_values h0 h1). Defined.

Theorem lam_opt_range : forall h0 h1 : Q,
  And (QleT' 0 (lam_opt h0 h1)) (QleT' (lam_opt h0 h1) 1).
Proof. intros h0 h1. exact (align_lambda_opt_range h0 h1). Defined.

Theorem lam_opt_min : forall (h0 h1 lam : Q),
  And (QleT' 0 lam) (QleT' lam 1) ->
  QleT' (lam_opt h0 h1 * h0 + (1 - lam_opt h0 h1) * h1)
        (lam * h0 + (1 - lam) * h1).
Proof.
  intros h0 h1 lam H01. destruct H01 as [Hlam0 Hlam1].
  pose proof (QleT'_to_Qle _ _ Hlam0) as Hp0.
  pose proof (QleT'_to_Qle _ _ Hlam1) as Hp1.
  unfold lam_opt, align_lambda_opt.
  destruct (Qle_bool h0 h1) eqn:E.
  - assert (Hd : (0 <= lam * h0 + (1 - lam) * h1
                       - (1 * h0 + (1 - 1) * h1))%Q).
    { assert (Er : lam * h0 + (1 - lam) * h1 - (1 * h0 + (1 - 1) * h1)
                   == (1 - lam) * (h1 - h0)) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam 1)). exact Hlam1.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' h0 h1)).
        apply xq_Qle_bool_le. exact E. }
    apply (snd (Qle_0_sub' _ _)).
    apply Qle_to_QleT'. exact Hd.
  - assert (Hge : (h1 <= h0)%Q)
      by (apply QleT'_to_Qle; apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * h0 + (1 - lam) * h1
                       - (0 * h0 + (1 - 0) * h1))%Q).
    { assert (Er : lam * h0 + (1 - lam) * h1 - (0 * h0 + (1 - 0) * h1)
                   == lam * (h0 - h1)) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + exact Hp0.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' h1 h0)).
        apply Qle_to_QleT'. exact Hge. }
    apply (snd (Qle_0_sub' _ _)).
    apply Qle_to_QleT'. exact Hd.
Defined.

Theorem H_lam_lam_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  And (QleT' 0 lam) (QleT' lam 1) ->
  QleT' (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
        (H_lam l s lam).
Proof.
  intros l s lam H01. destruct H01 as [Hlam0 Hlam1].
  exact (align_lambda_opt_min l s lam
           (conj (QleT'_to_Qle _ _ Hlam0) (QleT'_to_Qle _ _ Hlam1))).
Defined.

Theorem H_lam_lam_opt_endpoint : forall (l : list Q) (s : nat),
  Or (QeqT (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (P0 l)))
     (QeqT (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (Pinf l s))).
Proof. intros l s. exact (align_lambda_opt_endpoint l s). Defined.

Theorem lam_opt_cross_phase : forall (l : list Q) (s : nat),
  Id (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) 1%Q.
Proof.
  intros l s. unfold lam_opt, align_lambda_opt.
  destruct (id_sym
              (xq_Qle_bool_true _ _ (QleT'_to_Qle _ _ (H_adj_cross_phase_lb l s)))).
  apply eq_imp_id. reflexivity.
Defined.

Theorem align_lambda_id : forall lam : Q, QeqT (align_lambda lam) lam.
Proof.
  intro lam. apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem align_lambda_H_lam : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam l s (align_lambda lam)) (H_lam l s lam).
Proof.
  intros l s lam. apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem lam_opt_min_align : forall (l : list Q) (s : nat) (lam : Q),
  And (QleT' 0 lam) (QleT' lam 1) ->
  QleT' (H_lam l s (align_lambda (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s)))))
        (H_lam l s lam).
Proof.
  intros l s lam H01. destruct H01 as [Hlam0 Hlam1].
  apply Qle_to_QleT'.
  apply (Qle_trans _ (H_lam l s (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))).
  - apply QleT'_to_Qle. apply xq_Qeq_le.
    exact (qeqT_imp_qeq _ _
             (align_lambda_H_lam l s
                (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))))).
  - apply QleT'_to_Qle. apply H_lam_lam_opt_min.
    exact (Hlam0, Hlam1).
Defined.

Theorem align_lambda_range : forall lam : Q,
  And (QleT' 0 lam) (QleT' lam 1) ->
  And (QleT' 0 (align_lambda lam)) (QleT' (align_lambda lam) 1).
Proof.
  intros lam Hr. destruct Hr as [H0 H1].
  exact (H0, H1).
Defined.

Theorem H_lam_extrap_below_counterex :
  sigT (fun l : list Q =>
        sigT (fun s : nat =>
              sigT (fun lam : Q =>
                    And (QltT 1 lam)
                        (And (QltT (H_lam l s lam) (H_adj (P0 l)))
                             (QleT' (H_adj (P0 l)) (H_adj (Pinf l s))))))).
Proof.
  apply (existT _ [1; 5; 2]). apply (existT _ 0%nat). apply (existT _ 2%Q).
  split.
  - vm_compute. exact id_refl.
  - split.
    + vm_compute. exact id_refl.
    + apply H_adj_cross_phase_lb.
Defined.

Theorem H_lam_extrap_above_counterex :
  sigT (fun l : list Q =>
        sigT (fun s : nat =>
              sigT (fun lam : Q =>
                    And (QltT lam 0)
                        (And (QltT (H_adj (Pinf l s)) (H_lam l s lam))
                             (QleT' (H_adj (P0 l)) (H_adj (Pinf l s))))))).
Proof.
  apply (existT _ [1; 5; 2]). apply (existT _ 0%nat). apply (existT _ (-1)%Q).
  split.
  - vm_compute. exact id_refl.
  - split.
    + vm_compute. exact id_refl.
    + apply H_adj_cross_phase_lb.
Defined.

(* ========== Section M: the true-rotation lambda family ========== *)

Definition H_lam_cyc (l : list Q) (k : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (rotc k l).

Theorem H_lam_cyc_lam1 : forall (l : list Q) (k : nat),
  QeqT (H_lam_cyc l k 1) (H_adj (P0 l)).
Proof.
  intros l k. apply qeq_imp_qeqT. unfold H_lam_cyc.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Defined.

Theorem H_lam_cyc_lam0 : forall (l : list Q) (k : nat),
  QeqT (H_lam_cyc l k 0) (H_adj (rotc k l)).
Proof.
  intros l k. apply qeq_imp_qeqT. unfold H_lam_cyc.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Defined.

Theorem H_lam_cyc_k0_oldface : forall (l : list Q) (lam : Q),
  QeqT (H_lam_cyc l 0%nat lam) (lam * H_adj (P0 l) + (1 - lam) * H_adj l).
Proof.
  intros l lam. apply qeq_imp_qeqT. unfold H_lam_cyc.
  rewrite (id_eq _ _ (rotc_0 l)).
  apply Qeq_refl.
Defined.

Theorem H_lam_cyc_diff : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  QeqT (H_lam_cyc l k lam1 - H_lam_cyc l k lam2)
       ((lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l))).
Proof.
  intros l k lam1 lam2. unfold H_lam_cyc.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (rotc k l)) lam1 lam2).
Defined.

Theorem H_lam_cyc_mono_inc : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  QleT' (H_adj (rotc k l)) (H_adj (P0 l)) ->
  And (QleT' 0 lam1) (QleT' lam1 1) ->
  And (QleT' 0 lam2) (QleT' lam2 1) ->
  QleT' lam1 lam2 ->
  QleT' (H_lam_cyc l k lam1) (H_lam_cyc l k lam2).
Proof.
  intros l k lam1 lam2 Hle _ _ Hlam.
  assert (Hs : QleT' 0 ((lam2 - lam1) * (H_adj (P0 l) - H_adj (rotc k l)))).
  { apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply QleT'_to_Qle.
      apply (fst (Qle_0_sub' (H_adj (rotc k l)) (H_adj (P0 l)))). exact Hle. }
  apply (qleT_from_diff (H_lam_cyc l k lam1) (H_lam_cyc l k lam2)
           ((lam2 - lam1) * (H_adj (P0 l) - H_adj (rotc k l)))).
  - exact (H_lam_cyc_diff l k lam2 lam1).
  - exact Hs.
Defined.

Theorem H_lam_cyc_mono_dec : forall (l : list Q) (k : nat) (lam1 lam2 : Q),
  QleT' (H_adj (P0 l)) (H_adj (rotc k l)) ->
  And (QleT' 0 lam1) (QleT' lam1 1) ->
  And (QleT' 0 lam2) (QleT' lam2 1) ->
  QleT' lam1 lam2 ->
  QleT' (H_lam_cyc l k lam2) (H_lam_cyc l k lam1).
Proof.
  intros l k lam1 lam2 Hle _ _ Hlam.
  assert (Hs : QleT' 0 ((lam2 - lam1) * (H_adj (rotc k l) - H_adj (P0 l)))).
  { apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply QleT'_to_Qle.
      apply (fst (Qle_0_sub' (H_adj (P0 l)) (H_adj (rotc k l)))). exact Hle. }
  assert (Hsd : QeqT (H_lam_cyc l k lam1 - H_lam_cyc l k lam2)
                ((lam2 - lam1) * (H_adj (rotc k l) - H_adj (P0 l)))).
  { apply qeq_imp_qeqT.
    apply (Qeq_trans _ ((lam1 - lam2) * (H_adj (P0 l) - H_adj (rotc k l)))).
    + exact (qeqT_imp_qeq _ _ (H_lam_cyc_diff l k lam1 lam2)).
    + change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (rotc k l))
        with (H_adj (P0 l) + - H_adj (rotc k l))%Q.
      change (H_adj (rotc k l) - H_adj (P0 l))
        with (H_adj (rotc k l) + - H_adj (P0 l))%Q.
      ring. }
  apply (qleT_from_diff (H_lam_cyc l k lam2) (H_lam_cyc l k lam1)
           ((lam2 - lam1) * (H_adj (rotc k l) - H_adj (P0 l)))).
  - exact Hsd.
  - exact Hs.
Defined.

Theorem H_lam_cyc_oldface_separates :
  sigT (fun l : list Q =>
        sigT (fun k : nat =>
              sigT (fun lam : Q =>
                    NeqT (H_lam_cyc l k lam)
                         (lam * H_adj (P0 l) + (1 - lam) * H_adj l)))).
Proof.
  apply (existT _ [0; 1; 2]). apply (existT _ 1%nat). apply (existT _ (1#2)%Q).
  vm_compute. exact id_refl.
Defined.

Theorem H_lam_cyc_H_lam_separates :
  sigT (fun l : list Q =>
        sigT (fun k : nat =>
              sigT (fun s : nat =>
                    sigT (fun lam : Q =>
                          NeqT (H_lam_cyc l k lam) (H_lam l s lam))))).
Proof.
  apply (existT _ [0; 1; 2]). apply (existT _ 1%nat). apply (existT _ 0%nat).
  apply (existT _ (1#2)%Q).
  vm_compute. exact id_refl.
Defined.

Definition lam_opt_cyc (h0 hk : Q) : Q := lam_opt h0 hk.

Theorem lam_opt_cyc_values : forall h0 hk : Q,
  Or (Id (lam_opt_cyc h0 hk) 1%Q) (Id (lam_opt_cyc h0 hk) 0%Q).
Proof. intros h0 hk. exact (lam_opt_values h0 hk). Defined.

Theorem lam_opt_cyc_range : forall h0 hk : Q,
  And (QleT' 0 (lam_opt_cyc h0 hk)) (QleT' (lam_opt_cyc h0 hk) 1).
Proof. intros h0 hk. exact (lam_opt_range h0 hk). Defined.

Theorem H_lam_cyc_lam_opt_cyc_min : forall (l : list Q) (k : nat) (lam : Q),
  And (QleT' 0 lam) (QleT' lam 1) ->
  QleT' (H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l))))
        (H_lam_cyc l k lam).
Proof.
  intros l k lam H01. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam_cyc, lam_opt_cyc.
  apply lam_opt_min. exact (Hlam0, Hlam1).
Defined.

Theorem H_lam_cyc_lam_opt_cyc_endpoint : forall (l : list Q) (k : nat),
  Or (QeqT (H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l))))
           (H_adj (P0 l)))
     (QeqT (H_lam_cyc l k (lam_opt_cyc (H_adj (P0 l)) (H_adj (rotc k l))))
           (H_adj (rotc k l))).
Proof.
  intros l k. unfold lam_opt_cyc.
  destruct (lam_opt_values (H_adj (P0 l)) (H_adj (rotc k l))) as [E | E].
  - left. rewrite (id_eq _ _ E). apply H_lam_cyc_lam1.
  - right. rewrite (id_eq _ _ E). apply H_lam_cyc_lam0.
Defined.

(* ========== Section N: the middle phase ========== *)

Lemma H_adj_app : forall (l1 l2 : list Q),
  NeT l1 -> NeT l2 ->
  QeqT (H_adj (l1 ++ l2))
       (H_adj l1 + Qabs (lastq l1 - hd 0 l2) + H_adj l2).
Proof.
  intros l1 l2 H1 H2. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (H_adj_app_seam l1 l2 H1 H2)).
  rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm (lastq l1) (hd 0 l2))).
  ring.
Defined.

Theorem H_adj_Pmid_seam : forall (l : list Q) (s : nat) (k : nat),
  NatLe 1 k -> NatLe (S k) (length l) ->
  QeqT (H_adj (Pmid l s k))
       (H_adj (firstn k (P0 l)) + H_adj (skipn k l)
        + Qabs (hd 0 (skipn k l) - lastq (firstn k (P0 l)))).
Proof.
  intros l s k Hk Hlt.
  apply qeq_imp_qeqT. unfold Pmid.
  rewrite (id_eq _ _ (Pinf_true_id l s)).
  apply qeqT_imp_qeq. apply H_adj_app_seam.
  - apply firstn_neT.
    + exact Hk.
    + apply NatLe_lift. rewrite (id_eq _ _ (llm_P0_length_local l)).
      pose proof (NatLe_drop (S k) (length l) Hlt). lia.
  - exact (skipn_neT k l Hlt).
Defined.

Theorem H_adj_Pmid_decomp : forall (l : list Q) (s : nat) (k : nat),
  NatLe 1 k -> NatLe (S k) (length l) ->
  QeqT (H_adj (Pmid l s k))
       (H_adj (firstn k (P0 l))
        + Qabs (lastq (firstn k (P0 l)) - hd 0 (skipn k l))
        + H_adj (skipn k l)).
Proof.
  intros l s k Hk Hlt.
  apply qeq_imp_qeqT. unfold Pmid.
  rewrite (id_eq _ _ (Pinf_true_id l s)).
  apply qeqT_imp_qeq. apply H_adj_app.
  - apply firstn_neT.
    + exact Hk.
    + apply NatLe_lift. rewrite (id_eq _ _ (llm_P0_length_local l)).
      pose proof (NatLe_drop (S k) (length l) Hlt). lia.
  - exact (skipn_neT k l Hlt).
Defined.

Theorem Pmid_sorted_collapse : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> Id (Pmid l s k) l.
Proof.
  intros l s k HS.
  unfold Pmid.
  rewrite (id_eq _ _ (Pinf_true_id l s)).
  rewrite (id_eq _ _ (xq_sortQ_P0_id l HS)).
  apply eq_imp_id. apply firstn_skipn.
Defined.

Theorem H_adj_Pmid_sorted_exact : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> QeqT (H_adj (Pmid l s k)) (H_adj l).
Proof.
  intros l s k HS.
  rewrite (id_eq _ _ (Pmid_sorted_collapse l s k HS)).
  apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem H_adj_Pmid_sorted_ub2 : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> QleT' (H_adj (Pmid l s k)) (2 * (lastq (P0 l) - hd 0 (P0 l))).
Proof.
  intros l s k HS.
  apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (H_adj_Pmid_sorted_exact l s k HS)) as Hd.
  rewrite Hd.
  pose proof (id_eq _ _ (xq_sortQ_P0_id l HS)) as EP0.
  rewrite EP0.
  rewrite (qeqT_imp_qeq _ _ (xq_telescope l HS)).
  apply QleT'_to_Qle. apply rs_le_double.
  apply (fst (Qle_0_sub' (hd 0 l) (lastq l))).
  apply xq_hd_le_lastq. exact HS.
Defined.

Theorem H_adj_Pmid_ub_gen : forall (l : list Q) (s : nat) (k : nat),
  NatLe 1 k -> NatLe (S k) (length l) ->
  QleT' (H_adj (Pmid l s k))
        (2 * (lastq (P0 l) - hd 0 (P0 l)) + H_adj (skipn k l)).
Proof.
  intros l s k Hk Hlt.
  apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (H_adj_Pmid_decomp l s k Hk Hlt)) as Hd.
  rewrite Hd.
  assert (Hnef : NeT (firstn k (P0 l))).
  { apply firstn_neT.
    - exact Hk.
    - apply NatLe_lift. rewrite (id_eq _ _ (llm_P0_length_local l)).
      pose proof (NatLe_drop (S k) (length l) Hlt). lia. }
  assert (Hnes : NeT (skipn k l)) by exact (skipn_neT k l Hlt).
  assert (HmemA : InT (lastq (firstn k (P0 l))) (P0 l)).
  { apply (firstn_incl (P0 l) k).
    exact (inT_lastq (firstn k (P0 l)) Hnef). }
  assert (HmemB : InT (hd 0 (skipn k l)) (P0 l)).
  { apply inT_P0_intro.
    apply (skipn_incl l k).
    exact (inT_hd (skipn k l) Hnes). }
  assert (HmemAhd : InT (hd 0 (firstn k (P0 l))) (P0 l)).
  { apply (firstn_incl (P0 l) k).
    exact (inT_hd (firstn k (P0 l)) Hnef). }
  assert (Hpre : QleT' (H_adj (firstn k (P0 l)))
                       (lastq (P0 l) - hd 0 (P0 l))).
  { apply (qleT_trans (H_adj (firstn k (P0 l)))
                      (lastq (firstn k (P0 l)) - hd 0 (firstn k (P0 l)))
                      (lastq (P0 l) - hd 0 (P0 l))).
    - apply qleT_of_qeqT.
      exact (xq_telescope (firstn k (P0 l))
               (firstn_SortedQ (P0 l) k (xq_P0_sorted l))).
    - exact (sorted_sub_le_spread (P0 l) (lastq (firstn k (P0 l)))
               (hd 0 (firstn k (P0 l))) (xq_P0_sorted l) HmemA HmemAhd). }
  assert (Hseam : QleT' (Qabs (lastq (firstn k (P0 l)) - hd 0 (skipn k l)))
                        (lastq (P0 l) - hd 0 (P0 l)))
    by exact (sorted_abs_le_spread (P0 l) (lastq (firstn k (P0 l)))
                (hd 0 (skipn k l)) (xq_P0_sorted l) HmemA HmemB).
  assert (H2s : (2 * (lastq (P0 l) - hd 0 (P0 l))
                 == (lastq (P0 l) - hd 0 (P0 l))
                    + (lastq (P0 l) - hd 0 (P0 l)))%Q) by ring.
  rewrite H2s.
  apply QleT'_to_Qle. apply qadd_le.
  - apply QleT'_to_Qle. apply qadd_le;
      [ exact (QleT'_to_Qle _ _ Hpre) | exact (QleT'_to_Qle _ _ Hseam) ].
  - apply Qle_refl.
Defined.

Theorem H_adj_Pmid_k0 : forall (l : list Q) (s : nat),
  QeqT (H_adj (Pmid l s 0%nat)) (H_adj l).
Proof.
  intros l s. apply qeq_imp_qeqT.
  rewrite (id_eq _ _ (llm_Pmid_zero_local l s)).
  rewrite (id_eq _ _ (Pinf_true_id l s)).
  apply Qeq_refl.
Defined.

Theorem H_adj_Pmid_klen : forall (l : list Q) (s : nat),
  QeqT (H_adj (Pmid l s (length l))) (H_adj (P0 l)).
Proof.
  intros l s. apply qeq_imp_qeqT.
  rewrite (id_eq _ _
   (llm_Pmid_full_local l s (length l) (natle_reflT (length l)))).
  apply Qeq_refl.
Defined.

Theorem H_adj_Pmid_endpoints_sorted : forall (l : list Q) (s : nat),
  SortedQ l ->
  And (QeqT (H_adj (Pmid l s 0%nat)) (lastq l - hd 0 l))
      (QeqT (H_adj (Pmid l s (length l))) (lastq l - hd 0 l)).
Proof.
  intros l s HS. split.
  - apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (H_adj_Pmid_k0 l s)).
    exact (qeqT_imp_qeq _ _ (xq_telescope l HS)).
  - apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (H_adj_Pmid_klen l s)).
    rewrite (id_eq _ _ (xq_sortQ_P0_id l HS)).
    exact (qeqT_imp_qeq _ _ (xq_telescope l HS)).
Defined.

Definition pt_code (t : PhaseTag) : nat :=
  match t with
  | PhP0 => 0
  | PhMid => 1
  | PhPinf => 2
  end.

Definition phaseT_neq (u v : PhaseTag) : bool :=
  negb (Nat.eqb (pt_code u) (pt_code v)).

Theorem phase_classify_ne_PMid : forall (l : list Q) (s : nat),
  Id (phaseT_neq (phase_classify l s) PhMid) true.
Proof.
  intros l s.
  unfold phase_classify. cbv zeta.
  destruct (Qeq_bool (H_adj (Pmid l s 0%nat)) (H_adj (Pinf l s))) eqn:E.
  - destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0%nat))).
    + cbn [phaseT_neq pt_code negb Nat.eqb]. exact id_refl.
    + cbn [phaseT_neq pt_code negb Nat.eqb]. exact id_refl.
  - assert (Hid : H_adj (Pmid l s 0%nat) == H_adj (Pinf l s))
      by reflexivity.
    rewrite Hid in E.
    rewrite Qeq_bool_refl in E.
    discriminate E.
Defined.

Theorem Pmid_sorted_collapse_wit_012 :
  Id (Pmid [0; 1; 2] 0%nat 1%nat) [0; 1; 2].
Proof. vm_compute. exact id_refl. Defined.

Theorem H_adj_Pmid_decomp_wit_012 :
  QeqT (H_adj (Pmid [0; 1; 2] 0%nat 1%nat))
       (H_adj [0] + Qabs (lastq [0] - hd 0 [1; 2]) + H_adj [1; 2]).
Proof. vm_compute. exact id_refl. Defined.

(* ========== Section O: the true-middle-phase lambda family ========== *)

Definition H_lam_pmid (l : list Q) (s : nat) (k : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pmid l s k).

Theorem H_lam_pmid_lam1 : forall (l : list Q) (s : nat) (k : nat),
  QeqT (H_lam_pmid l s k 1) (H_adj (P0 l)).
Proof.
  intros l s k. apply qeq_imp_qeqT. unfold H_lam_pmid.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Defined.

Theorem H_lam_pmid_lam0 : forall (l : list Q) (s : nat) (k : nat),
  QeqT (H_lam_pmid l s k 0) (H_adj (Pmid l s k)).
Proof.
  intros l s k. apply qeq_imp_qeqT. unfold H_lam_pmid.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Defined.

Theorem H_lam_pmid_diff :
  forall (l : list Q) (s : nat) (k : nat) (lam1 lam2 : Q),
  QeqT (H_lam_pmid l s k lam1 - H_lam_pmid l s k lam2)
       ((lam1 - lam2) * (H_adj (P0 l) - H_adj (Pmid l s k))).
Proof.
  intros l s k lam1 lam2. unfold H_lam_pmid.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj (Pmid l s k)) lam1 lam2).
Defined.

Theorem H_lam_pmid_affine : forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  QeqT (H_lam_pmid l s k lam)
       (H_adj (Pmid l s k) + lam * (H_adj (P0 l) - H_adj (Pmid l s k))).
Proof.
  intros l s k lam. apply qeq_imp_qeqT. unfold H_lam_pmid.
  change (1 - lam) with (1 + - lam)%Q.
  change (H_adj (P0 l) - H_adj (Pmid l s k))
    with (H_adj (P0 l) + - H_adj (Pmid l s k))%Q.
  ring.
Defined.

Theorem H_lam_pmid_sorted_consistency :
  forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  SortedQ l -> QeqT (H_lam_pmid l s k lam) (H_lam l s lam).
Proof.
  intros l s k lam HS. apply qeq_imp_qeqT.
  unfold H_lam_pmid, H_lam.
  rewrite (id_eq _ _ (Pmid_sorted_collapse l s k HS)).
  rewrite (id_eq _ _ (Pinf_true_id l s)).
  apply Qeq_refl.
Defined.

Theorem H_lam_pmid_sorted_lam1 : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> QeqT (H_lam_pmid l s k 1) (H_adj l).
Proof.
  intros l s k HS. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (H_lam_pmid_lam1 l s k)).
  rewrite (id_eq _ _ (xq_sortQ_P0_id l HS)).
  apply Qeq_refl.
Defined.

Theorem H_lam_pmid_sorted_lam0 : forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> QeqT (H_lam_pmid l s k 0) (H_adj l).
Proof.
  intros l s k HS. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (H_lam_pmid_lam0 l s k)).
  exact (qeqT_imp_qeq _ _ (H_adj_Pmid_sorted_exact l s k HS)).
Defined.

Theorem H_lam_pmid_k0_oldface : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_pmid l s 0%nat lam) (H_lam l s lam).
Proof.
  intros l s lam. apply qeq_imp_qeqT.
  unfold H_lam_pmid, H_lam.
  rewrite (id_eq _ _ (llm_Pmid_zero_local l s)).
  apply Qeq_refl.
Defined.

Theorem H_lam_pmid_klen_const : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_pmid l s (length l) lam) (H_adj (P0 l)).
Proof.
  intros l s lam. apply qeq_imp_qeqT. unfold H_lam_pmid.
  rewrite (id_eq _ _
   (llm_Pmid_full_local l s (length l) (natle_reflT (length l)))).
  ring.
Defined.

Theorem H_lam_pmid_H_lam_separates :
  sigT (fun l : list Q =>
        sigT (fun k : nat =>
              sigT (fun s : nat =>
                    sigT (fun lam : Q =>
                          NeqT (H_lam_pmid l s k lam) (H_lam l s lam))))).
Proof.
  apply (existT _ [2; 0; 1]). apply (existT _ 1%nat). apply (existT _ 0%nat).
  apply (existT _ (1#2)%Q).
  vm_compute. exact id_refl.
Defined.

Theorem H_lam_pmid_wit_201 :
  QeqT (H_lam_pmid [2; 0; 1] 0%nat 1%nat (1#2)%Q) (3#2)%Q.
Proof. vm_compute. exact id_refl. Defined.

Theorem H_lam_pmid_wit_201_ends :
  And (QeqT (H_adj (P0 [2; 0; 1])) 2%Q)
      (QeqT (H_adj (Pmid [2; 0; 1] 0%nat 1%nat)) 1%Q).
Proof.
  split.
  - vm_compute. exact id_refl.
  - vm_compute. exact id_refl.
Defined.

(* ========== Section P: the deviation detector ========== *)

Definition phase_dev (l : list Q) (k : nat) : bool :=
  negb (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))).

Theorem phase_dev_witness :
  sigT (fun l : list Q => sigT (fun k : nat => Id (phase_dev l k) true)).
Proof.
  apply (existT _ [0; 1; 2]). apply (existT _ 1%nat).
  vm_compute. exact id_refl.
Defined.

Theorem phase_dev_true_iff : forall (l : list Q) (k : nat),
  IffT (Id (phase_dev l k) true)
       (Id (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) false).
Proof.
  intros l k. split.
  - intro H.
    pose proof (id_eq _ _ H) as Hp.
    unfold phase_dev in Hp.
    destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
    + simpl in Hp. discriminate Hp.
    + exact id_refl.
  - intro H.
    pose proof (id_eq _ _ H) as Hp.
    unfold phase_dev.
    rewrite Hp. apply eq_imp_id. reflexivity.
Defined.

Theorem phase_dev_rec_ne : forall (l : list Q) (k : nat),
  Id (phase_dev l k) true ->
  Id (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) false.
Proof.
  intros l k H.
  exact (fst (phase_dev_true_iff l k) H).
Defined.

Theorem phase_dev_le : forall (l : list Q) (k : nat),
  Id (phase_dev l k) true -> QleT' (H_adj (P0 l)) (H_adj (rotc k l)).
Proof.
  intros l k _. apply rotc_P0_min.
Defined.

Lemma phcyc_qle_false_ltT : forall x y : Q,
  Id (Qle_bool y x) false -> QltT x y.
Proof.
  intros x y H.
  apply Qlt_to_QltT.
  destruct x as [nx dx]. destruct y as [ny dy].
  pose proof (id_eq _ _ H) as Hp.
  unfold Qle_bool in Hp. simpl in Hp.
  apply (proj1 (Z.leb_gt (ny * Z.pos dx) (nx * Z.pos dy))) in Hp.
  exact Hp.
Defined.

Theorem phase_dev_strict_of_num : forall (l : list Q) (k : nat),
  Id (Qle_bool (H_adj (rotc k l)) (H_adj (P0 l))) false ->
  And (Id (phase_dev l k) true) (QltT (H_adj (P0 l)) (H_adj (rotc k l))).
Proof.
  intros l k Hfalse.
  pose proof (id_eq _ _ Hfalse) as Hf.
  split.
  - unfold phase_dev.
    destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
    + exfalso.
      assert (Hba : (H_adj (rotc k l) <= H_adj (P0 l))%Q).
      { apply QleT'_to_Qle. apply xq_Qeq_le.
        exact (Qeq_sym _ _
                 (Qeq_bool_eq (H_adj (P0 l)) (H_adj (rotc k l)) E)). }
      pose proof (id_eq _ _
         (xq_Qle_bool_true _ _ Hba)) as Hbt.
      rewrite Hbt in Hf. discriminate Hf.
    + apply eq_imp_id. reflexivity.
  - apply phcyc_qle_false_ltT. exact Hfalse.
Defined.

Theorem phase_dev_stable : forall (l : list Q) (k : nat),
  Id (phase_dev l k) false -> QeqT (H_adj (rotc k l)) (H_adj (P0 l)).
Proof.
  intros l k H.
  pose proof (id_eq _ _ H) as Hp.
  unfold phase_dev in Hp.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (rotc k l))) eqn:E.
  - apply qeq_imp_qeqT. apply Qeq_sym. apply Qeq_bool_eq. exact E.
  - simpl in Hp. discriminate Hp.
Defined.

Theorem phase_dev_0_eq : forall l : list Q,
  Id (phase_dev l 0) (negb (Qeq_bool (H_adj (P0 l)) (H_adj l))).
Proof.
  intro l. apply eq_imp_id. unfold phase_dev.
  rewrite (id_eq _ _ (rotc_0 l)).
  reflexivity.
Defined.

Theorem phase_dev_0_of_sorted : forall l : list Q,
  Id (P0 l) l -> Id (phase_dev l 0) false.
Proof.
  intros l HP.
  apply eq_imp_id. unfold phase_dev.
  rewrite (id_eq _ _ (rotc_0 l)).
  rewrite (id_eq _ _ HP).
  rewrite (id_eq _ _
   (Qeqb_true_of (H_adj l) (H_adj l) (Qeq_refl (H_adj l)))).
  reflexivity.
Defined.

Theorem phase_dev_0_sorted_example : Id (phase_dev [0; 1; 2] 0) false.
Proof. vm_compute. exact id_refl. Defined.

Theorem phase_dev_0_unsorted_counterex : Id (phase_dev [0; 2; 1] 0) true.
Proof. vm_compute. exact id_refl. Defined.

(* ========== Section Q: disposal of the identity-rotation legacy ========== *)
(* Registered note: the legacy statement [forall P, P l <-> P (rot n l)]   *)
(* quantifies over a Prop-valued predicate and therefore cannot carry a    *)
(* Set statement face; its full content is carried by                      *)
(* [rotc_supersedes_rot_id], since both sides collapse to [P l].           *)
(* The legacy permutation-class minimality statement over an arbitrary    *)
(* permutation [p] likewise has no Set carrier in this piece; the          *)
(* rotation-consumers are covered by [rotc_P0_min] below.                  *)

Theorem rotc_supersedes_rot_id : forall (n : nat) (l : list Q),
  Id (rot n l) l.
Proof.
  intros n l. apply eq_imp_id. unfold rot. revert n.
  induction l as [| a rest IH]; intros n.
  - destruct n as [| n']; reflexivity.
  - destruct n as [| n'].
    + reflexivity.
    + change (firstn (S n') (a :: rest) ++ skipn (S n') (a :: rest) = a :: rest)
        with (a :: (firstn n' rest ++ skipn n' rest) = a :: rest).
      rewrite IH. reflexivity.
Defined.

Theorem rot_cyclic_cluster_superseded : forall (n : nat) (l : list Q),
  And (Id (length (rot n l)) (length l))
      (And (Id (length (rotc n l)) (length l))
           (And (forall x : Q, InT x l -> InT x (rot n l))
                (forall x : Q, InT x l -> InT x (rotc n l)))).
Proof.
  intros n l. split.
  - apply eq_imp_id.
    rewrite (id_eq _ _ (rotc_supersedes_rot_id n l)).
    reflexivity.
  - split.
    + exact (rotc_length n l).
    + split.
      * intros x Hx.
        rewrite (id_eq _ _ (rotc_supersedes_rot_id n l)).
        exact Hx.
      * intros x Hx. exact (rotc_in l n x Hx).
Defined.

Theorem rot_H_adj_face_covered : forall (n : nat) (l : list Q),
  And (QeqT (H_adj (rot n l)) (H_adj l))
      (QeqT (H_adj (rotc 0%nat l)) (H_adj l)).
Proof.
  intros n l. split.
  - rewrite (id_eq _ _ (rotc_supersedes_rot_id n l)).
    apply qeq_imp_qeqT. apply Qeq_refl.
  - exact (rotc_0_H_adj l).
Defined.

Theorem Hsup_oldface_const : forall (l : list Q) (n : nat),
  Id (Hsup l n) (H_adj l).
Proof.
  intros l n. induction n as [| n IH].
  - apply eq_imp_id. cbn [Hsup].
    rewrite (id_eq _ _ (Pinf_true_id l 0%nat)). reflexivity.
  - apply eq_imp_id. rewrite (Hsup_S_eq l n).
    rewrite (id_eq _ _ IH).
    rewrite (id_eq _ _ (Pinf_true_id l (S n))).
    destruct (Qle_bool (H_adj l) (H_adj l)); reflexivity.
Defined.

Theorem deprecated_consumers_map_D5_Pinf_perm : forall (l : list Q) (s : nat),
  And (forall x : Q, InT x l -> InT x (Pinf l s))
      (forall x : Q, InT x l -> InT x (Pinf_c l s)).
Proof.
  intros l s. split.
  - intros x Hx. exact (inT_rot_intro l (Datatypes.S s) x Hx).
  - intros x Hx. exact (rotc_in l (S s) x Hx).
Defined.

Theorem deprecated_consumers_map_llm_Pmid_zero : forall (l : list Q) (s : nat),
  And (Id (Pmid l s 0%nat) l) (QeqT (H_adj (Pmid l s 0%nat)) (H_adj l)).
Proof.
  intros l s.
  assert (H0 : Id (Pmid l s 0%nat) l).
  { pose proof (id_eq _ _ (llm_Pmid_zero_local l s)) as E.
    rewrite E. apply Pinf_true_id. }
  split.
  - exact H0.
  - rewrite (id_eq _ _ H0). apply qeq_imp_qeqT. apply Qeq_refl.
Defined.

Theorem deprecated_consumers_map_P0_absorbs_Pmid :
  forall (l : list Q) (s : nat) (k : nat),
  SortedQ l -> Id (P0 (Pmid l s k)) (P0 l).
Proof.
  intros l s k HS.
  rewrite (id_eq _ _ (Pmid_sorted_collapse l s k HS)).
  exact id_refl.
Defined.

Theorem deprecated_consumers_map_Hsup_mono : forall (l : list Q) (n : nat),
  And (QleT' (Hsup l n) (Hsup l (S n)))
      (QleT' (Hsup_cyc l n) (Hsup_cyc l (S n))).
Proof.
  intros l n. split.
  - apply Qle_to_QleT'.
    rewrite (id_eq _ _ (Hsup_oldface_const l n)).
    rewrite (id_eq _ _ (Hsup_oldface_const l (S n))).
    apply Qle_refl.
  - apply Hsup_cyc_mono.
Defined.

Lemma Qle_one_succZ : forall z : Z,
  (0 <= z)%Z -> (1 <= (Z.succ z) # 1%positive)%Q.
Proof.
  intros z Hz. rewrite <- (Z.add_1_r z). unfold Qle. simpl.
  rewrite Z.mul_1_r. lia.
Defined.

Lemma Qle_le_succZ : forall z : Z,
  ((z # 1%positive) <= (Z.succ z) # 1%positive)%Q.
Proof.
  intros z. rewrite <- (Z.add_1_r z). unfold Qle. simpl.
  rewrite Z.mul_1_r. lia.
Defined.

(* Registered, not supplied: the legacy boundedness face
   [Hsup l n <= (Z.of_nat (length l) # 1)%Q * B * 2] (whose Prop-side
   twin [DTPT.DTPT.H_adj_bound] is landed and available) needs a twin
   whose membership premise is carried by [InT] and whose Z-level length
   arithmetic is discharged on the [Z] face.  The first half of its
   content ([Hsup l n == H_adj l]) is carried by [Hsup_oldface_const]
   above; the second half ([Hsup_cyc l n <= 3 * spread]) is carried by
   [Hsup_cyc_ub]; the length-bounded twin itself is left to the supply
   layer. *)

(* Theorem deprecated_consumers_map_Hsup_bounded : registered above. *)

Theorem deprecated_consumers_map_Pinf_eq_l : forall (l : list Q) (s : nat),
  And (Id (Pinf l s) l)
      (And (Id (Pinf_c l s) (rotc (S s) l))
           (forall x : Q, InT x l -> InT x (Pinf_c l s))).
Proof.
  intros l s. split.
  - apply Pinf_true_id.
  - split.
    + apply eq_imp_id. reflexivity.
    + intros x Hx. exact (rotc_in l (S s) x Hx).
Defined.

Theorem deprecated_consumers_map_H_adj_cross_phase_lb :
  forall (l : list Q) (s : nat) (k : nat),
  And (QleT' (H_adj (P0 l)) (H_adj (Pinf l s)))
      (And (QleT' (H_adj (P0 l)) (H_adj (rotc k l)))
           (QleT' (H_adj (P0 l)) (H_adj (Pinf_c l s)))).
Proof.
  intros l s k. split.
  - apply H_adj_cross_phase_lb.
  - split.
    + apply rotc_P0_min.
    + exact (rotc_P0_min l (S s)).
Defined.

Theorem deprecated_consumers_map_u12_phase_side_always_zero :
  forall (l : list Q) (s : nat),
  And (Id (phase_side l s) 0%nat)
      (Id ((if Qle_bool (H_adj (P0 l)) (H_adj (rotc s l)) then 0 else 1)%nat)
          0%nat).
Proof.
  intros l s. split.
  - unfold phase_side.
    destruct (id_sym
                (xq_Qle_bool_true _ _
                   (QleT'_to_Qle _ _ (H_adj_cross_phase_lb l s)))).
    apply eq_imp_id. reflexivity.
  - exact (phase_side_cyc_side_zero l s).
Defined.

Theorem H_lam_anti_mono_real : forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  QleT' lam1 lam2 -> QleT' (H_lam l s lam2) (H_lam l s lam1).
Proof.
  intros l s lam1 lam2 Hlam.
  assert (Hs : QleT' 0 ((lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l)))).
  { apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam1 lam2)). exact Hlam.
    - apply QleT'_to_Qle.
      apply (fst (Qle_0_sub' (H_adj (P0 l)) (H_adj (Pinf l s)))).
      rewrite (id_eq _ _ (Pinf_true_id l s)).
      apply H_adj_P0_min. }
  assert (Hsd : QeqT (H_lam l s lam1 - H_lam l s lam2)
                ((lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l)))).
  { apply qeq_imp_qeqT.
    apply (Qeq_trans _ ((lam1 - lam2) * (H_adj (P0 l) - H_adj (Pinf l s)))).
    - exact (qeqT_imp_qeq _ _ (H_lam_diff_sub l s lam1 lam2)).
    - change (lam1 - lam2) with (lam1 + - lam2)%Q.
      change (lam2 - lam1) with (lam2 + - lam1)%Q.
      change (H_adj (P0 l) - H_adj (Pinf l s))
        with (H_adj (P0 l) + - H_adj (Pinf l s))%Q.
      change (H_adj (Pinf l s) - H_adj (P0 l))
        with (H_adj (Pinf l s) + - H_adj (P0 l))%Q.
      ring. }
  apply (qleT_from_diff (H_lam l s lam2) (H_lam l s lam1)
           ((lam2 - lam1) * (H_adj (Pinf l s) - H_adj (P0 l)))).
  - exact Hsd.
  - exact Hs.
Defined.

Theorem lam_opt_cross_phase_real : forall (l : list Q) (s : nat),
  Id (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) 1%Q.
Proof.
  intros l s.
  apply (lam_opt_cross_phase l s).
Defined.

(* ========== Section R: the unified family ========== *)

Definition H_lam_gen (l l2 : list Q) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj l2.

Theorem H_lam_gen_diff :
  forall (l2 : list Q) (l : list Q) (s : nat) (lam1 lam2 : Q),
  QeqT (H_lam_gen l l2 lam1 - H_lam_gen l l2 lam2)
       ((lam1 - lam2) * (H_adj (P0 l) - H_adj l2)).
Proof.
  intros l2 l s lam1 lam2. unfold H_lam_gen.
  exact (lam_affine_diff_sub (H_adj (P0 l)) (H_adj l2) lam1 lam2).
Defined.

Theorem H_lam_gen_affine :
  forall (l2 : list Q) (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_gen l l2 lam)
       (H_adj l2 + lam * (H_adj (P0 l) - H_adj l2)).
Proof.
  intros l2 l s lam. apply qeq_imp_qeqT. unfold H_lam_gen.
  change (1 - lam) with (1 + - lam)%Q.
  change (H_adj (P0 l) - H_adj l2) with (H_adj (P0 l) + - H_adj l2)%Q.
  ring.
Defined.

Theorem H_lam_gen_H_lam : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_gen l l lam) (H_lam l s lam).
Proof.
  intros l s lam. apply qeq_imp_qeqT.
  unfold H_lam_gen, H_lam.
  rewrite (id_eq _ _ (Pinf_true_id l s)).
  apply Qeq_refl.
Defined.

Theorem H_lam_gen_H_lam_cyc : forall (l : list Q) (k : nat) (lam : Q),
  QeqT (H_lam_gen l (rotc k l) lam) (H_lam_cyc l k lam).
Proof.
  intros l k lam. apply qeq_imp_qeqT.
  unfold H_lam_gen, H_lam_cyc. apply Qeq_refl.
Defined.

Theorem H_lam_gen_H_lam_pmid :
  forall (l : list Q) (s : nat) (k : nat) (lam : Q),
  QeqT (H_lam_gen l (Pmid l s k) lam) (H_lam_pmid l s k lam).
Proof.
  intros l s k lam. apply qeq_imp_qeqT.
  unfold H_lam_gen, H_lam_pmid. apply Qeq_refl.
Defined.

Theorem H_lam_gen_opt : forall (l l2 : list Q) (lam : Q),
  And (QleT' 0 lam) (QleT' lam 1) ->
  QleT' (H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2)))
        (H_lam_gen l l2 lam).
Proof.
  intros l l2 lam H01.
  unfold H_lam_gen.
  apply lam_opt_min. exact H01.
Defined.

Theorem H_lam_gen_opt_endpoint : forall (l l2 : list Q),
  Or (QeqT (H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2))) (H_adj (P0 l)))
     (QeqT (H_lam_gen l l2 (lam_opt (H_adj (P0 l)) (H_adj l2))) (H_adj l2)).
Proof.
  intros l l2. unfold H_lam_gen.
  destruct (lam_opt_values (H_adj (P0 l)) (H_adj l2)) as [E | E].
  - left. rewrite (id_eq _ _ E). apply qeq_imp_qeqT.
    replace (1 - 1)%Q with 0%Q by reflexivity. ring.
  - right. rewrite (id_eq _ _ E). apply qeq_imp_qeqT.
    replace (1 - 0)%Q with 1%Q by reflexivity. ring.
Defined.

Theorem lam_opt_align_lambda_opt_eq : forall (h0 h1 : Q),
  Id (lam_opt h0 h1) (align_lambda_opt h0 h1).
Proof.
  intros h0 h1. apply eq_imp_id. reflexivity.
Defined.

Theorem H_lam_gen_end_rotc0 : forall (l : list Q) (lam : Q),
  QeqT (H_lam_gen l (rotc 0%nat l) lam) (H_lam_gen l l lam).
Proof.
  intros l lam. apply qeq_imp_qeqT.
  rewrite (id_eq _ _ (rotc_0 l)).
  apply Qeq_refl.
Defined.

Theorem H_lam_gen_end_pmid0 : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_gen l (Pmid l s 0%nat) lam) (H_lam_gen l l lam).
Proof.
  intros l s lam. apply qeq_imp_qeqT. unfold H_lam_gen.
  rewrite (qeqT_imp_qeq _ _ (H_adj_Pmid_k0 l s)).
  apply Qeq_refl.
Defined.

Theorem H_lam_gen_klen_const : forall (l : list Q) (s : nat) (lam : Q),
  QeqT (H_lam_gen l (Pmid l s (length l)) lam) (H_adj (P0 l)).
Proof.
  intros l s lam. apply qeq_imp_qeqT. unfold H_lam_gen.
  rewrite (qeqT_imp_qeq _ _ (H_adj_Pmid_klen l s)).
  ring.
Defined.

Theorem H_lam_gen_wit_201_id :
  QeqT (H_lam_gen [2; 0; 1] [2; 0; 1] (1#2)%Q) (5#2)%Q.
Proof. vm_compute. exact id_refl. Defined.

Theorem H_lam_gen_wit_201_pmid :
  QeqT (H_lam_gen [2; 0; 1] (Pmid [2; 0; 1] 0%nat 1%nat) (1#2)%Q) (3#2)%Q.
Proof. vm_compute. exact id_refl. Defined.

End DTPT_Rotation.
Import DTPT_Rotation.

(* ========== assumption audit: one line per statement ========== *)
Print Assumptions cyc_nat_cases.
Print Assumptions pb_NeT_drop.
Print Assumptions pb_InT_drop.
(* (pb_In_liftQ removed in rework.) *)
Print Assumptions qleT_arg_eq.
Print Assumptions qeqT_sym.
Print Assumptions qleT_trans.
Print Assumptions qleT_of_qeqT.
Print Assumptions cyc_le_triple.
Print Assumptions rs_le_double.
Print Assumptions firstn_incl.
Print Assumptions skipn_incl.
Print Assumptions firstn_SortedQ.
Print Assumptions skipn_SortedQ.
Print Assumptions rotc_two_runs.
Print Assumptions H_adj_app_seam.
Print Assumptions rotc_length.
Print Assumptions rotc_in.
Print Assumptions rotc_0.
Print Assumptions skipn_all_app.
Print Assumptions firstn_all_app.
Print Assumptions rotc_rot_app.
Print Assumptions rotc_inv.
Print Assumptions rotc_full.
Print Assumptions Pinf_c_length.
Print Assumptions Pinf_c_in.
Print Assumptions Pinf_true_id.
Print Assumptions H_rotc_span_lb.
Print Assumptions H_rotc_span_lb_wit.
Print Assumptions H_rotc_separates.
Print Assumptions rotc_Pinf_separates.
Print Assumptions skipn_neT.
Print Assumptions firstn_neT.
Print Assumptions rotc_skipn_all.
Print Assumptions rotc_firstn_all.
Print Assumptions rotc_ge_len_id.
Print Assumptions lastq_skipn_kept.
Print Assumptions hd_firstn_kept.
Print Assumptions sorted_hd_min.
Print Assumptions sorted_lastq_max.
Print Assumptions sorted_sub_le_spread.
Print Assumptions sorted_abs_le_spread.
Print Assumptions H_adj_rotc_exact_mid.
Print Assumptions H_adj_rotc_exact_0.
Print Assumptions H_adj_rotc_exact_ge.
Print Assumptions H_adj_rotc_exact_short.
Print Assumptions H_adj_rotc_sorted_exact.
Print Assumptions H_adj_rotc_ub3.
Print Assumptions qmax2_ub_l.
Print Assumptions qmax2_ub_r.
Print Assumptions Hsup_cyc_mono.
Print Assumptions Hsup_cyc_ub.
Print Assumptions Hsup_cyc_attained.
Print Assumptions rotc_H_wit_mid.
Print Assumptions rotc_H_wit_min.
Print Assumptions hs_skipn_app_le.
Print Assumptions hs_firstn_app_le.
Print Assumptions hs_skipn_app_r.
Print Assumptions hs_firstn_app_gen.
Print Assumptions rotc_add_local.
Print Assumptions rotc_freeze_local.
Print Assumptions rotc_periodic_naive_false.
Print Assumptions rotc_add_naive_false.
Print Assumptions qmax2_le.
Print Assumptions Hsup_cyc_mono_from.
Print Assumptions H_adj_eq_Hsup0.
Print Assumptions Hsup_cyc_step_frozen.
Print Assumptions Hsup_cyc_stable.
Print Assumptions rotc_spectrum_bound.
Print Assumptions H_adj_spectrum_bound.
Print Assumptions Hsup_cyc_attained_range.
Print Assumptions Hsup_cyc_stable_wit.
Print Assumptions Hsup_cyc_frozen_value_wit.
Print Assumptions rotc_periodic.
Print Assumptions rotc_class_folds.
Print Assumptions rs_lastq_cons_ne.
Print Assumptions rs_lastq_firstn_hd_skipn.
Print Assumptions rs_skipn_S_incl.
Print Assumptions rs_seam_order.
Print Assumptions rotc_class_sharp_ub.
Print Assumptions sorted_wit_002.
Print Assumptions rotc_class_sharp_attained.
Print Assumptions rotc_P0_min.
Print Assumptions rotc_0_H_adj.
Print Assumptions phase_side_cyc_side_degenerate.
Print Assumptions phase_side_cyc_side_zero.
Print Assumptions lam_affine_diff_sub.
Print Assumptions H_lam_diff_sub.
Print Assumptions H_lam_affine.
Print Assumptions H_lam_anti_mono.
Print Assumptions H_lam_mono_diff.
Print Assumptions H_lam_const_when_eq.
Print Assumptions H_lam_midpoint.
Print Assumptions lam_opt_values.
Print Assumptions lam_opt_range.
Print Assumptions lam_opt_min.
Print Assumptions H_lam_lam_opt_min.
Print Assumptions H_lam_lam_opt_endpoint.
Print Assumptions lam_opt_cross_phase.
Print Assumptions align_lambda_id.
Print Assumptions align_lambda_H_lam.
Print Assumptions lam_opt_min_align.
Print Assumptions align_lambda_range.
Print Assumptions H_lam_extrap_below_counterex.
Print Assumptions H_lam_extrap_above_counterex.
Print Assumptions H_lam_cyc_lam1.
Print Assumptions H_lam_cyc_lam0.
Print Assumptions H_lam_cyc_k0_oldface.
Print Assumptions H_lam_cyc_diff.
Print Assumptions H_lam_cyc_mono_inc.
Print Assumptions H_lam_cyc_mono_dec.
Print Assumptions H_lam_cyc_oldface_separates.
Print Assumptions H_lam_cyc_H_lam_separates.
Print Assumptions lam_opt_cyc_values.
Print Assumptions lam_opt_cyc_range.
Print Assumptions H_lam_cyc_lam_opt_cyc_min.
Print Assumptions H_lam_cyc_lam_opt_cyc_endpoint.
Print Assumptions H_adj_app.
Print Assumptions H_adj_Pmid_seam.
Print Assumptions H_adj_Pmid_decomp.
Print Assumptions Pmid_sorted_collapse.
Print Assumptions H_adj_Pmid_sorted_exact.
Print Assumptions H_adj_Pmid_sorted_ub2.
Print Assumptions H_adj_Pmid_ub_gen.
Print Assumptions H_adj_Pmid_k0.
Print Assumptions H_adj_Pmid_klen.
Print Assumptions H_adj_Pmid_endpoints_sorted.
Print Assumptions phase_classify_ne_PMid.
Print Assumptions Pmid_sorted_collapse_wit_012.
Print Assumptions H_adj_Pmid_decomp_wit_012.
Print Assumptions H_lam_pmid_lam1.
Print Assumptions H_lam_pmid_lam0.
Print Assumptions H_lam_pmid_diff.
Print Assumptions H_lam_pmid_affine.
Print Assumptions H_lam_pmid_sorted_consistency.
Print Assumptions H_lam_pmid_sorted_lam1.
Print Assumptions H_lam_pmid_sorted_lam0.
Print Assumptions H_lam_pmid_k0_oldface.
Print Assumptions H_lam_pmid_klen_const.
Print Assumptions H_lam_pmid_H_lam_separates.
Print Assumptions H_lam_pmid_wit_201.
Print Assumptions H_lam_pmid_wit_201_ends.
Print Assumptions phase_dev_witness.
Print Assumptions phase_dev_true_iff.
Print Assumptions phase_dev_rec_ne.
Print Assumptions phase_dev_le.
Print Assumptions phcyc_qle_false_ltT.
Print Assumptions phase_dev_strict_of_num.
Print Assumptions phase_dev_stable.
Print Assumptions phase_dev_0_eq.
Print Assumptions phase_dev_0_of_sorted.
Print Assumptions phase_dev_0_sorted_example.
Print Assumptions phase_dev_0_unsorted_counterex.
Print Assumptions rotc_supersedes_rot_id.
Print Assumptions rot_cyclic_cluster_superseded.
Print Assumptions rot_H_adj_face_covered.
Print Assumptions Hsup_oldface_const.
Print Assumptions deprecated_consumers_map_D5_Pinf_perm.
Print Assumptions deprecated_consumers_map_llm_Pmid_zero.
Print Assumptions deprecated_consumers_map_P0_absorbs_Pmid.
Print Assumptions deprecated_consumers_map_Hsup_mono.
(* Print Assumptions deprecated_consumers_map_Hsup_bounded : registered, not supplied. *)
Print Assumptions deprecated_consumers_map_Pinf_eq_l.
Print Assumptions deprecated_consumers_map_H_adj_cross_phase_lb.
Print Assumptions deprecated_consumers_map_u12_phase_side_always_zero.
Print Assumptions H_lam_anti_mono_real.
Print Assumptions lam_opt_cross_phase_real.
Print Assumptions H_lam_gen_diff.
Print Assumptions H_lam_gen_affine.
Print Assumptions H_lam_gen_H_lam.
Print Assumptions H_lam_gen_H_lam_cyc.
Print Assumptions H_lam_gen_H_lam_pmid.
Print Assumptions H_lam_gen_opt.
Print Assumptions H_lam_gen_opt_endpoint.
Print Assumptions lam_opt_align_lambda_opt_eq.
Print Assumptions H_lam_gen_end_rotc0.
Print Assumptions H_lam_gen_end_pmid0.
Print Assumptions H_lam_gen_klen_const.
Print Assumptions H_lam_gen_wit_201_id.
Print Assumptions H_lam_gen_wit_201_pmid.
