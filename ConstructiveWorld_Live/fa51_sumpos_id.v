(* ConstructiveWorld-Set -- finite-sum positivity on the Id carrier, over an enumerated state space. *)
(** * fa51_sumpos_id: positivity of finite sums and of the partition
    functions built on them.

    Mission.  Over a RealInterfaceEnhanced ordered ring, the finite
    sum fa51_sumd (a structural fold over a list of states) of a
    pointwise-nonnegative function is nonnegative, and the sum of a
    pointwise-positive function is positive whenever the list is
    provably nonempty (Not (Id enum nil)).  On this engine the file
    builds positivity of four partition faces: fa51_Z_align,
    fa51_Z_temp with its definitional specification
    fa51_Z_temp_spec_def, the Boltzmann weights
    fa51_boltzmann_dist_temp, and the eta-step partition fa51_Z_rel.

    Dependencies.  S01_BaseRing (the RealInterfaceEnhanced interface:
    order lt/le and equality Id valued in Set, with le_refl, le_id_l,
    le_plus_compat, plus_zero, id_sym, lt_le_iff, lt_le_trans,
    mult_positive, exp_neg_pos, inv_pos_pos) and Stdlib Lists.List.

    References.  UpReqSumD (sumd_sum_pos) carries the same engine on
    the req carrier; this file re-sits it on the Id carrier of
    S01_BaseRing, with every statement on the Set layer.

    Constructivity.  All proofs close by Qed; Axioms: none.  Proofs
    are explicit term assemblies (exact/apply chains, no rewriting
    tactics) over the Set-valued order face; a closing Print
    Assumptions sweep rechecks every statement.

    Build.  rocq c -native-compiler no -q -Q world "" fa51_sumpos_id.v
    (Rocq 9.1.0), same-world dependency .vo tree, cpu_guard wrapper. *)

Require Import S01_BaseRing.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa51SumPosID.

Context {RI : RealInterfaceEnhanced}.
Variable S : Set.
Variable enum : list S.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let opp      := @opp RI.
Let inv_pos  := @inv_pos RI.
Let le       := @le RI.
Let lt       := @lt RI.
Let exp_neg  := @exp_neg RI.

(* ========= Engine: the finite sum (structural fold over a list, Set layer) ========= *)

Fixpoint fa51_sumd (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (fa51_sumd f t)
  end.

(* ==== Engine 1: pointwise nonnegative implies sum nonnegative (list induction) ==== *)

Lemma fa51_sumd_nonneg :
  forall (f : S -> R) (l : list S),
    (forall s : S, le zero (f s)) -> le zero (fa51_sumd f l).
Proof.
  intros f l Hpt. induction l as [| x t IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus (f x) (fa51_sumd f t))
             (id_sym (plus_zero zero))
             (le_plus_compat zero (f x) zero (fa51_sumd f t) (Hpt x) IH)).
Qed.

(* ==== Engine 2: strict order lifts to weak order (lt_le_iff + inl) ==== *)

Lemma fa51_lt_le : forall a b : R, lt a b -> le a b.
Proof.
  intros a b H. exact (lt_le_iff a b (inl H)).
Qed.

(* ==== Engine 3: head-witnessed strict sum (Id-carrier form of UpReqSumD sumd_sum_pos) ==== *)

Lemma fa51_sumd_pos_cons :
  forall (f : S -> R) (x : S) (l : list S),
    (forall s : S, lt zero (f s)) -> lt zero (fa51_sumd f (x :: l)).
Proof.
  intros f x l H.
  exact (lt_le_trans zero (f x) (plus (f x) (fa51_sumd f l)) (H x)
           (le_id_l (f x) (plus (f x) zero) (plus (f x) (fa51_sumd f l))
              (id_sym (plus_zero (f x)))
              (le_plus_compat (f x) (f x) zero (fa51_sumd f l)
                 (le_refl (f x))
                 (fa51_sumd_nonneg f l (fun s => fa51_lt_le zero (f s) (H s)))))).
Qed.

(* ==== Engine 4: nonemptiness in Set-layer Not+Id form, passed as an explicit argument ==== *)

Lemma fa51_sumd_nonnil_pos :
  forall (f : S -> R) (l : list S),
    Not (Id l nil) -> (forall s : S, lt zero (f s)) -> lt zero (fa51_sumd f l).
Proof.
  intros f l Hne H. destruct l as [| x t].
  - destruct (Hne (@id_refl (list S) nil)).
  - exact (fa51_sumd_pos_cons f x t H).
Qed.

(* ==== Product positivity key (pointwise-positive product implies positive sum) ==== *)

Lemma fa51_sumd_mult_pos :
  forall (g h : S -> R),
    Not (Id enum nil) ->
    (forall s : S, lt zero (g s)) ->
    (forall s : S, lt zero (h s)) ->
    lt zero (fa51_sumd (fun s => mult (g s) (h s)) enum).
Proof.
  intros g h Hne Hg Hh.
  exact (fa51_sumd_nonnil_pos (fun s => mult (g s) (h s)) enum Hne
           (fun s => mult_positive (g s) (h s) (Hg s) (Hh s))).
Qed.

(* ==== Instantiation 1: positivity of the alignment partition function ==== *)
(* Target: Z_align = SUM_s pi_ref(s) * e^{-r(s)/beta}, and
   fa51_Z_align_pos : lt zero Z_align.
   Delivery: every summand is a product of two pointwise-positive factors,
   pi_ref and exp_neg (mult_positive), closed by Engine 4; nonemptiness of
   enum is an explicit premise carried by the caller. *)

Definition fa51_Z_align (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
                        (pi_ref : S -> R) : R :=
  fa51_sumd (fun s => mult (pi_ref s)
                           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
            enum.

Theorem fa51_Z_align_pos :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta) (pi_ref : S -> R),
    (forall s : S, lt zero (pi_ref s)) ->
    Not (Id enum nil) ->
    lt zero (fa51_Z_align reward beta beta_pos pi_ref).
Proof.
  intros reward beta beta_pos pi_ref Href Hne.
  unfold fa51_Z_align.
  apply (fa51_sumd_mult_pos pi_ref
           (fun s => exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
  - exact Hne.
  - exact Href.
  - intro s. exact (exp_neg_pos (opp (mult (inv_pos beta beta_pos) (reward s)))).
Qed.

(* ==== Instantiation 2: the temperature partition function family ==== *)
(* Target: Z_temp_spec : forall t Ht, Id (Z_temp t) (SUM_s e^{-e_s/t}).
   Delivery: fa51_Z_temp is by definition the finite sum, so the
   specification face holds by id_refl; the positivity face is closed by
   Engine 4 without side conditions. *)

Definition fa51_Z_temp (base_loss : S -> R) (t : R) (Ht : lt zero t) : R :=
  fa51_sumd (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s))) enum.

Theorem fa51_Z_temp_spec_def :
  forall (base_loss : S -> R) (t : R) (Ht : lt zero t),
    Id (fa51_Z_temp base_loss t Ht)
       (fa51_sumd (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s))) enum).
Proof.
  intros base_loss t Ht.
  exact (@id_refl _ (fa51_sumd (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s))) enum)).
Qed.

Theorem fa51_Z_temp_pos :
  forall (base_loss : S -> R) (t : R) (Ht : lt zero t),
    Not (Id enum nil) -> lt zero (fa51_Z_temp base_loss t Ht).
Proof.
  intros base_loss t Ht Hne. unfold fa51_Z_temp.
  apply fa51_sumd_nonnil_pos.
  - exact Hne.
  - intro s. exact (exp_neg_pos (mult (inv_pos t Ht) (base_loss s))).
Qed.

(* Pointwise positivity of the temperature Boltzmann distribution: the
   positivity of the partition feeds inv_pos (the boltzmann_dist_temp_pos
   face of the same chain). *)

Definition fa51_boltzmann_dist_temp (base_loss : S -> R) (t : R) (Ht : lt zero t)
                                    (Hne : Not (Id enum nil)) (s : S) : R :=
  mult (inv_pos (fa51_Z_temp base_loss t Ht) (fa51_Z_temp_pos base_loss t Ht Hne))
       (exp_neg (mult (inv_pos t Ht) (base_loss s))).

Theorem fa51_boltzmann_dist_temp_pos :
  forall (base_loss : S -> R) (t : R) (Ht : lt zero t) (Hne : Not (Id enum nil)) (s : S),
    lt zero (fa51_boltzmann_dist_temp base_loss t Ht Hne s).
Proof.
  intros base_loss t Ht Hne s. unfold fa51_boltzmann_dist_temp.
  apply mult_positive.
  - exact (inv_pos_pos (fa51_Z_temp base_loss t Ht)
                       (fa51_Z_temp_pos base_loss t Ht Hne)).
  - exact (exp_neg_pos (mult (inv_pos t Ht) (base_loss s))).
Qed.

(* ==== Instantiation 3: the temperature eta-update partition (Z_rel) ==== *)
(* Target: Z_rel = SUM pi_t * e^{-(eta/beta) * adv}; fa51_Z_rel_pos closes
   the same chain through the product positivity key. *)

Definition fa51_Z_rel (pi_t adv : S -> R) (beta eta_ : R)
                      (beta_pos : lt zero beta) : R :=
  fa51_sumd (fun s => mult (pi_t s)
                           (exp_neg (opp (mult (mult eta_ (inv_pos beta beta_pos))
                                               (adv s)))))
            enum.

Theorem fa51_Z_rel_pos :
  forall (pi_t adv : S -> R) (beta eta_ : R) (beta_pos : lt zero beta),
    (forall s : S, lt zero (pi_t s)) ->
    Not (Id enum nil) ->
    lt zero (fa51_Z_rel pi_t adv beta eta_ beta_pos).
Proof.
  intros pi_t adv beta eta_ beta_pos Hpi Hne.
  unfold fa51_Z_rel.
  apply (fa51_sumd_mult_pos pi_t
           (fun s => exp_neg (opp (mult (mult eta_ (inv_pos beta beta_pos)) (adv s))))).
  - exact Hne.
  - exact Hpi.
  - intro s. exact (exp_neg_pos (opp (mult (mult eta_ (inv_pos beta beta_pos)) (adv s)))).
Qed.

End Fa51SumPosID.

(* ===== Assumption-closure declaration: Print Assumptions over every statement ===== *)

Print Assumptions fa51_sumd_nonneg.
Print Assumptions fa51_lt_le.
Print Assumptions fa51_sumd_pos_cons.
Print Assumptions fa51_sumd_nonnil_pos.
Print Assumptions fa51_sumd_mult_pos.
Print Assumptions fa51_Z_align_pos.
Print Assumptions fa51_Z_temp_spec_def.
Print Assumptions fa51_Z_temp_pos.
Print Assumptions fa51_boltzmann_dist_temp_pos.
Print Assumptions fa51_Z_rel_pos.
