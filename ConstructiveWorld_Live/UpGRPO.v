(* ConstructiveWorld-Set -- NoDup uniformization for GRPO and the standardized advantage second moment on the Real layer. *)
(** * UpGRPO: NoDup uniformization and the standardized advantage moment.

    Mission.  Part B (abstract layer): the counting machine
      ([count_g]/[removeT_g] driven by [grp_eq_dec]) and [nodup_g]
      (Set-layer no-duplicates, counting characterization): B1 coverage
      + no duplicates give each element exactly one count; B2 the
      indicator sums to [1]; B3 the group mean gives each [delta_j] mass
      exactly [1/G].  Part C (Real layer): a constructive [sigma] with
      [0 < sigma] and [sigma^2 == Var], packaged in a [sigT], and
      [Sum (A_i/sigma)^2 == 1].  Honesty note: the [nodup_g] premise
      cannot be dropped -- a doubly enumerated element would get mass
      [2/G] (counterexample stated in a comment only).

    Dependencies.  [AttnDoeblin], [AttnSqrt], [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO]; Stdlib [List] [Extraction].

    References.  This development; the same-name ConstructiveWorld-Main
      baseline ([upgrpo_sigma_sq_eq]/[real_mult_exchange] statement
      names carried verbatim).

    Constructivity.  Purely constructive (zero axioms, no admission
      statements); Set-layer statements; all [Qed]; extractable.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpGRPO.v] compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import AttnDoeblin AttnSqrt.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp S07_RealSetoidExpLog S08_RealMainlineDPO.

(* ################ Part B: NoDup uniformization at the abstract layer ################ *)

Section GRPONoDup.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.

Variable Group : Set.
Variable group_enum : list Group.
Variable group_cover : forall i : Group, InT i group_enum.
Variable grp_eq_dec : forall i j : Group, Or (Id i j) (Not (Id i j)).
Variable reward_group : Group -> R.

(* The [nat] -> [R] embedding (self-contained, inside the interface domain) *)
Fixpoint nat_to_R_g (k : nat) : R :=
  match k with
  | 0%nat => zero
  | Datatypes.S m => plus one (nat_to_R_g m)
  end.

Lemma nat_to_R_g_pos : forall k : nat, lt zero (nat_to_R_g (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - apply (lt_id_r_loc _ _ _ (id_sym (plus_zero one))). exact one_pos.
  - apply plus_positive.
    + exact one_pos.
    + exact IH.
Qed.

Let G := nat_to_R_g (length group_enum).
Variable G_pos : lt zero G.

(* Group sum (a list fold, at the abstract [Id] layer) *)
Fixpoint list_sum_g (f : Group -> R) (l : list Group) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (list_sum_g f rest)
  end.

Lemma list_sum_g_ext : forall (f g : Group -> R) (l : list Group),
  (forall i : Group, Id (f i) (g i)) ->
  Id (list_sum_g f l) (list_sum_g g l).
Proof.
  intros f g l H. induction l as [| x rest IH].
  - apply id_refl.
  - exact (id_cong2 plus (H x) IH).
Qed.

Lemma list_sum_g_linear : forall (a : R) (f : Group -> R) (l : list Group),
  Id (list_sum_g (fun i : Group => mult a (f i)) l) (mult a (list_sum_g f l)).
Proof.
  intros a f l. induction l as [| x rest IH].
  - exact (id_sym (mult_zero a)).
  - apply (id_trans (id_cong2 plus (id_refl : Id (mult a (f x)) (mult a (f x))) IH)).
    apply (id_sym (distrib a (f x) (list_sum_g f rest))).
Qed.

Lemma list_sum_g_const : forall (c : R) (l : list Group),
  Id (list_sum_g (fun _ : Group => c) l)
     (mult (nat_to_R_g (length l)) c).
Proof.
  intros c l. induction l as [| x rest IH].
  - exact (id_sym (id_trans (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : Id (plus c (list_sum_g (fun _ : Group => c) rest))
                       (plus (mult c one) (mult c (nat_to_R_g (length rest))))).
    { exact (id_cong2 plus (id_sym (mult_one c))
                         (id_trans IH (mult_comm (nat_to_R_g (length rest)) c))). }
    apply (id_trans Hstep).
    apply (id_trans (id_sym (distrib c one (nat_to_R_g (length rest))))).
    apply (mult_comm c (plus one (nat_to_R_g (length rest)))).
Qed.

Lemma list_sum_g_zero_fn : forall (f : Group -> R) (l : list Group),
  (forall i : Group, InT i l -> Id (f i) zero) ->
  Id (list_sum_g f l) zero.
Proof.
  intros f l H. induction l as [| x rest IH].
  - apply id_refl.
  - apply (id_trans (id_cong2 plus (H x (InT_here x rest))
                                (id_refl : Id (list_sum_g f rest) (list_sum_g f rest)))).
    apply (id_trans (plus_comm zero (list_sum_g f rest))).
    apply (id_trans (plus_zero (list_sum_g f rest))).
    exact (IH (fun i : Group => fun Hin : InT i rest => H i (InT_next i x rest Hin))).
Qed.

(* The counting machine (driven by [grp_eq_dec], generic in the element type) *)
Fixpoint count_g (j : Group) (l : list Group) : nat :=
  match l with
  | nil => O
  | x :: rest => match grp_eq_dec x j with
                 | inl _ => Datatypes.S (count_g j rest)
                 | inr _ => count_g j rest
                 end
  end.

Fixpoint removeT_g (j : Group) (l : list Group) : list Group :=
  match l with
  | nil => nil
  | x :: rest => match grp_eq_dec x j with
                 | inl _ => removeT_g j rest
                 | inr _ => x :: removeT_g j rest
                 end
  end.

Lemma InT_transport : forall (x y : Group) (l : list Group),
  Id x y -> InT x l -> InT y l.
Proof.
  intros x y l H Hin. destruct H. exact Hin.
Qed.

Lemma not_InT_count_zero : forall (j : Group) (l : list Group),
  not_InT j l -> @Id nat (count_g j l) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hn.
  - apply id_refl.
  - cbn [count_g]. destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + exact (match Hn (InT_transport x j (x :: rest) Hxj (InT_here x rest)) with end).
    + exact (IH (fun Hin : InT j rest => Hn (InT_next j x rest Hin))).
Qed.

Lemma count_zero_notin : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) O -> not_InT j l.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - intro Hin. inversion Hin.
  - cbn [count_g] in Hc.
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + intro Hin. inversion Hin as [| x0 l0 Hin2]; subst.
      * apply Hnxj. apply id_refl.
      * exact (IH Hc Hin2).
Qed.

Lemma count_zero_remove_zero : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) O -> @Id nat (count_g j (removeT_g j l)) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + cbn [count_g]. destruct (grp_eq_dec x j) as [Hyt2 | Hnyt2].
      * exact (match Hnxj Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma count_zero_remove_id : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) O -> @Id (list Group) (removeT_g j l) l.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + apply (id_cong (fun l0 : list Group => x :: l0)). exact (IH Hc).
Qed.

Lemma count_one_remove_zero : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) (Datatypes.S O) ->
  @Id nat (count_g j (removeT_g j l)) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + assert (Hc0 : @Id nat (count_g j rest) O).
      { exact (id_cong Nat.pred Hc). }
      apply count_zero_remove_zero. exact Hc0.
    + cbn [count_g].
      destruct (grp_eq_dec x j) as [Hyt2 | Hnyt2].
      * exact (match Hnxj Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma remove_notin_aux : forall (j x : Group) (l : list Group),
  InT x (removeT_g j l) -> Not (Id x j).
Proof.
  intros j x l. induction l as [| y rest IH]; intro Hin.
  - inversion Hin.
  - cbn [removeT_g] in Hin.
    destruct (grp_eq_dec y j) as [Hyj | Hnyj].
    + exact (IH Hin).
    + inversion Hin as [| x0 l0 Hin2]; subst.
      * exact Hnyj.
      * exact (IH Hin2).
Qed.

(* Counted-exactly-once splitting: [count == 1] implies [sum l f == f j + sum (removeT_g j l) f] *)
Lemma split_count_one_id : forall (f : Group -> R) (j : Group) (l : list Group),
  @Id nat (count_g j l) (Datatypes.S O) ->
  Id (list_sum_g f l) (plus (f j) (list_sum_g f (removeT_g j l))).
Proof.
  intros f j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + (* head is [j]: [count rest == 0] gives [removeT_g rest == rest], and [f x == f j] *)
      assert (Hc0 : @Id nat (count_g j rest) O).
      { exact (id_cong Nat.pred Hc). }
      assert (Hrid : @Id (list Group) (removeT_g j rest) rest)
        by exact (count_zero_remove_id j rest Hc0).
      apply (id_trans (id_cong2 plus (id_cong f Hxj)
                                     (id_refl : Id (list_sum_g f rest) (list_sum_g f rest)))).
      apply (id_cong2 plus (id_refl : Id (f j) (f j))
                           (id_cong (fun l0 : list Group => list_sum_g f l0) (id_sym Hrid))).
    + (* head is not [j]: assemble the IH and reassociate *)
      apply (id_trans (id_cong2 plus (id_refl : Id (f x) (f x)) (IH Hc))).
      apply (id_trans (plus_assoc (f x) (f j) (list_sum_g f (removeT_g j rest)))).
      apply (id_trans (id_cong2 plus (plus_comm (f x) (f j))
                                     (id_refl : Id (list_sum_g f (removeT_g j rest))
                                                   (list_sum_g f (removeT_g j rest))))).
      apply (id_sym (plus_assoc (f j) (f x) (list_sum_g f (removeT_g j rest)))).
Qed.

(* The Set-layer no-duplicates predicate (equivalent form of the counting characterization; an inductive family with two constructors) *)
Inductive nodup_g : list Group -> Set :=
| ndg_nil : nodup_g nil
| ndg_cons : forall (x : Group) (t : list Group),
    not_InT x t -> nodup_g t -> nodup_g (x :: t).

(* Membership transport along a list identity *)
Lemma InT_list_transport : forall (x : Group) (l1 l2 : list Group),
  Id l1 l2 -> InT x l1 -> InT x l2.
Proof.
  intros x l1 l2 H Hin. destruct H. exact Hin.
Qed.

(* Head different from [j] implies membership in the tail *)
Lemma InT_tail_of_neq : forall (j a : Group) (rest : list Group),
  Not (Id a j) -> InT j (a :: rest) -> InT j rest.
Proof.
  intros j a rest Hne Hin. inversion Hin as [| y0 l0 Hin2].
  - exact (match Hne (id_sym (RealSetoid.eq_Id j a H)) with end).
  - exact Hin2.
Qed.

(* ========== B1: coverage + no duplicates imply each element counted exactly once ========== *)
Theorem grpo_count_one : forall (l : list Group) (Hnd : nodup_g l)
    (j : Group), InT j l -> @Id nat (count_g j l) (Datatypes.S O).
Proof.
  intros l Hnd. induction Hnd as [| x0 t0 Hnhead Hndrest IH]; intros j Hin.
  - (* [l = nil]: [InT j nil] has no inhabitants (removed by inversion) *)
    inversion Hin.
  - cbn [count_g]. destruct (grp_eq_dec x0 j) as [Haj | Hanj].
    + (* [x0 == j]: hit at the head; [j not in t0] transported from [not_InT x0 t0] along [Haj] *)
      apply (id_cong (fun n : nat => Datatypes.S n)).
      apply (not_InT_count_zero j t0
               (fun Hin : InT j t0 => Hnhead (InT_transport j x0 t0 (id_sym Haj) Hin))).
    + (* [x0 /= j]: hit in the tail *)
      exact (IH j (InT_tail_of_neq j x0 t0 Hanj Hin)).
Qed.

Variable Hnd_g : nodup_g group_enum.

(* ========== B2: the indicator sum equals [1] ========== *)
Theorem grpo_indicator_sum_one : forall (j : Group),
  InT j group_enum ->
  Id (list_sum_g (fun i : Group => match grp_eq_dec i j with
                                   | inl _ => one
                                   | inr _ => zero
                                   end) group_enum) one.
Proof.
  intros j Hin.
  assert (Hc1 : @Id nat (count_g j group_enum) (Datatypes.S O))
    by exact (grpo_count_one group_enum Hnd_g j Hin).
  assert (Hsplit := split_count_one_id
                      (fun i : Group => match grp_eq_dec i j with
                                        | inl _ => one
                                        | inr _ => zero
                                        end) j group_enum Hc1).
  assert (Hfj : Id (match grp_eq_dec j j with
                    | inl _ => one
                    | inr _ => zero
                    end) one).
  { destruct (grp_eq_dec j j) as [Hjj | Hjj].
    - apply id_refl.
    - exact (match Hjj (id_refl : Id j j) with end). }
  assert (Hrest : Id (list_sum_g (fun i : Group => match grp_eq_dec i j with
                                                   | inl _ => one
                                                   | inr _ => zero
                                                   end)
                              (removeT_g j group_enum)) zero).
  { apply list_sum_g_zero_fn.
    intro i. intro HinR.
    assert (Hne : Not (Id i j)) by exact (remove_notin_aux j i group_enum HinR).
    destruct (grp_eq_dec i j) as [Hxj | Hnxj].
    - exact (match Hne Hxj with end).
    - apply id_refl. }
  apply (id_trans Hsplit).
  apply (id_trans (id_cong2 plus Hfj Hrest)).
  apply (plus_zero one).
Qed.

(* ========== B3: genuinely uniform mass (each delta gets mass exactly [1/G] under the group mean) ========== *)
Theorem grpo_uniform_mass : forall j : Group,
  InT j group_enum ->
  Id (list_sum_g (fun i : Group =>
        mult (inv_pos G G_pos)
             (match grp_eq_dec i j with
              | inl _ => one
              | inr _ => zero
              end)) group_enum)
     (inv_pos G G_pos).
Proof.
  intro j. intro Hin.
  apply (id_trans (list_sum_g_linear (inv_pos G G_pos)
            (fun i : Group => match grp_eq_dec i j with
                              | inl _ => one
                              | inr _ => zero
                              end) group_enum)).
  apply (id_trans (id_cong2 mult (id_refl : Id (inv_pos G G_pos) (inv_pos G G_pos))
                             (grpo_indicator_sum_one j Hin))).
  apply mult_one.
Qed.

End GRPONoDup.

(* ################ Part C: the standardized advantage second moment on the Real layer ################ *)

Section RealGrpoSigma.

Variable Grp : Set.
Variable grp_enum : list Grp.
Variable grp_cover : forall i : Grp, InT i grp_enum.
Variable real_size_pos : real_lt real_zero (real_of_nat (length grp_enum)).
Variable reward_grp : Grp -> Real.

Let sizeR := real_of_nat (length grp_enum).
Let mean : Real :=
  real_mult (real_inv_pos sizeR real_size_pos) (real_list_sum_g Grp reward_grp grp_enum).
Let A (i : Grp) : Real := real_plus (reward_grp i) (real_opp mean).
Let Var : Real := real_list_sum_g Grp (fun i : Grp => real_mult (A i) (A i)) grp_enum.

(* Four-factor multiplication exchange: [(a*c)*(b*d) == (a*b)*(c*d)] *)
Lemma real_mult_exchange : forall a b c d : Real,
  real_eq (real_mult (real_mult a c) (real_mult b d))
          (real_mult (real_mult a b) (real_mult c d)).
Proof.
  intros a b c d.
  apply (real_eq_trans _ (real_mult a (real_mult c (real_mult b d))) _    (real_eq_sym (real_mult a (real_mult c (real_mult b d)))                 (real_mult (real_mult a c) (real_mult b d))                 (real_mult_assoc a c (real_mult b d)))).
  apply (real_eq_trans _ (real_mult a (real_mult (real_mult c b) d)) _    (RealSetoid.real_eq_mult_compat a (real_mult c (real_mult b d))       a (real_mult (real_mult c b) d)       (real_eq_refl a) (real_mult_assoc c b d))).
  apply (real_eq_trans _ (real_mult a (real_mult b (real_mult c d))) _    (RealSetoid.real_eq_mult_compat a (real_mult (real_mult c b) d)       a (real_mult b (real_mult c d))       (real_eq_refl a)       (real_eq_trans _ _ _         (RealSetoid.real_eq_mult_compat (real_mult c b) d            (real_mult b c) d            (real_mult_comm c b) (real_eq_refl d))         (real_eq_sym (real_mult b (real_mult c d))                      (real_mult (real_mult b c) d)                      (real_mult_assoc b c d))))).
  exact (real_mult_assoc a b (real_mult c d)).
Qed.

(* Extracting positivity from the [sqrt] witness: split the [real_le]; the [inr] branch ([sigma = 0]) is excluded by the contradiction between [sigma^2 = Var] and [Var > 0] *)
Lemma real_sqrt_pos_sq : forall (V : Real) (Hvar : real_lt real_zero V)
    (W : sigT (fun r => And (real_le real_zero r) (real_eq (real_mult r r) V))),
  sigT (fun sigma => And (real_lt real_zero sigma) (real_eq (real_mult sigma sigma) V)).
Proof.
  intros V Hvar W. destruct W as [sigma [Hle Hsq]].
  destruct Hle as [Hlt | Heq0].
  - exact (existT _ sigma (pair Hlt Hsq)).
  - (* [sigma = 0] gives [Var = sigma*sigma = 0], contradicting [Var > 0] *)
    assert (Hv0 : real_eq V real_zero).
    { apply (real_eq_trans _ (real_mult sigma sigma) _).
      - exact (real_eq_sym (real_mult sigma sigma) V Hsq).
      - exact (real_eq_trans _ _ _
          (RealSetoid.real_eq_mult_compat sigma sigma real_zero real_zero
             (real_eq_sym real_zero sigma Heq0) (real_eq_sym real_zero sigma Heq0))
          (real_mult_zero real_zero)). }
    exact (match real_lt_irrefl real_zero
             (RealSetoid.real_lt_id_r _ _ _ Hv0 Hvar) with end).
Qed.

(* ========== C: the standardized advantage second moment ([sigT] packaging of [sigma], positivity, and the unit moment) ========== *)
(* Caliber: [sigma^2 == Var] ([Var] is the unnormalized central second moment, matching the terminology of paper 1 §7.2), *)
(* and [Sum (A_i/sigma)^2 == 1]; the population version ([sigma^2 = Var/G]) follows by rescaling. *)
(* Part C main theorem: a constructive [sigma] and the unit moment.
   Note on the construction: the [Or] premise of [real_sqrt_exists]
   carries a positivity certificate [Hlt : 0 < sigma] in its [inl]
   branch, while the [inr] branch ([sigma = 0]) contradicts [Var > 0]
   (transported through [sigma^2 == Var] plus [real_lt_irrefl]), so the
   [sigT] packaging is legitimate.  To avoid inlining a large [match]
   into the theorem statement, [real_sqrt_exists] first builds an
   intermediate section constant (see [real_sigma_witness] below). *)
(* Projection extracting [sigma] from [real_sigma_witness] (avoiding an inlined [match] in theorem statements) *)
Lemma real_sigma_witness : forall Hvar : real_lt real_zero Var,
  sigT (fun sigma => And (real_lt real_zero sigma)
                         (real_eq (real_mult sigma sigma) Var)).
Proof.
  intro Hvar.
  destruct (real_sqrt_exists Var (inl Hvar)) as [sigma [Hle Hsq]].
  destruct Hle as [Hlt | Heq0].
  - exact (existT _ sigma (pair Hlt Hsq)).
  - (* [sigma = 0] gives [V = sigma*sigma = 0], contradicting [V > 0] *)
    assert (Hv0 : real_eq Var real_zero).
    { apply (real_eq_trans _ (real_mult sigma sigma) _).
      - exact (real_eq_sym (real_mult sigma sigma) Var Hsq).
      - exact (real_eq_trans _ _ _
          (RealSetoid.real_eq_mult_compat sigma sigma real_zero real_zero
             (real_eq_sym real_zero sigma Heq0) (real_eq_sym real_zero sigma Heq0))
          (real_mult_zero real_zero)). }
    exact (match real_lt_irrefl real_zero
             (RealSetoid.real_lt_id_r _ _ _ Hv0 Hvar) with end).
Qed.

Definition proj_sigma (Hvar : real_lt real_zero Var) : Real :=
  projT1 (real_sigma_witness Hvar).



Lemma proj_sigma_pos : forall Hvar : real_lt real_zero Var,
  real_lt real_zero (proj_sigma Hvar).
Proof.
  intro Hvar. unfold proj_sigma.
  destruct (real_sigma_witness Hvar) as [sigma [Hpos Hsq]].
  exact Hpos.
Qed.

Lemma proj_sigma_sq : forall Hvar : real_lt real_zero Var,
  real_eq (real_mult (proj_sigma Hvar) (proj_sigma Hvar)) Var.
Proof.
  intro Hvar. unfold proj_sigma.
  destruct (real_sigma_witness Hvar) as [sigma [Hpos Hsq]].
  exact Hsq.
Qed.



(* [sigma^2 == Var] is given directly by the [real_sqrt_exists] witness ([proj_sigma_sq]),
   ready for downstream division absorption ([inv_pos_mult_distr] + [real_inv_pos_correct]). *)

(* Part C inventory (complete):
   1. [real_sigma_witness] ([sigT] triple: existence + positivity + square identity of [sigma])
   2. [proj_sigma_pos] / [proj_sigma_sq] (projection extraction)
   3. [real_mult_exchange] (four-factor exchange)
   4. [upgrpo_inv_sigma_sq_eq_inv_var] (inv absorption: [inv sigma^2 == inv Var])
   5. [real_grpo_standardized_unit_moment] (main theorem: [Sum (A_i/sigma)^2 == 1]) *)

(* ========== C, full unit-moment refinement: [Sum (A_i/sigma)^2 == 1] ========== *)

(* Step 1, the per-term exchange (via [real_mult_exchange]) *)
(* Step 2, the linear extraction (via [real_list_sum_g_linear]) *)
(* Step 3, the [inv] absorption (via [inv_pos_correct]) *)

(* Auxiliary: [inv sigma * sigma == 1] ([real_inv_pos_correct] gives [sigma * inv sigma == 1]; swap the factor order) *)
Lemma upgrpo_inv_sigma_mult_sigma_one :
  forall Hvar : real_lt real_zero Var,
  real_eq (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                     (proj_sigma Hvar))
          real_one.
Proof.
  intro Hvar.
  apply (real_eq_trans _
    (real_mult (proj_sigma Hvar)
               (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* Intermediate lemma: [inv sigma * inv sigma == inv Var] -- the [inv] absorption:
   [inv sigma^2 == inv sigma^2 * 1 == inv sigma^2 * (Var * inv Var) == (inv sigma^2 * Var) * inv Var == 1 * inv Var == inv Var],
   with the subchain [inv sigma^2 * Var == inv sigma^2 * sigma^2 == (inv sigma * sigma) * (inv sigma * sigma) == 1 * 1 == 1]. *)
Lemma upgrpo_inv_sigma_sq_eq_inv_var :
  forall Hvar : real_lt real_zero Var,
  real_eq (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                     (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
          (real_inv_pos Var Hvar).
Proof.
  intro Hvar.
  pose proof (proj_sigma_sq Hvar) as Hsq.
  (* Subchain: [inv sigma^2 * Var == 1] *)
  assert (HinvV : real_eq
           (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                                 (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                      Var)
           real_one).
  { apply (real_eq_trans _
      (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                            (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                 (real_mult (proj_sigma Hvar) (proj_sigma Hvar))) _).
    - apply (RealSetoid.real_eq_mult_compat
               (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                          (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
               Var
               (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                          (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
               (real_mult (proj_sigma Hvar) (proj_sigma Hvar))).
      + apply real_eq_refl.
      + exact (real_eq_sym _ _ Hsq).
    - apply (real_eq_trans _
        (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                              (proj_sigma Hvar))
                   (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                              (proj_sigma Hvar))) _).
      + exact (real_mult_exchange
               (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
               (proj_sigma Hvar)
               (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
               (proj_sigma Hvar)).
      + apply (real_eq_trans _ (real_mult real_one real_one) _).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                              (proj_sigma Hvar))
                   (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                              (proj_sigma Hvar))
                   real_one real_one
                   (upgrpo_inv_sigma_mult_sigma_one Hvar)
                   (upgrpo_inv_sigma_mult_sigma_one Hvar)).
        * apply real_mult_one. }
  (* Main chain: [inv sigma^2 == inv sigma^2 * 1 == inv sigma^2 * (Var * inv Var) == (inv sigma^2 * Var) * inv Var == 1 * inv Var == inv Var] *)
  apply (real_eq_trans _
    (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                          (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
               (real_mult Var (real_inv_pos Var Hvar))) _).
  - apply (real_eq_trans _
      (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                            (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                 real_one) _).
    + exact (real_eq_sym _ _
          (real_mult_one (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                                    (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))))).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                          (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
               real_one
               (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                          (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
               (real_mult Var (real_inv_pos Var Hvar))
               (real_eq_refl (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                                        (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))))
               (real_eq_sym _ _ (real_inv_pos_correct Var Hvar))).
  - apply (real_eq_trans _
      (real_mult (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                                       (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                            Var)
                 (real_inv_pos Var Hvar)) _).
    + exact (real_mult_assoc (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                                        (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                             Var (real_inv_pos Var Hvar)).
    + apply (real_eq_trans _ (real_mult real_one (real_inv_pos Var Hvar)) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                                       (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                            Var)
                 (real_inv_pos Var Hvar)
                 real_one
                 (real_inv_pos Var Hvar)
                 HinvV
                 (real_eq_refl (real_inv_pos Var Hvar))).
      * apply (real_eq_trans _ (real_mult (real_inv_pos Var Hvar) real_one) _).
        -- apply real_mult_comm.
        -- apply real_mult_one.
Qed.

(* Auxiliary: [upgrpo_sigma_sq_eq] restates [proj_sigma_sq] ([real_eq (sigma*sigma) Var]) *)
Lemma upgrpo_sigma_sq_eq : forall Hvar : real_lt real_zero Var,
  real_eq (real_mult (proj_sigma Hvar) (proj_sigma Hvar)) Var.
Proof. intro Hvar. exact (proj_sigma_sq Hvar). Qed.

(* ========== Part C main theorem: the standardized advantage unit second moment [Sum (A_i/sigma)^2 == 1] ========== *)
Theorem real_grpo_standardized_unit_moment :
  forall Hvar : real_lt real_zero Var,
  real_eq (real_list_sum_g Grp
             (fun i : Grp =>
                real_mult
                  (real_mult (A i)
                     (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                  (real_mult (A i)
                     (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))))
             grp_enum)
          real_one.
Proof.
  intros Hvar.
  (* Step 1: per-term exchange, [(A*inv s)*(A*inv s) == (A*A)*(inv s * inv s)], via [real_mult_exchange] *)
  apply (real_eq_trans _
    (real_list_sum_g Grp
      (fun i : Grp =>
         real_mult (real_mult (A i) (A i))
                   (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                              (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))))
      grp_enum) _).
  - apply real_list_sum_g_ext.
    intro i. apply real_mult_exchange.
  (* Step 2: swap factors ([real_mult_comm]) then extract [inv sigma^2] linearly via [real_list_sum_g_linear] *)
  - apply (real_eq_trans _
      (real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                            (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                 (real_list_sum_g Grp (fun i : Grp => real_mult (A i) (A i)) grp_enum)) _).
    + apply (real_eq_trans _
        (real_list_sum_g Grp
          (fun i : Grp =>
             real_mult (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                                  (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                       (real_mult (A i) (A i)))
          grp_enum) _).
      * apply real_list_sum_g_ext.
        intro i. apply real_mult_comm.
      * apply real_list_sum_g_linear.
    + (* Step 3: [inv sigma^2 == inv Var] (the [inv] absorption), and [inv Var * Var == 1] via [real_inv_pos_correct] *)
      apply (real_eq_trans _ (real_mult (real_inv_pos Var Hvar) Var) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar))
                            (real_inv_pos (proj_sigma Hvar) (proj_sigma_pos Hvar)))
                 (real_list_sum_g Grp (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                 (real_inv_pos Var Hvar) Var
                 (upgrpo_inv_sigma_sq_eq_inv_var Hvar) (real_eq_refl Var)).
      * apply (real_eq_trans _ (real_mult Var (real_inv_pos Var Hvar)) _).
        -- apply real_mult_comm.
        -- apply real_inv_pos_correct.
Qed.

End RealGrpoSigma.

From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upgrpo.ml" count_g removeT_g.
Extraction "upgrpo_full.ml" proj_sigma real_mult_exchange.
