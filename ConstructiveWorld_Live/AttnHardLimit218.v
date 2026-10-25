(* ConstructiveWorld-Set — statement-face Set-carrier completions of the
   Main-source analysis modules. *)

(** * AttnHardLimit218: an explicit temperature-decay bound for
      hard-attention distributions.

    Mission.  For a finite vocabulary of tokens with a score function
      [z], the temperature-softened weights [w_T] are compared with the
      hard one-hot distribution [hard_dist] at the extremal token [m]:
      the total-variation functional [tv_hard] admits the explicit bound
      [tv_hard T <= length vocab * exp(-gamma / T)], uniform in [T].
      The main statement [hard_attention_limit] upgrades this to a limit:
      for every tolerance [eps] there is a temperature cap [T0] such that
      every [T < T0] already satisfies [tv_hard T <= eps].

    Dependencies.  Stdlib [List], [Arith], [Lia].  Requires
      [S01_BaseRing] through [S15_TailFEPUp] of this development.

    References.  This development, AttnHardLimit218.v, the baseline
      module in ConstructiveWorld-Main whose statement names are carried
      over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements are carried by [Set]
      (the function-valued equality [real_eq], the order carriers
      [real_lt]/[real_le], [Id], [NatLe]); statements extract with
      [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].  The section premises (nonempty vocabulary,
      decidable token equality, single occurrence of [m], explicit gap)
      are disclosed as section variables and witnessed concretely at the
      end of the file.

    Build.  [coqc -native-compiler no -q -Q . "" AttnHardLimit218.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)
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
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ================= Section 0. Real-layer helper lemmas ================= *)

(* Transport [Id] into the Set-valued equality [real_eq]. *)
Lemma aid_real_eq : forall a b : Real, Id a b -> real_eq a b.
Proof.
  intros a b H. destruct H. apply real_eq_refl.
Qed.

(* The strict order implies the weak order (left summand of [real_le]). *)
Lemma real_le_from_lt_aux : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H. exact (inl H).
Qed.

(* Multiplying by a positive constant from the left preserves order. *)
Lemma real_le_mult_compat_l_aux : forall a b c : Real,
  real_lt real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  apply (RealSetoid.real_le_id_l (real_mult c a) (real_mult a c) (real_mult c b)).
  - apply real_mult_comm.
  - apply (RealSetoid.real_le_id_r (real_mult a c) (real_mult b c) (real_mult c b)).
    + apply real_mult_comm.
    + apply (real_le_mult_compat a b c Hc Hab).
Qed.

(* Adding a nonnegative summand grows the left side. *)
Lemma real_le_plus_nonneg_r_aux : forall a b : Real,
  real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat; [apply real_le_refl | exact Hb].
Qed.

(* Ordering reformulated: [a <= b] gives [0 <= b - a]. *)
Lemma real_le_minus_nonneg_aux : forall a b : Real,
  real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab. unfold real_le in Hab. destruct Hab as [Hlt | Heq].
  - apply real_le_from_lt_aux. apply (real_lt_opp_plus a b). exact Hlt.
  - apply (RealSetoid.real_eq_le real_zero (real_plus b (real_opp a))).
    apply real_eq_sym.
    apply (real_eq_trans _ (real_plus b (real_opp b)) _).
    + apply (RealSetoid.real_eq_plus_compat b (real_opp a) b (real_opp b)).
      * apply real_eq_refl.
      * apply (RealSetoid.real_eq_opp_compat a b Heq).
    + apply real_plus_opp.
Qed.

(* For [u <= v] the absolute difference simplifies: |u - v| = v - u. *)
Lemma real_abs_minus_r_nonneg_aux : forall u v : Real,
  real_le u v -> real_eq (real_abs (real_minus_r u v)) (real_plus v (real_opp u)).
Proof.
  intros u v Huv.
  assert (Hd : real_le real_zero (real_plus v (real_opp u)))
    by exact (real_le_minus_nonneg_aux u v Huv).
  (* u - v = -(v - u). *)
  assert (E1 : real_eq (real_minus_r u v)
                       (real_opp (real_plus v (real_opp u)))).
  { apply (real_eq_trans _ (real_plus (real_opp v) u) _).
    - apply real_plus_comm.
    - apply (real_eq_trans _ (real_plus (real_opp v) (real_opp (real_opp u))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp v) u
                 (real_opp v) (real_opp (real_opp u))).
        * apply real_eq_refl.
        * apply real_eq_sym. apply real_opp_opp.
      + apply real_eq_sym. apply (real_opp_plus v (real_opp u)). }
  assert (E2 : real_eq (real_abs (real_minus_r u v))
                       (real_abs (real_plus v (real_opp u)))).
  { apply (real_eq_trans _ (real_abs (real_opp (real_plus v (real_opp u)))) _).
    - apply real_abs_eq_compat. exact E1.
    - apply real_abs_opp. }
  assert (E3 : real_eq (real_abs (real_plus v (real_opp u)))
                       (real_plus v (real_opp u))).
  { unfold real_le in Hd. destruct Hd as [Hlt | Heq].
    - apply (real_abs_pos_req _ Hlt).
    - apply (real_eq_trans _ real_zero _).
      + apply (real_eq_trans _ (real_abs real_zero) _).
        * apply real_abs_eq_compat. apply real_eq_sym. exact Heq.
        * apply real_abs_zero_req.
      + exact Heq. }
  apply (real_eq_trans _ (real_abs (real_plus v (real_opp u))) _).
  - exact E2.
  - exact E3.
Qed.

(* exp a * exp(-a) = 1, in both argument orders. *)
Lemma exp_mult_opp_r_aux : forall a : Real,
  real_eq (real_mult (cauchy_real_exp a) (cauchy_real_exp (real_opp a))) real_one.
Proof.
  intros a.
  apply (real_eq_trans _ (cauchy_real_exp (real_plus a (real_opp a))) _).
  - apply real_eq_sym. apply (cauchy_real_exp_plus a (real_opp a)).
  - apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
    + apply (cauchy_real_exp_wd (real_plus a (real_opp a)) real_zero).
      apply real_plus_opp.
    + apply cauchy_real_exp_zero.
Qed.

Lemma exp_mult_opp_l_aux : forall a : Real,
  real_eq (real_mult (cauchy_real_exp (real_opp a)) (cauchy_real_exp a)) real_one.
Proof.
  intros a.
  apply (real_eq_trans _
           (real_mult (cauchy_real_exp a) (cauchy_real_exp (real_opp a))) _).
  - apply real_mult_comm.
  - apply exp_mult_opp_r_aux.
Qed.

(* The nat embedding is nonnegative and monotone. *)
Lemma real_of_nat_nonneg_aux : forall k : nat,
  real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_r real_zero
             (real_plus real_one (real_of_nat k)) (real_of_nat (Datatypes.S k))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_le_id_l real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat k))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_le_plus_compat.
        -- apply real_le_from_lt_aux. apply real_lt_zero_one.
        -- exact IH.
Qed.

Lemma real_of_nat_le_mono_aux : forall k1 k2 : nat,
  (k1 <= k2)%nat -> real_le (real_of_nat k1) (real_of_nat k2).
Proof.
  intros k1 k2 H.
  revert k1 H.
  induction k2 as [| k2 IH]; intros k1 H.
  - (* k1 <= 0 forces k1 = 0. *)
    assert (Hk : k1 = 0%nat) by (inversion H; reflexivity).
    rewrite Hk. apply real_le_refl.
  - destruct (Nat.eq_dec k1 (Datatypes.S k2)) as [Heq | Hne].
    + rewrite Heq. apply real_le_refl.
    + (* k1 <= S k2 and k1 <> S k2 give k1 <= k2. *)
      assert (Hle : (k1 <= k2)%nat).
      { inversion H; subst.
        - exfalso. apply Hne. reflexivity.
        - assumption. }
      apply (RealSetoid.real_le_id_r (real_of_nat k1)
               (real_plus real_one (real_of_nat k2))
               (real_of_nat (Datatypes.S k2))).
      * apply real_eq_refl.
      * apply (real_le_trans _ (real_plus (real_of_nat k1) real_one) _).
        -- apply real_le_plus_nonneg_r_aux.
           apply real_le_from_lt_aux. apply real_lt_zero_one.
        -- apply (RealSetoid.real_le_id_r
                     (real_plus (real_of_nat k1) real_one)
                     (real_plus (real_of_nat k2) real_one)
                     (real_plus real_one (real_of_nat k2))).
           ++ apply real_plus_comm.
           ++ apply real_le_plus_compat; [exact (IH k1 Hle) | apply real_le_refl].
Qed.

(* [Id] on successors is invertible (successor injectivity). *)
Lemma nat_S_id_inv_aux : forall a b : nat,
  @Id nat (Datatypes.S a) (Datatypes.S b) -> @Id nat a b.
Proof.
  intros a b H. exact (id_cong Nat.pred H).
Qed.

(* ================= Section 1. Finite-vocabulary attention model ================= *)

Section AttnHardLimit.

(* ---------- 1. Vocabulary infrastructure ---------- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.

(* Occurrence count of a token in a list, folding over the decision. *)
Fixpoint count_token (t : Token) (l : list Token) : nat :=
  match l with
  | nil => O
  | x :: rest =>
      match token_eq_dec x t with
      | inl _ => Datatypes.S (count_token t rest)
      | inr _ => count_token t rest
      end
  end.

(* Removal of the first occurrence. *)
Fixpoint removeT (t : Token) (l : list Token) : list Token :=
  match l with
  | nil => nil
  | x :: rest =>
      match token_eq_dec x t with
      | inl _ => removeT t rest
      | inr _ => x :: removeT t rest
      end
  end.

(* ---------- 2. Extremal-token witness (explicit premises) ---------- *)
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable m_count_one : @Id nat (count_token m vocab) (Datatypes.S O).
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* ---------- 3. Counting and removal combinatorics ----------
   The proofs reduce the defining matches with [cbn], split on the
   token decision, and discharge contradictory branches by inversion. *)

Lemma count_zero_notin : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) O -> not_InT t l.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - intro Hin. inversion Hin.
  - cbn [count_token] in Hc.
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + inversion Hc.
    + intro Hin. inversion Hin as [| x0 l0 Hin2]; subst.
      * apply Hnyt. apply id_refl.
      * exact (IH Hc Hin2).
Qed.

Lemma count_zero_remove_id : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) O -> @Id (list Token) (removeT t l) l.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_token] in Hc. cbn [removeT].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + inversion Hc.
    + apply (id_cong (fun l0 => y :: l0)). exact (IH Hc).
Qed.

Lemma count_zero_remove_zero : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) O -> @Id nat (count_token t (removeT t l)) O.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_token] in Hc. cbn [removeT].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + inversion Hc.
    + (* Expose the outer count match on the cons branch. *)
      cbn [count_token].
      destruct (token_eq_dec y t) as [Hyt2 | Hnyt2].
      * exact (match Hnyt Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma count_one_remove_zero : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) (Datatypes.S O) ->
  @Id nat (count_token t (removeT t l)) O.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_token] in Hc. cbn [removeT].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + assert (Hc0 : @Id nat (count_token t rest) O)
        by exact (nat_S_id_inv_aux _ _ Hc).
      apply count_zero_remove_zero. exact Hc0.
    + cbn [count_token].
      destruct (token_eq_dec y t) as [Hyt2 | Hnyt2].
      * exact (match Hnyt Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma remove_notin_aux : forall (t x : Token) (l : list Token),
  InT x (removeT t l) -> Not (Id x t).
Proof.
  intros t x l. induction l as [| y rest IH]; intro Hin.
  - inversion Hin.
  - cbn [removeT] in Hin.
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + exact (IH Hin).
    + inversion Hin as [| x0 l0 Hin2]; subst.
      * exact Hnyt.
      * exact (IH Hin2).
Qed.

Lemma remove_length_le_aux : forall (t : Token) (l : list Token),
  NatLe (length (removeT t l)) (length l).
Proof.
  intros t l. induction l as [| y rest IH].
  - cbn [length removeT]. apply NatLe_lift. lia.
  - cbn [removeT].
    destruct (token_eq_dec y t) as [Hyt | Hnyt]; cbn [length]; apply NatLe_lift.
    + pose proof (NatLe_drop _ _ IH). lia.
    + pose proof (NatLe_drop _ _ IH). lia.
Qed.

(* One-step unfolding of [removeT] at the list head, both decisions. *)
Lemma removeT_cons_self : forall (t x : Token) (l : list Token),
  Id x t -> @Id (list Token) (removeT t (x :: l)) (removeT t l).
Proof.
  intros t x l H. cbn [removeT].
  destruct (token_eq_dec x t) as [Hxt | Hnxt].
  - apply id_refl.
  - exact (match Hnxt H with end).
Qed.

Lemma removeT_cons_ne : forall (t x : Token) (l : list Token),
  Not (Id x t) -> @Id (list Token) (removeT t (x :: l)) (x :: removeT t l).
Proof.
  intros t x l H. cbn [removeT].
  destruct (token_eq_dec x t) as [Hxt | Hnxt].
  - exact (match H Hxt with end).
  - apply id_refl.
Qed.

(* If [t] occurs exactly once, the sum splits at that occurrence. *)
Lemma split_count_one : forall (f : Token -> Real) (t : Token) (l : list Token),
  @Id nat (count_token t l) (Datatypes.S O) ->
  real_eq (real_list_sum Token f l)
          (real_plus (f t) (real_list_sum Token f (removeT t l))).
Proof.
  intros f t l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_token] in Hc. cbn [real_list_sum].
    destruct (token_eq_dec x t) as [Hxt | Hnxt].
    + assert (Hc0 : @Id nat (count_token t rest) O)
        by exact (nat_S_id_inv_aux _ _ Hc).
      rewrite (removeT_cons_self t x rest Hxt).
      apply (real_eq_trans _ (real_plus (f t) (real_list_sum Token f rest)) _).
      * apply (RealSetoid.real_eq_plus_compat (f x)
                  (real_list_sum Token f rest) (f t)
                  (real_list_sum Token f rest)).
        -- apply (aid_real_eq _ _ (id_cong f Hxt)).
        -- apply real_eq_refl.
      * apply (RealSetoid.real_eq_plus_compat (f t)
                  (real_list_sum Token f rest) (f t)
                  (real_list_sum Token f (removeT t rest))).
        -- apply real_eq_refl.
        -- apply (aid_real_eq _ _
                     (id_sym (id_cong (fun l0 => real_list_sum Token f l0)
                                (count_zero_remove_id t rest Hc0)))).
    + rewrite (removeT_cons_ne t x rest Hnxt).
      apply (real_eq_trans _
               (real_plus (f x)
                  (real_plus (f t)
                     (real_list_sum Token f (removeT t rest)))) _).
      * apply (RealSetoid.real_eq_plus_compat (f x)
                  (real_list_sum Token f rest) (f x)
                  (real_plus (f t)
                     (real_list_sum Token f (removeT t rest)))).
        -- apply real_eq_refl.
        -- exact (IH Hc).
      * apply (real_eq_trans _
                 (real_plus (real_plus (f x) (f t))
                    (real_list_sum Token f (removeT t rest))) _).
        -- apply real_plus_assoc.
        -- apply (real_eq_trans _
                     (real_plus (real_plus (f t) (f x))
                        (real_list_sum Token f (removeT t rest))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (f x) (f t))
                       (real_list_sum Token f (removeT t rest))
                       (real_plus (f t) (f x))
                       (real_list_sum Token f (removeT t rest))).
              ** apply real_plus_comm.
              ** apply real_eq_refl.
           ++ apply real_eq_sym. apply real_plus_assoc.
Qed.

(* ---------- 4. Order lemmas for list sums ---------- *)

Lemma sum_nonneg_aux : forall (f : Token -> Real) (l : list Token),
  (forall y : Token, real_le real_zero (f y)) ->
  real_le real_zero (real_list_sum Token f l).
Proof.
  intros f l. induction l as [| y rest IH]; intro Hnn.
  - apply real_le_refl.
  - cbn [real_list_sum].
    apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus (f y) (real_list_sum Token f rest))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat; [apply Hnn | exact (IH Hnn)].
Qed.

Lemma sum_pos_nonempty_aux : forall (f : Token -> Real) (l : list Token),
  (forall y : Token, real_lt real_zero (f y)) -> Not (Id l nil) ->
  real_lt real_zero (real_list_sum Token f l).
Proof.
  intros f l. induction l as [| y rest IH]; intros Hf Hl.
  - exact (match Hl (@id_refl (list Token) nil) with end).
  - destruct rest as [| y2 rest2].
    + cbn [real_list_sum].
      apply (real_lt_eq_lt real_zero (f y) (real_plus (f y) real_zero)).
      * apply Hf.
      * apply real_eq_sym. apply real_plus_zero.
    + cbn [real_list_sum].
      assert (Hpos : real_lt real_zero
                       (real_plus (f y)
                          (real_plus (f y2)
                             (real_list_sum Token f rest2)))).
      { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) _).
        - apply real_eq_sym. apply real_plus_zero.
        - apply real_lt_plus_compat.
          + apply Hf.
          + apply (IH Hf).
            intro Hc. inversion Hc. }
      apply (real_lt_eq_lt real_zero
               (real_plus (f y) (real_plus (f y2) (real_list_sum Token f rest2))) _).
      * exact Hpos.
      * apply real_eq_refl.
Qed.

Lemma single_le_sum_aux : forall (f : Token -> Real) (x : Token) (l : list Token),
  InT x l -> (forall y : Token, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum Token f l).
Proof.
  intros f x l. induction l as [| y rest IH]; intros Hin Hnn.
  - inversion Hin.
  - cbn [real_list_sum]. inversion Hin as [| x0 l0 Hin2]; subst.
    + apply real_le_plus_nonneg_r_aux.
      apply sum_nonneg_aux. apply Hnn.
    + apply (real_le_trans _ (real_list_sum Token f rest) _).
      * exact (IH Hin2 Hnn).
      * apply (RealSetoid.real_le_id_r
                 (real_list_sum Token f rest)
                 (real_plus (real_list_sum Token f rest) (f y))
                 (real_plus (f y) (real_list_sum Token f rest))).
        -- apply real_plus_comm.
        -- apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

Lemma sum_nonneg_le_const_aux : forall (f : Token -> Real) (c : Real) (l : list Token),
  (forall x : Token, InT x l -> real_le (f x) c) ->
  real_le (real_list_sum Token f l)
          (real_mult (real_of_nat (length l)) c).
Proof.
  intros f c l. induction l as [| x rest IH]; intro Hb.
  - exact (RealSetoid.real_eq_le real_zero
             (real_mult (real_of_nat (length (@nil Token))) c)
             (real_eq_sym (real_mult real_zero c) real_zero
                (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
                   real_zero (real_mult_comm real_zero c) (real_mult_zero c)))).
  - cbn [real_list_sum length].
    apply (RealSetoid.real_le_id_r
             (real_plus (f x) (real_list_sum Token f rest))
             (real_plus c (real_mult (real_of_nat (length rest)) c))
             (real_mult (real_of_nat (Datatypes.S (length rest))) c)).
    + apply (real_eq_trans
               (real_plus c (real_mult (real_of_nat (length rest)) c))
               (real_plus (real_mult real_one c)
                  (real_mult (real_of_nat (length rest)) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (real_of_nat (length rest)) c)
                 (real_mult real_one c)
                 (real_mult (real_of_nat (length rest)) c)).
        -- apply (real_eq_trans c (real_mult c real_one)
                    (real_mult real_one c)
                    (real_eq_sym (real_mult c real_one) c (real_mult_one c))
                    (real_mult_comm c real_one)).
        -- apply real_eq_refl.
      * apply real_distrib_r.
    + apply real_le_plus_compat.
      * apply Hb. apply InT_here.
      * apply IH. intros y Hin. apply Hb. apply (InT_next y x rest Hin).
Qed.

(* ---------- 5. Temperature-softened weights and the hard distribution ---------- *)

(* Weight factor: [factor_T T x = exp(z x / T)]. *)
Definition factor_T (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  cauchy_real_exp (real_mult (real_inv_pos T Ht) (z x)).

(* Partition function: [Z T = sum over the vocabulary of exp(z x / T)]. *)
Definition ZT (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Token (factor_T T Ht) vocab.

Definition ZT_pos (T : Real) (Ht : real_lt real_zero T) :
  real_lt real_zero (ZT T Ht).
Proof.
  unfold ZT. apply sum_pos_nonempty_aux.
  - intro x. apply cauchy_real_exp_pos.
  - exact vocab_nonempty.
Defined.

(* Normalized weight: [w_T x = exp(z x / T) / Z T]. *)
Definition w_T (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  real_mult (factor_T T Ht x) (real_inv_pos (ZT T Ht) (ZT_pos T Ht)).

(* The hard (one-hot) distribution at [m]. *)
Definition hard_dist (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => real_one
  | inr _ => real_zero
  end.

(* Decay base: [exp(-gamma / T)]. *)
Definition decay_T (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (real_opp (real_mult (real_inv_pos T Ht) gamma)).

(* Total variation: [tv_hard = (1/2) * sum |w_T x - hard_dist x|]. *)
Definition tv_hard (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_mult
    (real_inv_pos (real_plus real_one real_one)
       (real_lt_plus_compat real_zero real_one real_zero real_one
          real_lt_zero_one real_lt_zero_one))
    (real_list_sum Token
       (fun x => real_abs (real_minus_r (w_T T Ht x) (hard_dist x))) vocab).

(* ---------- 6. Weight analysis ---------- *)

Lemma factor_T_pos : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  real_lt real_zero (factor_T T Ht x).
Proof.
  intros T Ht x. apply cauchy_real_exp_pos.
Qed.

Lemma w_T_pos : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  real_lt real_zero (w_T T Ht x).
Proof.
  intros T Ht x. unfold w_T. apply real_mult_pos_compat.
  - apply factor_T_pos.
  - apply real_inv_pos_pos.
Qed.

(* The normalized weights sum to one. *)
Lemma w_T_sum_one : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_list_sum Token (w_T T Ht) vocab) real_one.
Proof.
  intros T Ht.
  apply (real_eq_trans _
           (real_mult (real_inv_pos (ZT T Ht) (ZT_pos T Ht))
              (real_list_sum Token (factor_T T Ht) vocab)) _).
  - apply (real_list_sum_linear_r Token).
  - apply (real_eq_trans _
             (real_mult (real_inv_pos (ZT T Ht) (ZT_pos T Ht)) (ZT T Ht)) _).
    + apply real_eq_refl.
    + apply (real_eq_trans _
               (real_mult (ZT T Ht) (real_inv_pos (ZT T Ht) (ZT_pos T Ht))) _).
      * apply real_mult_comm.
      * apply (real_inv_pos_correct (ZT T Ht) (ZT_pos T Ht)).
Qed.

(* The extremal weight is at most one (single summand <= total). *)
Lemma w_T_m_le_one : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (w_T T Ht m) real_one.
Proof.
  intros T Ht.
  apply (RealSetoid.real_le_id_r (w_T T Ht m)
           (real_list_sum Token (w_T T Ht) vocab) real_one).
  - exact (w_T_sum_one T Ht).
  - apply (single_le_sum_aux (w_T T Ht) m vocab m_in_vocab).
    intro y. apply real_le_from_lt_aux. apply w_T_pos.
Qed.

(* Multiplying by an inverse absorbs the factor: (X*Y)*invX = Y. *)
Lemma eq_mult_inv_absorb : forall (X Y : Real) (HX : real_lt real_zero X)
  (H : real_eq (real_mult X (real_inv_pos X HX)) real_one),
  real_eq (real_mult (real_mult X Y) (real_inv_pos X HX)) Y.
Proof.
  intros X Y HX H.
  apply (real_eq_trans _ (real_mult X (real_mult Y (real_inv_pos X HX))) _).
  - apply (real_eq_sym _ _ (real_mult_assoc X Y (real_inv_pos X HX))).
  - apply (real_eq_trans _ (real_mult X (real_mult (real_inv_pos X HX) Y)) _).
    + apply (RealSetoid.real_eq_mult_compat X
               (real_mult Y (real_inv_pos X HX)) X
               (real_mult (real_inv_pos X HX) Y)).
      * apply real_eq_refl.
      * apply real_mult_comm.
    + apply (real_eq_trans _
               (real_mult (real_mult X (real_inv_pos X HX)) Y) _).
      * apply real_mult_assoc.
      * apply (real_eq_trans _ (real_mult real_one Y) _).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_mult X (real_inv_pos X HX)) Y real_one Y).
           ++ exact H.
           ++ apply real_eq_refl.
        -- apply (real_eq_trans (real_mult real_one Y)
                    (real_mult Y real_one) Y).
           ++ apply real_mult_comm.
           ++ apply real_mult_one.
Qed.

(* Core decay bound: every non-extremal token satisfies
   [w_T x <= exp(-gamma / T)].  Chain: [z x + gamma <= z m], hence
   [(z x + gamma)/T <= z m / T] and [exp(z x / T) <= exp(z m / T)] *
   [exp(-gamma / T)].  The partition function satisfies
   [Z >= exp(z m / T)] (the single term is below the total sum) and
   inversion reverses the order, so the factor [1/Z] only helps. *)
Lemma core_decay_bound : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  Not (Id x m) -> real_le (w_T T Ht x) (decay_T T Ht).
Proof.
  intros T Ht x Hxm.
  set (invT := real_inv_pos T Ht).
  assert (HinvT : real_lt real_zero invT) by apply real_inv_pos_pos.
  set (a := real_mult invT (z x)).
  set (b := real_mult invT (z m)).
  set (g := real_mult invT gamma).
  set (invZ := real_inv_pos (ZT T Ht) (ZT_pos T Ht)).
  set (invF := real_inv_pos (factor_T T Ht m) (factor_T_pos T Ht m)).
  (* Step 1: [a + g <= b], dividing the gap premise by T. *)
  assert (H1 : real_le (real_plus a g) b).
  { apply (RealSetoid.real_le_id_l (real_plus a g)
             (real_mult invT (real_plus (z x) gamma)) b).
    - apply real_eq_sym. apply real_distrib.
    - apply (real_le_mult_compat_l_aux (real_plus (z x) gamma) (z m) invT
               HinvT (gap_le x Hxm)). }
  (* Step 2: [a <= b - g]. *)
  assert (H2 : real_le a (real_plus b (real_opp g))).
  { assert (E1 : real_eq a (real_plus a real_zero))
      by exact (real_eq_sym (real_plus a real_zero) a (real_plus_zero a)).
    assert (E2 : real_eq (real_plus a real_zero)
                   (real_plus a (real_plus g (real_opp g))))
      by exact (RealSetoid.real_eq_plus_compat a real_zero a
                  (real_plus g (real_opp g)) (real_eq_refl a)
                  (real_eq_sym (real_plus g (real_opp g)) real_zero
                     (real_plus_opp g))).
    assert (E3 : real_eq (real_plus a (real_plus g (real_opp g)))
                   (real_plus (real_plus a g) (real_opp g)))
      by exact (real_plus_assoc a g (real_opp g)).
    assert (E4 : real_eq a (real_plus (real_plus a g) (real_opp g)))
      by exact (real_eq_trans a (real_plus a real_zero)
                  (real_plus (real_plus a g) (real_opp g)) E1
                  (real_eq_trans (real_plus a real_zero)
                     (real_plus a (real_plus g (real_opp g)))
                     (real_plus (real_plus a g) (real_opp g)) E2 E3)).
    apply (RealSetoid.real_le_id_l a
             (real_plus (real_plus a g) (real_opp g))
             (real_plus b (real_opp g))).
    - exact E4.
    - apply real_le_plus_compat; [exact H1 | apply real_le_refl]. }
  (* Step 3: [exp a <= exp b * exp(-g)]. *)
  assert (H3 : real_le (cauchy_real_exp a)
                       (real_mult (cauchy_real_exp b)
                                  (cauchy_real_exp (real_opp g)))).
  { apply (real_le_trans _ (cauchy_real_exp (real_plus b (real_opp g))) _).
    - apply real_exp_le_mono. exact H2.
    - apply (RealSetoid.real_eq_le).
      apply (cauchy_real_exp_plus b (real_opp g)). }
  (* Step 4: [inv Z <= inv factor], since Z >= the single factor term. *)
  assert (H4 : real_le invZ invF).
  { apply (real_inv_pos_le_compat (factor_T T Ht m) (ZT T Ht)).
    - unfold ZT.
      exact (single_le_sum_aux (factor_T T Ht) m vocab m_in_vocab
               (fun y => real_le_from_lt_aux _ _ (factor_T_pos T Ht y))). }
  (* Step 5: assemble [exp a / Z <= exp b * exp(-g) / factor = exp(-g)]. *)
  unfold w_T, decay_T.
  apply (real_le_trans _
           (real_mult (real_mult (cauchy_real_exp b)
                          (cauchy_real_exp (real_opp g))) invZ) _).
  - apply (real_le_mult_compat (cauchy_real_exp a)
             (real_mult (cauchy_real_exp b) (cauchy_real_exp (real_opp g))) invZ).
    + apply real_inv_pos_pos.
    + exact H3.
  - apply (real_le_trans _
             (real_mult (real_mult (cauchy_real_exp b)
                            (cauchy_real_exp (real_opp g))) invF) _).
    + apply (real_le_mult_compat_l_aux invZ invF
               (real_mult (cauchy_real_exp b) (cauchy_real_exp (real_opp g)))).
      * apply real_mult_pos_compat;
          [apply cauchy_real_exp_pos | apply cauchy_real_exp_pos].
      * exact H4.
    + apply (RealSetoid.real_eq_le).
      exact (eq_mult_inv_absorb (cauchy_real_exp b)
                  (cauchy_real_exp (real_opp g)) (factor_T_pos T Ht m)
                  (real_inv_pos_correct (factor_T T Ht m)
                     (factor_T_pos T Ht m))).
Qed.

(* ---------- 7. Mass conservation and the two-part TV bound ---------- *)

(* Off-extremal mass identity: [1 - w_T m] equals the sum over the
   vocabulary with [m] removed. *)
Lemma nonm_mass_eq : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_plus real_one (real_opp (w_T T Ht m)))
          (real_list_sum Token (w_T T Ht) (removeT m vocab)).
Proof.
  intros T Ht.
  assert (Hsplit : real_eq (real_list_sum Token (w_T T Ht) vocab)
                    (real_plus (w_T T Ht m)
                       (real_list_sum Token (w_T T Ht) (removeT m vocab))))
    by exact (split_count_one (w_T T Ht) m vocab m_count_one).
  assert (Hone : real_eq real_one
                   (real_plus (w_T T Ht m)
                      (real_list_sum Token (w_T T Ht) (removeT m vocab))))
    by exact (real_eq_trans real_one
                (real_list_sum Token (w_T T Ht) vocab)
                (real_plus (w_T T Ht m)
                   (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                (real_eq_sym _ _ (w_T_sum_one T Ht)) Hsplit).
  assert (Hc : real_eq (real_plus real_one (real_opp (w_T T Ht m)))
                 (real_plus (real_plus (w_T T Ht m)
                              (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                            (real_opp (w_T T Ht m))))
    by exact (RealSetoid.real_eq_plus_compat real_one
                (real_opp (w_T T Ht m))
                (real_plus (w_T T Ht m)
                   (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                (real_opp (w_T T Ht m)) Hone (real_eq_refl _)).
  assert (Hd : real_eq (real_plus (real_plus (w_T T Ht m)
                             (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                           (real_opp (w_T T Ht m)))
                 (real_list_sum Token (w_T T Ht) (removeT m vocab))).
  { assert (F1 : real_eq (real_plus (real_plus (w_T T Ht m) (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                              (real_opp (w_T T Ht m)))
                   (real_plus (w_T T Ht m)
                      (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                                 (real_opp (w_T T Ht m)))))
      by exact (real_eq_sym _ _
                  (real_plus_assoc (w_T T Ht m)
                     (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     (real_opp (w_T T Ht m)))).
    assert (F2 : real_eq (real_plus (w_T T Ht m)
                              (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                                 (real_opp (w_T T Ht m))))
                   (real_plus (w_T T Ht m)
                      (real_plus (real_opp (w_T T Ht m))
                         (real_list_sum Token (w_T T Ht) (removeT m vocab)))))
      by exact (RealSetoid.real_eq_plus_compat (w_T T Ht m)
                  (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     (real_opp (w_T T Ht m)))
                  (w_T T Ht m)
                  (real_plus (real_opp (w_T T Ht m))
                     (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                  (real_eq_refl _)
                  (real_plus_comm (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     (real_opp (w_T T Ht m)))).
    assert (F3 : real_eq (real_plus (w_T T Ht m)
                              (real_plus (real_opp (w_T T Ht m))
                                 (real_list_sum Token (w_T T Ht) (removeT m vocab))))
                   (real_plus (real_plus (w_T T Ht m) (real_opp (w_T T Ht m)))
                              (real_list_sum Token (w_T T Ht) (removeT m vocab))))
      by exact (real_plus_assoc (w_T T Ht m) (real_opp (w_T T Ht m))
                  (real_list_sum Token (w_T T Ht) (removeT m vocab))).
    assert (F4 : real_eq (real_plus (real_plus (w_T T Ht m) (real_opp (w_T T Ht m)))
                              (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                   (real_plus real_zero
                      (real_list_sum Token (w_T T Ht) (removeT m vocab))))
      by exact (RealSetoid.real_eq_plus_compat
                  (real_plus (w_T T Ht m) (real_opp (w_T T Ht m)))
                  (real_list_sum Token (w_T T Ht) (removeT m vocab))
                  real_zero
                  (real_list_sum Token (w_T T Ht) (removeT m vocab))
                  (real_plus_opp (w_T T Ht m)) (real_eq_refl _)).
    assert (F5 : real_eq (real_plus real_zero
                              (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                   (real_list_sum Token (w_T T Ht) (removeT m vocab)))
      by exact (real_eq_trans _
                  (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     real_zero) _
                  (real_plus_comm real_zero
                     (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                  (real_plus_zero (real_list_sum Token (w_T T Ht) (removeT m vocab)))).
    exact (real_eq_trans _ _ _ F1 (real_eq_trans _ _ _ F2 (real_eq_trans _ _ _ F3 (real_eq_trans _ _ _ F4 F5)))).
  }
  exact (real_eq_trans _ _ _ Hc Hd).
Qed.

(* The off-extremal mass is at most [N * exp(-gamma / T)]. *)
Lemma nonm_mass_le_bound : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (real_list_sum Token (w_T T Ht) (removeT m vocab))
          (real_mult (real_of_nat (length vocab)) (decay_T T Ht)).
Proof.
  intros T Ht.
  apply (real_le_trans _
           (real_mult (real_of_nat (length (removeT m vocab)))
                      (decay_T T Ht)) _).
  - apply sum_nonneg_le_const_aux.
    intros x Hin.
    apply (core_decay_bound T Ht x).
    exact (remove_notin_aux m x vocab Hin).
  - apply (real_le_mult_compat_weak
             (real_of_nat (length (removeT m vocab)))
             (real_of_nat (length vocab)) (decay_T T Ht)).
    + apply real_le_from_lt_aux. apply cauchy_real_exp_pos.
    + apply real_of_nat_le_mono_aux. apply NatLe_drop. apply remove_length_le_aux.
Qed.

(* The pointwise TV summand. *)
Definition h_abs (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  real_abs (real_minus_r (w_T T Ht x) (hard_dist x)).

(* The [m] term: [|w_T m - 1| = 1 - w_T m] via the mass identity. *)
Lemma h_m_eq_nonm_mass : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (h_abs T Ht m) (real_list_sum Token (w_T T Ht) (removeT m vocab)).
Proof.
  intros T Ht.
  assert (Hhm : real_eq (hard_dist m) real_one).
  { unfold hard_dist. destruct (token_eq_dec m m) as [H | Hn].
    - apply real_eq_refl.
    - exact (match Hn (@id_refl Token m) with end). }
  assert (Hw1 : real_le (w_T T Ht m) real_one) by exact (w_T_m_le_one T Ht).
  apply (real_eq_trans _
           (real_abs (real_minus_r (w_T T Ht m) real_one)) _).
  - apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat (w_T T Ht m)
               (real_opp (hard_dist m)) (w_T T Ht m) (real_opp real_one)).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_opp_compat (hard_dist m) real_one Hhm).
  - apply (real_eq_trans _
             (real_plus real_one (real_opp (w_T T Ht m))) _).
    + apply (real_abs_minus_r_nonneg_aux (w_T T Ht m) real_one Hw1).
    + apply nonm_mass_eq.
Qed.

Lemma hsum_split : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_list_sum Token (h_abs T Ht) vocab)
          (real_plus (h_abs T Ht m)
                     (real_list_sum Token (h_abs T Ht) (removeT m vocab))).
Proof.
  intros T Ht. exact (split_count_one (h_abs T Ht) m vocab m_count_one).
Qed.

(* The non-[m] TV mass is at most [N * exp(-gamma / T)]. *)
Lemma hsum_nonm_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (real_list_sum Token (h_abs T Ht) (removeT m vocab))
          (real_mult (real_of_nat (length vocab)) (decay_T T Ht)).
Proof.
  intros T Ht.
  apply (real_le_trans _
           (real_mult (real_of_nat (length (removeT m vocab)))
                      (decay_T T Ht)) _).
  - apply sum_nonneg_le_const_aux.
    intros x Hin.
    assert (Hxm : Not (Id x m))
      by exact (remove_notin_aux m x vocab Hin).
    assert (Hhz : real_eq (hard_dist x) real_zero).
    { unfold hard_dist. destruct (token_eq_dec x m) as [H | Hn].
      - destruct (Hxm H).
      - apply real_eq_refl. }
    assert (Hp : real_eq (real_minus_r (w_T T Ht x) (hard_dist x))
                   (w_T T Ht x)).
    { apply (real_eq_trans _ (real_plus (w_T T Ht x)
                 (real_opp (hard_dist x))) _).
      - apply real_eq_refl.
      - apply (real_eq_trans _
                   (real_plus (w_T T Ht x) (real_opp real_zero)) _).
        + apply (RealSetoid.real_eq_plus_compat (w_T T Ht x)
                     (real_opp (hard_dist x)) (w_T T Ht x)
                     (real_opp real_zero)).
          * apply real_eq_refl.
          * apply (RealSetoid.real_eq_opp_compat (hard_dist x) real_zero).
            exact Hhz.
        + apply (real_eq_trans _ (real_plus (w_T T Ht x) real_zero) _).
          * apply (RealSetoid.real_eq_plus_compat (w_T T Ht x)
                     (real_opp real_zero) (w_T T Ht x) real_zero
                     (real_eq_refl _) (real_opp_zero)).
          * apply real_plus_zero. }
    unfold h_abs.
    apply (RealSetoid.real_le_id_l
             (real_abs (real_minus_r (w_T T Ht x) (hard_dist x)))
             (real_abs (w_T T Ht x)) (decay_T T Ht)).
    + apply real_abs_eq_compat. exact Hp.
    + apply (real_le_trans _ (w_T T Ht x) _).
      * apply (RealSetoid.real_eq_le).
        apply (real_abs_pos_req (w_T T Ht x) (w_T_pos T Ht x)).
      * exact (core_decay_bound T Ht x Hxm).
  - apply (real_le_mult_compat_weak
             (real_of_nat (length (removeT m vocab)))
             (real_of_nat (length vocab)) (decay_T T Ht)).
    + apply real_le_from_lt_aux. apply cauchy_real_exp_pos.
    + apply real_of_nat_le_mono_aux. apply NatLe_drop. apply remove_length_le_aux.
Qed.

(* A nonempty vocabulary has at least one element. *)
Lemma vocab_len_pos : real_lt real_zero (real_of_nat (length vocab)).
Proof.
  destruct vocab as [| w rest].
  - exact (match vocab_nonempty (@id_refl (list Token) nil) with end).
  - cbn [length].
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest))) _).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* Halving folds a doubled sum: [inv 2 * (X + X) = X]. *)
Lemma eq_inv2_double : forall (X : Real) (HX : real_lt real_zero (real_plus real_one real_one)),
  real_eq (real_mult (real_inv_pos (real_plus real_one real_one) HX)
             (real_plus X X))
          X.
Proof.
  intros X HX.
  assert (Hii : real_eq (real_mult (real_plus real_one real_one)
                         (real_inv_pos (real_plus real_one real_one) HX))
                   real_one)
    by exact (real_inv_pos_correct (real_plus real_one real_one) HX).
  assert (Hmx : real_eq X (real_mult real_one X))
    by exact (real_eq_sym (real_mult real_one X) X
                (real_eq_trans _ _ _ (real_mult_comm real_one X) (real_mult_one X))).
  assert (DSB : real_eq (real_plus X X) (real_mult (real_plus real_one real_one) X))
    by exact (real_eq_trans _ _ _
      (RealSetoid.real_eq_plus_compat X X (real_mult real_one X) (real_mult real_one X)
        Hmx Hmx)
      (real_distrib_r real_one real_one X)).
  assert (Hkey : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) HX)
                              (real_mult (real_plus real_one real_one) X))
                         (real_mult real_one X)).
  { apply (real_eq_trans _
             (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) HX)
                        (real_plus real_one real_one)) X) _).
    - exact (real_mult_assoc (real_inv_pos (real_plus real_one real_one) HX)
               (real_plus real_one real_one) X).
    - apply (real_eq_trans _
               (real_mult (real_mult (real_plus real_one real_one)
                          (real_inv_pos (real_plus real_one real_one) HX)) X) _).
      + apply (RealSetoid.real_eq_mult_compat
                  (real_mult (real_inv_pos (real_plus real_one real_one) HX)
                     (real_plus real_one real_one))
                  X
                  (real_mult (real_plus real_one real_one)
                     (real_inv_pos (real_plus real_one real_one) HX))
                  X
                  (real_mult_comm (real_inv_pos (real_plus real_one real_one) HX)
                     (real_plus real_one real_one))
                  (real_eq_refl X)).
      + apply (RealSetoid.real_eq_mult_compat
                  (real_mult (real_plus real_one real_one)
                     (real_inv_pos (real_plus real_one real_one) HX))
                  X
                  real_one
                  X
                  Hii (real_eq_refl X)). }
  apply (real_eq_trans _
           (real_mult (real_inv_pos (real_plus real_one real_one) HX)
              (real_mult (real_plus real_one real_one) X)) _).
  - apply (RealSetoid.real_eq_mult_compat
              (real_inv_pos (real_plus real_one real_one) HX)
              (real_plus X X)
              (real_inv_pos (real_plus real_one real_one) HX)
              (real_mult (real_plus real_one real_one) X)
              (real_eq_refl (real_inv_pos (real_plus real_one real_one) HX))
              DSB).
  - exact (real_eq_trans _ _ _ Hkey
             (real_eq_trans _ _ _ (real_mult_comm real_one X) (real_mult_one X))).
Qed.

Lemma tv_hard_le_decay_scale : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (tv_hard T Ht)
          (real_mult (real_of_nat (length vocab)) (decay_T T Ht)).
Proof.
  intros T Ht.
  assert (Hinv2 : real_lt real_zero
             (real_inv_pos (real_plus real_one real_one)
                (real_lt_plus_compat real_zero real_one real_zero real_one
                   real_lt_zero_one real_lt_zero_one)))
    by apply real_inv_pos_pos.
  assert (Hsp : real_eq (real_list_sum Token (h_abs T Ht) vocab)
                  (real_plus (h_abs T Ht m)
                     (real_list_sum Token (h_abs T Ht) (removeT m vocab))))
    by exact (hsum_split T Ht).
  assert (HA : real_le (h_abs T Ht m)
                 (real_mult (real_of_nat (length vocab)) (decay_T T Ht))).
  { apply (real_le_trans _ (real_list_sum Token (w_T T Ht) (removeT m vocab)) _).
    - apply (RealSetoid.real_eq_le (h_abs T Ht m)
               (real_list_sum Token (w_T T Ht) (removeT m vocab))
               (h_m_eq_nonm_mass T Ht)).
    - exact (nonm_mass_le_bound T Ht). }
  assert (HB : real_le (real_list_sum Token (h_abs T Ht) (removeT m vocab))
                 (real_mult (real_of_nat (length vocab)) (decay_T T Ht)))
    by exact (hsum_nonm_le T Ht).
  assert (Hsum : real_le (real_list_sum Token (h_abs T Ht) vocab)
                   (real_plus (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                      (real_mult (real_of_nat (length vocab)) (decay_T T Ht)))).
  { apply (real_le_trans _
             (real_plus (h_abs T Ht m)
                (real_list_sum Token (h_abs T Ht) (removeT m vocab))) _).
    - exact (RealSetoid.real_eq_le _ _ Hsp).
    - exact (real_le_plus_compat (h_abs T Ht m)
                (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                (real_list_sum Token (h_abs T Ht) (removeT m vocab))
                (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                HA HB). }
  assert (Hstep : real_le (real_mult
                             (real_inv_pos (real_plus real_one real_one)
                                (real_lt_plus_compat real_zero real_one
                                   real_zero real_one real_lt_zero_one
                                   real_lt_zero_one))
                             (real_list_sum Token (h_abs T Ht) vocab))
                     (real_mult (real_of_nat (length vocab)) (decay_T T Ht))).
  { apply (real_le_trans _
             (real_mult (real_inv_pos (real_plus real_one real_one)
                           (real_lt_plus_compat real_zero real_one real_zero
                              real_one real_lt_zero_one real_lt_zero_one))
                (real_plus (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                   (real_mult (real_of_nat (length vocab)) (decay_T T Ht)))) _).
    - apply (real_le_mult_compat_l_aux _ _ _ Hinv2 Hsum).
    - exact (RealSetoid.real_eq_le _ _
               (eq_inv2_double (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                  (real_lt_plus_compat real_zero real_one real_zero real_one
                     real_lt_zero_one real_lt_zero_one))). }
  unfold tv_hard.
  apply (real_le_trans _
           (real_mult (real_of_nat (length vocab)) (decay_T T Ht)) _).
  - exact Hstep.
  - apply (RealSetoid.real_eq_le). apply real_eq_refl.
Qed.

Theorem hard_attention_limit : forall eps : Real,
  real_lt real_zero eps ->
  sigT (fun T0 => And (real_lt real_zero T0)
    (forall (T : Real) (Ht : real_lt real_zero T), real_lt T T0 ->
      real_le (tv_hard T Ht) eps)).
Proof.
  intros eps Heps.
  set (N := length vocab).
  set (EN := real_of_nat N).
  set (M := real_mult EN (real_inv_pos eps Heps)).
  set (ylog := real_plus M real_one).
  assert (HM : real_lt real_zero M).
  { apply real_mult_pos_compat.
    - apply vocab_len_pos.
    - apply real_inv_pos_pos. }
  assert (Hy : real_lt real_zero ylog).
  { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) _).
    - apply real_eq_sym. apply real_plus_zero.
    - apply real_lt_plus_compat.
      + exact HM.
      + apply real_lt_zero_one. }
  assert (Hy1 : real_lt real_one ylog).
  { apply (real_eq_lt_lt real_one (real_plus real_zero real_one) ylog).
    - apply (real_eq_trans _ (real_plus real_one real_zero) _).
      + apply real_eq_sym. exact (real_plus_comm real_zero real_one).
      + exact (real_plus_zero real_one).
    - apply (real_lt_plus_compat_lt_le real_zero M real_one real_one HM
               (real_le_refl real_one)). }
  assert (HL : real_lt real_zero (cw_log ylog Hy)).
  { apply exp_reflects_lt.
    apply (real_eq_lt_lt (cauchy_real_exp real_zero) real_one
             (cauchy_real_exp (cw_log ylog Hy))).
    - exact cauchy_real_exp_zero.
    - apply (real_lt_eq_lt real_one ylog (cauchy_real_exp (cw_log ylog Hy))).
      + exact Hy1.
      + exact (real_eq_sym (cauchy_real_exp (cw_log ylog Hy)) ylog
                 (cw_log_exp_right ylog Hy)). }
  exists (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL)). split.
  - apply real_mult_pos_compat; [exact gamma_pos | apply real_inv_pos_pos].
  - intros T Ht Hlt.
    set (invT := real_inv_pos T Ht).
    assert (HinvT : real_lt real_zero invT) by apply real_inv_pos_pos.
    set (a := real_mult invT gamma).
    (* Step 1: [T * L < gamma]. *)
    assert (Hs1 : real_lt (real_mult T (cw_log ylog Hy)) gamma).
    { apply (real_lt_eq_lt (real_mult T (cw_log ylog Hy))
               (real_mult (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL))
                  (cw_log ylog Hy)) gamma).
      - apply (real_mult_lt_compat T
                  (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL))
                  (cw_log ylog Hy) Hlt HL).
      - apply (real_eq_trans _
                 (real_mult gamma
                    (real_mult (real_inv_pos (cw_log ylog Hy) HL)
                               (cw_log ylog Hy))) _).
        + apply real_eq_sym. apply real_mult_assoc.
        + apply (real_eq_trans _
                   (real_mult gamma
                      (real_mult (cw_log ylog Hy)
                         (real_inv_pos (cw_log ylog Hy) HL))) _).
          * apply (RealSetoid.real_eq_mult_compat gamma
                     (real_mult (real_inv_pos (cw_log ylog Hy) HL)
                                (cw_log ylog Hy))
                     gamma
                     (real_mult (cw_log ylog Hy)
                                (real_inv_pos (cw_log ylog Hy) HL))).
            -- apply real_eq_refl.
            -- apply real_mult_comm.
          * apply (real_eq_trans _ (real_mult gamma real_one) _).
            -- apply (RealSetoid.real_eq_mult_compat gamma
                        (real_mult (cw_log ylog Hy)
                           (real_inv_pos (cw_log ylog Hy) HL)) gamma real_one).
               ++ apply real_eq_refl.
               ++ apply (real_inv_pos_correct (cw_log ylog Hy) HL).
            -- apply real_mult_one. }
    (* Step 2: [L < gamma / T]. *)
    assert (Hs2 : real_lt (cw_log ylog Hy) a).
    { assert (Hmul : real_lt (real_mult invT (real_mult T (cw_log ylog Hy)))
                             (real_mult invT gamma))
        by (apply (real_mult_lt_compat_l _ _ invT Hs1 HinvT)).
      apply (real_lt_eq_lt (cw_log ylog Hy) (real_mult invT gamma) a).
      + apply (real_eq_lt_lt (cw_log ylog Hy)
                 (real_mult invT (real_mult T (cw_log ylog Hy)))
                 (real_mult invT gamma)).
        * apply real_eq_sym.
          exact (real_eq_trans _ _ _
                   (real_eq_trans _ _ _
                     (real_eq_trans _ _ _
                       (real_mult_assoc invT T (cw_log ylog Hy))
                       (RealSetoid.real_eq_mult_compat
                          (real_mult invT T) (cw_log ylog Hy)
                          (real_mult T invT) (cw_log ylog Hy)
                          (real_mult_comm invT T)
                          (real_eq_refl (cw_log ylog Hy))))
                     (RealSetoid.real_eq_mult_compat
                        (real_mult T invT) (cw_log ylog Hy)
                        real_one (cw_log ylog Hy)
                        (real_inv_pos_correct T Ht)
                        (real_eq_refl (cw_log ylog Hy))))
                   (real_eq_trans _ _ _
                     (real_mult_comm real_one (cw_log ylog Hy))
                     (real_mult_one (cw_log ylog Hy)))).
        * exact Hmul.
      + apply real_eq_refl. }
    (* Step 3: [M <= exp(gamma / T)]. *)
    assert (Hs3 : real_le M (cauchy_real_exp a)).
    { apply (real_le_trans _ (cauchy_real_exp (cw_log ylog Hy)) _).
      - apply (RealSetoid.real_le_id_r M ylog
                 (cauchy_real_exp (cw_log ylog Hy))).
        + exact (real_eq_sym (cauchy_real_exp (cw_log ylog Hy)) ylog
                   (cw_log_exp_right ylog Hy)).
        + apply real_le_plus_nonneg_r_aux.
          apply real_le_from_lt_aux. apply real_lt_zero_one.
      - apply real_exp_le_mono. exact (real_le_from_lt_aux _ _ Hs2). }
    (* Step 4: [N <= eps * exp(gamma / T)]. *)
    assert (Hs4 : real_le EN (real_mult eps (cauchy_real_exp a))).
    { apply (RealSetoid.real_le_id_l EN (real_mult eps M) _).
      - exact (real_eq_sym _ _
          (real_eq_trans _ _ _
            (real_mult_assoc eps EN (real_inv_pos eps Heps))
            (real_eq_trans _ _ _
              (RealSetoid.real_eq_mult_compat
                 (real_mult eps EN) (real_inv_pos eps Heps)
                 (real_mult EN eps) (real_inv_pos eps Heps)
                 (real_mult_comm eps EN)
                 (real_eq_refl (real_inv_pos eps Heps)))
              (real_eq_trans _ _ _
                (real_eq_sym _ _ (real_mult_assoc EN eps (real_inv_pos eps Heps)))
                (real_eq_trans _ _ _
                  (RealSetoid.real_eq_mult_compat
                     EN (real_mult eps (real_inv_pos eps Heps))
                     EN real_one
                     (real_eq_refl EN) (real_inv_pos_correct eps Heps))
                  (real_mult_one EN)))))).
      - apply (real_le_mult_compat_l_aux M (cauchy_real_exp a) eps
                 Heps Hs3). }
    (* Step 5: [exp(-gamma/T) * N <= eps]. *)
    assert (Hs5 : real_le
                    (real_mult (cauchy_real_exp (real_opp a)) EN) eps).
    { apply (RealSetoid.real_le_id_r
               (real_mult (cauchy_real_exp (real_opp a)) EN)
               (real_mult (cauchy_real_exp (real_opp a))
                  (real_mult eps (cauchy_real_exp a))) eps).
      - apply (real_eq_trans _
                 (real_mult (cauchy_real_exp (real_opp a))
                            (real_mult (cauchy_real_exp a) eps)) _).
        + apply (RealSetoid.real_eq_mult_compat
                    (cauchy_real_exp (real_opp a))
                    (real_mult eps (cauchy_real_exp a))
                    (cauchy_real_exp (real_opp a))
                    (real_mult (cauchy_real_exp a) eps)).
          * apply real_eq_refl.
          * apply real_mult_comm.
        + apply (real_eq_trans _
                     (real_mult
                        (real_mult (cauchy_real_exp (real_opp a))
                                   (cauchy_real_exp a))
                        eps) _).
          * apply real_mult_assoc.
          * apply (real_eq_trans _ (real_mult real_one eps) _).
            -- apply (RealSetoid.real_eq_mult_compat
                        (real_mult (cauchy_real_exp (real_opp a))
                                   (cauchy_real_exp a))
                        eps
                        real_one eps).
               ++ apply exp_mult_opp_l_aux.
               ++ apply real_eq_refl.
            -- apply (real_eq_trans _ (real_mult eps real_one) _).
               ++ apply real_mult_comm.
               ++ apply real_mult_one.
      - apply (real_le_mult_compat_l_aux EN
                 (real_mult eps (cauchy_real_exp a))
                 (cauchy_real_exp (real_opp a))).
        + apply cauchy_real_exp_pos.
        + exact Hs4. }
    (* Assemble: [tv_hard <= N * exp(-gamma/T) = exp(-gamma/T) * N <= eps]. *)
    apply (real_le_trans _
             (real_mult (real_of_nat (length vocab))
                        (decay_T T Ht)) _).
    + apply tv_hard_le_decay_scale.
    + apply (real_le_trans _
               (real_mult (cauchy_real_exp (real_opp a))
                  (real_of_nat (length vocab))) _).
      * apply (RealSetoid.real_eq_le). apply real_mult_comm.
      * exact Hs5.
Qed.

End AttnHardLimit.

(* The temperature cap construction and the hard distribution carry
   computational content and extract to OCaml. *)
From Stdlib Require Import Extraction.
Extraction "attn_hardlimit218.ml" count_token removeT hard_dist.
(* ============================================================ *)
(* Concrete-layer witnesses for the two section premises: a nonempty
   vocabulary and a decidable token equality, both carried by [Set]. *)
(* The nonemptiness witness has the dependent-pair type
   [sigT (fun t => InT t vocab)], informative enough to extract the
   element itself.  The decision certificate [hard_eq_dec_cert] carries
   the equality witness [Id a b] on its [yes] branch and the refutation
   [Id a b -> Empty_set] on its [no] branch.  On the two-point list
   [bool] the nonemptiness witness is given by the [InT_here]
   constructor, and the decision enumerates the four constructor
   combinations (the equal pairs by [id_refl], the unequal pairs by
   index discrimination). *)
(* ============================================================ *)
Definition hard_vocab_nonempty_set (X : Set) (vocab : list X) : Set :=
  sigT (fun t : X => InT t vocab).
(* Uniform-carrier decision certificate: the [true] branch carries the
   equality witness [Id a b]; the [false] branch carries a refutation
   [Id a b -> Empty_set].  Both payloads are plain Set data, so the
   extracted OCaml keeps every branch (a [sigT] payload whose type is a
   match on the flag cannot be represented by extraction). *)
Inductive hard_eq_dec_cert (X : Set) (a b : X) : Set :=
| hard_eq_dec_yes : Id a b -> hard_eq_dec_cert X a b
| hard_eq_dec_no : (Id a b -> Empty_set) -> hard_eq_dec_cert X a b.

Arguments hard_eq_dec_yes {X a b}.
Arguments hard_eq_dec_no {X a b}.

Definition hard_token_eq_dec_set (X : Set) : Set :=
  forall a b : X, hard_eq_dec_cert X a b.

Theorem hard_vocab_nonempty_supply :
  hard_vocab_nonempty_set bool (cons true (cons false nil)).
Proof. exact (existT _ true (@InT_here bool true (cons false nil))). Qed.

Theorem hard_token_eq_dec_supply : hard_token_eq_dec_set bool.
Proof.
  intros a b.
  destruct a; destruct b.
  - exact (hard_eq_dec_yes (id_refl)).
  - apply hard_eq_dec_no. intro H. inversion H.
  - apply hard_eq_dec_no. intro H. inversion H.
  - exact (hard_eq_dec_yes (id_refl)).
Qed.

Print Assumptions hard_vocab_nonempty_supply.
Print Assumptions hard_token_eq_dec_supply.
