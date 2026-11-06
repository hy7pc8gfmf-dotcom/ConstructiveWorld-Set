(* ConstructiveWorld-Set -- hard-attention uniform limit over tied maxima. *)

(** * UpReqAttnUniformLimit: uniform limit of hard attention over tied copies.

    Mission.  With tied copies of the maximizer [m] in the vocabulary, the
      hard weights [w_T] tend to the uniform distribution on the copies.
      [alm_gap_witness] certifies the decidable Q maximum, its multiplicity
      and the two-tier gap [alm_gap_cert]; the m-switch sum identities
      [swg_switch_sum_gen]/[swg_switch_sum] and the chain [alu_mass_split]
      through [alu_l1_le] give [alm_uniform_limit]: for every [eps] > 0
      some [T0] > 0 makes L1(w_T, u) <= eps whenever 0 < T < T0.

    Dependencies.  Stdlib [List], [Arith], [Lia], [micromega.Lqa],
      [QArith.QArith], [QArith.Qring], [Extraction].  Requires of this
      development [AttnHardLimit218], [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp].

    References.  This development, UpReqAttnUniformLimit.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqAttnUniformLimit.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

Require Import AttnHardLimit218.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import QArith.QArith QArith.Qring.
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
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S14_B5BatchBlock.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S14_B5BatchBlock.
Import ListNotations.

(* ============================================================ *)
(* Section 1. Q-level tied-gap certificate (decidable enumeration, *)
(* fully constructive).                                            *)
(* ============================================================ *)

(* Maximum of a nonempty list: the head element seeds the fold, so no
   spurious maximum appears on all-negative tables. *)
(* Qle_bool is the decidable comparison basis here; the two lemmas
   below bridge it to the order relations on Q. *)
Lemma alm_qleb_true : forall a b : Q, Qle_bool a b = true -> Qle a b.
Proof.
  intros a b H. apply Qle_bool_iff. exact H.
Qed.

Lemma alm_qleb_false : forall a b : Q, Qle_bool a b = false -> Qlt b a.
Proof.
  intros a b H. apply Qnot_le_lt. intro Hle.
  assert (Hb : Qle_bool a b = true) by exact (proj2 (Qle_bool_iff a b) Hle).
  rewrite H in Hb. discriminate Hb.
Qed.

(* The order lemmas Qplus_lt_compat_r, Qeq_lt and Qlt_refl are not
   available on this Q installation, so strict right-monotonicity of
   addition is derived from Qplus_le_l (right cancellation in iff
   form) with Qlt_irrefl and Qlt_le_trans; it also stands in for
   Qeq_lt on the strict side of the witness below. *)
Lemma alm_qlt_compat_r : forall x y z : Q, Qlt x y -> Qlt (x + z) (y + z).
Proof.
  intros x y z Hxy.
  apply (Qnot_le_lt (y + z)%Q (x + z)%Q).
  intro Hle.
  assert (Hyx : Qle y x) by exact (proj1 (Qplus_le_l y x z) Hle).
  exact (Qlt_irrefl x (Qlt_le_trans x y x Hxy Hyx)).
Qed.

Fixpoint alm_max_ne (q : Q) (tab : list Q) : Q :=
  match tab with
  | nil => q
  | y :: r =>
      match Qle_bool q (alm_max_ne y r) with
      | true => alm_max_ne y r
      | false => q
      end
  end.

Lemma alm_max_ne_ub : forall (tab : list Q) (q x : Q),
  In x (q :: tab) -> Qle x (alm_max_ne q tab).
Proof.
  intros tab. induction tab as [| y rest IH]; intros q x Hin.
  - destruct Hin as [Heq | Hin'].
    + subst. apply Qle_refl.
    + destruct Hin'.
  - cbn [alm_max_ne].
    destruct (Qle_bool q (alm_max_ne y rest)) eqn:Hd.
    + inversion Hin as [Heq | Hin']; subst.
      * exact (alm_qleb_true _ _ Hd).
      * exact (IH y x Hin').
    + inversion Hin as [Heq | Hin'].
      * rewrite <- Heq. apply Qle_refl.
      * apply Qlt_le_weak.
        apply (Qle_lt_trans x (alm_max_ne y rest) q).
        -- exact (IH y x Hin').
        -- exact (alm_qleb_false _ _ Hd).
Qed.

Lemma alm_max_ne_in : forall (tab : list Q) (q : Q),
  In (alm_max_ne q tab) (q :: tab).
Proof.
  intros tab. induction tab as [| y rest IH]; intro q.
  - apply in_eq.
  - cbn [alm_max_ne].
    destruct (Qle_bool q (alm_max_ne y rest)).
    + apply in_cons. exact (IH y).
    + apply in_eq.
Qed.

(** Set-level membership certificate for the decidable maximum: the
    InT form parallel to alm_max_ne_in, each branch built directly by
    InT_here / InT_next. *)
Lemma alm_max_ne_inT : forall (tab : list Q) (q : Q),
  InT (alm_max_ne q tab) (q :: tab).
Proof.
  intros tab. induction tab as [| y rest IH]; intro q.
  - cbn [alm_max_ne]. apply InT_here.
  - cbn [alm_max_ne].
    destruct (Qle_bool q (alm_max_ne y rest)).
    + apply InT_next. exact (IH y).
    + apply InT_here.
Qed.

Lemma alm_qeqb_false : forall a b : Q, Qeq_bool a b = false -> ~ (a == b).
Proof.
  intros a b H Heq.
  destruct (Qeq_bool_iff a b) as [_ Hb].
  specialize (Hb Heq). rewrite Hb in H. discriminate H.
Qed.

(* Maximum over the table entries that differ from qmax, as an option;
   the fold uses no filter. *)
Fixpoint alm_below_max (qmax : Q) (tab : list Q) : option Q :=
  match tab with
  | nil => None
  | y :: r =>
      match Qeq_bool y qmax with
      | true => alm_below_max qmax r
      | false =>
          match alm_below_max qmax r with
          | None => Some y
          | Some m => if Qle_bool y m then Some m else Some y
          end
      end
  end.

(* Case P2: the below-filtered maximum is None only when every entry
   of the table equals qmax. *)
Lemma alm_below_max_none : forall tab qmax q,
  In q tab -> alm_below_max qmax tab = None -> q == qmax.
Proof.
  intros tab. induction tab as [| y rest IH]; intros qmax q Hin H.
  - exact (match Hin with end).
  - revert H. cbn [alm_below_max].
    destruct (Qeq_bool y qmax) eqn:Hy; simpl.
    + inversion Hin as [Heq | Hin']; subst.
      * intro H. apply Qeq_bool_eq. exact Hy.
      * intro H. exact (IH qmax q Hin' H).
    + intro H. destruct (alm_below_max qmax rest) as [m' |].
      * destruct (Qle_bool y m'); discriminate H.
      * discriminate H.
Qed.

(* Case P1a: if the below-filtered maximum is Some m, then m occurs in
   the table and m differs from qmax. *)
Lemma alm_below_max_in : forall tab qmax m,
  alm_below_max qmax tab = Some m ->
  In m tab /\ (~ (m == qmax)).
Proof.
  intros tab. induction tab as [| y rest IH]; intros qmax m H.
  - discriminate H.
  - revert H. cbn [alm_below_max].
    destruct (Qeq_bool y qmax) eqn:Hy; simpl.
    + intros H. destruct (IH qmax m H) as [Hin Hne].
      split.
      * apply in_cons. exact Hin.
      * exact Hne.
    + destruct (alm_below_max qmax rest) as [m' |] eqn:Hr.
      * destruct (Qle_bool y m') eqn:Hyle.
        -- simpl. intros H. inversion H. subst.
           destruct (IH qmax m Hr) as [Hinm Hne].
           split.
           ++ apply in_cons. exact Hinm.
           ++ exact Hne.
        -- simpl. intros H. inversion H. subst.
           split.
           ++ apply in_eq.
           ++ exact (alm_qeqb_false _ _ Hy).
      * intros H. inversion H. subst.
        split.
        ++ apply in_eq.
        ++ exact (alm_qeqb_false _ _ Hy).
Qed.

(* Case P1b: if the below-filtered maximum is Some m, every entry of
   the table distinct from qmax is at most m. *)
Lemma alm_below_max_ub : forall tab qmax m q,
  In q tab -> alm_below_max qmax tab = Some m ->
  ~ (q == qmax) -> Qle q m.
Proof.
  intros tab. induction tab as [| y rest IH]; intros qmax m q Hin H Hne.
  - exact (match Hin with end).
  - revert Hin H Hne. revert q. cbn [alm_below_max].
    destruct (Qeq_bool y qmax) eqn:Hy.
    + simpl. intros q Hin H Hne.
      inversion Hin as [Heq | Hin']; subst.
      * exact (match Hne (Qeq_bool_eq _ _ Hy) with end).
      * exact (IH qmax m q Hin' H Hne).
    + simpl. destruct (alm_below_max qmax rest) as [m' |] eqn:Hr.
      * assert (IH' : forall q : Q,
            In q rest -> alm_below_max qmax rest = Some m' ->
            ~ (q == qmax) -> Qle q m')
          by exact (IH qmax m').
        destruct (Qle_bool y m') eqn:Hyle.
        -- simpl. intros q Hin H Hne. inversion H. subst.
           destruct Hin as [Heq | Hin']; subst.
           ++ exact (alm_qleb_true _ _ Hyle).
           ++ exact (IH' q Hin' Hr Hne).
        -- simpl. intros q Hin H Hne. inversion H. subst.
           destruct Hin as [Heq | Hin']; subst.
           ++ apply Qle_refl.
           ++ apply (Qle_trans q m' m).
              ** exact (IH' q Hin' Hr Hne).
              ** apply Qlt_le_weak. exact (alm_qleb_false _ _ Hyle).
      * simpl. intros q Hin H Hne. inversion H. subst.
        destruct Hin as [Heq | Hin']; subst.
        ++ apply Qle_refl.
        ++ exact (match Hne (alm_below_max_none _ _ _ Hin' Hr) with end).
Qed.


(* ============ Section 1a. Binary choice on Q tables and the two-tier gap certificate ============ *)

(** Set-level binary choice: a constructive fork on two Set payloads
    that extracts as an ordinary variant type, with no projection
    operators. *)
Inductive alm_pick2 (A B : Set) : Set :=
| alm_pick2_l : A -> alm_pick2 A B
| alm_pick2_r : B -> alm_pick2 A B.

(** Back-translation of the membership certificate: InT rewrites as
    List.In, so the propositional-layer lemmas remain reusable. *)
Lemma alm_inT_in : forall (x : Q) (l : list Q), InT x l -> In x l.
Proof.
  intros x l H. induction H as [l0 | y l0 HinT IH].
  - apply in_eq.
  - apply in_cons. exact IH.
Qed.

(** Two-tier certificate for the tied gap: the uniform tier carries the
    pointwise equality of the whole table with qmax, the gap tier
    carries a positive gap together with the pointwise binary choice
    (equal to qmax, or qmax still an upper bound after adding g).  All
    payloads live in Set (QeqT / QltT / QleT'), so the choice stays
    informative under extraction. *)
Inductive alm_gap_cert (tab : list Q) (qmax g : Q) : Set :=
| alm_cert_uniform : (forall q : Q, InT q tab -> QeqT q qmax) ->
    alm_gap_cert tab qmax g
| alm_cert_gap : QltT 0%Q g ->
    (forall q : Q, InT q tab ->
       alm_pick2 (QeqT q qmax) (QleT' (q + g) qmax)) ->
    alm_gap_cert tab qmax g.

(** Tied-gap certificate: on a nonempty Q table there exist a maximum
    qmax, a natural number k >= 1 and a gap g such that qmax belongs
    to the table, the whole table is bounded above by qmax, and one of
    the two tiers holds: every entry equals qmax, or g > 0 and each
    entry either equals qmax or stays within qmax after adding g.  All
    predicates are carried at the Set level, the two tiers expressed
    by the constructors of alm_gap_cert.  Proof: the decidable
    enumeration alm_max_ne picks the maximum and the outcome of the
    alm_below_max enumeration dispatches the two tiers; every
    predicate crosses from its propositional lemma in the library to
    its Set carrier through the one-way S02 bridges. *)
Theorem alm_gap_witness : forall (q0 : Q) (rest : list Q),
  sigT (fun qmax => sigT (fun k => sigT (fun g =>
    And (InT qmax (q0 :: rest))
    (And (NatLe 1 k)
    (And (forall q : Q, InT q (q0 :: rest) -> QleT' q qmax)
         (alm_gap_cert (q0 :: rest) qmax g)))))).
Proof.
  intros q0 rest.
  assert (Hqmaxub : forall q : Q, In q (q0 :: rest) -> Qle q (alm_max_ne q0 rest))
    by exact (alm_max_ne_ub rest q0).
  assert (HqmaxinT : InT (alm_max_ne q0 rest) (q0 :: rest))
    by exact (alm_max_ne_inT rest q0).
  assert (HqmaxubT : forall q : Q, InT q (q0 :: rest) -> QleT' q (alm_max_ne q0 rest)).
  { intros q HinT. apply Qle_to_QleT'.
    exact (Hqmaxub q (alm_inT_in q (q0 :: rest) HinT)). }
  destruct (alm_below_max (alm_max_ne q0 rest) (q0 :: rest)) as [mb |] eqn:Hbm.
  + (* gap tier: g := qmax - (the below-filtered maximum) *)
    destruct (alm_below_max_in _ _ _ Hbm) as [Hmbin Hmbne].
    assert (Hltmb : Qlt mb (alm_max_ne q0 rest)).
    { destruct (Qle_lt_or_eq _ _ (Hqmaxub _ Hmbin)) as [Hlt | Heqq].
      - exact Hlt.
      - exfalso. apply Hmbne. exact Heqq. }
    exists (alm_max_ne q0 rest).
    exists (Datatypes.S (length (q0 :: rest))).
    exists (alm_max_ne q0 rest - mb)%Q.
    split; [exact HqmaxinT | ].
    split; [apply NatLe_lift; apply le_n_S; apply Nat.le_0_l | ].
    split; [exact HqmaxubT | ].
    apply alm_cert_gap.
    * apply Qlt_to_QltT.
      rewrite <- (Qplus_opp_r mb) at 1.
      apply (alm_qlt_compat_r mb (alm_max_ne q0 rest) (- mb)%Q).
      exact Hltmb.
    * intros q HinT. destruct (Qeq_dec q (alm_max_ne q0 rest)) as [Heqq | Hneqq].
      -- apply alm_pick2_l. apply qeq_imp_qeqT. exact Heqq.
      -- apply alm_pick2_r. apply Qle_to_QleT'.
         assert (Hqle : Qle q mb)
           by exact (alm_below_max_ub _ _ _ q
                       (alm_inT_in q (q0 :: rest) HinT) Hbm Hneqq).
         unfold Qminus. lra.
  + (* uniform tier: the whole table shares one value *)
    exists (alm_max_ne q0 rest).
    exists (Datatypes.S (length (q0 :: rest))).
    exists 0%Q.
    split; [exact HqmaxinT | ].
    split; [apply NatLe_lift; apply le_n_S; apply Nat.le_0_l | ].
    split; [exact HqmaxubT | ].
    apply alm_cert_uniform.
    intros q HinT. apply qeq_imp_qeqT.
    exact (alm_below_max_none _ _ _ (alm_inT_in q (q0 :: rest) HinT) Hbm).
Qed.

(* ============================================================ *)
(* Section 2. Real-level uniform limit over tied copies: the        *)
(* definition face and the computational core.                      *)
(* ============================================================ *)

Section AlmUniform.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.

(* Witness data for the argmax: uniqueness is not required, the tied
   copies enter explicitly. *)
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* Multiplicity of the tied copies: the number of occurrences of m in
   vocab, any value >= 1 (the count need not be 1). *)
Definition alm_k : nat := count_token Token token_eq_dec m vocab.

Lemma alm_count_ge_one_aux : forall (t : Token) (l : list Token),
  InT t l -> (1 <= count_token Token token_eq_dec t l)%nat.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hin.
  - exact (match Hin with end).
  - cbn [count_token].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + apply le_n_S. apply Nat.le_0_l.
    + inversion Hin as [| x0 l0 Hin2]; subst.
      * exact (match Hnyt id_refl with end).
      * exact (IH Hin2).
Qed.

Lemma alm_k_ge_one : (1 <= alm_k)%nat.
Proof.
  unfold alm_k. exact (alm_count_ge_one_aux m vocab m_in_vocab).
Qed.

Lemma alm_k_pos : real_lt real_zero (real_of_nat alm_k).
Proof.
  destruct alm_k as [| j] eqn:Hk.
  - exfalso.
    assert (Hc := alm_k_ge_one). rewrite Hk in Hc. inversion Hc.
  - apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat j))
             (real_of_nat (Datatypes.S j))).
    + apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat j))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* Per-copy share: 1/k. *)
Definition alm_invk : Real :=
  real_inv_pos (real_of_nat alm_k) alm_k_pos.

(* The uniform target on the copies: u(m) = 1/k and u(x) = 0 off m. *)
Definition alm_uniform (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => alm_invk
  | inr _ => real_zero
  end.

(* The m-switch function: branch c1 on the copies, branch c2 elsewhere;
   an auxiliary construction for the sum identities. *)
Definition alm_switch (c1 c2 : Real) (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => c1
  | inr _ => c2
  end.

(* Sum identity for the m-switch, the combinatorial core of the limit
   theorem: the sum of switch(c,g) over vocab equals k*c plus the sum
   of switch(0,g) over vocab.  Induction on the vocabulary list; the
   copy branch folds real_distrib with the definitional unfolding of
   of_nat (S n), the other branch uses commutativity and associativity
   of plus. *)

(* The two lemmas below complete the m-switch sum identity.  The
   induction runs on the explicit list vl; the section variables are
   fixed by the context, so vocab itself is not inducted on.  The
   algebra rests on real_list_sum and real_of_nat (S08: O maps to 0
   and S n to 1 + of_nat n by definitional folding), the real_eq
   reflexivity/symmetry/transitivity trio, real_plus_comm/assoc/zero,
   real_mult_zero/one, real_distrib (S02), real_distrib_r (S09) and
   RealSetoid.real_eq_plus_compat (S07).  real_eq is a Set-level
   equality, so both statement faces stay free of propositional
   premises. *)

Lemma swg_switch_sum_gen : forall (c g : Real) (vl : list Token),
  real_eq (real_list_sum Token (alm_switch c g) vl)
    (real_plus
       (real_mult (real_of_nat (count_token Token token_eq_dec m vl)) c)
       (real_list_sum Token (alm_switch real_zero g) vl)).
Proof.
  intros c g vl. induction vl as [| y rest IH].
  - (* empty list: 0 == 0*c + 0, as real_of_nat O folds to real_zero *)
    cbn [real_list_sum count_token alm_switch real_of_nat].
    apply (real_eq_trans _ (real_plus real_zero real_zero) _).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_zero real_zero
               (real_mult real_zero c) real_zero).
      * apply (real_eq_trans _ (real_mult c real_zero) _).
        -- apply (real_eq_sym (real_mult c real_zero) real_zero).
           apply (real_mult_zero c).
        -- apply (real_mult_comm c real_zero).
      * apply real_eq_refl.
  - cbn [real_list_sum count_token]. unfold alm_switch.
    destruct (token_eq_dec y m) as [Hym | Hnym].
    + (* copy branch: of_nat (S k) folds to 1 + of_nat k; the core is
         (1+a)*c == c + a*c, by right distributivity with the left
         unit crossing through commutativity *)
      cbn [real_of_nat].
      assert (Hcore : real_eq
                (real_mult (real_plus real_one
                              (real_of_nat
                                 (count_token Token token_eq_dec m rest))) c)
                (real_plus c
                   (real_mult (real_of_nat
                                 (count_token Token token_eq_dec m rest)) c))).
      { apply (real_eq_trans _
            (real_plus (real_mult real_one c)
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)) _).
        - apply (real_eq_sym
              (real_plus (real_mult real_one c)
                         (real_mult
                            (real_of_nat
                               (count_token Token token_eq_dec m rest)) c))
              (real_mult (real_plus real_one
                            (real_of_nat
                               (count_token Token token_eq_dec m rest))) c)).
          apply (real_distrib_r real_one
                   (real_of_nat (count_token Token token_eq_dec m rest)) c).
        - apply (RealSetoid.real_eq_plus_compat (real_mult real_one c)
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)
                   c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)).
          + apply (real_eq_trans _ (real_mult c real_one) _).
            * apply (real_mult_comm real_one c).
            * apply (real_mult_one c).
          + apply real_eq_refl. }
      apply (real_eq_trans _
        (real_plus c
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alm_switch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_list_sum Token (alm_switch c g) rest) c
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus c
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alm_switch real_zero g) rest)) _).
        -- apply (real_plus_assoc c
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c))
                (real_plus real_zero
                   (real_list_sum Token (alm_switch real_zero g) rest))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alm_switch real_zero g) rest)
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym
                         (real_plus real_zero
                            (real_list_sum Token (alm_switch real_zero g)
                               rest))
                         (real_list_sum Token (alm_switch real_zero g)
                            rest)).
                 apply (real_eq_trans _
                           (real_plus
                              (real_list_sum Token (alm_switch real_zero g)
                                 rest) real_zero) _).
                 apply (real_plus_comm real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest)).
                 apply (real_plus_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest))
                       (real_mult
                          (real_plus real_one
                             (real_of_nat
                                (count_token Token token_eq_dec m rest))) c)
                       (real_plus real_zero
                          (real_list_sum Token (alm_switch real_zero g)
                             rest))).
              ** apply (real_eq_sym
                          (real_mult
                             (real_plus real_one
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest)))
                             c)
                          (real_plus c
                             (real_mult
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest))
                                c))).
                 exact Hcore.
              ** apply real_eq_refl.
    + (* non-copy branch: the induction premise with assoc and comm
           swaps the middle summand *)
      apply (real_eq_trans _
        (real_plus g
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alm_switch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat g
                 (real_list_sum Token (alm_switch c g) rest) g
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus g
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alm_switch real_zero g) rest)) _).
        -- apply (real_plus_assoc g
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alm_switch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c) g)
                (real_list_sum Token (alm_switch real_zero g) rest)) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus g
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alm_switch real_zero g) rest)
                       (real_plus
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          g)
                       (real_list_sum Token (alm_switch real_zero g) rest)).
              ** apply (real_plus_comm g
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)).
              ** apply real_eq_refl.
           ++ apply (real_eq_sym
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_plus g
                       (real_list_sum Token (alm_switch real_zero g)
                          rest)))
                 (real_plus
                    (real_plus
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c) g)
                    (real_list_sum Token (alm_switch real_zero g) rest))).
              ** apply (real_plus_assoc
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          g
                          (real_list_sum Token (alm_switch real_zero g)
                             rest)).
Qed.

(* Closing lemma: instantiate the general identity at vocab, where
   alm_k is exactly count_token m vocab. *)
Lemma swg_switch_sum : forall c g : Real,
  real_eq (real_list_sum Token (alm_switch c g) vocab)
    (real_plus (real_mult (real_of_nat alm_k) c)
               (real_list_sum Token (alm_switch real_zero g) vocab)).
Proof.
  intros c g. unfold alm_k.
  apply (swg_switch_sum_gen c g vocab).
Qed.

End AlmUniform.

Section AluChain.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable gamma : Real.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* Abbreviation for the hard-attention weight: w_T cited argument-wise
   after the section close, its premise carried explicitly. *)
Definition alu_w (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  w_T Token vocab vocab_nonempty z T Ht x.

(* Function-form m-switch: the constant c on the copies, g x elsewhere.
   The slots c : Real and g : Token -> Real generalize the two constant
   slots of alm_switch to a function payload. *)
Definition alu_mswitch (c : Real) (g : Token -> Real) (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => c
  | inr _ => g x
  end.

(* The off-copy mass M: the vocab sum of switch(0, w_T). *)
Definition alu_M (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Token (alu_mswitch real_zero (alu_w T Ht)) vocab.

(* ---------- function-form m-switch sum identity ---------- *)
(* The sum of alu_mswitch c g equals count(m)*c plus the sum of
   alu_mswitch 0 g, by induction on the explicit list vl: the empty
   list is the zero case, the copy branch folds of_nat (S n)
   definitionally with right distributivity and the left unit via
   commutativity, the non-copy branch swaps the middle summand.  The
   payload g is a function, the function-slot completion of the
   constant-payload switch. *)

Lemma alu_switch_sum_fun : forall (c : Real) (g : Token -> Real) (vl : list Token),
  real_eq (real_list_sum Token (alu_mswitch c g) vl)
    (real_plus
       (real_mult (real_of_nat (count_token Token token_eq_dec m vl)) c)
       (real_list_sum Token (alu_mswitch real_zero g) vl)).
Proof.
  intros c g vl. induction vl as [| y rest IH].
  - (* empty list: 0 == 0*c + 0, as real_of_nat O folds to real_zero *)
    cbn [real_list_sum count_token real_of_nat].
    apply (real_eq_trans _ (real_plus real_zero real_zero) _).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_zero real_zero
               (real_mult real_zero c) real_zero).
      * apply (real_eq_trans _ (real_mult c real_zero) _).
        -- apply (real_eq_sym (real_mult c real_zero) real_zero).
           apply (real_mult_zero c).
        -- apply (real_mult_comm c real_zero).
      * apply real_eq_refl.
  - cbn [real_list_sum count_token]. unfold alu_mswitch.
    destruct (token_eq_dec y m) as [Hym | Hnym].
    + (* copy branch: of_nat (S k) folds to 1 + of_nat k; the core is
         (1+a)*c == c + a*c, by right distributivity with the left
         unit crossing through commutativity *)
      cbn [real_of_nat].
      assert (Hcore : real_eq
                (real_mult (real_plus real_one
                              (real_of_nat
                                 (count_token Token token_eq_dec m rest))) c)
                (real_plus c
                   (real_mult (real_of_nat
                                 (count_token Token token_eq_dec m rest)) c))).
      { apply (real_eq_trans _
            (real_plus (real_mult real_one c)
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)) _).
        - apply (real_eq_sym
              (real_plus (real_mult real_one c)
                         (real_mult
                            (real_of_nat
                               (count_token Token token_eq_dec m rest)) c))
              (real_mult (real_plus real_one
                            (real_of_nat
                               (count_token Token token_eq_dec m rest))) c)).
          apply (real_distrib_r real_one
                   (real_of_nat (count_token Token token_eq_dec m rest)) c).
        - apply (RealSetoid.real_eq_plus_compat (real_mult real_one c)
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)
                   c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)).
          + apply (real_eq_trans _ (real_mult c real_one) _).
            * apply (real_mult_comm real_one c).
            * apply (real_mult_one c).
          + apply real_eq_refl. }
      apply (real_eq_trans _
        (real_plus c
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alu_mswitch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_list_sum Token (alu_mswitch c g) rest) c
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus c
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alu_mswitch real_zero g) rest)) _).
        -- apply (real_plus_assoc c
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c))
                (real_plus real_zero
                   (real_list_sum Token (alu_mswitch real_zero g)
                      rest))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym
                         (real_plus real_zero
                            (real_list_sum Token (alu_mswitch real_zero g)
                               rest))
                         (real_list_sum Token (alu_mswitch real_zero g)
                            rest)).
                 apply (real_eq_trans _
                           (real_plus
                              (real_list_sum Token (alu_mswitch real_zero g)
                                 rest) real_zero) _).
                 apply (real_plus_comm real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest)).
                 apply (real_plus_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest))
                       (real_mult
                          (real_plus real_one
                             (real_of_nat
                                (count_token Token token_eq_dec m rest))) c)
                       (real_plus real_zero
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest))).
              ** apply (real_eq_sym
                          (real_mult
                             (real_plus real_one
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest)))
                             c)
                          (real_plus c
                             (real_mult
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest))
                                c))).
                 exact Hcore.
              ** apply real_eq_refl.
    + (* non-copy branch: the induction premise with assoc and comm
           swaps the middle summand *)
      apply (real_eq_trans _
        (real_plus (g y)
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (alu_mswitch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat (g y)
                 (real_list_sum Token (alu_mswitch c g) rest) (g y)
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus (g y)
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (alu_mswitch real_zero g) rest)) _).
        -- apply (real_plus_assoc (g y)
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (alu_mswitch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c) (g y))
                (real_list_sum Token (alu_mswitch real_zero g) rest)) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (g y)
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)
                       (real_plus
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          (g y))
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)).
              ** apply (real_plus_comm (g y)
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)).
              ** apply real_eq_refl.
           ++ apply (real_eq_sym
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_plus (g y)
                       (real_list_sum Token (alu_mswitch real_zero g)
                          rest)))
                 (real_plus
                    (real_plus
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)
                       (g y))
                    (real_list_sum Token (alu_mswitch real_zero g)
                       rest))).
              ** apply (real_plus_assoc
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          (g y)
                          (real_list_sum Token (alu_mswitch real_zero g)
                             rest)).
Qed.

(* ---------- part 0: switch (f m, f) is pointwise f (mass-split face) ---------- *)

Lemma alu_switch_self_eq : forall (f : Token -> Real) (x : Token),
  real_eq (alu_mswitch (f m) f x) (f x).
Proof.
  intros f x. unfold alu_mswitch.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* Id is not the setoid equality: bridge through id_cong, id_sym
       and aid_real_eq *)
    exact (aid_real_eq (f m) (f x) (id_sym (id_cong f Hxm))).
  - apply real_eq_refl.
Qed.

Lemma alu_sum_switch_self : forall f : Token -> Real,
  real_eq (real_list_sum Token (alu_mswitch (f m) f) vocab)
          (real_list_sum Token f vocab).
Proof.
  intro f. apply real_list_sum_ext. intro w.
  exact (alu_switch_self_eq f w).
Qed.

(* ---------- part 1: minus_r restores by right cancellation,
   (a - b) + b == a ---------- *)

Lemma alu_minus_r_plus : forall a b : Real,
  real_eq (real_plus (real_minus_r a b) b) a.
Proof.
  intros a b. unfold real_minus_r.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) b)) _).
  - (* (a + -b) + b == a + (-b + b): the right-nested form is the
       symmetric image of associativity *)
    apply (real_eq_sym (real_plus a (real_plus (real_opp b) b))
                       (real_plus (real_plus a (real_opp b)) b)).
    apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a (real_plus b (real_opp b))) _).
    + apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) b) a (real_plus b (real_opp b))).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply (real_eq_trans _ (real_plus a real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat a
                 (real_plus b (real_opp b)) a real_zero).
        -- apply real_eq_refl.
        -- apply real_plus_opp.
      * apply real_plus_zero.
Qed.

(* ---------- part 2: right cancellation of addition on Real ----------
   c + a == c + b yields a == b.  Add -c on both sides by
   compatibility, fold (-c + c) to 0 by assoc/comm and 0 + d to d; no
   order decision enters, the argument is pure equational algebra. *)

Lemma alu_plus_reg_r : forall a b c : Real,
  real_eq (real_plus c a) (real_plus c b) -> real_eq a b.
Proof.
  intros a b c H.
  assert (Hshift : forall d : Real,
    real_eq (real_plus (real_opp c) (real_plus c d)) d).
  { intro d.
    apply (real_eq_trans _ (real_plus (real_plus (real_opp c) c) d) _).
    - apply (real_plus_assoc (real_opp c) c d).
    - apply (real_eq_trans _ (real_plus (real_plus c (real_opp c)) d) _).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_opp c) c) d
                 (real_plus c (real_opp c)) d).
        * apply real_plus_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _ (real_plus real_zero d) _).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_plus c (real_opp c)) d real_zero d).
          -- apply real_plus_opp.
          -- apply real_eq_refl.
        * apply (real_eq_trans _ (real_plus d real_zero) _).
          -- apply real_plus_comm.
          -- apply real_plus_zero. }
  apply (real_eq_trans a (real_plus (real_opp c) (real_plus c a)) b).
  - exact (real_eq_sym _ _ (Hshift a)).
  - apply (real_eq_trans (real_plus (real_opp c) (real_plus c a))
             (real_plus (real_opp c) (real_plus c b)) b).
    + apply (RealSetoid.real_eq_plus_compat (real_opp c) (real_plus c a)
               (real_opp c) (real_plus c b)).
      * apply real_eq_refl.
      * exact H.
    + exact (Hshift b).
Qed.

(* ---------- part 3: M >= 0, the switch preserves nonnegativity and
   sum_nonneg sums it ---------- *)

Lemma alu_M_nonneg : forall (T : Real) (Ht : real_lt real_zero T),
  real_le real_zero (alu_M T Ht).
Proof.
  intros T Ht. unfold alu_M.
  apply (sum_nonneg_aux Token (alu_mswitch real_zero (alu_w T Ht)) vocab).
  intro y. unfold alu_mswitch.
  destruct (token_eq_dec y m) as [Hym | Hnym].
  - apply real_le_refl.
  - apply real_le_from_lt_aux.
    exact (w_T_pos Token vocab vocab_nonempty z T Ht y).
Qed.

(* ---------- part 4: w_T(m) <= 1/k ----------
   Chain: k*w(m) + M == sum w == 1 together with M >= 0 gives
   k*w(m) <= 1 == k*(1/k); right-multiplying by the positive 1/k
   preserves order, and eq_mult_inv_absorb reorders both sides to
   close the bound. *)

Lemma alu_wm_le_invk : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (alu_w T Ht m) (alm_invk Token vocab token_eq_dec m m_in_vocab).
Proof.
  intros T Ht.
  assert (Hk1 : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                             (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        real_one)
    by exact (real_inv_pos_correct (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
  (* step 1: k*w(m) <= 1 *)
  assert (Hle1 : real_le (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (alu_w T Ht m))
                         real_one).
  { apply (RealSetoid.real_le_id_r
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m)) (alu_w T Ht m))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))
                        (alu_M T Ht))
             real_one).
    - apply (real_eq_trans
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (alu_w T Ht m))
                          (alu_M T Ht))
               (real_list_sum Token (alu_w T Ht) vocab) real_one).
      + apply (real_eq_trans
                 (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                       (alu_w T Ht m))
                            (alu_M T Ht))
                 (real_list_sum Token
                    (alu_mswitch (alu_w T Ht m) (alu_w T Ht)) vocab) _).
        * exact (real_eq_sym _ _
                   (alu_switch_sum_fun (alu_w T Ht m) (alu_w T Ht) vocab)).
        * exact (alu_sum_switch_self (alu_w T Ht)).
      + exact (w_T_sum_one Token vocab vocab_nonempty z T Ht).
    - apply (real_le_plus_nonneg_r_aux _ _ (alu_M_nonneg T Ht)). }
  (* step 2: k*w(m) <= k*(1/k), rewriting 1 == k*(1/k) and applying
     step 1 *)
  assert (Hle2 : real_le (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (alu_w T Ht m))
                         (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))).
  { apply (RealSetoid.real_le_id_r
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m)) (alu_w T Ht m))
             real_one
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))).
    - exact (real_eq_sym _ _ Hk1).
    - exact Hle1. }
  (* step 3: right-multiplication by the positive 1/k preserves order *)
  assert (Hle4 : real_le (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                (alu_w T Ht m))
                                     (alm_invk Token vocab token_eq_dec m m_in_vocab))
                         (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                (alm_invk Token vocab token_eq_dec m m_in_vocab))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))).
  { apply (real_le_mult_compat _ _
             (alm_invk Token vocab token_eq_dec m m_in_vocab)).
    - exact (real_inv_pos_pos (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
    - exact Hle2. }
  (* step 4: eq_mult_inv_absorb reorders both sides and the order
     adaptation closes *)
  apply (RealSetoid.real_le_id_l (alu_w T Ht m)
           (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                 (alu_w T Ht m))
                      (alm_invk Token vocab token_eq_dec m m_in_vocab))
           (alm_invk Token vocab token_eq_dec m m_in_vocab)).
  - apply (real_eq_sym _ _ (eq_mult_inv_absorb
              (real_of_nat (alm_k Token vocab token_eq_dec m))
              (alu_w T Ht m)
              (alm_k_pos Token vocab token_eq_dec m m_in_vocab) Hk1)).
  - apply (RealSetoid.real_le_id_r
             (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alu_w T Ht m))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))
             (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))
             (alm_invk Token vocab token_eq_dec m m_in_vocab)).
    + exact (eq_mult_inv_absorb
               (real_of_nat (alm_k Token vocab token_eq_dec m))
               (alm_invk Token vocab token_eq_dec m m_in_vocab)
               (alm_k_pos Token vocab token_eq_dec m m_in_vocab) Hk1).
    + exact Hle4.
Qed.

(* ============================================================ *)
(* Chain link 1.  alu_mass_split: the vocab mass split.               *)
(*   The sum of w_T equals k*w_T(m) + M; the pointwise self-equality  *)
(*   feeds alu_switch_sum_fun directly.                               *)
(* ============================================================ *)

Theorem alu_mass_split : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_list_sum Token (alu_w T Ht) vocab)
          (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                (alu_w T Ht m))
                     (alu_M T Ht)).
Proof.
  intros T Ht.
  apply (real_eq_trans
           (real_list_sum Token (alu_w T Ht) vocab)
           (real_list_sum Token
              (alu_mswitch (alu_w T Ht m) (alu_w T Ht)) vocab) _).
  - apply (real_eq_sym _ _ (alu_sum_switch_self (alu_w T Ht))).
  - exact (alu_switch_sum_fun (alu_w T Ht m) (alu_w T Ht) vocab).
Qed.

(* ============================================================ *)
(* Chain link 2.  alu_deficit_eq: the deficit identity.                *)
(*   k*(1/k - w_T(m)) == M: the deficit equals the overflow.           *)
(*   Chain: D + w(m) == 1/k by the minus_r right cancellation, so      *)
(*   k*(D + w(m)) == k*(1/k) == 1 == k*w(m) + M by link 1 with         *)
(*   sum w == 1; commutativity then lets alu_plus_reg_r cancel.        *)
(* ============================================================ *)

Theorem alu_deficit_eq : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                   (alu_w T Ht m)))
          (alu_M T Ht).
Proof.
  intros T Ht.
  assert (Hk1 : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                             (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        real_one)
    by exact (real_inv_pos_correct (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
  (* k*w(m) + M == 1, by link 1 and sum w == 1 *)
  assert (Hsum1 : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (alu_w T Ht m))
                                      (alu_M T Ht))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))
                        (alu_M T Ht))
             (real_list_sum Token (alu_w T Ht) vocab) _).
    - exact (real_eq_sym _ _ (alu_mass_split T Ht)).
    - exact (w_T_sum_one Token vocab vocab_nonempty z T Ht). }
  (* D + w(m) == 1/k, the right-cancellation restore of
     D := 1/k - w(m) *)
  assert (Hcan : real_eq (real_plus (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m))
                                    (alu_w T Ht m))
                         (alm_invk Token vocab token_eq_dec m m_in_vocab))
    by exact (alu_minus_r_plus _ _).
  (* k*(D + w(m)) == k*D + k*w(m), distributivity in the left factor *)
  assert (Hdist : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (real_plus (real_minus_r
                                            (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                            (alu_w T Ht m))
                                         (alu_w T Ht m)))
                  (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                        (real_minus_r
                                           (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                           (alu_w T Ht m)))
                             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                        (alu_w T Ht m))))
    by exact (real_distrib _ _ _).
  (* k*D + k*w(m) == k*(D + w(m)) == k*(1/k) == 1 *)
  assert (Hone2 : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (real_minus_r
                                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                    (alu_w T Ht m)))
                                      (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (alu_w T Ht m)))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m)))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m)))
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                        (real_plus (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m))
                                   (alu_w T Ht m))) _).
    - exact (real_eq_sym _ _ Hdist).
    - apply (real_eq_trans
               (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                          (real_plus (real_minus_r
                                        (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                        (alu_w T Ht m))
                                     (alu_w T Ht m)))
               (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                          (alm_invk Token vocab token_eq_dec m m_in_vocab)) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_of_nat (alm_k Token vocab token_eq_dec m))
                 (real_plus (real_minus_r
                               (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (alu_w T Ht m))
                            (alu_w T Ht m))
                 (real_of_nat (alm_k Token vocab token_eq_dec m))
                 (alm_invk Token vocab token_eq_dec m m_in_vocab)).
        * apply real_eq_refl.
        * exact Hcan.
      + exact Hk1. }
  (* commutativity, the passage through 1 and right cancellation give
     k*D == M *)
  assert (Hswap : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (alu_w T Ht m))
                                      (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (real_minus_r
                                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                    (alu_w T Ht m))))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m))))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (alu_w T Ht m)))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (alu_w T Ht m))) _).
    - apply real_plus_comm.
    - exact Hone2. }
  exact (alu_plus_reg_r _ _ _
           (real_eq_trans _ _ _ Hswap (real_eq_sym _ _ Hsum1))).
Qed.

(* ============================================================ *)
(* Chain link 3.  alu_mass_rest_le: upper bound for the off-copy mass. *)
(*   M <= n*e^(-gamma/T); pointwise, the copy branch has 0 <= decay    *)
(*   (the exponential stays positive) and the other branch reuses      *)
(*   core_decay_bound; the sum step is sum_nonneg_le_const_aux with    *)
(*   n = length vocab.                                                 *)
(* ============================================================ *)

Theorem alu_mass_rest_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (alu_M T Ht)
          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)).
Proof.
  intros T Ht. unfold alu_M.
  apply (sum_nonneg_le_const_aux Token
           (alu_mswitch real_zero (alu_w T Ht))
           (decay_T gamma T Ht) vocab).
  intros x Hin. unfold alu_mswitch.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* copy branch: 0 <= decay_T, the exponential stays positive *)
    apply real_le_from_lt_aux. unfold decay_T. apply cauchy_real_exp_pos.
  - (* non-copy branch: w_T(x) <= decay_T, the decay bound that needs
       no uniqueness premise on the maximizer count *)
    exact (core_decay_bound Token vocab vocab_nonempty z m m_in_vocab
              gamma gap_le T Ht x Hnxm).
Qed.

(* ---------- part 5: pointwise |u - w| == switch(D, w) ----------
   u = alm_uniform; on the copies D := 1/k - w(m) >= 0 (part 4), so
   real_abs_minus_r_nonneg_aux folds the absolute value; on the other
   tokens |0 - w(x)| == w(x) since w >= 0.  The two unfolds precede
   the case split. *)

Lemma alu_abs_pointwise : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  real_eq (real_abs (real_minus_r (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                                  (alu_w T Ht x)))
          (alu_mswitch (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (alu_w T Ht m))
                       (alu_w T Ht) x).
Proof.
  intros T Ht x.
  assert (Hwmle : real_le (alu_w T Ht m)
                    (alm_invk Token vocab token_eq_dec m m_in_vocab))
    by exact (alu_wm_le_invk T Ht).
  unfold alu_mswitch, alm_uniform.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* copy branch: transport along Id x == m through the id_cong
       chain, then |D| == D by the fold for D >= 0 *)
    assert (HTx : real_eq (real_minus_r
                             (alm_invk Token vocab token_eq_dec m m_in_vocab)
                             (alu_w T Ht x))
                          (real_minus_r
                             (alm_invk Token vocab token_eq_dec m m_in_vocab)
                             (alu_w T Ht m)))
      by exact (aid_real_eq _ _
                  (id_cong (fun t =>
                              real_minus_r
                                (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                t)
                     (id_cong (alu_w T Ht) Hxm))).
    apply (real_eq_trans
             (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (alu_w T Ht x)))
             (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (alu_w T Ht m))) _).
    + exact (real_abs_eq_compat _ _ HTx).
    + (* |1/k - w(m)| == |-(w(m) - 1/k)| == |w(m) - 1/k| == 1/k - w(m) *)
      apply (real_eq_trans
               (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                       (alu_w T Ht m)))
               (real_abs (real_opp (real_minus_r (alu_w T Ht m)
                                                 (alm_invk Token vocab token_eq_dec m m_in_vocab)))) _).
      * (* 1/k - w(m) == -(w(m) - 1/k): comm, opp_opp and opp_plus
           flip the sign *)
        apply real_abs_eq_compat.
        apply (real_eq_trans
                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (alu_w T Ht m))
                 (real_plus (real_opp (alu_w T Ht m))
                            (alm_invk Token vocab token_eq_dec m m_in_vocab)) _).
        -- apply real_plus_comm.
        -- apply (real_eq_trans
                    (real_plus (real_opp (alu_w T Ht m))
                               (alm_invk Token vocab token_eq_dec m m_in_vocab))
                    (real_plus (real_opp (alu_w T Ht m))
                               (real_opp (real_opp
                                            (alm_invk Token vocab token_eq_dec m m_in_vocab)))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_opp (alu_w T Ht m))
                       (alm_invk Token vocab token_eq_dec m m_in_vocab)
                       (real_opp (alu_w T Ht m))
                       (real_opp (real_opp
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym _ _
                       (real_opp_opp
                          (alm_invk Token vocab token_eq_dec m m_in_vocab))).
           ++ apply (real_eq_sym _ _ (real_opp_plus (alu_w T Ht m)
                        (real_opp (alm_invk Token vocab token_eq_dec m m_in_vocab)))).
      * (* |-(w(m) - 1/k)| == |w(m) - 1/k| == 1/k - w(m), with part 4
           entering as the nonnegativity premise *)
        apply (real_eq_trans
                 (real_abs (real_opp (real_minus_r (alu_w T Ht m)
                                                   (alm_invk Token vocab token_eq_dec m m_in_vocab))))
                 (real_abs (real_minus_r (alu_w T Ht m)
                                         (alm_invk Token vocab token_eq_dec m m_in_vocab))) _).
        -- exact (real_abs_opp (real_minus_r (alu_w T Ht m)
                              (alm_invk Token vocab token_eq_dec m m_in_vocab))).
        -- exact (real_abs_minus_r_nonneg_aux (alu_w T Ht m)
                    (alm_invk Token vocab token_eq_dec m m_in_vocab) Hwmle).
  - (* non-copy branch: |0 - w(x)| == |-w(x)| == w(x) since w >= 0 *)
    apply (real_eq_trans
             (real_abs (real_minus_r real_zero (alu_w T Ht x)))
             (real_abs (real_opp (alu_w T Ht x))) _).
    + apply real_abs_eq_compat.
      apply (real_eq_trans
               (real_minus_r real_zero (alu_w T Ht x))
               (real_plus (real_opp (alu_w T Ht x)) real_zero) _).
      * apply real_plus_comm.
      * apply real_plus_zero.
    + apply (real_eq_trans (real_abs (real_opp (alu_w T Ht x)))
               (real_abs (alu_w T Ht x)) (alu_w T Ht x)).
      * apply real_abs_opp.
      * apply (real_abs_pos_req (alu_w T Ht x)
                  (w_T_pos Token vocab vocab_nonempty z T Ht x)).
Qed.

(* ============================================================ *)
(* Chain link 4.  alu_l1_le: closing the L1 upper bound.                *)
(*   L1(w_T, u) = sum |u - w| == 2M <= 2*(n*decay), with 2n*decay       *)
(*   written directly as n*decay + n*decay.  Assembly: the pointwise    *)
(*   abs folding of part 5, alu_switch_sum_fun as in link 1, the        *)
(*   deficit identity of link 2 (k*D == M) and link 3.                  *)
(* ============================================================ *)

Theorem alu_l1_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (real_list_sum Token
             (fun x : Token => real_abs (real_minus_r
                            (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                            (alu_w T Ht x))) vocab)
          (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                     (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))).
Proof.
  intros T Ht.
  (* L1 == k*D + M by the pointwise folding and the function-form
     switch sum identity, hence == M + M <= n*d + n*d *)
  apply (real_le_trans
           (real_list_sum Token
              (fun x : Token => real_abs (real_minus_r
                             (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                             (alu_w T Ht x))) vocab)
           (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                               (alu_w T Ht m)))
                      (alu_M T Ht))
           (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                      (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
  - (* L1 <= k*D + M: the equational chain followed by a real_le_refl
       adaptation *)
    apply (RealSetoid.real_le_id_l
             (real_list_sum Token
                (fun x : Token => real_abs (real_minus_r
                               (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                               (alu_w T Ht x))) vocab)
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (alu_w T Ht m)))
                        (alu_M T Ht))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (alu_w T Ht m)))
                        (alu_M T Ht))).
    + apply (real_eq_trans
               (real_list_sum Token
                  (fun x : Token => real_abs (real_minus_r
                                 (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                                 (alu_w T Ht x))) vocab)
               (real_list_sum Token
                  (alu_mswitch (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                             (alu_w T Ht m))
                               (alu_w T Ht)) vocab)
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                   (alu_w T Ht m)))
                          (alu_M T Ht))).
      * apply real_list_sum_ext. intro w.
        exact (alu_abs_pointwise T Ht w).
      * exact (alu_switch_sum_fun
                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (alu_w T Ht m))
                 (alu_w T Ht) vocab).
    + apply real_le_refl.
  - (* k*D + M == M + M by link 2, then M + M <= n*d + n*d by
       link 3 applied twice *)
    apply (real_le_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (alu_w T Ht m)))
                        (alu_M T Ht))
             (real_plus (alu_M T Ht) (alu_M T Ht))
             (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                        (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
    + apply (RealSetoid.real_le_id_l
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                   (alu_w T Ht m)))
                          (alu_M T Ht))
               (real_plus (alu_M T Ht) (alu_M T Ht))
               (real_plus (alu_M T Ht) (alu_M T Ht))).
      * exact (RealSetoid.real_eq_plus_compat
                 (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                            (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                          (alu_w T Ht m)))
                 (alu_M T Ht) (alu_M T Ht) (alu_M T Ht)
                 (alu_deficit_eq T Ht) (real_eq_refl (alu_M T Ht))).
      * apply real_le_refl.
    + apply (real_le_trans
               (real_plus (alu_M T Ht) (alu_M T Ht))
               (real_plus (alu_M T Ht)
                          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))
               (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
      * apply real_le_plus_compat.
        -- apply real_le_refl.
        -- exact (alu_mass_rest_le T Ht).
      * apply real_le_plus_compat.
        -- exact (alu_mass_rest_le T Ht).
        -- apply real_le_refl.
Qed.

End AluChain.

(* ============================================================ *)
(* Section 2.9.  Closing the main statement: alm_uniform_limit.          *)
(*   For every eps > 0 there is T0 > 0 such that L1(w_T, u) <= eps for   *)
(*   all T with 0 < T < T0.  The mass-split chain gives L1 <= n*d +      *)
(*   n*d with d = e^(-gamma/T); the gap certificate, the copy count,     *)
(*   the uniform target and the switch core are the alm_ pieces of       *)
(*   Sections 1 and 2.  The threshold is T0 := gamma*delta with          *)
(*   delta := (eps/2)*(1/n): no logarithm on Real is at hand, so the     *)
(*   log-free route real_exp_ge_linear (e^t > 1+t) with monotonicity     *)
(*   of exp and delta*e^(gamma/T) >= delta*inv(delta) == 1 closes the    *)
(*   bound, with no nested inverses and no classical logic.              *)
(* ============================================================ *)

Theorem alm_uniform_limit :
  forall (Token : Set) (vocab : list Token)
    (vocab_nonempty : Not (Id vocab nil))
    (token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)))
    (z : Token -> Real)
    (m : Token) (m_in_vocab : InT m vocab)
    (gamma : Real) (gamma_pos : real_lt real_zero gamma)
    (gap_le : forall x : Token, Not (Id x m) ->
      real_le (real_plus (z x) gamma) (z m))
    (eps : Real),
    real_lt real_zero eps ->
    sigT (fun T0 =>
      And (real_lt real_zero T0)
        (forall (T : Real) (Ht : real_lt real_zero T),
          real_lt T T0 ->
          real_le
            (real_list_sum Token
               (fun x : Token =>
                  real_abs (real_minus_r
                    (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                    (w_T Token vocab vocab_nonempty z T Ht x)))
               vocab)
            eps)).
Proof.
  intros Token vocab vocab_nonempty token_eq_dec z m m_in_vocab gamma
    gamma_pos gap_le eps Heps.
  (* ---------- threshold material: the half, delta := (eps/2)*(1/n),
     T0 := gamma*delta ---------- *)
  assert (H2lt0 : real_lt real_zero (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
             (real_plus real_one real_one)).
    - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    - apply (real_lt_plus_compat_lt_le real_zero real_one
               real_zero real_one real_lt_zero_one).
      apply (real_le_from_lt_aux real_zero real_one real_lt_zero_one). }
  assert (Hnatpos : forall n : nat, (1 <= n)%nat ->
    real_lt real_zero (real_of_nat n)).
  { intros n Hn. destruct n as [| j].
    - lia.
    - apply (real_lt_eq_lt real_zero
               (real_plus real_one (real_of_nat j))
               (real_of_nat (Datatypes.S j))).
      + apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                 (real_plus real_one (real_of_nat j))).
        * apply real_eq_sym. apply real_plus_zero.
        * apply real_lt_plus_compat_lt_le.
          -- apply real_lt_zero_one.
          -- apply real_of_nat_nonneg_aux.
      + apply real_eq_refl. }
  assert (Hn1 : (1 <= length vocab)%nat).
  { destruct vocab as [| y rest].
    - exact (match vocab_nonempty id_refl with end).
    - cbn [length]. lia. }
  assert (Hnpos : real_lt real_zero (real_of_nat (length vocab)))
    by exact (Hnatpos (length vocab) Hn1).
  set (h2 := real_inv_pos (real_plus real_one real_one) H2lt0).
  assert (Hh2 : real_lt real_zero h2)
    by exact (real_inv_pos_pos (real_plus real_one real_one) H2lt0).
  set (HALF := real_mult eps h2).
  assert (HHALF : real_lt real_zero HALF)
    by exact (real_mult_pos_compat eps h2 Heps Hh2).
  set (invn := real_inv_pos (real_of_nat (length vocab)) Hnpos).
  assert (Hinvn : real_lt real_zero invn)
    by exact (real_inv_pos_pos (real_of_nat (length vocab)) Hnpos).
  set (delta := real_mult HALF invn).
  assert (Hdelta : real_lt real_zero delta)
    by exact (real_mult_pos_compat HALF invn HHALF Hinvn).
  exists (real_mult gamma delta).
  split.
  - exact (real_mult_pos_compat gamma delta gamma_pos Hdelta).
  - intros T Ht HTl.
    set (invT := real_inv_pos T Ht).
    assert (HinvT : real_lt real_zero invT)
      by exact (real_inv_pos_pos T Ht).
    set (u := real_mult invT gamma).
    assert (Hu : real_lt real_zero u)
      by exact (real_mult_pos_compat invT gamma HinvT gamma_pos).
    set (invd := real_inv_pos delta Hdelta).
    assert (Hinvd : real_lt real_zero invd)
      by exact (real_inv_pos_pos delta Hdelta).
    (* step 1: T*inv(delta) <= gamma; right-multiply T < gamma*delta by
       inv(delta) and fold delta*inv(delta) == 1 *)
    assert (Hs1 : real_le (real_mult T invd) gamma).
    { apply (real_le_trans (real_mult T invd)
               (real_mult (real_mult gamma delta) invd) gamma).
      - apply (real_le_mult_compat T (real_mult gamma delta) invd Hinvd).
        exact (real_le_from_lt_aux T (real_mult gamma delta) HTl).
      - apply (RealSetoid.real_eq_le _ _).
        apply (real_eq_trans (real_mult (real_mult gamma delta) invd)
                 (real_mult gamma (real_mult delta invd)) gamma).
        + apply (real_eq_sym _ _ (real_mult_assoc gamma delta invd)).
        + apply (real_eq_trans
                   (real_mult gamma (real_mult delta invd))
                   (real_mult gamma real_one) gamma).
          * apply (RealSetoid.real_eq_mult_compat gamma
                     (real_mult delta invd) gamma real_one).
            -- apply real_eq_refl.
            -- exact (real_inv_pos_correct delta Hdelta).
          * exact (real_mult_one gamma). }
    (* step 2: inv(delta) <= u := inv(T)*gamma; right-multiply step 1
       by inv(T) and fold inv(T)*T == 1 *)
    assert (Hs2 : real_le invd u).
    { apply (RealSetoid.real_le_id_l invd
               (real_mult invT (real_mult T invd)) u).
      - apply (real_eq_sym _ _).
        apply (real_eq_trans
                 (real_mult invT (real_mult T invd))
                 (real_mult real_one invd) invd).
        + apply (real_eq_trans
                   (real_mult invT (real_mult T invd))
                   (real_mult (real_mult invT T) invd)
                   (real_mult real_one invd)).
          * apply real_mult_assoc.
          * apply (RealSetoid.real_eq_mult_compat
                     (real_mult invT T) invd real_one invd).
            -- apply (real_eq_trans (real_mult invT T)
                       (real_mult T invT) real_one).
               ++ apply real_mult_comm.
               ++ exact (real_inv_pos_correct T Ht).
            -- apply real_eq_refl.
        + apply (real_eq_trans (real_mult real_one invd)
                   (real_mult invd real_one) invd).
          * apply real_mult_comm.
          * exact (real_mult_one invd).
      - exact (real_le_mult_compat_l_aux (real_mult T invd) gamma invT
                 HinvT Hs1). }
    (* step 3: inv(delta) <= e^u; the chain inv(delta) <= 1 + inv(delta)
       <= e^(inv(delta)) <= e^u uses real_exp_ge_linear and
       monotonicity *)
    assert (Hs3 : real_le invd (cauchy_real_exp u)).
    { assert (Hmid : real_le (real_plus real_one invd)
                       (cauchy_real_exp invd)).
      { exact (real_le_from_lt_aux (real_plus real_one invd)
                 (cauchy_real_exp invd) (real_exp_ge_linear invd Hinvd)). }
      apply (real_le_trans invd (cauchy_real_exp invd) (cauchy_real_exp u)).
      - apply (real_le_trans invd (real_plus real_one invd)
                 (cauchy_real_exp invd)).
        + apply (RealSetoid.real_le_id_l invd
                   (real_plus real_zero invd) (real_plus real_one invd)).
          * exact (real_eq_trans invd (real_plus invd real_zero)
                     (real_plus real_zero invd)
                     (real_eq_sym (real_plus invd real_zero) invd
                        (real_plus_zero invd))
                     (real_plus_comm invd real_zero)).
          * apply (real_le_plus_compat real_zero real_one invd invd).
            -- exact (real_le_from_lt_aux real_zero real_one
                        real_lt_zero_one).
            -- apply real_le_refl.
        + exact Hmid.
      - apply real_exp_le_mono. exact Hs2. }
    (* step 4: 1 <= delta*e^u; left-multiply step 3 by delta and fold
       delta*inv(delta) == 1 *)
    assert (Hs4 : real_le real_one (real_mult delta (cauchy_real_exp u))).
    { apply (RealSetoid.real_le_id_l real_one
               (real_mult delta invd) (real_mult delta (cauchy_real_exp u))).
      - exact (real_eq_sym (real_mult delta invd) real_one
                 (real_inv_pos_correct delta Hdelta)).
      - exact (real_le_mult_compat_l_aux invd (cauchy_real_exp u) delta
                 Hdelta Hs3). }
    (* step 5: d <= delta; d*e^u == 1 by exp_mult_opp_l, with step 4
       and cancellation through the positive inverse of e^u *)
    assert (Hs5 : real_le (decay_T gamma T Ht) delta).
    { set (E := cauchy_real_exp u).
      assert (HE : real_lt real_zero E) by exact (cauchy_real_exp_pos u).
      set (invE := real_inv_pos E HE).
      assert (HinvE : real_lt real_zero invE)
        by exact (real_inv_pos_pos E HE).
      assert (Hcancel : real_le (real_mult (decay_T gamma T Ht) E)
                                (real_mult delta E)).
      { apply (real_le_trans (real_mult (decay_T gamma T Ht) E)
                 real_one (real_mult delta E)).
        - apply (RealSetoid.real_eq_le _ _).
          exact (exp_mult_opp_l_aux u).
        - exact Hs4. }
      assert (Hrhs : real_eq (real_mult (real_mult delta E) invE) delta).
      { apply (real_eq_trans
                 (real_mult (real_mult delta E) invE)
                 (real_mult delta (real_mult E invE)) delta).
        - apply (real_eq_sym _ _ (real_mult_assoc delta E invE)).
        - apply (real_eq_trans _
                   (real_mult delta real_one) _).
          + apply (RealSetoid.real_eq_mult_compat delta
                     (real_mult E invE) delta real_one).
            * apply real_eq_refl.
            * exact (real_inv_pos_correct E HE).
          + exact (real_mult_one delta). }
      apply (RealSetoid.real_le_id_l (decay_T gamma T Ht)
               (real_mult (real_mult (decay_T gamma T Ht) E) invE) delta).
      - apply (real_eq_sym _ _).
        apply (real_eq_trans
                 (real_mult (real_mult (decay_T gamma T Ht) E) invE)
                 (real_mult (decay_T gamma T Ht) (real_mult E invE))
                 (decay_T gamma T Ht)).
        + apply (real_eq_sym _ _
                   (real_mult_assoc (decay_T gamma T Ht) E invE)).
        + apply (real_eq_trans _
                   (real_mult (decay_T gamma T Ht) real_one) _).
          * apply (RealSetoid.real_eq_mult_compat (decay_T gamma T Ht)
                     (real_mult E invE) (decay_T gamma T Ht) real_one).
            -- apply real_eq_refl.
            -- exact (real_inv_pos_correct E HE).
          * exact (real_mult_one (decay_T gamma T Ht)).
      - apply (RealSetoid.real_le_id_r
                 (real_mult (real_mult (decay_T gamma T Ht) E) invE)
                 (real_mult (real_mult delta E) invE) delta).
        + exact Hrhs.
        + apply (real_le_mult_compat (real_mult (decay_T gamma T Ht) E)
                   (real_mult delta E) invE HinvE Hcancel). }
    (* steps 6-7: L1 <= n*d + n*d <= n*delta + n*delta == eps, the
       chain closes *)
    apply (real_le_trans
             (real_list_sum Token
                (fun x : Token => real_abs (real_minus_r
                   (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                   (alu_w Token vocab vocab_nonempty z T Ht x))) vocab)
             (real_plus (real_mult (real_of_nat (length vocab)) delta)
                        (real_mult (real_of_nat (length vocab)) delta))
             eps).
    + apply (real_le_trans
               (real_list_sum Token
                  (fun x : Token => real_abs (real_minus_r
                     (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                     (alu_w Token vocab vocab_nonempty z T Ht x))) vocab)
               (real_plus
                  (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht))
                  (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht)))
               (real_plus (real_mult (real_of_nat (length vocab)) delta)
                          (real_mult (real_of_nat (length vocab)) delta))).
      * exact (alu_l1_le Token vocab vocab_nonempty token_eq_dec z
                 m m_in_vocab gamma gap_le T Ht).
      * apply (real_le_plus_compat
                 (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht))
                 (real_mult (real_of_nat (length vocab)) delta)
                 (real_mult (real_of_nat (length vocab))
                             (decay_T gamma T Ht))
                 (real_mult (real_of_nat (length vocab)) delta)).
        -- apply (RealSetoid.real_le_id_l
                    (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                    (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                    (real_mult (real_of_nat (length vocab)) delta)).
           ++ apply real_mult_comm.
           ++ apply (RealSetoid.real_le_id_r
                       (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                       (real_mult delta (real_of_nat (length vocab)))
                       (real_mult (real_of_nat (length vocab)) delta)).
              ** apply real_mult_comm.
              ** exact (real_le_mult_compat (decay_T gamma T Ht) delta
                          (real_of_nat (length vocab)) Hnpos Hs5).
        -- apply (RealSetoid.real_le_id_l
                    (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                    (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                    (real_mult (real_of_nat (length vocab)) delta)).
           ++ apply real_mult_comm.
           ++ apply (RealSetoid.real_le_id_r
                       (real_mult (decay_T gamma T Ht) (real_of_nat (length vocab)))
                       (real_mult delta (real_of_nat (length vocab)))
                       (real_mult (real_of_nat (length vocab)) delta)).
              ** apply real_mult_comm.
              ** exact (real_le_mult_compat (decay_T gamma T Ht) delta
                          (real_of_nat (length vocab)) Hnpos Hs5).
    + apply (RealSetoid.real_eq_le _ _).
      assert (Hnd : real_eq
                 (real_mult (real_of_nat (length vocab)) delta) HALF).
      { apply (real_eq_trans
                 (real_mult (real_of_nat (length vocab)) delta)
                 (real_mult HALF
                    (real_mult (real_of_nat (length vocab)) invn)) HALF).
        - apply (real_eq_trans _
                   (real_mult (real_mult HALF (real_of_nat (length vocab)))
                      invn) _).
          * apply (real_eq_trans _
                     (real_mult (real_mult (real_of_nat (length vocab)) HALF)
                        invn) _).
            -- apply real_mult_assoc.
            -- apply (RealSetoid.real_eq_mult_compat
                       (real_mult (real_of_nat (length vocab)) HALF) invn
                       (real_mult HALF (real_of_nat (length vocab))) invn).
               ++ apply (real_mult_comm (real_of_nat (length vocab)) HALF).
               ++ apply real_eq_refl.
          * apply (real_eq_sym _ _ (real_mult_assoc HALF
                       (real_of_nat (length vocab)) invn)).
        - apply (real_eq_trans
                   (real_mult HALF (real_mult (real_of_nat (length vocab)) invn))
                   (real_mult HALF real_one) HALF).
          * apply (RealSetoid.real_eq_mult_compat HALF
                     (real_mult (real_of_nat (length vocab)) invn)
                     HALF real_one).
            -- apply real_eq_refl.
            -- exact (real_inv_pos_correct (real_of_nat (length vocab)) Hnpos).
          * exact (real_mult_one HALF). }
      apply (real_eq_trans
               (real_plus (real_mult (real_of_nat (length vocab)) delta)
                  (real_mult (real_of_nat (length vocab)) delta))
               (real_plus HALF HALF) eps).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_of_nat (length vocab)) delta)
                 (real_mult (real_of_nat (length vocab)) delta)
                 HALF HALF Hnd Hnd).
      * apply (real_eq_trans (real_plus HALF HALF)
                 (real_mult eps (real_plus h2 h2)) eps).
        -- apply (real_eq_sym _ _ (real_distrib eps h2 h2)).
        -- apply (real_eq_trans _
                     (real_mult eps
                        (real_mult (real_plus real_one real_one) h2)) _).
           ++ apply (RealSetoid.real_eq_mult_compat eps (real_plus h2 h2)
                      eps (real_mult (real_plus real_one real_one) h2)).
              ** apply real_eq_refl.
              ** apply (real_eq_trans
                          (real_plus h2 h2)
                          (real_plus (real_mult real_one h2)
                             (real_mult real_one h2))
                          (real_mult (real_plus real_one real_one) h2)).
                 --- apply (RealSetoid.real_eq_plus_compat h2 h2
                              (real_mult real_one h2)
                              (real_mult real_one h2)).
                     +++ exact (real_eq_trans h2
                                  (real_mult h2 real_one)
                                  (real_mult real_one h2)
                                  (real_eq_sym (real_mult h2 real_one) h2
                                     (real_mult_one h2))
                                  (real_mult_comm h2 real_one)).
                     +++ exact (real_eq_trans h2
                                  (real_mult h2 real_one)
                                  (real_mult real_one h2)
                                  (real_eq_sym (real_mult h2 real_one) h2
                                     (real_mult_one h2))
                                  (real_mult_comm h2 real_one)).
                 --- exact (real_distrib_r real_one real_one h2).
           ++ apply (real_eq_trans
                       (real_mult eps
                          (real_mult (real_plus real_one real_one) h2))
                       (real_mult eps real_one) eps).
              ** apply (RealSetoid.real_eq_mult_compat eps
                          (real_mult (real_plus real_one real_one) h2)
                          eps real_one).
                 --- apply real_eq_refl.
                 --- exact (real_inv_pos_correct
                              (real_plus real_one real_one) H2lt0).
              ** exact (real_mult_one eps).
Qed.

Print Assumptions alm_uniform_limit.
(* ============================================================ *)
(* Section 3. Extraction outlets and the assumption audit.        *)
(* ============================================================ *)

(* Extraction outlet for the computational core, shaped like the
   attn_hardlimit218.ml outlet. *)
From Stdlib Require Import Extraction.
Extraction "attn_uniformlimit_q18.ml"
  alm_max_ne alm_count_ge_one_aux alm_k alm_uniform alm_switch count_token.

Print Assumptions alm_gap_witness.
Print Assumptions alm_k_pos.
Print Assumptions alm_uniform.

(* Assumption audit for the m-switch sum identities
   swg_switch_sum_gen and swg_switch_sum. *)
Print Assumptions swg_switch_sum_gen.
Print Assumptions swg_switch_sum.
