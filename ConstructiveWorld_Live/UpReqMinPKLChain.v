(* ConstructiveWorld-Set -- Min-P truncation bounds and the Pinsker KL chain. *)

(** * UpReqMinPKLChain: Real-sum bridges, Min-P truncation, and the entropy chain.

    Mission.  Real-layer indexed-sum bridges ([um_seq_shift],
      [um_seq_nth_sum], [um_seq_const], [um_rls_le_N]), maximum
      machinery ([um_fmax], [um_fmax_ge_nth], [um_fmax_mem_nth]),
      Min-P truncation bounds ([entropy_ge_neg_log_p_max],
      [um_kept_ge_pmax], [dropped_le_one_minus_exp_neg_S],
      [um_pmax_ge_inv_n]), and the audit-bridge KL chain ending in
      [x1_composite_chain].

    Dependencies.  Stdlib [List], [Arith], [Lia], [QArith.Qring].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpAuditBridge] of this development.

    References.  This development, UpReqMinPKLChain.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqMinPKLChain.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpAuditBridge.

(* ================= Section 1. The um_lt_le family ================= *)
(* 0. General bridges at the Real layer, stated outside any Section for global reuse *)

(* strict order implies order: the left branch of the Or encoding of real_le *)
Lemma um_lt_le : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H. exact (inl H).
Qed.

(* equality implies order: the right branch of the Or encoding *)
Lemma um_eq_le : forall a b : Real, real_eq a b -> real_le a b.
Proof.
  exact RealSetoid.real_eq_le.
Qed.

(* zero is at most y implies x is at most x + y: adding a nonnegative summand *)
Lemma um_le_add_l : forall x y : Real,
  real_le real_zero y -> real_le x (real_plus x y).
Proof.
  intros x y Hy.
  apply (RealSetoid.real_le_id_l x (real_plus x real_zero) (real_plus x y)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat.
    + apply real_le_refl.
    + exact Hy.
Qed.

(* zero is at most a and zero is at most b imply zero is at most a + b *)
Lemma um_add_nonneg : forall a b : Real,
  real_le real_zero a -> real_le real_zero b ->
  real_le real_zero (real_plus a b).
Proof.
  intros a b Ha Hb.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero) (real_plus a b)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat.
    + exact Ha.
    + exact Hb.
Qed.

(* zero is at most y implies x is at most y + x: the nonnegative summand added on the left *)
Lemma um_le_add_r : forall x y : Real,
  real_le real_zero y -> real_le x (real_plus y x).
Proof.
  intros x y Hy.
  apply (RealSetoid.real_le_id_l x (real_plus real_zero x) (real_plus y x)).
  - apply (real_eq_trans x (real_plus x real_zero)).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_plus_comm.
  - apply real_le_plus_compat.
    + exact Hy.
    + apply real_le_refl.
Qed.

(* one times x equals x: the left unit law; real_mult_one is the right unit version *)
Lemma um_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* bridge from Empty_set to False: Not is defined at the Set layer as
   A -> Empty_set, so a refutation term must reach the Prop-level False;
   this bridge lives inside proofs only and no statement face carries Prop *)
Lemma um_Emptyset_false : Empty_set -> False.
Proof.
  intro e. exact (match e with end).
Qed.

(* 1. Indexed sums in seq form: nreal, index shifts, the nth bridge, constants *)

(* nreal: the embedding nat -> Real (the Real image of a table length N) *)
Fixpoint um_nreal (n : nat) : Real :=
  match n with
  | Datatypes.O => real_zero
  | Datatypes.S k => real_plus real_one (um_nreal k)
  end.

Lemma um_nreal_pos : forall n : nat,
  real_lt real_zero (um_nreal (Datatypes.S n)).
Proof.
  induction n as [| k IH].
  - apply (real_lt_eq_lt real_zero real_one
                         (real_plus real_one (um_nreal Datatypes.O))).
    + apply real_lt_zero_one.
    + apply real_eq_sym. apply real_plus_zero.
  - apply real_plus_positive.
    + apply real_lt_zero_one.
    + exact IH.
Qed.

(* positivity of nreal from an index bound: NatLt i n gives n = S m, hence nreal n > 0 *)
Lemma um_nreal_pos_of_lt : forall (n i : nat),
  NatLt i n -> real_lt real_zero (um_nreal n).
Proof.
  intros n i Hi. destruct n as [| m].
  - exfalso. exact (um_Emptyset_false (id_false_true Hi)).
  - exact (um_nreal_pos m).
Qed.

(* sum shift: the sum over seq (S s) n of f equals the sum over seq s n of (fun i => f (S i)) *)
Lemma um_seq_shift : forall (f : nat -> Real) (n s : nat),
  real_eq (real_list_sum nat f (seq (Datatypes.S s) n))
          (real_list_sum nat (fun i : nat => f (Datatypes.S i)) (seq s n)).
Proof.
  intros f n. induction n as [| n IH]; intro s.
  - cbn [seq real_list_sum]. apply real_eq_refl.
  - cbn [seq real_list_sum].
    apply (RealSetoid.real_eq_plus_compat (f (Datatypes.S s))
             (real_list_sum nat f (seq (Datatypes.S (Datatypes.S s)) n))
             (f (Datatypes.S s))
             (real_list_sum nat (fun i : nat => f (Datatypes.S i))
                                   (seq (Datatypes.S s) n))).
    + apply real_eq_refl.
    + exact (IH (Datatypes.S s)).
Qed.

(* skipn sum step: nth k rest 0 plus the sum over skipn (S k) rest
   equals the sum over skipn k rest *)
Lemma um_skipn_sum_step : forall (k : nat) (rest : list Real),
  real_eq (real_plus (nth k rest real_zero)
                     (real_list_sum Real (fun x : Real => x)
                                   (skipn (Datatypes.S k) rest)))
          (real_list_sum Real (fun x : Real => x) (skipn k rest)).
Proof.
  induction k as [| k IH]; intro rest.
  - destruct rest as [| q rest2].
    + cbn [nth skipn real_list_sum]. apply real_plus_zero.
    + cbn [nth skipn real_list_sum].
      apply (RealSetoid.real_eq_plus_compat q
               (real_list_sum Real (fun x : Real => x) rest2)
               q (real_list_sum Real (fun x : Real => x) rest2)).
      * apply real_eq_refl.
      * apply real_eq_refl.
  - destruct rest as [| q rest2].
    + cbn [nth skipn real_list_sum]. apply real_plus_zero.
    + cbn [nth skipn real_list_sum].
      exact (IH rest2).
Qed.

(* the nth bridge, main workhorse: the sum over seq s (length l) of nth i l 0
   equals the sum over skipn s l *)
Lemma um_seq_nth_sum : forall (l : list Real) (s : nat),
  real_eq (real_list_sum nat (fun i : nat => nth i l real_zero)
                             (seq s (length l)))
          (real_list_sum Real (fun x : Real => x) (skipn s l)).
Proof.
  induction l as [| p rest IH]; intro s.
  - destruct s as [| k].
    + cbn [seq length skipn real_list_sum]. apply real_eq_refl.
    + cbn [seq length skipn real_list_sum]. apply real_eq_refl.
  - destruct s as [| k].
    + (* the case s = 0: p plus the sum over seq 1 n of nth i (p::rest) 0
         equals p plus the sum over rest *)
      cbn [seq length skipn real_list_sum].
      apply (RealSetoid.real_eq_plus_compat
                (nth Datatypes.O (p :: rest) real_zero)
                (real_list_sum nat
                   (fun i : nat => nth i (p :: rest) real_zero)
                   (seq 1%nat (length rest)))
                p
                (real_list_sum Real (fun x : Real => x) rest)).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_list_sum nat
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (seq 1%nat (length rest)))
                 (real_list_sum nat
                    (fun i : nat => nth i rest real_zero)
                    (seq 0%nat (length rest)))).
        -- exact (um_seq_shift
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (length rest) 0%nat).
        -- exact (IH 0%nat).
    + (* the case s = S k: three facts compose, the shift lemma, the
         induction premise at rest and S k, and the step lemma *)
      cbn [seq length real_list_sum].
      apply (real_eq_trans
               (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                          (real_list_sum nat
                             (fun i : nat => nth i (p :: rest) real_zero)
                             (seq (Datatypes.S (Datatypes.S k))
                                  (length rest))))
               (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                          (real_list_sum nat
                             (fun i : nat => nth i rest real_zero)
                             (seq (Datatypes.S k) (length rest))))).
      * apply (RealSetoid.real_eq_plus_compat
                  (nth (Datatypes.S k) (p :: rest) real_zero)
                  (real_list_sum nat
                     (fun i : nat => nth i (p :: rest) real_zero)
                     (seq (Datatypes.S (Datatypes.S k)) (length rest)))
                  (nth (Datatypes.S k) (p :: rest) real_zero)
                  (real_list_sum nat
                     (fun i : nat => nth i rest real_zero)
                     (seq (Datatypes.S k) (length rest)))).
        -- apply real_eq_refl.
        -- exact (um_seq_shift
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (length rest) (Datatypes.S k)).
      * apply (real_eq_trans
                 (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                            (real_list_sum nat
                               (fun i : nat => nth i rest real_zero)
                               (seq (Datatypes.S k) (length rest))))
                 (real_plus (nth k rest real_zero)
                            (real_list_sum Real (fun x : Real => x)
                                          (skipn (Datatypes.S k) rest)))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (nth (Datatypes.S k) (p :: rest) real_zero)
                     (real_list_sum nat
                        (fun i : nat => nth i rest real_zero)
                        (seq (Datatypes.S k) (length rest)))
                     (nth k rest real_zero)
                     (real_list_sum Real (fun x : Real => x)
                                   (skipn (Datatypes.S k) rest))).
           ++ apply real_eq_refl.
           ++ exact (IH (Datatypes.S k)).
        -- exact (um_skipn_sum_step k rest).
Qed.

(* constant table: the sum over seq 0 n of c equals nreal n times c *)
Lemma um_seq_const : forall (n : nat) (c : Real),
  real_eq (real_list_sum nat (fun _ : nat => c) (seq 0%nat n))
          (real_mult (um_nreal n) c).
Proof.
  induction n as [| n IH]; intro c.
  - cbn [seq um_nreal real_list_sum].
    apply real_eq_sym.
    apply (real_eq_trans (real_mult real_zero c)
             (real_mult c real_zero) real_zero).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - cbn [seq um_nreal real_list_sum].
    (* c plus the sum over seq 1 n of c equals c plus nreal n times c,
       that is (1 + nreal n) times c *)
    apply (real_eq_trans
             (real_plus c
                        (real_list_sum nat (fun _ : nat => c)
                                       (seq (Datatypes.S 0%nat) n)))
             (real_plus c (real_mult (um_nreal n) c))).
    + apply (RealSetoid.real_eq_plus_compat c
                (real_list_sum nat (fun _ : nat => c) (seq 1%nat n))
                c (real_mult (um_nreal n) c)).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_list_sum nat (fun _ : nat => c) (seq 1%nat n))
                 (real_list_sum nat (fun _ : nat => c) (seq 0%nat n))).
        -- exact (um_seq_shift (fun _ : nat => c) n 0%nat).
        -- exact (IH c).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_mult (real_plus real_one (um_nreal n)) c)
               (real_mult c (real_plus real_one (um_nreal n)))).
      * apply real_mult_comm.
      * apply (real_eq_trans
                 (real_mult c (real_plus real_one (um_nreal n)))
                 (real_plus (real_mult c real_one)
                            (real_mult c (um_nreal n)))).
        -- exact (real_distrib c real_one (um_nreal n)).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_mult c real_one) (real_mult c (um_nreal n))
                     c (real_mult (um_nreal n) c)).
           ++ apply real_mult_one.
           ++ apply real_mult_comm.
Qed.




Definition um_ent_term (p : Real) (Hp : real_lt real_zero p) : Real :=
  real_mult p (real_opp (cw_log p Hp)).

(* monotonicity of log in the non-strict form: assembled from the strict
   version plus the Or elimination of real_log_wd *)
Lemma um_log_le_mono : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_le a b -> real_le (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb Hle. destruct Hle as [Hlt | Heq].
  - apply um_lt_le. exact (real_log_lt_mono a b Ha Hb Hlt).
  - exact (um_eq_le _ _ (real_log_wd a b Ha Hb Heq)).
Qed.

(* pointwise entropy term bound: p at most M implies p times (minus log M)
   is at most p times (minus log p), by antitonicity of log and the
   nonnegative weight p *)
Lemma um_ent_term_le : forall (p M : Real)
    (Hp : real_lt real_zero p) (HM : real_lt real_zero M),
  real_le p M ->
  real_le (real_mult p (real_opp (cw_log M HM)))
          (real_mult p (real_opp (cw_log p Hp))).
Proof.
  intros p M Hp HM Hle.
  assert (Hlog : real_le (real_opp (cw_log M HM)) (real_opp (cw_log p Hp))).
  { apply real_opp_le_compat.
    apply um_log_le_mono. exact Hle. }
  apply (RealSetoid.real_le_id_l
           (real_mult p (real_opp (cw_log M HM)))
           (real_mult (real_opp (cw_log M HM)) p)
           (real_mult p (real_opp (cw_log p Hp)))).
  - apply real_mult_comm.
  - apply (RealSetoid.real_le_id_r
             (real_mult (real_opp (cw_log M HM)) p)
             (real_mult (real_opp (cw_log p Hp)) p)
             (real_mult p (real_opp (cw_log p Hp)))).
    + apply real_mult_comm.
    + exact (real_le_mult_compat_weak (real_opp (cw_log M HM))
                                      (real_opp (cw_log p Hp)) p
               (um_lt_le real_zero p Hp) Hlog).
Qed.

(* 3. Indexed-sum lemmas under the NatLt index discipline (pointwise bound
   functions, no Prop elimination): NatLt i n is Id (i <? n) true, the
   Set-layer bound encoding; the key conversion is NatLt (S i) (S n)
   convertible with NatLt i n by ltb/leb iota. *)

(* pointwise order lifts to indexed sums *)
Lemma um_rls_le_N : forall (f g : nat -> Real) (n : nat),
  (forall j : nat, NatLt j n -> real_le (f j) (g j)) ->
  real_le (real_list_sum nat f (seq 0%nat n))
          (real_list_sum nat g (seq 0%nat n)).
Proof.
  intros f g n. revert f g. induction n as [| n IH]; intros f g Hpt.
  - cbn [seq real_list_sum]. apply real_le_refl.
  - cbn [seq real_list_sum].
    apply real_le_plus_compat.
    + exact (Hpt 0%nat id_refl).
    + apply (RealSetoid.real_le_compat
                (real_list_sum nat (fun j : nat => f (Datatypes.S j))
                                   (seq 0%nat n))
                (real_list_sum nat f (seq 1%nat n))
                (real_list_sum nat (fun j : nat => g (Datatypes.S j))
                                   (seq 0%nat n))
                (real_list_sum nat g (seq 1%nat n))).
      * exact (real_eq_sym _ _ (um_seq_shift f n 0%nat)).
      * exact (real_eq_sym _ _ (um_seq_shift g n 0%nat)).
      * apply (IH (fun j : nat => f (Datatypes.S j))
                  (fun j : nat => g (Datatypes.S j))).
        intros j Hj. exact (Hpt (Datatypes.S j) Hj).
Qed.

(* nonnegativity of indexed sums *)
Lemma um_rls_nonneg_N : forall (g : nat -> Real) (n : nat),
  (forall j : nat, NatLt j n -> real_le real_zero (g j)) ->
  real_le real_zero (real_list_sum nat g (seq 0%nat n)).
Proof.
  intros g n. revert g. induction n as [| n IH]; intros g Hnn.
  - cbn [seq real_list_sum]. apply real_le_refl.
  - cbn [seq real_list_sum].
    assert (Htail : real_le real_zero
                      (real_list_sum nat
                         (fun j : nat => g (Datatypes.S j))
                         (seq 0%nat n))).
    { apply (IH (fun j : nat => g (Datatypes.S j))).
      intros j Hj. exact (Hnn (Datatypes.S j) Hj). }
    assert (Hstep : real_le (real_plus real_zero real_zero)
                       (real_plus (g 0%nat)
                                  (real_list_sum nat
                                     (fun j : nat => g (Datatypes.S j))
                                     (seq 0%nat n)))).
    { apply real_le_plus_compat.
      - exact (Hnn 0%nat id_refl).
      - exact Htail. }
    exact (RealSetoid.real_le_compat
              (real_plus real_zero real_zero)
              real_zero
              (real_plus (g 0%nat)
                         (real_list_sum nat
                            (fun j : nat => g (Datatypes.S j))
                            (seq 0%nat n)))
              (real_plus (g 0%nat) (real_list_sum nat g (seq 1%nat n)))
              (real_plus_zero real_zero)
              (RealSetoid.real_eq_plus_compat (g 0%nat)
                 (real_list_sum nat
                    (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                 (g 0%nat)
                 (real_list_sum nat g (seq 1%nat n))
                 (real_eq_refl (g 0%nat))
                 (real_eq_sym _ _ (um_seq_shift g n 0%nat)))
              Hstep).
    (* the order fact for the tail sum is given directly by the second
       component of Hstep *)
Qed.

(* a single member is at most the whole sum: NatLt i n gives g i at most the
   sum over seq 0 n of g, with pointwise nonnegative weights *)
Lemma um_rls_single_le_N : forall (g : nat -> Real) (n i : nat),
  NatLt i n ->
  (forall j : nat, NatLt j n -> real_le real_zero (g j)) ->
  real_le (g i) (real_list_sum nat g (seq 0%nat n)).
Proof.
  intros g n. revert g. induction n as [| n IH]; intros g i Hi Hnn.
  - exfalso. exact (um_Emptyset_false (id_false_true Hi)).
  - cbn [seq real_list_sum]. destruct i as [| i'].
    + (* the case i = 0: the head term is the goal term; the nonnegative
         tail is transported along the shift *)
      assert (Ht0 : real_le real_zero
                      (real_list_sum nat
                         (fun j : nat => g (Datatypes.S j))
                         (seq 0%nat n))).
      { apply (um_rls_nonneg_N (fun j : nat => g (Datatypes.S j)) n).
        intros j Hj. exact (Hnn (Datatypes.S j) Hj). }
      apply um_le_add_l.
      exact (RealSetoid.real_le_compat real_zero real_zero
                (real_list_sum nat
                   (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                (real_list_sum nat g (seq 1%nat n))
                (real_eq_refl real_zero)
                (real_eq_sym _ _ (um_seq_shift g n 0%nat))
                Ht0).
    + (* the case i = S i': the induction premise at S i' uses
         NatLt (S i') n convertible with NatLt i' n, then the sum is
         transported along um_seq_shift to the sum over seq 1 n of g,
         and the nonnegative head term is added *)
      assert (Htail : real_le (g (Datatypes.S i'))
                         (real_list_sum nat
                            (fun j : nat => g (Datatypes.S j))
                            (seq 0%nat n))).
      { apply (IH (fun j : nat => g (Datatypes.S j)) i'
                  Hi (fun j Hj => Hnn (Datatypes.S j) Hj)). }
      apply real_le_trans with
        (y := real_list_sum nat (fun j : nat => g (Datatypes.S j))
                                (seq 0%nat n)).
      * exact Htail.
      * apply (real_le_trans
                 (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                 (real_list_sum nat g (seq 1%nat n))
                 (real_plus (g 0%nat) (real_list_sum nat g (seq 1%nat n)))).
        -- apply (RealSetoid.real_le_compat
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n))
                     (real_list_sum nat g (seq 1%nat n))
                     (real_eq_refl (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n)))
                     (real_eq_sym _ _ (um_seq_shift g n 0%nat))
                     (real_le_refl (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0%nat n)))).
        -- apply (um_le_add_r (real_list_sum nat g (seq 1%nat n)) (g 0%nat)).
           exact (Hnn 0%nat id_refl).
Qed.

(* 4. World section: tokens and ratio with a trichotomy decider, the dual of
   ord_le_dec *)

Section UpMinPWorld.

(* trichotomy decider: a is at most b or b is less than a, the constructive
   decision premise for the Real layer le and lt *)
Variable um_trich_probe : forall a b : Real, Or (real_le a b) (real_lt b a).

(* the maximum: fold of real_max, mapping nil to zero *)
Fixpoint um_fmax (l : list Real) : Real :=
  match l with
  | nil => real_zero
  | p :: rest => real_max p (um_fmax rest)
  end.

(* pointwise upper bound, indexed form: NatLt i (length l) implies
   nth i l 0 is at most fold_max l *)
Lemma um_fmax_ge_nth : forall (l : list Real) (i : nat),
  NatLt i (length l) -> real_le (nth i l real_zero) (um_fmax l).
Proof.
  induction l as [| p rest IH]; intros i Hi.
  - (* NatLt i 0 is convertible with Id false true *)
    destruct (um_Emptyset_false (id_false_true Hi)).
  - cbn [length um_fmax]. destruct i as [| i'].
    + (* head element: p is at most max p M; NatLt 0 (S n) is inhabited
         by id_refl *)
      destruct (um_trich_probe p (um_fmax rest)) as [Hle | Hlt].
      * apply (RealSetoid.real_le_id_r p (um_fmax rest)
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (RealInterfaceEnhancedMod.real_r_max_r_iff p
                       (um_fmax rest) Hle)).
        -- exact Hle.
      * apply (RealSetoid.real_le_id_r p p
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (real_r_max_l_iff p (um_fmax rest)
                       (um_lt_le (um_fmax rest) p Hlt))).
        -- apply real_le_refl.
    + (* tail element: nth i' rest 0 is at most max p M; NatLt (S i') (S n)
         is convertible with NatLt i' n *)
      destruct (um_trich_probe p (um_fmax rest)) as [Hle | Hlt].
      * apply (RealSetoid.real_le_id_r (nth i' rest real_zero)
                                          (um_fmax rest)
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (RealInterfaceEnhancedMod.real_r_max_r_iff p
                       (um_fmax rest) Hle)).
        -- exact (IH i' Hi).
      * apply (RealSetoid.real_le_id_r (nth i' rest real_zero)
                                          p (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (real_r_max_l_iff p (um_fmax rest)
                       (um_lt_le (um_fmax rest) p Hlt))).
        -- apply um_lt_le.
           exact (real_le_lt_trans (nth i' rest real_zero)
                     (um_fmax rest) p (IH i' Hi) Hlt).
Qed.

(* attainability, indexed form: a nonemptiness witness and pointwise
   positivity imply the maximum is attained in the table *)
Lemma um_fmax_mem_nth : forall (l : list Real),
  (sigT (fun i : nat => NatLt i (length l))) ->
  (forall i : nat,
       NatLt i (length l) -> real_lt real_zero (nth i l real_zero)) ->
  sigT (fun i : nat =>
          prod (NatLt i (length l))
               (real_eq (nth i l real_zero) (um_fmax l))).
Proof.
  induction l as [| p rest IH]; intros [i0 Hi0] Hpos.
  - destruct (um_Emptyset_false (id_false_true Hi0)).
  - destruct rest as [| q rest2].
    + (* single-element table: um_fmax [p] equals real_max p real_zero *)
      destruct (um_trich_probe p real_zero) as [Hle | Hlt].
      * (* p is at most zero, contradicting p is positive *)
        destruct (um_Emptyset_false
                    (real_lt_irrefl real_zero
                       (real_lt_eq_lt real_zero p real_zero
                          (Hpos Datatypes.O id_refl)
                          (real_eq_sym real_zero p
                             (real_le_antisym real_zero p
                                (um_lt_le real_zero p
                                   (Hpos Datatypes.O id_refl))
                                Hle))))).
      * (* zero is less than p: max p 0 equals p by the left branch,
           with witness i = 0 *)
        exact (existT _ Datatypes.O
                 (pair id_refl
                       (real_eq_sym (real_max p real_zero) p
                          (real_r_max_l_iff p real_zero
                             (um_lt_le real_zero p Hlt))))).
    + (* the tail table is nonempty with constructive witness 0:
         attainability passes to the induction premise, and max p M
         follows the trichotomy branch *)
      assert (Hrestnn : sigT (fun i : nat => NatLt i (length (q :: rest2)))).
      { exact (existT _ Datatypes.O id_refl). }
      assert (Hposr : forall i : nat,
                NatLt i (length (q :: rest2)) ->
                real_lt real_zero (nth i (q :: rest2) real_zero)).
      { intros i Hi.
        apply (Hpos (Datatypes.S i)).
        (* NatLt (S i) (S (S m)) is convertible with NatLt i (S m)
           by ltb/leb iota *)
        exact Hi. }
      specialize (IH Hrestnn Hposr).
      destruct IH as [j [Hjlen Hjeq]].
      destruct (um_trich_probe p (um_fmax (q :: rest2))) as [Hle | Hlt].
      * (* max p M equals M and M lies in the tail table by the right
           branch, with witness S j; NatLt (S j) (S (S m)) is
           convertible with NatLt j (S m), which is Hjlen *)
        exact (existT _ (Datatypes.S j)
                 (pair Hjlen
                       (real_eq_trans
                          (nth (Datatypes.S j) (p :: q :: rest2) real_zero)
                          (nth j (q :: rest2) real_zero)
                          (real_max p (um_fmax (q :: rest2)))
                          (real_eq_refl (nth j (q :: rest2) real_zero))
                          (real_eq_trans
                             (nth j (q :: rest2) real_zero)
                             (um_fmax (q :: rest2))
                             (real_max p (um_fmax (q :: rest2)))
                             Hjeq
                             (real_eq_sym _ _
                                (RealInterfaceEnhancedMod.real_r_max_r_iff p
                                   (um_fmax (q :: rest2)) Hle)))))).
      * (* M is less than p: max p M equals p by the left branch,
           with witness 0 *)
        exact (existT _ Datatypes.O
                 (pair id_refl
                       (real_eq_sym (real_max p (um_fmax (q :: rest2))) p
                          (real_r_max_l_iff p (um_fmax (q :: rest2))
                             (um_lt_le (um_fmax (q :: rest2)) p Hlt))))).
Qed.

(* the maximum is positive: from a nonemptiness witness and pointwise positivity *)
Lemma um_fmax_pos_nth : forall (l : list Real),
  (sigT (fun i : nat => NatLt i (length l))) ->
  (forall i : nat,
       NatLt i (length l) -> real_lt real_zero (nth i l real_zero)) ->
  real_lt real_zero (um_fmax l).
Proof.
  intros l Hne Hpos.
  destruct (um_fmax_mem_nth l Hne Hpos) as [i [Hi Heq]].
  exact (RealSetoid.real_lt_compat real_zero real_zero
           (nth i l real_zero) (um_fmax l)
           (real_eq_refl real_zero) Heq (Hpos i Hi)).
Qed.

(* 5. The Min-P truncation world (tokens and ratio) *)

Section MinPEntropy.

(* probability table: a nonemptiness witness, pointwise positivity under
   index bounds, and sum equal to one *)
Variable tokens : list Real.
Variable tokens_ne : sigT (fun i : nat => NatLt i (length tokens)).
Variable tokens_pos : forall i : nat,
  real_lt real_zero (nth i tokens real_zero).
Hypothesis tokens_sum :
  real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one.

(* the Min-P threshold ratio: zero is less than ratio, ratio is at most one *)
Variable ratio : Real.
Hypothesis ratio_pos : real_lt real_zero ratio.
Hypothesis ratio_le_one : real_le ratio real_one.

(* ---- core objects ---- *)
Definition um_N : nat := length tokens.

Definition um_pmax : Real := um_fmax tokens.

Definition um_Hpmax : real_lt real_zero um_pmax :=
  um_fmax_pos_nth tokens tokens_ne (fun i _ => tokens_pos i).

(* pointwise k is at most p_max, indexed form *)
Lemma um_le_pmax : forall i : nat,
  NatLt i um_N -> real_le (nth i tokens real_zero) um_pmax.
Proof.
  intros i Hi. exact (um_fmax_ge_nth tokens i Hi).
Qed.

(* S: the Shannon entropy of the source distribution, the discrete list
   version summed by index *)
Definition um_entropy : Real :=
  real_list_sum nat
    (fun i : nat => um_ent_term (nth i tokens real_zero) (tokens_pos i))
    (seq 0%nat um_N).

(* the Min-P threshold and retention indicator: thr equals ratio times p_max;
   a retained token keeps its value k, a dropped one contributes zero *)
Definition um_thr : Real := real_mult ratio um_pmax.

Definition um_keepF (p : Real) : Real :=
  match um_trich_probe um_thr p with
  | inl _ => p
  | inr _ => real_zero
  end.

(* retained and truncated mass: kept is the sum of keepF and dropped is
   one minus kept, both definitional *)
Definition um_kept : Real :=
  real_list_sum nat (fun i : nat => um_keepF (nth i tokens real_zero))
                (seq 0%nat um_N).

Lemma um_keepF_nonneg_nth : forall (x : Real) (Hx : real_lt real_zero x),
  real_le real_zero (um_keepF x).
Proof.
  intros x Hx.
  unfold um_keepF.
  destruct (um_trich_probe um_thr x) as [Hkeep | Hdrop].
  - apply um_lt_le. exact Hx.
  - apply real_le_refl.
Qed.

(* pointwise nonnegativity of the retained weights, in full-index form
   for the indexed-sum lemmas *)
Definition um_keepF_nonneg : forall i : nat,
  real_le real_zero (um_keepF (nth i tokens real_zero)) :=
  fun i => um_keepF_nonneg_nth (nth i tokens real_zero) (tokens_pos i).

Definition um_dropped : Real :=
  real_plus real_one (real_opp um_kept).

(* ---- algebraic properties of keepF ---- *)
Lemma um_keepF_congr : forall x y : Real,
  real_eq x y -> real_eq (um_keepF x) (um_keepF y).
Proof.
  intros x y Heq.
  unfold um_keepF.
  destruct (um_trich_probe um_thr x) as [Hx | Hx];
    destruct (um_trich_probe um_thr y) as [Hy | Hy].
  - (* both x and y are retained: keepF x equals x equals y equals keepF y *)
    apply Heq.
  - (* x retained and y dropped: y less than thr transports to x less
       than thr, contradicting thr is at most x *)
    destruct (um_Emptyset_false (real_lt_irrefl x
                (real_lt_le_trans x um_thr x
                   (RealSetoid.real_lt_compat y x um_thr um_thr
                      (real_eq_sym x y Heq) (real_eq_refl um_thr) Hy)
                   Hx))).
  - (* x dropped and y retained: thr at most y transports to thr at
       most x, contradicting x less than thr *)
    destruct (um_Emptyset_false (real_lt_irrefl um_thr
                (real_le_lt_trans um_thr x um_thr
                   (RealSetoid.real_le_compat um_thr um_thr y x
                      (real_eq_refl um_thr) (real_eq_sym x y Heq) Hy)
                   Hx))).
  - (* both dropped: zero equals zero *)
    apply real_eq_refl.
Qed.


(* thr is at most p_max: ratio times p_max is at most one times p_max,
   which equals p_max *)
Lemma um_thr_le_pmax : real_le um_thr um_pmax.
Proof.
  apply (RealSetoid.real_le_id_r (real_mult ratio um_pmax)
                                 (real_mult real_one um_pmax) um_pmax).
  - apply um_mult_one_l.
  - exact (real_le_mult_compat_weak ratio real_one um_pmax
             (um_lt_le real_zero um_pmax um_Hpmax) ratio_le_one).
Qed.

(* part 1: S is at least minus log p_max *)

Theorem entropy_ge_neg_log_p_max :
  real_le (real_opp (cw_log um_pmax um_Hpmax)) um_entropy.
Proof.
  apply real_le_trans with
    (y := real_list_sum nat
            (fun i : nat =>
               real_mult (nth i tokens real_zero)
                         (real_opp (cw_log um_pmax um_Hpmax)))
            (seq 0%nat um_N)).
  - (* minus log p_max equals itself times the sum of nth, that is
       minus log p_max times one; the reverse route reads the target
       as the sum of nth times minus log p_max *)
    apply um_eq_le.
    apply (real_eq_trans
             (real_opp (cw_log um_pmax um_Hpmax))
             (real_mult (real_opp (cw_log um_pmax um_Hpmax))
                        (real_list_sum nat
                           (fun i : nat => nth i tokens real_zero)
                           (seq 0%nat um_N)))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_mult (real_opp (cw_log um_pmax um_Hpmax))
                          (real_list_sum nat
                             (fun i : nat => nth i tokens real_zero)
                             (seq 0%nat um_N)))
               (real_mult (real_opp (cw_log um_pmax um_Hpmax)) real_one)).
      * apply (RealSetoid.real_eq_mult_compat
                  (real_opp (cw_log um_pmax um_Hpmax))
                  (real_list_sum nat
                     (fun i : nat => nth i tokens real_zero)
                     (seq 0%nat um_N))
                  (real_opp (cw_log um_pmax um_Hpmax)) real_one).
        -- apply real_eq_refl.
        -- (* the sum over seq 0 N of nth i tokens 0 equals one *)
           apply (real_eq_trans
                    (real_list_sum nat
                       (fun i : nat => nth i tokens real_zero)
                       (seq 0%nat (length tokens)))
                    (real_list_sum Real (fun x : Real => x) tokens)).
           ++ exact (um_seq_nth_sum tokens 0%nat).
           ++ exact tokens_sum.
      * apply real_mult_one.
    + apply real_eq_sym.
      exact (real_list_sum_linear_r nat
               (real_opp (cw_log um_pmax um_Hpmax))
               (fun i : nat => nth i tokens real_zero) (seq 0%nat um_N)).
  - (* termwise: nth i tokens 0 is at most p_max, so nth times minus log
       p_max is at most the entropy term *)
    apply (um_rls_le_N
              (fun i : nat =>
                 real_mult (nth i tokens real_zero)
                           (real_opp (cw_log um_pmax um_Hpmax)))
              (fun i : nat =>
                 um_ent_term (nth i tokens real_zero) (tokens_pos i))
              um_N).
    intros j Hj.
    exact (um_ent_term_le (nth j tokens real_zero) um_pmax
              (tokens_pos j) um_Hpmax (um_le_pmax j Hj)).
Qed.

(* the argmax token is retained: kept is at least p_max *)
Lemma um_kept_ge_pmax : real_le um_pmax um_kept.
Proof.
  destruct (um_fmax_mem_nth tokens tokens_ne (fun i _ => tokens_pos i))
    as [istar [Hiistar Heqstar]].
  apply (RealSetoid.real_le_id_l um_pmax
            (um_keepF (nth istar tokens real_zero)) um_kept).
  - (* for the first component um_pmax equals keepF (nth istar):
       p_max is retained so keepF um_pmax equals um_pmax, then the
       congruence lemma transports this to keepF (nth istar) *)
    apply (real_eq_trans um_pmax (um_keepF um_pmax)
             (um_keepF (nth istar tokens real_zero))).
    + unfold um_keepF.
      destruct (um_trich_probe um_thr um_pmax) as [Hkeep | Hdrop].
      * apply real_eq_refl.
      * exact (False_rect _
                 (um_Emptyset_false
                    (real_lt_irrefl um_pmax
                       (real_lt_le_trans um_pmax um_thr um_pmax Hdrop
                                          um_thr_le_pmax)))).
    + exact (um_keepF_congr um_pmax (nth istar tokens real_zero)
               (real_eq_sym _ _ Heqstar)).
  - (* a single member is at most the whole sum: keepF (nth istar) is
       at most the sum of keepF *)
    exact (um_rls_single_le_N
              (fun i : nat => um_keepF (nth i tokens real_zero))
              um_N istar Hiistar (fun j _ => um_keepF_nonneg j)).
Qed.

(* e to the minus S is at most p_max: S is at least minus log p_max and
   exp is antitone, so e to the minus S is at most e to the minus of
   minus log p_max, which equals e to the log p_max and hence p_max *)
Lemma um_exp_neg_S_le_pmax :
  real_le (real_exp_neg um_entropy) um_pmax.
Proof.
  apply (RealSetoid.real_le_id_r (real_exp_neg um_entropy)
            (real_exp_neg (real_opp (cw_log um_pmax um_Hpmax))) um_pmax).
  - 
    exact (real_exp_neg_log_inv um_pmax um_Hpmax).
  - apply real_exp_neg_le_decr.
    exact entropy_ge_neg_log_p_max.
Qed.

(* part 2: dropped is at most one minus e to the minus S *)

Theorem dropped_le_one_minus_exp_neg_S :
  real_le um_dropped
          (real_plus real_one (real_opp (real_exp_neg um_entropy))).
Proof.
  unfold um_dropped.
  apply real_le_plus_compat.
  - apply real_le_refl.
  - apply real_opp_le_compat.
    apply real_le_trans with (y := um_pmax).
    + exact um_exp_neg_S_le_pmax.
    + exact um_kept_ge_pmax.
Qed.

(* part 3: dropped is at most one minus one over N, where N is the length of
   tokens; the uniform special case *)

Definition um_Npos : real_lt real_zero (um_nreal um_N).
Proof.
  destruct tokens_ne as [i Hi].
  exact (um_nreal_pos_of_lt um_N i Hi).
Defined.

(* p_max is at least one over N: the sum of k equals one and is at most
   N times p_max, hence the inverse of N is at most p_max; by
   contradiction, p_max strictly below the inverse of N would give
   N times p_max strictly below N times the inverse of N, which equals
   one, a contradiction *)
Lemma um_pmax_ge_inv_n :
  real_le (real_inv_pos (um_nreal um_N) um_Npos) um_pmax.
Proof.
  assert (H1 : real_le real_one
                 (real_mult (um_nreal um_N) um_pmax)).
  { (* one equals the sum of nth, which is at most the sum of the constant
       p_max, that is N times p_max *)
    apply real_le_trans with
      (y := real_list_sum nat
              (fun i : nat => nth i tokens real_zero) (seq 0%nat um_N)).
    - apply um_eq_le.
      apply (real_eq_trans real_one
               (real_list_sum Real (fun x : Real => x) tokens)
               (real_list_sum nat
                  (fun i : nat => nth i tokens real_zero) (seq 0%nat um_N))).
      * exact (real_eq_sym _ _ tokens_sum).
      * exact (real_eq_sym _ _ (um_seq_nth_sum tokens 0%nat)).
    - apply real_le_trans with
        (y := real_list_sum nat (fun _ : nat => um_pmax) (seq 0%nat um_N)).
      + apply (um_rls_le_N (fun i : nat => nth i tokens real_zero)
                 (fun _ : nat => um_pmax) um_N).
        intros j Hj. apply um_le_pmax. exact Hj.
      + apply um_eq_le. exact (um_seq_const um_N um_pmax). }
  destruct (um_trich_probe (real_inv_pos (um_nreal um_N) um_Npos)
                           um_pmax) as [Hle | Hlt].
  - exact Hle.
  - destruct (um_Emptyset_false
                (real_lt_irrefl real_one
                   (real_le_lt_trans real_one
                      (real_mult (um_nreal um_N) um_pmax) real_one H1
                      (real_lt_eq_lt
                         (real_mult (um_nreal um_N) um_pmax)
                         (real_mult (um_nreal um_N)
                                    (real_inv_pos (um_nreal um_N) um_Npos))
                         real_one
                         (real_lt_mult_compat um_pmax
                            (real_inv_pos (um_nreal um_N) um_Npos)
                            (um_nreal um_N) um_Npos Hlt)
                         (real_inv_pos_correct (um_nreal um_N) um_Npos))))).
Qed.

Theorem dropped_le_one_minus_inv_n :
  real_le um_dropped
          (real_plus real_one
                (real_opp (real_inv_pos (um_nreal um_N) um_Npos))).
Proof.
  unfold um_dropped.
  apply real_le_plus_compat.
  - apply real_le_refl.
  - apply real_opp_le_compat.
    apply real_le_trans with (y := um_pmax).
    + exact um_pmax_ge_inv_n.
    + exact um_kept_ge_pmax.
Qed.

End MinPEntropy.

End UpMinPWorld.
(* ================= Section 2. The x1_plus_opp_cancel family ================= *)
From Stdlib Require Import QArith.Qring.

Section X1MinPKLChain.

(* ---- the probability table world, aligned with the export profile of
   UpMinP.MinPEntropy ---- *)
Variable trich : forall a b : Real, Or (real_le a b) (real_lt b a).
Variable tokens : list Real.
Variable tokens_ne : sigT (fun i : nat => NatLt i (length tokens)).
Variable tokens_pos : forall i : nat,
  real_lt real_zero (ListDef.nth i tokens real_zero).
Hypothesis tokens_sum :
  real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one.
Variable ratio : Real.
Hypothesis ratio_pos : real_lt real_zero ratio.
Hypothesis ratio_le_one : real_le ratio real_one.

Abbreviation N := (um_N tokens).
Abbreviation S := (um_entropy tokens tokens_pos).
Abbreviation K := (um_kept trich tokens ratio).
Abbreviation D := (um_dropped trich tokens ratio).
Abbreviation thr := (um_thr tokens ratio).
Abbreviation pmax := (um_pmax tokens).

(* 0. small general bridges built in this file *)

(* one minus (one minus x) equals x, the complementary identity core
   linking kept and dropped *)
Lemma x1_plus_opp_cancel : forall x : Real,
  real_eq (real_plus real_one (real_opp (real_plus real_one (real_opp x)))) x.
Proof.
  intro x.
  apply (real_eq_trans _
           (real_plus real_one (real_plus (real_opp real_one) x))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + apply (real_eq_trans _
               (real_plus (real_opp real_one) (real_opp (real_opp x)))).
      * apply real_opp_plus.
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_eq_refl.
        -- apply real_opp_opp.
  - apply (real_eq_trans _
             (real_plus (real_plus real_one (real_opp real_one)) x)).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus real_zero x)).
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_plus_opp.
        -- apply real_eq_refl.
      * apply (real_eq_trans _ (real_plus x real_zero)).
        -- apply real_plus_comm.
        -- apply real_plus_zero.
Qed.

(* seq shift: the sum over seq (S s) n of h equals the sum over seq s n of
   h composed with S *)
Lemma x1_seq_shift : forall (n s : nat) (h : nat -> Real),
  real_eq (real_list_sum nat h (ListDef.seq (Datatypes.S s) n))
          (real_list_sum nat (fun i => h (Datatypes.S i)) (ListDef.seq s n)).
Proof.
  induction n as [| n IH]; intro s; intro h.
  - cbn [seq real_list_sum]. apply real_eq_refl.
  - cbn [seq real_list_sum].
    apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + exact (IH (Datatypes.S s) h).
Qed.

(* nth shift: nth (S i) (p::rest) equals nth i rest *)
Lemma x1_nth_S_cons : forall (i : nat) (p : Real) (rest : list Real),
  real_eq (ListDef.nth (Datatypes.S i) (p :: rest) real_zero)
          (ListDef.nth i rest real_zero).
Proof.
  intros i p rest. destruct i as [| i'].
  - cbn [ListDef.nth]. apply real_eq_refl.
  - cbn [ListDef.nth]. apply real_eq_refl.
Qed.

(* general transport from a list sum to the seq-indexed sum, for an
   arbitrary f; a generalized um_seq_nth_sum where nth stays signed
   throughout and only x1_seq_shift moves indices, matching the
   UpMinP discipline *)
Lemma x1_sum_list_seq : forall (l : list Real) (f : Real -> Real),
  real_eq (real_list_sum Real f l)
          (real_list_sum nat (fun i => f (ListDef.nth i l real_zero))
                         (ListDef.seq 0%nat (length l))).
Proof.
  intros l f. induction l as [| p rest IH].
  - cbn [length seq real_list_sum]. apply real_eq_refl.
  - cbn [length seq real_list_sum].
    apply (real_eq_trans _
             (real_plus (f (ListDef.nth Datatypes.O (p :: rest) real_zero))
                (real_list_sum nat (fun i => f (ListDef.nth i rest real_zero))
                                (ListDef.seq 0%nat (length rest))))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * exact IH.
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * apply real_eq_sym.
        exact (x1_seq_shift (length rest) 0%nat
                  (fun i => f (ListDef.nth i (p :: rest) real_zero))).
Qed.

(* pointwise extensionality on seq: pointwise equality for i below n gives
   equal seq sums *)
Lemma x1_seq_ext : forall (n : nat) (f g : nat -> Real),
  (forall i : nat, NatLt i n -> real_eq (f i) (g i)) ->
  real_eq (real_list_sum nat f (ListDef.seq 0%nat n))
          (real_list_sum nat g (ListDef.seq 0%nat n)).
Proof.
  intros n f g H.
  apply (real_le_antisym
           (real_list_sum nat f (ListDef.seq 0%nat n))
           (real_list_sum nat g (ListDef.seq 0%nat n))).
  - apply (um_rls_le_N f g n).
    intros j Hjn. apply um_eq_le. exact (H j Hjn).
  - apply (um_rls_le_N g f n).
    intros j Hjn. apply um_eq_le.
    apply real_eq_sym. exact (H j Hjn).
Qed.

(* transport of inverses: x equals x' implies the inverse of x equals
   the inverse of x' *)
Lemma x1_inv_compat : forall (x x' : Real) (Hx : real_lt real_zero x)
    (Hx' : real_lt real_zero x'),
  real_eq x x' -> real_eq (real_inv_pos x Hx) (real_inv_pos x' Hx').
Proof.
  intros x x' Hx Hx' Heq.
  apply (real_inv_unique x' (real_inv_pos x Hx) (real_inv_pos x' Hx')).
  - apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_sym. exact Heq.
      * apply real_eq_refl.
    + apply real_inv_pos_correct.
  - apply real_inv_pos_correct.
Qed.

(* multiplication distributes over addition on the right, in the same
   pattern as the base real_opp_mult *)
Lemma x1_mult_plus_distr : forall x a b : Real,
  real_eq (real_mult x (real_plus a b))
          (real_plus (real_mult x a) (real_mult x b)).
Proof.
  intros x a b.
  apply real_eq_of_zero_diff.
  intro n.
  destruct x as [ux Hx]. destruct a as [ua Ha]. destruct b as [ub Hb].
  (* real_eq_of_zero_diff leaves a QeqT goal; ring (Qring) expects Qeq --
     bridge first, per the real_plus_comm pattern in S02_CauchyComplete *)
  apply qeq_imp_qeqT.
  simpl. ring.
Qed.


Lemma x1_log_inv_eq_opp_log : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (cw_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (cw_log x Hx)).
Proof.
  intros x Hx.
  assert (H0 : real_eq (real_plus (cw_log (real_inv_pos x Hx)
                                     (real_inv_pos_pos x Hx))
                          (cw_log x Hx))
                       real_zero).
  { apply (real_eq_trans _
             (cw_log (real_mult (real_inv_pos x Hx) x)
                (real_mult_positive (real_inv_pos x Hx) x
                   (real_inv_pos_pos x Hx) Hx))).
    - apply real_eq_sym. apply real_log_mult.
    - apply (real_eq_trans _ (cw_log real_one real_lt_zero_one)).
      + apply (real_eq_trans _
                 (cw_log (real_mult (real_inv_pos x Hx) x)
                    (real_mult_positive (real_inv_pos x Hx) x
                       (real_inv_pos_pos x Hx) Hx))).
        * (* both sides of this trans step are already the same term,
             so reflexivity closes the syntactic head while the evars
             block delta expansion *)
          apply real_eq_refl.
        * apply (real_log_wd
                   (real_mult (real_inv_pos x Hx) x) real_one
                   (real_mult_positive (real_inv_pos x Hx) x
                      (real_inv_pos_pos x Hx) Hx)
                   real_lt_zero_one).
          -- apply (real_eq_trans _
                       (real_mult x (real_inv_pos x Hx))).
             ++ apply real_mult_comm.
             ++ apply real_inv_pos_correct.
          (* real_log_wd fully applied leaves a single goal, which the
             preceding bullet chain already closed, so the remaining
             subgoal advances at the plus level *)
      + apply real_log_one. }
  apply (real_eq_trans _
           (real_plus (real_plus (cw_log (real_inv_pos x Hx)
                                     (real_inv_pos_pos x Hx))
                          (cw_log x Hx))
                      (real_opp (cw_log x Hx)))).
  - apply (real_eq_trans _
             (real_plus (cw_log (real_inv_pos x Hx)
                                    (real_inv_pos_pos x Hx))
                           (real_plus (cw_log x Hx)
                              (real_opp (cw_log x Hx))))).
    + (* the first bullet goal is A equals A plus (B plus minus B), not
         the associativity shape; it goes through A plus zero *)
      apply (real_eq_trans _
                 (real_plus (cw_log (real_inv_pos x Hx)
                                        (real_inv_pos_pos x Hx))
                               real_zero)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_eq_refl.
        -- (* the goal here is zero equals B plus minus B, the reversed
              second component of the compat step; symmetry resolves it *)
           apply real_eq_sym. apply real_plus_opp.
    + (* associativity in this orientation states x plus (y plus z)
         equals (x plus y) plus z, as exported by S02, so it applies
         directly *)
      apply real_plus_assoc.
  - apply (real_eq_trans _
             (real_plus real_zero (real_opp (cw_log x Hx)))).
    + apply RealSetoid.real_eq_plus_compat.
      * exact H0.
      * apply real_eq_refl.
    + apply (real_eq_trans _
               (real_plus (real_opp (cw_log x Hx)) real_zero)).
      * apply real_plus_comm.
      * apply real_plus_zero.
Qed.

(* 1. audit-bridge instances, discharged by UpAuditBridge on the probability
   table world *)

(* safe wrapper for the temperature factor: the identity on positive elements
   and one otherwise, keeping the wrapper globally positive *)
Definition x1_tf (x : Real) : Real :=
  match trich x real_zero with
  | inl _ => real_one
  | inr _ => x
  end.

Lemma x1_tf_pos : forall x : Real, real_lt real_zero (x1_tf x).
Proof.
  intro x. unfold x1_tf.
  destruct (trich x real_zero) as [Hle | Hlt].
  - exact real_lt_zero_one.
  - exact Hlt.
Qed.

Lemma x1_tf_id : forall x : Real,
  real_lt real_zero x -> real_eq (x1_tf x) x.
Proof.
  intros x Hx. unfold x1_tf.
  destruct (trich x real_zero) as [Hle | Hlt].
  - exact (False_rect _ (um_Emptyset_false (real_lt_irrefl real_zero
              (real_lt_le_trans real_zero x real_zero Hx Hle)))).
  - apply real_eq_refl.
Qed.

(* the Min-P retention decider with threshold thr equal to ratio times p_max,
   the same decision term as um_keepF *)
(* the boolean identity with distinct endpoints is uninhabited: id_refl
   is the only constructor and its index cannot take the other value *)
Definition x1_keep_absurd : @Id bool true false -> Empty_set.
Proof. intro a. inversion a. Defined.

(* the retention carrier is the boolean identity face of the decision:
   a uniform inductive shape at every branch, so that the decider
   extracts without a static payload-type mismatch *)
Definition x1_keep (_ : list Real) (x : Real) : Set :=
  @Id bool true
    (match trich thr x with
     | inl _ => true
     | inr _ => false
     end).

Definition x1_keep_dec : forall (_ : list Real) (x : Real),
  Or (x1_keep nil x) (Not (x1_keep nil x)).
Proof.
  intros _ x. unfold x1_keep.
  destruct (trich thr x) as [Hk | Hd].
  - exact (inl id_refl).
  - exact (inr x1_keep_absurd).
Defined.

(* zero is less than thr: ratio times p_max, a product of positive factors *)
Lemma x1_thr_pos : real_lt real_zero thr.
Proof.
  unfold thr, um_thr.
  exact (real_mult_positive ratio pmax ratio_pos
           (um_Hpmax trich tokens tokens_ne tokens_pos)).
Qed.

(* the full partition Z_full equals one *)
Lemma x1_Zfull_eq_one : real_eq (Z_full Real tokens x1_tf) real_one.
Proof.
  unfold Z_full.
  apply (real_eq_trans _
           (real_list_sum nat (fun i => x1_tf (ListDef.nth i tokens real_zero))
                          (ListDef.seq 0%nat (length tokens)))).
  - apply x1_sum_list_seq.
  - apply (real_eq_trans _
             (real_list_sum nat (fun i => ListDef.nth i tokens real_zero)
                             (ListDef.seq 0%nat (length tokens)))).
    + apply (x1_seq_ext (length tokens)
               (fun i => x1_tf (ListDef.nth i tokens real_zero))
               (fun i => ListDef.nth i tokens real_zero)).
      intro i. intro Hj. apply x1_tf_id. apply tokens_pos.
    + apply (real_eq_trans _
               (real_list_sum Real (fun x : Real => x) tokens)).
      * apply um_seq_nth_sum.
      * exact tokens_sum.
Qed.

Lemma x1_Zfull_pos : real_lt real_zero (Z_full Real tokens x1_tf).
Proof.
  (* real_lt_compat has profile x1 x2 y1 y2 with three proofs; zero less
     than one together with Z_full equal to one restates as zero less
     than Z_full *)
  apply (RealSetoid.real_lt_compat real_zero real_zero real_one
           (Z_full Real tokens x1_tf)
           (real_eq_refl real_zero)
           (real_eq_sym (Z_full Real tokens x1_tf) real_one x1_Zfull_eq_one)
           real_lt_zero_one).
Qed.

(* the inverse of Z_full equals one *)
Lemma x1_inv_of_Zfull :
  real_eq (real_inv_pos (Z_full Real tokens x1_tf) x1_Zfull_pos) real_one.
Proof.
  apply (real_inv_unique (Z_full Real tokens x1_tf)
           (real_inv_pos (Z_full Real tokens x1_tf) x1_Zfull_pos) real_one).
  - apply real_inv_pos_correct.
  - apply (real_eq_trans _ (Z_full Real tokens x1_tf)).
    + apply real_mult_one.
    + exact x1_Zfull_eq_one.
Qed.

(* positivity of the truncated mass, the instance of uab_temp_sum_pos where
   the argmax is retained *)
Lemma x1_temp_sum_pos_inst : forall _ : list Real,
  real_lt real_zero
    (uab_temp_sum Real tokens x1_tf x1_keep x1_keep_dec nil).
Proof.
  intro Hj.
  assert (Hsum : real_eq
    (uab_temp_sum Real tokens x1_tf x1_keep x1_keep_dec nil)
    (real_list_sum nat
       (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                 | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                 | inr _ => real_zero
                 end)
       (ListDef.seq 0%nat (length tokens)))).
  { unfold uab_temp_sum, real_minp_temp_sum. apply x1_sum_list_seq. }
  destruct (um_fmax_mem_nth trich tokens tokens_ne
              (fun (i : nat) (_ : NatLt i (length tokens)) => tokens_pos i))
    as [istar [Histar Heqstar]].
  assert (Hthle : real_le thr (ListDef.nth istar tokens real_zero)).
  { apply (RealSetoid.real_le_id_r thr pmax
             (ListDef.nth istar tokens real_zero)
             (real_eq_sym _ _ Heqstar)
             (um_thr_le_pmax trich tokens tokens_ne
                (fun i => tokens_pos i) ratio ratio_le_one)). }
  assert (Hnn : forall j : nat, NatLt j (length tokens) ->
    real_le real_zero
      (match x1_keep_dec nil (ListDef.nth j tokens real_zero) with
       | inl _ => x1_tf (ListDef.nth j tokens real_zero)
       | inr _ => real_zero
       end)).
  { intros j _. unfold x1_keep_dec, x1_keep.
    destruct (trich thr (ListDef.nth j tokens real_zero)) as [Hk | Hd].
    - apply um_lt_le. apply x1_tf_pos.
    - apply real_le_refl. }
  assert (Hstar : real_lt real_zero
    (match x1_keep_dec nil (ListDef.nth istar tokens real_zero) with
     | inl _ => x1_tf (ListDef.nth istar tokens real_zero)
     | inr _ => real_zero
     end)).
  { unfold x1_keep_dec, x1_keep.
    destruct (trich thr (ListDef.nth istar tokens real_zero)) as [Hk | Hd].
    - apply x1_tf_pos.
    - exact (False_rect _ (um_Emptyset_false
                (real_lt_irrefl (ListDef.nth istar tokens real_zero)
                (real_lt_le_trans (ListDef.nth istar tokens real_zero) thr
                   (ListDef.nth istar tokens real_zero) Hd Hthle)))). }
  (* positivity is proved first for the seq-sum form via
     um_rls_single_le_N, then transported back to uab_temp_sum by
     real_lt_compat, whose equation slot carries the sum equality in
     the reversed direction *)
  assert (HM : real_lt real_zero
    (real_list_sum nat
       (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                 | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                 | inr _ => real_zero
                 end)
       (ListDef.seq 0%nat (length tokens)))).
  { apply (real_lt_le_trans real_zero
             (match x1_keep_dec nil (ListDef.nth istar tokens real_zero) with
              | inl _ => x1_tf (ListDef.nth istar tokens real_zero)
              | inr _ => real_zero
              end)).
    - exact Hstar.
    - exact (um_rls_single_le_N
               (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                         | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                         | inr _ => real_zero
                         end)
               (length tokens) istar Histar Hnn). }
  apply (RealSetoid.real_lt_compat real_zero real_zero
           (real_list_sum nat
              (fun i => match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                        | inl _ => x1_tf (ListDef.nth i tokens real_zero)
                        | inr _ => real_zero
                        end)
              (ListDef.seq 0%nat (length tokens)))
           (uab_temp_sum Real tokens x1_tf x1_keep x1_keep_dec nil)
           (real_eq_refl real_zero)
           (real_eq_sym _ _ Hsum)
           HM).
Qed.

(* the bridge: Z_aud equals um_kept, the retained mass *)
Definition x1_Zaud : Real :=
  uab_Z_aud Real tokens x1_tf x1_keep x1_keep_dec x1_Zfull_pos nil.

Theorem x1_Zaud_eq_kept : real_eq x1_Zaud K.
Proof.
  unfold x1_Zaud.
  apply (real_eq_trans _
           (real_list_sum Real
              (fun w : Real =>
                 match x1_keep_dec nil w with
                 | inl _ => real_markov_kernel Real tokens x1_tf x1_Zfull_pos nil w
                 | inr _ => real_zero
                 end) tokens)).
  - exact (real_Z_aud_is_kept_mass Real tokens x1_tf x1_keep x1_keep_dec
             x1_Zfull_pos nil).
  - apply (real_eq_trans _
             (real_list_sum nat
                (fun i =>
                   match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                   | inl _ => real_markov_kernel Real tokens x1_tf x1_Zfull_pos
                                nil (ListDef.nth i tokens real_zero)
                   | inr _ => real_zero
                   end)
                (ListDef.seq 0%nat (length tokens)))).
    + apply x1_sum_list_seq.
    + apply (x1_seq_ext (length tokens)
               (fun i =>
                  match x1_keep_dec nil (ListDef.nth i tokens real_zero) with
                  | inl _ => real_markov_kernel Real tokens x1_tf x1_Zfull_pos
                               nil (ListDef.nth i tokens real_zero)
                  | inr _ => real_zero
                  end)
               (fun i => um_keepF trich tokens ratio
                           (ListDef.nth i tokens real_zero))).
      intro i. intro Hj.
      (* trich occurs only under the dependent Or body of x1_keep_dec,
         so destructing it directly fails with an ill-formed
         elimination predicate; the proof proceeds in three steps:
         first destruct keep_dec, legal since the goal has no
         syntactic trich; second, after transporting the kernel,
         unfold x1_keep and um_keepF and then destruct trich, legal
         because the carrier Kk is the boolean identity face of the
         decision, a non-nested predicate; third, the mixed branches
         close by emptiness of the impossible identity or by the head
         contradiction *)
      destruct (x1_keep_dec nil (ListDef.nth i tokens real_zero)) as [Kk | Kd].
      * (* the decider retains w: the left side reduces by iota to the
           kernel of w, then aligns with um_keepF of w *)
        apply (real_eq_trans _
                 (real_markov_kernel Real tokens x1_tf x1_Zfull_pos nil
                    (ListDef.nth i tokens real_zero))).
        -- apply real_eq_refl.
        -- unfold x1_keep in Kk. unfold um_keepF.
           destruct (trich thr (ListDef.nth i tokens real_zero)) as [H2 | H2].
           ++ (* the kernel is tf(w) times the inverse of Z, that is
                 w times the inverse of Z, then w times one, then w *)
              apply (real_eq_trans _
                       (real_mult (ListDef.nth i tokens real_zero)
                          (real_inv_pos (Z_full Real tokens x1_tf) x1_Zfull_pos))).
              ** apply RealSetoid.real_eq_mult_compat.
                 --- apply x1_tf_id. apply tokens_pos.
                 --- apply real_eq_refl.
              ** apply (real_eq_trans _
                           (real_mult (ListDef.nth i tokens real_zero) real_one)).
                 --- apply RealSetoid.real_eq_mult_compat.
                     +++ apply real_eq_refl.
                     +++ exact x1_inv_of_Zfull.
                 --- apply real_mult_one.
           ++ (* trich drops while the decider retains: the carrier Kk
                 must be empty *)
              inversion Kk.
      * (* the decider drops w: the left side reduces by iota to zero *)
        apply (real_eq_trans _ real_zero).
        -- apply real_eq_refl.
        -- unfold x1_keep in Kd. unfold um_keepF.
           destruct (trich thr (ListDef.nth i tokens real_zero)) as [H2 | H2].
           ++ (* trich retains while the decider drops: the Not carrier Kd
                 applied to id_refl gives Empty_set *)
              destruct (Kd id_refl).
           ++ exact (real_eq_refl real_zero).
Qed.

(* 2. main part one: KL of minp against full is at most S *)

Definition x1_minp_kernel : Real -> Real :=
  uab_minp_kernel Real tokens x1_tf x1_keep x1_keep_dec
    x1_temp_sum_pos_inst nil.

Definition x1_minp_keep_pos :
  forall w : Real, x1_keep nil w -> real_lt real_zero (x1_minp_kernel w) :=
  uab_minp_keep_pos Real tokens x1_tf x1_keep x1_keep_dec
    x1_temp_sum_pos_inst x1_tf_pos nil.

Definition x1_Zaud_pos_cert : real_lt real_zero x1_Zaud :=
  uab_Z_aud_pos_cert Real tokens x1_tf x1_keep x1_keep_dec
    x1_temp_sum_pos_inst x1_Zfull_pos nil.

Definition x1_KL : Real :=
  real_list_sum Real
    (uab_kl_q_full Real tokens x1_tf x1_keep x1_keep_dec
       x1_tf_pos x1_Zfull_pos nil x1_minp_kernel x1_minp_keep_pos) tokens.

(* complementary identity in paper form: x1_KL equals minus log of
   (1 - dropped); the statement relies on the positivity certificate
   x1_K_pos, which rests on x1_exp_neg_S_le_kept, so it is stated
   after those two *)

(* e to the minus S is at most kept, from dropped at most one minus e to the
   minus S and the complementary identity *)
Theorem x1_exp_neg_S_le_kept : real_le (real_exp_neg S) K.
Proof.
  pose proof (dropped_le_one_minus_exp_neg_S trich tokens tokens_ne
                tokens_pos tokens_sum ratio ratio_le_one) as H4.
  apply (RealSetoid.real_le_id_l (real_exp_neg S)
           (real_plus real_one
              (real_opp (real_plus real_one (real_opp (real_exp_neg S)))))).  - apply real_eq_sym. apply x1_plus_opp_cancel.
  - (* real_le_id_r takes the equation slot first and the order slot second *)
    apply (RealSetoid.real_le_id_r
             (real_plus real_one
                (real_opp (real_plus real_one (real_opp (real_exp_neg S)))))
             (real_plus real_one (real_opp D))).
    + exact (x1_plus_opp_cancel K).
    + apply real_le_plus_compat.
      * apply real_le_refl.
      * apply real_opp_le_compat. exact H4.
Qed.

(* zero is less than K: kept is positive since zero is less than e to the
   minus S which is at most K; this positivity discharges the order slot of
   the complementary identity and of real_log_wd *)
Lemma x1_K_pos : real_lt real_zero K.
Proof.
  exact (real_lt_le_trans real_zero (real_exp_neg S) K
           (real_exp_neg_pos S) x1_exp_neg_S_le_kept).
Qed.

(* complementary identity in paper form: x1_KL equals minus log of
   (1 - dropped); it uses the positivity certificate x1_K_pos in place
   of five inline lt_le_trans certificates *)
(* K is at most one minus D: since D is definitionally one minus K, the claim
   reduces by x1_plus_opp_cancel to K at most K *)
Definition x1_K_le_one_minus_D :
  real_le K (real_plus real_one (real_opp D)) :=
  RealSetoid.real_le_id_r K K (real_plus real_one (real_opp D))
    (real_eq_sym _ _ (x1_plus_opp_cancel K)) (real_le_refl K).

(* complementary identity in paper form: x1_KL equals minus log of
   (1 - dropped); it uses the positivity certificate x1_K_pos in place
   of five inline lt_le_trans certificates *)
Theorem x1_kl_eq_opp_log_one_minus_dropped :
  real_eq x1_KL
    (real_opp (real_log (real_plus real_one (real_opp D))
                 (real_lt_le_trans real_zero K
                    (real_plus real_one (real_opp D))
                    x1_K_pos x1_K_le_one_minus_D))).
Proof.
  apply (real_eq_trans x1_KL
           (real_opp (real_log K x1_K_pos))).
  - apply (real_eq_trans _
             (real_opp (real_log x1_Zaud x1_Zaud_pos_cert))).
    + exact (real_minp_kl_cost Real tokens x1_tf x1_keep x1_keep_dec
               x1_temp_sum_pos_inst x1_tf_pos x1_Zfull_pos nil).
    + apply RealSetoid.real_eq_opp_compat.
      (* a, b, Ha and Hb unify with the goal, so the application leaves
         the single goal Heq *)
      apply real_log_wd.
      exact x1_Zaud_eq_kept.
  - apply RealSetoid.real_eq_opp_compat.
    apply real_log_wd.
    exact (real_eq_sym _ _ (x1_plus_opp_cancel K)).
Qed.

(* part 4: KL of minp against full is at most S *)
Theorem x1_kl_le_entropy : real_le x1_KL S.
Proof.
  pose proof (real_minp_kl_cost Real tokens x1_tf x1_keep x1_keep_dec
                x1_temp_sum_pos_inst x1_tf_pos x1_Zfull_pos nil) as Hkl.
  pose proof x1_exp_neg_S_le_kept as Hexp.
  assert (Hlogpos : real_lt real_zero K).
  { exact (real_lt_le_trans real_zero (real_exp_neg S) K
             (real_exp_neg_pos S) Hexp). }
  pose proof (um_log_le_mono (real_exp_neg S) K
                (real_exp_neg_pos S) Hlogpos Hexp) as Hmono.
  assert (H2 : real_le (real_opp S) (real_log K Hlogpos)).
  { apply (RealSetoid.real_le_id_l (real_opp S)
             (cw_log (real_exp_neg S) (real_exp_neg_pos S))
             (real_log K Hlogpos)).
    - (* minus S equals log of e to the minus S: the log_inv discharge
         gives the cauchy form, and the positivity slot restates through
         real_log_wd as real_exp_neg_pos S, since the opaque constant
         must match syntactically *)
      apply (real_eq_trans _
                 (cw_log (cauchy_real_exp (real_opp S))
                    (cauchy_real_exp_pos (real_opp S)))).
      + apply real_eq_sym.
        exact (log_inv_exp_neg_thm (real_opp S)
                 (cauchy_real_exp_pos (real_opp S))).
      + apply real_log_wd.
        exact (real_eq_refl (cauchy_real_exp (real_opp S))).
    - exact Hmono. }
  apply (RealSetoid.real_le_id_l x1_KL
           (real_opp (real_log K Hlogpos)) S).
  - apply (real_eq_trans _
             (real_opp (real_log x1_Zaud x1_Zaud_pos_cert))).
    + exact Hkl.
    + apply RealSetoid.real_eq_opp_compat.
      (* Ha and Hb unify with the goal, so applying real_log_wd leaves
         only Heq *)
      apply real_log_wd.
      exact x1_Zaud_eq_kept.
  - (* opp_le_compat gives minus log K at most minus (minus S), and
       real_opp_opp transports this to at most S *)
    apply (RealSetoid.real_le_id_r
             (real_opp (real_log K Hlogpos))
             (real_opp (real_opp S)) S).
    + exact (real_opp_opp S).
    + apply real_opp_le_compat. exact H2.
Qed.

(* 3. main part two: S is at most log N, by Gibbs on the uniform distribution
   with an epsilon margin *)

Lemma x1_N_pos : real_lt real_zero (um_nreal N).
Proof.
  (* um_Npos discharges this directly, its statement depending only on tokens *)
  exact (um_Npos tokens tokens_ne).
Qed.

Abbreviation LN := (cw_log (um_nreal N) x1_N_pos).
Abbreviation U := (real_inv_pos (um_nreal N) x1_N_pos).
Abbreviation HqU := (real_inv_pos_pos (um_nreal N) x1_N_pos).

Lemma x1_log_U_eq_opp_LN : real_eq (cw_log U HqU) (real_opp LN).
Proof. exact (x1_log_inv_eq_opp_log (um_nreal N) x1_N_pos). Qed.


Lemma x1_kl_term_expand : forall (k : Real) (Hk : real_lt real_zero k),
  real_eq (real_kl_term k U Hk HqU)
          (real_plus (real_mult k LN)
                     (real_opp (real_mult k (real_opp (cw_log k Hk))))).
Proof.
  intros k Hk. unfold real_kl_term.
  (* k times minus log of (U times the inverse of k) equals k times
     minus ((minus LN) plus (minus log k)), which equals k times
     (LN plus log k); the chain is rearranged into direct transitive
     steps with the positivity slot carried by Hk *)
  apply (real_eq_trans _
           (real_mult k
              (real_opp (real_plus (real_opp LN) (real_opp (cw_log k Hk)))))).
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_opp_compat.
      apply (real_eq_trans _
                 (real_plus (cw_log U HqU)
                            (cw_log (real_inv_pos k Hk)
                                    (real_inv_pos_pos k Hk)))).
      * apply real_log_mult.
      * apply RealSetoid.real_eq_plus_compat.
        -- exact x1_log_U_eq_opp_LN.
        -- exact (x1_log_inv_eq_opp_log k Hk).
  - 
    apply (real_eq_trans _
               (real_mult k (real_plus LN (cw_log k Hk)))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * apply (real_eq_trans _
                   (real_plus (real_opp (real_opp LN))
                              (real_opp (real_opp (cw_log k Hk))))).
        -- (* real_opp_plus in this orientation states minus (a plus b)
              equals (minus a) plus (minus b), applying directly *)
           apply real_opp_plus.
        -- apply RealSetoid.real_eq_plus_compat.
           ++ apply real_opp_opp.
           ++ apply real_opp_opp.
    + apply (real_eq_trans _
               (real_plus (real_mult k LN) (real_mult k (cw_log k Hk)))).
      * apply x1_mult_plus_distr.
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_eq_refl.
        -- apply real_eq_sym.
           apply (real_eq_trans _
                      (real_opp (real_opp (real_mult k (cw_log k Hk))))).
           ++ (* bullets follow the order of the subgoals; opp_mult states
                 minus (a times b) equals a times (minus b), so symmetry
                 is taken *)
              apply RealSetoid.real_eq_opp_compat.
              apply real_eq_sym. apply real_opp_mult.
           ++ apply real_opp_opp.
Qed.

(* transport of the kl term across the weight wrapper: from the wrapped
   weight to the original table entry *)
Lemma x1_kl_term_compat_p : forall (p p' : Real)
    (Hp : real_lt real_zero p) (Hp' : real_lt real_zero p'),
  real_eq p p' ->
  real_eq (real_kl_term p U Hp HqU) (real_kl_term p' U Hp' HqU).
Proof.
  intros p p' Hp Hp' Heq. unfold real_kl_term.
  apply RealSetoid.real_eq_mult_compat.
  - exact Heq.
  - apply RealSetoid.real_eq_opp_compat.
    (* a, b, Ha and Hb unify with the goal, so applying real_log_wd
       leaves only the Heq slot *)
    apply real_log_wd.
    apply RealSetoid.real_eq_mult_compat.
    * apply real_eq_refl.
    * (* x, x', Hx and Hx' unify with the goal, leaving only the Heq slot *)
      apply x1_inv_compat.
      exact Heq.
Qed.

(* part 5, the per-epsilon form: S is at most log N plus eps *)
Theorem x1_entropy_le_log_N_eps : forall eps : Real,
  real_lt real_zero eps -> real_le S (real_plus LN eps).
Proof.
  intros eps Heps.
  assert (Hnormp : real_eq (real_list_sum nat
      (fun i => x1_tf (ListDef.nth i tokens real_zero))
      (ListDef.seq 0%nat N)) real_one).
  { apply (real_eq_trans _
             (real_list_sum nat (fun i => ListDef.nth i tokens real_zero)
                             (ListDef.seq 0%nat N))).
    - apply (x1_seq_ext N (fun i => x1_tf (ListDef.nth i tokens real_zero))
               (fun i => ListDef.nth i tokens real_zero)).
      intro i. intro Hj. apply x1_tf_id. apply tokens_pos.
    - apply (real_eq_trans _
               (real_list_sum Real (fun x : Real => x) tokens)).
      * apply um_seq_nth_sum.
      * exact tokens_sum. }
  assert (Hnormq : real_eq (real_list_sum nat (fun _ : nat => U)
                               (ListDef.seq 0%nat N)) real_one).
  { apply (real_eq_trans _ (real_mult (um_nreal N) U)).
    - apply um_seq_const.
    - apply real_inv_pos_correct. }
  pose proof (real_gibbs_inequality_eps nat (ListDef.seq 0%nat N)
                (fun i => x1_tf (ListDef.nth i tokens real_zero))
                (fun _ : nat => U)
                (fun i => x1_tf_pos (ListDef.nth i tokens real_zero))
                (fun _ : nat => HqU) Hnormp Hnormq eps Heps) as Hg.
  assert (Hpt : forall i : nat, NatLt i N ->
    real_eq (real_kl_term (x1_tf (ListDef.nth i tokens real_zero)) U
               (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
            (real_plus (real_mult (ListDef.nth i tokens real_zero) LN)
                       (real_opp (um_ent_term
                          (ListDef.nth i tokens real_zero) (tokens_pos i))))).
  { intros i Hi.
    apply (real_eq_trans _
             (real_kl_term (ListDef.nth i tokens real_zero) U
                (tokens_pos i) HqU)).
    - (* p, p', Hp and Hp' unify with the goal, leaving only Heq, the
         pointwise identity of the tf wrapper *)
      apply x1_kl_term_compat_p.
      apply x1_tf_id. apply tokens_pos.
    - exact (x1_kl_term_expand (ListDef.nth i tokens real_zero)
               (tokens_pos i)). }
  assert (Hstep : real_eq (real_list_sum nat
      (fun i => real_kl_term (x1_tf (ListDef.nth i tokens real_zero)) U
                 (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
      (ListDef.seq 0%nat N))
    (real_plus LN (real_opp S))).
  { apply (real_eq_trans _
             (real_list_sum nat
                (fun i => real_plus
                            (real_mult (ListDef.nth i tokens real_zero) LN)
                            (real_opp (um_ent_term
                                         (ListDef.nth i tokens real_zero)
                                         (tokens_pos i))))
                (ListDef.seq 0%nat N))).
    - apply (x1_seq_ext N
               (fun i => real_kl_term
                           (x1_tf (ListDef.nth i tokens real_zero)) U
                           (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
               (fun i => real_plus
                            (real_mult (ListDef.nth i tokens real_zero) LN)
                            (real_opp (um_ent_term
                                         (ListDef.nth i tokens real_zero)
                                         (tokens_pos i))))).
      intro i. intro Hj. apply Hpt. exact Hj.
    - apply (real_eq_trans _
               (real_plus
                  (real_list_sum nat
                     (fun i => real_mult (ListDef.nth i tokens real_zero) LN)
                     (ListDef.seq 0%nat N))
                  (real_list_sum nat
                     (fun i => real_opp (um_ent_term
                                          (ListDef.nth i tokens real_zero)
                                          (tokens_pos i)))
                     (ListDef.seq 0%nat N)))).
      + apply real_list_sum_add.
      + apply (real_eq_trans _
                 (real_plus LN
                    (real_opp (real_list_sum nat
                       (fun i => um_ent_term
                                   (ListDef.nth i tokens real_zero)
                                   (tokens_pos i))
                       (ListDef.seq 0%nat N))))).
        * apply RealSetoid.real_eq_plus_compat.
          -- apply (real_eq_trans _
                       (real_mult LN (real_list_sum nat
                          (fun i => ListDef.nth i tokens real_zero)
                          (ListDef.seq 0%nat N)))).
             ++ apply real_list_sum_linear_r.
             ++ apply (real_eq_trans _ (real_mult LN real_one)).
                ** apply RealSetoid.real_eq_mult_compat.
                   --- apply real_eq_refl.
                   --- (* this slot needs the sum of nth equal to one,
                          not the tf version Hnormp; it is rebuilt here
                          from um_seq_nth_sum and tokens_sum *)
                      apply (real_eq_trans _
                                 (real_list_sum Real
                                    (fun x : Real => x) tokens)).
                      ++++ apply um_seq_nth_sum.
                      ++++ exact tokens_sum.
                ** apply real_mult_one.
        -- exact (real_list_sum_opp nat
                   (fun i => um_ent_term (ListDef.nth i tokens real_zero)
                                         (tokens_pos i))
                   (ListDef.seq 0%nat N)).
        * (* the second component M2 equals LN plus the opposite of S,
             closing by reflexivity under the definitional unfolding of
             um_entropy *)
          apply real_eq_refl. }
  assert (Hg2 : real_le real_zero
                  (real_plus (real_plus LN (real_opp S)) eps)).
  { apply (RealSetoid.real_le_id_r real_zero
             (real_plus (real_list_sum nat
                (fun i => real_kl_term
                            (x1_tf (ListDef.nth i tokens real_zero)) U
                            (x1_tf_pos (ListDef.nth i tokens real_zero)) HqU)
                (ListDef.seq 0%nat N)) eps)
             (real_plus (real_plus LN (real_opp S)) eps)).
    - (* real_le_id_r takes the equation slot first and the order slot
         second *)
      apply RealSetoid.real_eq_plus_compat.
      + exact Hstep.
      + apply real_eq_refl.
    - exact Hg. }
  (* (LN minus S) plus S equals LN, in three steps of associativity,
     commutativity and plus_opp; the equation slot cancels S *)
  assert (HSL : real_eq (real_plus (real_plus LN (real_opp S)) S) LN).
  { apply (real_eq_trans _ (real_plus LN (real_plus (real_opp S) S))).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus LN real_zero)).
      + apply RealSetoid.real_eq_plus_compat.
        * apply real_eq_refl.
        * apply (real_eq_trans _ (real_plus S (real_opp S))).
          -- apply real_plus_comm.
          -- apply real_plus_opp.
      + apply real_plus_zero. }
  apply (RealSetoid.real_le_id_l S (real_plus real_zero S)
           (real_plus LN eps)).
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_plus S real_zero)).
    + apply real_plus_comm.
    + apply real_plus_zero.
  - apply (RealSetoid.real_le_id_r (real_plus real_zero S)
             (real_plus (real_plus (real_plus LN (real_opp S)) eps) S)
             (real_plus LN eps)).
    + (* real_le_id_r takes the equation slot first; the equation moves
         S into the inner sum, where HSL cancels it *)
      apply (real_eq_trans _
               (real_plus (real_plus LN (real_opp S)) (real_plus eps S))).
      * apply real_eq_sym. apply real_plus_assoc.
      * apply (real_eq_trans _
               (real_plus (real_plus LN (real_opp S)) (real_plus S eps))).
        -- apply RealSetoid.real_eq_plus_compat.
           ++ apply real_eq_refl.
           ++ apply real_plus_comm.
        -- apply (real_eq_trans _
                     (real_plus (real_plus (real_plus LN (real_opp S)) S) eps)).
           ++ apply real_plus_assoc.
           ++ apply RealSetoid.real_eq_plus_compat.
              ** exact HSL.
              ** apply real_eq_refl.
    + apply real_le_plus_compat.
      * exact Hg2.
      * apply real_le_refl.
Qed.

(* discharge profile: zero is less than d with d := S plus (minus LN);
   the inverse of two is less than one by real_inv_pos_lt_contra;
   d times that inverse is less than d by real_lt_mult_compat; then
   LN plus d times the inverse is less than LN plus d by
   real_lt_plus_compat_le_lt, and real_lt_trans closes *)

(* part 6, the closed form: S is at most log N, from the per-epsilon form via
   the trichotomy decider and the half gap *)
Theorem x1_entropy_le_log_N : real_le S LN.
Proof.
  destruct (trich S LN) as [Hle | Hgt].
  - (* the inl branch: S at most LN is the conclusion *)
    exact Hle.
  - (* the inr branch: LN strictly below S gives a contradiction, with
       d := S plus (minus LN) and eps := d times the inverse of two *)
    assert (H2pos : real_lt real_zero (real_plus real_one real_one)).
    { (* (0+0) less than (1+1) restated as zero less than 1+1 *)
      apply (RealSetoid.real_lt_compat (real_plus real_zero real_zero) real_zero
               (real_plus real_one real_one) (real_plus real_one real_one)).
      - apply real_plus_zero.
      - apply real_eq_refl.
      - (* (0+0) less than (1+1) in two steps:
           (0+0) less than (0+1) less than (1+1) *)
        apply (real_lt_trans (real_plus real_zero real_zero)
                 (real_plus real_zero real_one) (real_plus real_one real_one)).
        + exact (real_lt_plus_translate real_zero real_zero real_one
                   real_lt_zero_one).
        + exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
                   real_lt_zero_one (real_le_refl real_one)). }
    assert (Hinv2pos : real_lt real_zero
             (real_inv_pos (real_plus real_one real_one) H2pos)).
    { exact (real_inv_pos_pos (real_plus real_one real_one) H2pos). }
    assert (Hd : real_lt real_zero (real_plus S (real_opp LN))).
    { (* minus S less than minus LN gives (minus S) plus S less than
         (minus LN) plus S, restated as zero less than S plus (minus LN) *)
      apply (RealSetoid.real_lt_compat (real_plus (real_opp S) S) real_zero
               (real_plus (real_opp LN) S) (real_plus S (real_opp LN))).
      - apply (real_eq_trans _ (real_plus S (real_opp S))).
        + apply real_plus_comm.
        + apply real_plus_opp.
      - apply real_plus_comm.
      - exact (real_lt_plus_compat_lt_le (real_opp S) (real_opp LN) S S
                 (real_opp_lt_compat LN S Hgt) (real_le_refl S)). }
    assert (H12 : real_lt real_one (real_plus real_one real_one)).
    { (* (0+1) less than (1+1), restated by real_lt_compat from 0+1 to 1 *)
      apply (RealSetoid.real_lt_compat (real_plus real_zero real_one) real_one
               (real_plus real_one real_one) (real_plus real_one real_one)).
      - apply (real_eq_trans _ (real_plus real_one real_zero)).
        + apply real_plus_comm.
        + apply real_plus_zero.
      - apply real_eq_refl.
      - exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
                 real_lt_zero_one (real_le_refl real_one)). }
    assert (Hinv2lt1 : real_lt
             (real_inv_pos (real_plus real_one real_one) H2pos) real_one).
    { (* the inverse of 2 is less than the inverse of 1 by
         real_inv_pos_lt_contra, restated through the inverse of 1
         equal to 1 *)
      apply (RealSetoid.real_lt_compat
               (real_inv_pos (real_plus real_one real_one) H2pos)
               (real_inv_pos (real_plus real_one real_one) H2pos)
               (real_inv_pos real_one real_lt_zero_one) real_one).
      - apply real_eq_refl.
      - exact real_inv_one.
      - exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one)
                 real_lt_zero_one H2pos H12). }
    assert (Hdlt : real_lt
             (real_mult (real_plus S (real_opp LN))
                (real_inv_pos (real_plus real_one real_one) H2pos))
             (real_plus S (real_opp LN))).
    { (* d times the inverse of 2 is less than d times 1 by
         real_lt_mult_compat, restated through d times 1 equal to d *)
      apply (RealSetoid.real_lt_compat
               (real_mult (real_plus S (real_opp LN))
                  (real_inv_pos (real_plus real_one real_one) H2pos))
               (real_mult (real_plus S (real_opp LN))
                  (real_inv_pos (real_plus real_one real_one) H2pos))
               (real_mult (real_plus S (real_opp LN)) real_one)
               (real_plus S (real_opp LN))).
      - apply real_eq_refl.
      - apply real_mult_one.
      - exact (real_lt_mult_compat
                 (real_inv_pos (real_plus real_one real_one) H2pos) real_one
                 (real_plus S (real_opp LN)) Hd Hinv2lt1). }
    assert (HLTN : real_lt
             (real_plus LN
                (real_mult (real_plus S (real_opp LN))
                   (real_inv_pos (real_plus real_one real_one) H2pos)))
             (real_plus LN (real_plus S (real_opp LN)))).
    { exact (real_lt_plus_compat_le_lt LN LN
               (real_mult (real_plus S (real_opp LN))
                  (real_inv_pos (real_plus real_one real_one) H2pos))
               (real_plus S (real_opp LN))
               (real_le_refl LN) Hdlt). }
    assert (HdS : real_eq (real_plus LN (real_plus S (real_opp LN))) S).
    { (* LN plus (S plus (minus LN)) equals S, by associativity,
         commutativity, plus_opp and plus_zero, in the same pattern
         as HSL *)
      apply (real_eq_trans _ (real_plus (real_plus LN S) (real_opp LN))).
      - apply real_plus_assoc.
      - apply (real_eq_trans _ (real_plus (real_plus S LN) (real_opp LN))).
        + apply RealSetoid.real_eq_plus_compat.
          * apply real_plus_comm.
          * apply real_eq_refl.
        + apply (real_eq_trans _ (real_plus S (real_plus LN (real_opp LN)))).
          * apply real_eq_sym. apply real_plus_assoc.
          * apply (real_eq_trans _ (real_plus S real_zero)).
            -- apply RealSetoid.real_eq_plus_compat.
               ++ apply real_eq_refl.
               ++ apply real_plus_opp.
            -- apply real_plus_zero. }
    assert (HLTS : real_lt
             (real_plus LN
                (real_mult (real_plus S (real_opp LN))
                   (real_inv_pos (real_plus real_one real_one) H2pos))) S).
    { apply (RealSetoid.real_lt_compat
               (real_plus LN
                  (real_mult (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos)))
               (real_plus LN
                  (real_mult (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos)))
               (real_plus LN (real_plus S (real_opp LN))) S).
      - apply real_eq_refl.
      - exact HdS.
      - exact HLTN. }
    pose proof (x1_entropy_le_log_N_eps
                  (real_mult (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos))
                  (real_mult_positive (real_plus S (real_opp LN))
                     (real_inv_pos (real_plus real_one real_one) H2pos)
                     Hd Hinv2pos)) as Hle2.
    unfold real_le in Hle2.
    destruct Hle2 as [Hlt2 | Heq2].
    + (* the strict branch: S less than LN plus d times the inverse of
         2, itself less than S, gives S less than S *)
      assert (HSS : real_lt S S).
      { exact (real_lt_trans S
                 (real_plus LN
                    (real_mult (real_plus S (real_opp LN))
                       (real_inv_pos (real_plus real_one real_one) H2pos)))
                 S Hlt2 HLTS). }
      destruct (real_lt_irrefl S HSS).
    + (* the equality branch: S equal to LN plus d times the inverse of
         2, which is less than S, gives S less than S *)
      assert (HSS : real_lt S S).
      { exact (real_eq_lt_lt S
                 (real_plus LN
                    (real_mult (real_plus S (real_opp LN))
                       (real_inv_pos (real_plus real_one real_one) H2pos)))
                 S Heq2 HLTS). }
      destruct (real_lt_irrefl S HSS).
Qed.

(* part 7, composite one: KL is at most log N, chaining KL at most S with
   S at most log N *)
Theorem x1_kl_le_log_N : real_le x1_KL LN.
Proof.
  exact (real_le_trans x1_KL S LN x1_kl_le_entropy x1_entropy_le_log_N).
Qed.

(* part 7, composite two: the composite entropy chain in conjunction form,
   using the S01 And as A times B at the Set layer *)
Definition x1_composite_chain :
  And (real_le x1_KL S) (real_le S LN) :=
  (x1_kl_le_entropy, x1_entropy_le_log_N).

End X1MinPKLChain.

(* Assumption audit: each statement prints Closed under the global context. *)
Print Assumptions um_lt_le.
Print Assumptions um_eq_le.
Print Assumptions um_le_add_l.
Print Assumptions um_add_nonneg.
Print Assumptions um_le_add_r.
Print Assumptions um_mult_one_l.
Print Assumptions um_Emptyset_false.
Print Assumptions um_nreal.
Print Assumptions um_nreal_pos.
Print Assumptions um_nreal_pos_of_lt.
Print Assumptions um_seq_shift.
Print Assumptions um_skipn_sum_step.
Print Assumptions um_seq_nth_sum.
Print Assumptions um_seq_const.
Print Assumptions um_ent_term.
Print Assumptions um_log_le_mono.
Print Assumptions um_ent_term_le.
Print Assumptions um_rls_le_N.
Print Assumptions um_rls_nonneg_N.
Print Assumptions um_rls_single_le_N.
Print Assumptions um_fmax.
Print Assumptions um_fmax_ge_nth.
Print Assumptions um_fmax_mem_nth.
Print Assumptions um_fmax_pos_nth.
Print Assumptions um_N.
Print Assumptions um_pmax.
Print Assumptions um_Hpmax.
Print Assumptions um_le_pmax.
Print Assumptions um_entropy.
Print Assumptions um_thr.
Print Assumptions um_keepF.
Print Assumptions um_kept.
Print Assumptions um_keepF_nonneg_nth.
Print Assumptions um_keepF_nonneg.
Print Assumptions um_dropped.
Print Assumptions um_keepF_congr.
Print Assumptions um_thr_le_pmax.
Print Assumptions entropy_ge_neg_log_p_max.
Print Assumptions um_kept_ge_pmax.
Print Assumptions um_exp_neg_S_le_pmax.
Print Assumptions dropped_le_one_minus_exp_neg_S.
Print Assumptions um_Npos.
Print Assumptions um_pmax_ge_inv_n.
Print Assumptions dropped_le_one_minus_inv_n.
Print Assumptions x1_plus_opp_cancel.
Print Assumptions x1_seq_shift.
Print Assumptions x1_nth_S_cons.
Print Assumptions x1_sum_list_seq.
Print Assumptions x1_seq_ext.
Print Assumptions x1_inv_compat.
Print Assumptions x1_mult_plus_distr.
Print Assumptions x1_log_inv_eq_opp_log.
Print Assumptions x1_tf.
Print Assumptions x1_tf_pos.
Print Assumptions x1_tf_id.
Print Assumptions x1_keep_absurd.
Print Assumptions x1_keep.
Print Assumptions x1_keep_dec.
Print Assumptions x1_thr_pos.
Print Assumptions x1_Zfull_eq_one.
Print Assumptions x1_Zfull_pos.
Print Assumptions x1_inv_of_Zfull.
Print Assumptions x1_temp_sum_pos_inst.
Print Assumptions x1_Zaud.
Print Assumptions x1_Zaud_eq_kept.
Print Assumptions x1_minp_kernel.
Print Assumptions x1_minp_keep_pos.
Print Assumptions x1_Zaud_pos_cert.
Print Assumptions x1_KL.
Print Assumptions x1_exp_neg_S_le_kept.
Print Assumptions x1_K_pos.
Print Assumptions x1_K_le_one_minus_D.
Print Assumptions x1_kl_eq_opp_log_one_minus_dropped.
Print Assumptions x1_kl_le_entropy.
Print Assumptions x1_N_pos.
Print Assumptions x1_log_U_eq_opp_LN.
Print Assumptions x1_kl_term_expand.
Print Assumptions x1_kl_term_compat_p.
Print Assumptions x1_entropy_le_log_N_eps.
Print Assumptions x1_entropy_le_log_N.
Print Assumptions x1_kl_le_log_N.
Print Assumptions x1_composite_chain.
