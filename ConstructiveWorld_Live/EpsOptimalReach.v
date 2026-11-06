(* ConstructiveWorld-Set -- statement-family compendium: eps-optimal reachability and min-p truncation theorems. *)

(** * EpsOptimalReach: argmin engines and eps-optimal reach witnesses.

    Mission.  Formalizes the req-layer argmin engine, the min-p truncation
      budget ([req_rsum_le_const_mp], [mpd_minp_max_ge_inv_vocab_size],
      [mpd_minp_dropped_mass_le_inv_vocab_size]), its generic engine
      ([rae_argmin_aux_min], [rae_pick_optimal]), and the eps-optimal
      reach witnesses ([finite_table_eps_optimal_witness],
      [trajectory_eps_optimal_reach], [quad_cost_descent_eps_bound]).

    Dependencies.  Stdlib [List], [QArith], [Lia].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqDist], [UpReqAlignRestB], [UpReqAlgebra], and
      [UpReqPropLiftShim] of this development.

    References.  This development, EpsOptimalReach.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" EpsOptimalReach.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import UpReqDist.
Require Import UpReqAlignRestB.
Require Import UpReqAlgebra.
From Stdlib Require Import List.
Require Import UpReqPropLiftShim.
From Stdlib Require Import List QArith Lia.

(* ================= Section 1. The reqd_of_nat_succ family ================= *)
(* ================= Section 1. The reqd_of_nat_succ family ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* Interface adaptation: the interface class in this tree is unparameterized; its carrier is
   the global Real (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid
   plus the global Instance RealEnhancedReal; abbreviation passthrough in the sense of the
   world's own UpReqAlign3.v / UpReqAlignRestB.v precedent, spelled with the Abbreviation
   vernacular -- the non-deprecated form of the identical syntactic abbreviation).  The
   parameterized section binders
   Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are removed throughout; the carrier
   R is bound to the global Real by the Abbreviation below, and the class fields
   (req/lt/le/zero/one/plus/mult/opp/inv_pos/exp_neg and the lemma fields) resolve through the
   global instance RealEnhancedReal.  Because the instance is concrete, plain simpl/cbn would
   delta-unfold the field projections through it; the proofs therefore reduce with
   cbn -[...] blacklisting the field names (the UpReqAlignRestB.v Part-0 form), which restores
   the pointwise-stuck face the source proofs were written under.  Zero Obj.magic, zero Prop
   casts; statement names and proof bodies are unchanged apart from the dropped binder
   arguments and the cbn blacklist. *)
Abbreviation R := Real.
(* The interface fields used below are bound to the concrete global twins -- the very
   bindings that the global RealEnhancedReal instance assigns to these fields
   (S07_RealSetoidExpLog.v instance block).  This keeps every statement elaborating to the
   same term as before while making the extracted signatures informative: the extractor
   renders accessor applications of the Set-valued fields (req/lt/le) as casts over the
   erased type face, so each field occurrence must be the concrete constant for the
   extraction to be cast-free. *)
Abbreviation lt := real_lt.
Abbreviation req := real_eq.
Abbreviation le := real_le.
Abbreviation req_refl := real_eq_refl.
Abbreviation req_sym := real_eq_sym.
Abbreviation req_trans := real_eq_trans.
Abbreviation zero := real_zero.
Abbreviation one := real_one.
Abbreviation plus := real_plus.
Abbreviation mult := real_mult.
Abbreviation opp := real_opp.
Abbreviation req_plus_compat := RealSetoid.real_eq_plus_compat_adapt.
Abbreviation req_mult_compat := RealSetoid.real_eq_mult_compat_adapt.
Abbreviation req_opp_compat := RealSetoid.real_eq_opp_compat.
Abbreviation plus_zero := real_plus_zero.
Abbreviation plus_comm := real_plus_comm.
Abbreviation distrib := real_distrib.
Abbreviation lt_plus_compat := real_lt_plus_compat.
Abbreviation mult_assoc := real_mult_assoc.
Abbreviation mult_comm := real_mult_comm.
Abbreviation mult_one := real_mult_one.
Abbreviation mult_zero := real_mult_zero.
Abbreviation le_refl := real_le_refl.
Abbreviation le_trans := real_le_trans.
Abbreviation lt_le_iff := RealSetoid.real_lt_le_iff_req.
Abbreviation le_id_l := RealSetoid.real_le_id_l.
Abbreviation le_id_r := RealSetoid.real_le_id_r.
Abbreviation lt_id_r := RealSetoid.real_lt_id_r.
Abbreviation lt_id_l := RealSetoid.real_lt_id_l.
Abbreviation inv_pos := real_inv_pos.
Abbreviation inv_pos_correct := real_inv_pos_correct.
Abbreviation inv_pos_pos := real_inv_pos_pos.
Abbreviation one_pos := real_lt_zero_one.
Abbreviation le_plus_compat := real_le_plus_compat.
Abbreviation plus_positive := real_plus_positive.
Abbreviation mult_positive := real_mult_positive.
Abbreviation le_mult_compat := real_le_mult_compat.
Abbreviation le_mult_compat_weak := real_le_mult_compat_weak.
Abbreviation opp_le_compat := real_opp_le_compat.
Abbreviation exp_neg := real_exp_neg.
Abbreviation exp_neg_pos := real_exp_neg_pos.
Abbreviation exp_neg_le_decr := real_exp_neg_le_decr.

(* ============ Concrete-carrier specializations of the Part-0 list-sum machine ============ *)
(*   The rls_* family of UpReqAlignRestB.v and the req_le_mult_le_one_r bound are stated
   over the class fields, whose faces the extractor renders as erased types; consuming
   them from the concrete carriers of this file would leave casts at every seam.  These
   one-off specializations restate exactly those statements over the concrete S02
   carriers (proof bodies transplanted verbatim modulo the concrete lemma names and the
   targeted cbn), per the M34b specialization rule. *)
Lemma rls_pos_c : forall (A : Set) (f : A -> R),
  (forall a : A, lt zero (f a)) ->
  forall l : list A, Not (Id l nil) -> lt zero (rsum A f l).
Proof.
  intros A f Hf l. induction l as [|w rest IH].
  - intro Hnil. exact (match Hnil (@id_refl (list A) nil) with end).
  - destruct rest as [|w' rest'].
    + cbn [rsum]. intro Hc0. apply (lt_id_r zero (f w) (plus (f w) zero)).
      * apply (req_sym (plus (f w) zero) (f w)). apply plus_zero.
      * apply Hf.
    + cbn [rsum]. intro Hc1. apply (lt_id_l zero (plus zero zero)
                                             (plus (f w) (plus (f w') (rsum A f rest')))).
      * apply (req_sym (plus zero zero) zero). apply plus_zero.
      * apply lt_plus_compat.
        -- apply Hf.
        -- apply IH. intro Hc. inversion Hc.
Qed.

Lemma rls_ext_c : forall (A : Set) (f g : A -> R),
  (forall a : A, req (f a) (g a)) -> forall l : list A, req (rsum A f l) (rsum A g l).
Proof.
  intros A f g Hfg l. induction l as [|w rest IH].
  - cbn [rsum]. apply req_refl.
  - cbn [rsum]. apply req_plus_compat.
    + apply Hfg.
    + exact IH.
Qed.

Lemma rls_linear_c : forall (A : Set) (a : R) (f : A -> R) (l : list A),
  req (rsum A (fun x => mult a (f x)) l) (mult a (rsum A f l)).
Proof.
  intros A a f l. induction l as [|w rest IH].
  - cbn [rsum]. apply req_sym. apply mult_zero.
  - cbn [rsum].
    apply (req_trans (plus (mult a (f w)) (rsum A (fun x => mult a (f x)) rest))
                     (plus (mult a (f w)) (mult a (rsum A f rest)))
                     (mult a (plus (f w) (rsum A f rest)))).
    + apply (req_plus_compat (mult a (f w)) (mult a (f w))
                             (rsum A (fun x => mult a (f x)) rest)
                             (mult a (rsum A f rest))).
      * apply req_refl.
      * exact IH.
    + apply (req_sym (mult a (plus (f w) (rsum A f rest)))
                     (plus (mult a (f w)) (mult a (rsum A f rest)))).
      apply distrib.
Qed.

Lemma rls_nonneg_c : forall (A : Set) (f : A -> R),
  (forall a : A, le zero (f a)) -> forall l : list A, le zero (rsum A f l).
Proof.
  intros A f Hf l. induction l as [|w rest IH].
  - cbn [rsum]. apply le_refl.
  - cbn [rsum]. apply (le_id_l zero (plus zero zero) (plus (f w) (rsum A f rest))).
    + apply (req_sym (plus zero zero) zero). apply plus_zero.
    + apply (le_plus_compat zero (f w) zero (rsum A f rest)).
      * apply Hf.
      * exact IH.
Qed.

Lemma rls_single_le_c : forall (A : Set) (f : A -> R) (x : A) (l : list A),
  InT x l -> (forall y : A, le zero (f y)) -> le (f x) (rsum A f l).
Proof.
  intros A f x l Hin Hnn.
  induction Hin as [l0 | y l0 Hin IH].
  - cbn [rsum]. exact (req_le_plus_nonneg_r (f x) (rsum A f l0) (rls_nonneg_c A f Hnn l0)).
  - cbn [rsum]. apply (le_trans (f x) (rsum A f l0) (plus (f y) (rsum A f l0))).
    + exact IH.
    + exact (le_id_r (rsum A f l0) (plus (rsum A f l0) (f y))
                     (plus (f y) (rsum A f l0)) (plus_comm (rsum A f l0) (f y))
                     (req_le_plus_nonneg_r (rsum A f l0) (f y) (Hnn y))).
Qed.

Lemma rls_le_c : forall (A : Set) (f g : A -> R),
  (forall a : A, le (f a) (g a)) -> forall l : list A, le (rsum A f l) (rsum A g l).
Proof.
  intros A f g Hfg l. induction l as [|w rest IH].
  - cbn [rsum]. apply le_refl.
  - cbn [rsum]. apply le_plus_compat.
    + apply Hfg.
    + exact IH.
Qed.

Lemma req_le_mult_le_one_r_c : forall a b : R,
  le zero a -> le b one -> le (mult b a) a.
Proof.
  intros a b Ha Hb.
  assert (H1 : le zero (req_minus one b)).
  { apply req_le_minus_nonneg. exact Hb. }
  assert (H2 : le zero (mult (req_minus one b) a)).
  { apply (le_id_l zero (mult a zero) (mult (req_minus one b) a)).
    - apply (req_sym (mult a zero) zero). apply mult_zero.
    - apply (le_id_r (mult a zero) (mult a (req_minus one b))
                     (mult (req_minus one b) a)).
      + apply mult_comm.
      + exact (req_le_mult_compat_r a zero (req_minus one b) Ha H1). }
  assert (H3 : req (mult (req_minus one b) a) (req_minus a (mult b a))).
  { apply (req_trans (mult (req_minus one b) a)
                     (mult a (req_minus one b))
                     (req_minus a (mult b a))).
    - apply mult_comm.
    - apply (req_trans (mult a (req_minus one b))
                       (req_minus (mult a one) (mult a b))
                       (req_minus a (mult b a))).
      + apply req_mult_minus_distr_l.
      + unfold req_minus. apply req_plus_compat.
        * apply mult_one.
        * apply req_opp_compat. apply mult_comm. }
  assert (H2' : le zero (req_minus a (mult b a))).
  { exact (le_id_r zero (mult (req_minus one b) a)
                   (req_minus a (mult b a)) H3 H2). }
  assert (H4 : le (plus (mult b a) zero)
                  (plus (mult b a) (req_minus a (mult b a)))).
  { apply (le_plus_compat (mult b a) (mult b a) zero (req_minus a (mult b a))).
    - apply le_refl.
    - exact H2'. }
  exact (le_id_r (mult b a) (plus (mult b a) (req_minus a (mult b a))) a
                 (req_minus_plus_cancel (mult b a) a)
                 (le_id_l (mult b a) (plus (mult b a) zero)
                          (plus (mult b a) (req_minus a (mult b a)))
                          (req_sym (plus (mult b a) zero) (mult b a)
                                   (plus_zero (mult b a)))
                          H4)).
Qed.
(* B6W adaptation (the first set of the AA13 explicit premises): the pls_ lift adapter plugs in, *)
(* so that the three sections can lift their old negative-shape vocab_nonempty premises to the sigT witness form. *)

(* Engine section ReqMpEngineNum: the shared bridge for the nat-to-req-R embedding (reqd_of_nat) *)
Section ReqMpEngineNum.

(* E1, the successor bridge: reqd_of_nat (S n) and 1 + reqd_of_nat n agree pointwise by delta *)
Lemma reqd_of_nat_succ : forall n : nat,
  req (reqd_of_nat (Datatypes.S n)) (plus one (reqd_of_nat n)).
Proof.
  intro n. exact (req_refl (reqd_of_nat (Datatypes.S n))).
Qed.

(* E2, positivity of the embedding, matching attn_nat_to_R_pos (S13): 0 < reqd_of_nat (S k).
   The induction mirrors the original proof: the base reshapes (1+0 == 1, one_pos); the step is plus_positive. *)
Lemma reqd_of_nat_pos : forall k : nat, lt zero (reqd_of_nat (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - (* Base: reqd_of_nat 1 == 1 + 0, reshaped back to one for one_pos *)
    apply (lt_id_r zero one (reqd_of_nat (Datatypes.S O))).
    + apply (req_trans one (plus one zero) (reqd_of_nat (Datatypes.S O))).
      * apply (req_sym (plus one zero) one). apply plus_zero.
      * apply req_refl.
    + exact one_pos.
  - (* Step: reqd_of_nat (S (S k)) is 1 + reqd_of_nat (S k), both factors positive *)
    apply (lt_id_r zero (plus one (reqd_of_nat (Datatypes.S k)))
                      (reqd_of_nat (Datatypes.S (Datatypes.S k)))).
    + apply req_refl.
    + apply plus_positive.
      * exact one_pos.
      * exact IH.
Qed.

(* E3 <- le_one_mult_le_inv_mp (S06):
   0 < G and 1 <= G*M give inv G <= M.
   The three Id-family steps (assoc / comm+inv_correct / one cancellation) become req_trans chains pointwise;
   the Id intermediate Habs becomes a req Habs; the finishing le_id_r/le_id_l transport plus
   req_le_mult_compat_r (multiplication by a positive factor preserves the order, UpReqAlgebra L465). *)
Lemma req_le_one_mult_le_inv_mp : forall (G M : R) (Hg : lt zero G),
  le one (mult G M) -> le (inv_pos G Hg) M.
Proof.
  intros G M Hg Hle.
  assert (Habs : req (mult (inv_pos G Hg) (mult G M)) M).
  { apply (req_trans (mult (inv_pos G Hg) (mult G M))
                     (mult (mult (inv_pos G Hg) G) M)).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos G Hg) G) M)
                       (mult (mult G (inv_pos G Hg)) M)).
      + apply (req_mult_compat (mult (inv_pos G Hg) G)
                               (mult G (inv_pos G Hg)) M M).
        * apply mult_comm.
        * apply req_refl.
      + apply (req_trans (mult (mult G (inv_pos G Hg)) M) (mult one M)).
        * apply (req_mult_compat (mult G (inv_pos G Hg)) one M M).
          -- exact (inv_pos_correct G Hg).
          -- apply req_refl.
        * apply req_mult_one_l. }
  apply (le_id_r (inv_pos G Hg) (mult (inv_pos G Hg) (mult G M)) M Habs).
  apply (le_id_l (inv_pos G Hg) (mult (inv_pos G Hg) one)
                 (mult (inv_pos G Hg) (mult G M))).
  - apply (req_sym (mult (inv_pos G Hg) one) (inv_pos G Hg)).
    apply mult_one.
  - apply (req_le_mult_compat_r (inv_pos G Hg) one (mult G M)).
    + apply (lt_le_iff zero (inv_pos G Hg)). left. apply (inv_pos_pos G Hg).
    + exact Hle.
Qed.

End ReqMpEngineNum.

(* Instance section ReqMpNatDomain: the two items of the nat counting domain (I1 / I2) *)
Section ReqMpNatDomain.
Variable Token : Set.

(* I1 <- mp_of_nat_pos (S06):
   the missing nat-to-req-R bridge is supplied by this file); a nonempty length has the shape S k, reducing to E2. *)
Lemma reqd_mp_of_nat_pos : forall l : list Token,
  Not (Id l nil) -> lt zero (reqd_of_nat (length l)).
Proof.
  intros l Hl. destruct l as [| w rest].
  - exact (match Hl (@id_refl (list Token) nil) with end).
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. exact (reqd_of_nat_pos (length rest)).
Qed.

(* I2 <- list_sum_le_const_mp (S06):
   pointwise f w <= M gives sum f l <= of_nat(|l|)*M.
   The summation carrier list_sum becomes rsum (the RestB Part 0 req machine);
   the base/step Id reshapes (mult_plus_distr_r / mult_one cancellation) become req chains pointwise;
   mp_of_nat becomes reqd_of_nat (the same bridge). *)
Lemma req_rsum_le_const_mp : forall (f : Token -> R) (M : R) (l : list Token),
  (forall w : Token, InT w l -> le (f w) M) ->
  le (rsum Token f l) (mult (reqd_of_nat (length l)) M).
Proof.
  intros f M l. induction l as [| w rest IH]; intros Hf;
  cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - (* Base: 0 <= 0*M == 0 *)
    apply (le_id_l zero (mult zero M) (mult zero M)).
    + apply (req_sym (mult zero M) zero).
      apply (req_trans (mult zero M) (mult M zero) zero).
      * apply mult_comm.
      * apply mult_zero.
    + apply le_refl.
  - (* Step: f w <= M and the rest-sum <= N*M give the total <= (1+N)*M == M + N*M *)
    apply (le_id_r (plus (f w) (rsum Token f rest))
                   (plus M (mult (reqd_of_nat (length rest)) M))
                   (mult (plus one (reqd_of_nat (length rest))) M)).
    + apply (req_trans (plus M (mult (reqd_of_nat (length rest)) M))
                       (plus (mult one M) (mult (reqd_of_nat (length rest)) M))).
      * apply (req_plus_compat M (mult one M)
                               (mult (reqd_of_nat (length rest)) M)
                               (mult (reqd_of_nat (length rest)) M)).
        -- apply (req_sym (mult one M) M). apply req_mult_one_l.
        -- apply req_refl.
      * apply (req_sym (mult (plus one (reqd_of_nat (length rest))) M)
                       (plus (mult one M) (mult (reqd_of_nat (length rest)) M))).
        apply req_mult_plus_distr_r.
    + apply le_plus_compat.
      * apply (Hf w). apply InT_here.
      * apply IH. intros w' Hw'. apply (Hf w'). apply InT_next. exact Hw'.
Qed.

End ReqMpNatDomain.

(* Instance section ReqMpKernelWorld: the Min-P kernel domain (I3 / I4) *)
(*   The interface premises sit at the same positions as the base MinPSampling L5934-5945 (the Token/vocab/ *)
(*   total_loss/temperature six-item closure); the mpd_* definition family is delta-transparently shape-matched *)
(*   to the RestB alb_temp_factor/alb_partition_temp/alb_markov_ *)
(*   kernel (the precedent of carrying the closure explicitly). *)
Section ReqMpKernelWorld.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* B6W adaptation point (AA13 #11): the old negative-shape premise is lifted through the pls_ adapter to the sigT witness form -- *)
(* the deep-adaptation use point: pls_vocab_ne_lift raises the in-section old-shape Variable to a witness in place, *)
(* and downstream code can take mpd_vocab_ne_witness_s1 directly through the sigT route. The old statement is kept verbatim. *)
Definition mpd_vocab_ne_witness_s1 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* The base temp_factor L30703 counterpart: e^(-inv(T)*loss) *)
Definition mpd_temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos)
                (total_loss (prefix ++ [w]))).

(* The base partition_temp L30705 counterpart: sum_w temp_factor *)
Definition mpd_partition_temp (prefix : list Token) : R :=
  rsum Token (mpd_temp_factor prefix) vocab.

(* The base partition_temp_pos L30768 counterpart (the proof shape of RestB req_partition_temp_pos) *)
Lemma mpd_partition_temp_pos : forall prefix : list Token,
  lt zero (mpd_partition_temp prefix).
Proof.
  intro prefix. unfold mpd_partition_temp.
  apply (rls_pos_c Token (mpd_temp_factor prefix)).
  - intro w. unfold mpd_temp_factor. apply exp_neg_pos.
  - apply vocab_nonempty.
Qed.

(* The base markov_kernel L30859 counterpart: tf * inv(partition) *)
Definition mpd_markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (mpd_temp_factor prefix w)
       (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)).

(* I3 <- markov_kernel_normalized_mp (S06):
   sum_w kernel w == 1. The original Hext (mult_comm pointwise) / Hlin (linearity of the sum) /
   Hp (inv_pos_correct) three steps align pointwise:
   Id rewrite/id_cong become req_trans; list_sum_linear becomes rls_linear;
   list_sum_ext becomes rls_ext. *)
Lemma req_markov_kernel_normalized_mp : forall prefix : list Token,
  req (rsum Token (mpd_markov_kernel prefix) vocab) one.
Proof.
  intro prefix. unfold mpd_markov_kernel.
  apply (req_trans
    (rsum Token (fun w : Token =>
        mult (mpd_temp_factor prefix w)
             (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))) vocab)
    (mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
          (rsum Token (mpd_temp_factor prefix) vocab))
    one
    (req_trans
      (rsum Token (fun w : Token =>
          mult (mpd_temp_factor prefix w)
               (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))) vocab)
      (rsum Token (fun w : Token =>
          mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
               (mpd_temp_factor prefix w)) vocab)
      (mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
            (rsum Token (mpd_temp_factor prefix) vocab))
      (rls_ext_c Token
         (fun w : Token => mult (mpd_temp_factor prefix w)
              (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))
         (fun w : Token => mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
              (mpd_temp_factor prefix w))
         (fun w : Token => mult_comm (mpd_temp_factor prefix w)
              (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))
         vocab)
      (rls_linear_c Token (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
                  (mpd_temp_factor prefix) vocab))
    (req_trans (mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
                     (mpd_partition_temp prefix))
               (mult (mpd_partition_temp prefix)
                     (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))
               one
               (mult_comm (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
                          (mpd_partition_temp prefix))
               (inv_pos_correct (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))).
Qed.

(* I4 <- temp_factor_antitone_mp (S06):
   loss a <= loss b gives tf b <= tf a (exp_neg is antitone and multiplication by a positive factor preserves the order) *)
Lemma req_temp_factor_antitone_mp : forall (prefix : list Token) (a b : Token),
  le (total_loss (prefix ++ [a])) (total_loss (prefix ++ [b])) ->
  le (mpd_temp_factor prefix b) (mpd_temp_factor prefix a).
Proof.
  intros prefix a b Hloss. unfold mpd_temp_factor.
  apply (exp_neg_le_decr (mult (inv_pos temperature temperature_pos)
                               (total_loss (prefix ++ [a])))
                         (mult (inv_pos temperature temperature_pos)
                               (total_loss (prefix ++ [b])))).
  apply (req_le_mult_compat_r (inv_pos temperature temperature_pos)
                              (total_loss (prefix ++ [a]))
                              (total_loss (prefix ++ [b]))).
  - apply (lt_le_iff zero (inv_pos temperature temperature_pos)). left.
    apply (inv_pos_pos temperature temperature_pos).
  - exact Hloss.
Qed.

End ReqMpKernelWorld.


(* ------------------------------------------------------------
      argmin traversal minimality -- ord_le_dec is replaced by the req_le_dec bridge premise (the RestB
      T2 position 1 counterpart), with le_refl/le_trans replaced directly by interface fields; InT case analysis stays
      at the Id layer (the list machinery is not migrated; the section 1.1 boundary 2). Difficulty: medium.
      The snd identity invariant -- a pure Id-layer induction (the middle-branch decision replaced by req_le_dec),
      with the statement Id equation kept (best_loss = ... is an Id). Difficulty: low-medium.
      pick_best optimality -- depends on 1+2 plus the vocab case analysis; difficulty: medium.
      kernel w <= max -- depends on 3 plus I4 (temp_factor_antitone) plus
      the weak form of le_mult_compat (the interface field is on file); difficulty: low (the engine is complete).
      1 == sum kernel (I3) <= |S|*max (the I2 instance) gives inv(|S|) <= max
      (E3); a chained assembly whose Id/req equation bridges follow the RestB normalization theorem shape.
      Difficulty: medium (all three branches are on file).
      chain 2): dropped <= 1 - p_max (the RestB req_minp_dropped_mass_le_
      one_minus_max lemma on file) plus chain 1 plus an opp_le_compat assembly; difficulty: medium.
   Note: the req in-section counterparts of the three definitions
   argmin_aux_token / pick_best_token / max_markov_prob (RestB alb_max_markov_prob already has the max counterpart;
   argmin is newly built here and later sections may extend ReqMpKernelWorld).
   ============================================================ *)
(* The X3b2 block: the remaining 6 mp-domain items all discharged (the argmin cluster of 3 plus the assembly of 3) *)
(* ------------------------------------------------------------
     1 mpd_argmin_aux_token_min_mp <- argmin_aux_token_min_mp
        (S06; the decision replaced by the req_le_dec bridge premise at position 1;
        the original not_le_lt step (an S01 decidable-order field with no same-named field in the req domain) is replaced by
        the three-way split of the bridge premise at position 2, req_lt_dec -- the RestB ReqSamplingWorld
        position 2 counterpart; le_refl/le_trans/le_id_l replaced directly by interface fields)
        (a pure Id-layer induction with the middle-branch decision replaced by req_le_dec; the statement Id equation is kept)
        (depends on 1+2 plus the vocab case analysis; the snd identity is transported by an Id-layer rewrite,
        inside the list-Id no-migration boundary)
        (the le_mult_compat_weak interface field used directly plus I4 req_temp_factor_
        antitone_mp plus item 3)
        (the I3 normalization plus I2 req_rsum_le_const_mp plus the E3 req_le_one_mult_
        le_inv_mp three-branch assembly; the mp_of_nat to reqd_of_nat bridge)
     6 mpd_minp_dropped_mass_le_inv_vocab_size <- S06 /
         chain 2 (the dropped <= 1-max branch ported in the proof shape of RestB req_minp_dropped_
        mass_le_one_minus_max (renamed alb_ to mpd_ pointwise), plus
        chain 1 plus an opp_le_compat assembly)
   Definition clusters (the S06-6061/L6167-6171/L6174-6191/L6504 counterparts;
   the RestB alb_ precedent of carrying closures explicitly; the first discharged group such as mpd_markov_kernel
   is used with the closure spelled out in full):
     mpd_argmin_aux_token / mpd_pick_best_token (with the default_token item,
     the S06 counterpart) / mpd_pick_max_token / mpd_max_markov_prob /
     mpd_minp_threshold / mpd_minp_keep / mpd_minp_keep_dec /
     mpd_minp_temp_sum / mpd_minp_dropped_mass
   Bridge premises: position 1 req_le_dec (the RestB position 1 counterpart); position 2 req_lt_dec
   ============================================================ *)
Section ReqMpKernelWorld2.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* B6W adaptation point (AA13 #12): the same deep adaptation as #11 -- the use point of the old shape lifted to the sigT witness form. *)
Definition mpd_vocab_ne_witness_s2 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.
Variable min_p : R.
Variable min_p_lt_one : lt min_p one.

(* Bridge premise at position 1: the req counterpart copy of DecidableOrder ord_le_dec (the S01 L331 counterpart) *)
Hypothesis req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* Bridge premise at position 2: the three-way decision (the RestB ReqSamplingWorld position 2 counterpart) *)
Hypothesis req_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* ---- Definition cluster 1: the argmin machine (the S06 L6044-6061 counterpart; candidate_token inlined) ---- *)
Fixpoint mpd_argmin_aux_token (prefix : list Token) (l : list Token)
         (best : (Token * R)%type) : (Token * R)%type :=
  match l with
  | nil => best
  | w :: rest =>
      match req_le_dec (total_loss (prefix ++ [w])) (snd best) with
      | inl _ => mpd_argmin_aux_token prefix rest (w, total_loss (prefix ++ [w]))
      | inr _ => mpd_argmin_aux_token prefix rest best
      end
  end.

Definition mpd_pick_best_token (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest => fst (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* The InT head insertion (the S06 L6086 counterpart; the Id-layer machinery kept, the no-migration boundary 2) *)
Lemma mpd_InT_head_extend : forall (x y a : Token) (l : list Token),
  InT x (y :: l) -> InT x (y :: a :: l).
Proof.
  intros x y a l H. inversion H; subst.
  - apply InT_here.
  - apply InT_next. apply InT_next. assumption.
Qed.

(* 1 <- argmin_aux_token_min_mp (S06):
   An And-two-branch traversal induction; the not_le_lt step for the middle branch with best w = a is replaced by the req_lt_dec
   three-way split (inl lt goes to lt_le_iff; mid req goes to le_id_l + le_refl;
   inr lt contradicts Hnot and is discharged). *)
Lemma mpd_argmin_aux_token_min_mp : forall (prefix : list Token) (l : list Token)
         (best_token : Token) (best_loss : R),
  And (forall w : Token, InT w l ->
         le (snd (mpd_argmin_aux_token prefix l (best_token, best_loss)))
            (total_loss (prefix ++ [w])))
      (le (snd (mpd_argmin_aux_token prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - assert (Hempty : forall w : Token, InT w nil ->
      le (snd (mpd_argmin_aux_token prefix nil (best_token, best_loss)))
         (total_loss (prefix ++ [w]))).
    { intros w HIn. destruct (pls_inT_nil_empty _ w HIn). }
    exact (pair Hempty (le_refl _)).
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    destruct (req_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + destruct (IH a (total_loss (prefix ++ [a]))) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
    + destruct (IH best_token best_loss) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- destruct (req_lt_dec best_loss (total_loss (prefix ++ [a])))
                    as [Hlt | [Heq | Hgt]].
           ++ exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
           ++ exact (le_trans _ best_loss _ IH_le
                       (le_id_l best_loss (total_loss (prefix ++ [a]))
                                (total_loss (prefix ++ [a])) Heq
                                (le_refl (total_loss (prefix ++ [a]))))).
           ++ exact (match Hnot (lt_le_iff _ _ (inl Hgt)) with end).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* 2 <- argmin_aux_token_snd_correct_mp (S06):
   the snd identity invariant; a pure Id-layer induction with the middle-branch decision replaced by req_le_dec. *)
Lemma mpd_argmin_aux_token_snd_correct_mp : forall (prefix : list Token) (l : list Token)
         (best_token : Token) (best_loss : R),
  best_loss = total_loss (prefix ++ [best_token]) ->
  snd (mpd_argmin_aux_token prefix l (best_token, best_loss)) =
  total_loss (prefix ++ [fst (mpd_argmin_aux_token prefix l (best_token, best_loss))]).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. exact Hinit.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    destruct (req_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) eq_refl).
    + exact (IH best_token best_loss Hinit).
Qed.

(* The traversal membership helper (the S06 L6077 argmin_aux_token_mem counterpart) *)
Lemma mpd_argmin_aux_token_mem : forall (prefix : list Token) (l : list Token)
         (best_token : Token) (best_loss : R),
  InT (fst (mpd_argmin_aux_token prefix l (best_token, best_loss))) (best_token :: l).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply InT_here.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. destruct (req_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + apply InT_next. apply IH.
    + apply mpd_InT_head_extend. apply IH.
Qed.

(* pick_best is in vocab (the S06 L6096 pick_best_in_vocab' counterpart) *)
Lemma mpd_pick_best_in_vocab : forall prefix : list Token,
  InT (mpd_pick_best_token prefix) vocab.
Proof.
  intro prefix. unfold mpd_pick_best_token.
  destruct vocab as [| w0 rest].
  - exact (match vocab_nonempty (@id_refl (list Token) nil) with end).
  - apply (mpd_argmin_aux_token_mem prefix rest w0 (total_loss (prefix ++ [w0]))).
Qed.

(* 3 <- pick_best_optimal_mp (S06):
   depends on 1+2; the two vocab cases; the snd identity transported by an Id-layer rewrite. *)
Theorem mpd_pick_best_optimal_mp : forall (prefix : list Token) (w : Token),
  InT w vocab ->
  le (total_loss (prefix ++ [mpd_pick_best_token prefix]))
     (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold mpd_pick_best_token.
  destruct vocab as [| w0 rest].
  - inversion Hw.
  - destruct (mpd_argmin_aux_token_min_mp prefix rest w0 (total_loss (prefix ++ [w0])))
      as [Hmin Hle].
    assert (Hsnd : snd (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))) =
                   total_loss (prefix ++ [fst (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))]))
      by exact (mpd_argmin_aux_token_snd_correct_mp prefix rest w0
                  (total_loss (prefix ++ [w0])) eq_refl).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + assert (Hr : le (snd (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w0]))) by exact Hle.
      rewrite Hsnd in Hr.
      exact Hr.
    + assert (Hr : le (snd (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w]))) by exact (Hmin w Hwrest).
      rewrite Hsnd in Hr.
      exact Hr.
Qed.

(* ---- Definition cluster 2: max (the S06 L6167-6171 counterpart; the first discharged group used with closures in full) ---- *)
Definition mpd_pick_max_token (prefix : list Token) : Token := mpd_pick_best_token prefix.

Definition mpd_max_markov_prob (prefix : list Token) : R :=
  mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix
                    (mpd_pick_max_token prefix).

(* 4 <- markov_kernel_le_max_mp (S06):
   the le_mult_compat_weak interface field (le zero c -> le a b -> le a*c <= b*c)
   used directly; the monotone branch = I4 + item 3. *)
Lemma mpd_markov_kernel_le_max_mp : forall (prefix : list Token) (w : Token),
  InT w vocab ->
  le (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
     (mpd_max_markov_prob prefix).
Proof.
  intros prefix w Hw.
  unfold mpd_max_markov_prob, mpd_markov_kernel.
  apply (le_mult_compat_weak
           (mpd_temp_factor Token total_loss temperature temperature_pos prefix w)
           (mpd_temp_factor Token total_loss temperature temperature_pos prefix
                              (mpd_pick_max_token prefix))
           (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                    (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
  - apply (lt_le_iff zero
             (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
    left. apply (inv_pos_pos
                   (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                   (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
  - apply (req_temp_factor_antitone_mp Token total_loss temperature temperature_pos
                                       prefix (mpd_pick_max_token prefix) w).
    apply (mpd_pick_best_optimal_mp prefix w Hw).
Qed.

(* 5 <- minp_max_ge_inv_vocab_size (S06, chain 1):
   inv(|S|) <= max. Three branches: the I3 normalization (sum kernel == 1) plus the I2 pointwise sum bound
   (sum kernel <= |S|*max, pointwise = item 4) plus E3 division by a positive number. *)
Lemma mpd_minp_max_ge_inv_vocab_size : forall prefix : list Token,
  le (inv_pos (reqd_of_nat (length vocab))
              (reqd_mp_of_nat_pos Token vocab vocab_nonempty))
     (mpd_max_markov_prob prefix).
Proof.
  intro prefix.
  apply (req_le_one_mult_le_inv_mp (reqd_of_nat (length vocab)) (mpd_max_markov_prob prefix)
                                   (reqd_mp_of_nat_pos Token vocab vocab_nonempty)).
  apply (le_id_l one
                 (rsum Token
                    (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                       temperature_pos prefix) vocab)
                 (mult (reqd_of_nat (length vocab)) (mpd_max_markov_prob prefix))).
  - apply (req_sym (rsum Token
                     (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                        temperature_pos prefix) vocab) one).
    apply (req_markov_kernel_normalized_mp Token vocab vocab_nonempty total_loss temperature
                                           temperature_pos prefix).
  - apply (req_rsum_le_const_mp Token
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix)
             (mpd_max_markov_prob prefix) vocab).
    intro w. intro Hw. apply (mpd_markov_kernel_le_max_mp prefix w Hw).
Qed.

(* ---- Definition cluster 3: the minp truncation machine (the S06 L6174-6191/L6504 counterpart; the RestB alb_ isomorph) ---- *)
Definition mpd_minp_threshold (prefix : list Token) : R :=
  mult min_p (mpd_max_markov_prob prefix).

Definition mpd_minp_keep (prefix : list Token) (w : Token) : Set :=
  le (mpd_minp_threshold prefix)
     (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).

Definition mpd_minp_keep_dec (prefix : list Token) (w : Token) :
  Or (mpd_minp_keep prefix w) (Not (mpd_minp_keep prefix w)) :=
  req_le_dec (mpd_minp_threshold prefix)
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).

Definition mpd_minp_temp_sum (prefix : list Token) : R :=
  rsum Token (fun w : Token =>
           match mpd_minp_keep_dec prefix w with
           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
           | inr _ => zero
           end) vocab.

Definition mpd_minp_dropped_mass (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_minp_temp_sum prefix)).

(* The kernel positivity helper (the proof shape of RestB req_markov_pos) *)
Lemma mpd_markov_pos : forall (prefix : list Token) (w : Token),
  lt zero (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).
Proof.
  intros prefix w. unfold mpd_markov_kernel. apply mult_positive.
  - unfold mpd_temp_factor. apply exp_neg_pos.
  - apply (inv_pos_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                       (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
Qed.

(* pick_max retention (the proof shape of RestB req_pick_max_minp_keep:
   kernel >= 0 and min_p < 1 give min_p*kernel <= kernel) *)
Lemma mpd_pick_max_minp_keep : forall prefix : list Token,
  mpd_minp_keep prefix (mpd_pick_max_token prefix).
Proof.
  intro prefix. unfold mpd_minp_keep, mpd_minp_threshold.
  apply (req_le_mult_le_one_r_c
           (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix
                              (mpd_pick_max_token prefix))
           min_p).
  - apply (lt_le_iff zero
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix
                                (mpd_pick_max_token prefix))).
    left. apply (mpd_markov_pos prefix (mpd_pick_max_token prefix)).
  - apply (lt_le_iff min_p one). left. exact min_p_lt_one.
Qed.

(* The single tf term of pick_max is at most the truncated sum (the RestB req_pick_max_tf_le_minp_sum
   proof shape: the keep decision Or split plus the rls_single_le single-term lower bound) *)
Lemma mpd_pick_max_tf_le_minp_sum : forall prefix : list Token,
  le (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
     (mpd_minp_temp_sum prefix).
Proof.
  intro prefix. unfold mpd_minp_temp_sum.
  assert (Heq : req (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                    (match mpd_minp_keep_dec prefix (mpd_pick_max_token prefix) with
                     | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)
                     | inr _ => zero
                     end)).
  { destruct (mpd_minp_keep_dec prefix (mpd_pick_max_token prefix)) as [Hk | Hd].
    - apply req_refl.
    - destruct (Hd (mpd_pick_max_minp_keep prefix)). }
  apply (le_id_l (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                 (match mpd_minp_keep_dec prefix (mpd_pick_max_token prefix) with
                  | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)
                  | inr _ => zero
                  end)
                 (rsum Token (fun w : Token =>
                           match mpd_minp_keep_dec prefix w with
                           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab)).
  - exact Heq.
  - apply (rls_single_le_c Token
           (fun w : Token => match mpd_minp_keep_dec prefix w with
                             | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
                             | inr _ => zero
                             end)
           (mpd_pick_max_token prefix) vocab).
    + apply mpd_pick_best_in_vocab.
    + intro w. destruct (mpd_minp_keep_dec prefix w) as [Hk2 | Hd2].
      * apply (lt_le_iff zero (mpd_temp_factor Token total_loss temperature temperature_pos prefix w)). left.
        unfold mpd_temp_factor. apply exp_neg_pos.
      * apply le_refl.
Qed.

(* tf(pick_max) == max*partition (the proof shape of RestB req_temp_factor_max_eq;
   the delta unfolding of max_prob == tf*inv_p is a conversion, finished by req_refl) *)
Lemma mpd_temp_factor_max_eq : forall prefix : list Token,
  req (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
      (mult (mpd_max_markov_prob prefix)
            (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)).
Proof.
  intro prefix.
  apply (req_trans
    (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
    (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
          (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                         (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
    (mult (mpd_max_markov_prob prefix)
          (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))).
  - apply (req_trans
      (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
      (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)) one)
      (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
            (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))).
    + apply (req_sym
               (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)) one)
               (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))).
      apply mult_one.
    + apply req_mult_compat.
      * apply req_refl.
      * apply (req_trans
          one
          (mult (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                         (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
          (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                         (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))).
        -- apply (req_sym
                    (mult (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                          (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                   (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                    one).
           apply inv_pos_correct.
        -- apply mult_comm.
  - apply mult_assoc.
Qed.

(* max <= inv_p * truncated sum (the proof shape of RestB req_minp_scaled_sum_ge_max:
   the Hid algebra chain plus the H1 single-term lower bound plus multiplication by a positive factor) *)
Lemma mpd_minp_scaled_sum_ge_max : forall prefix : list Token,
  le (mpd_max_markov_prob prefix)
     (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                    (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
           (mpd_minp_temp_sum prefix)).
Proof.
  intro prefix.
  assert (Hid : req (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                   (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                          (mult (mpd_max_markov_prob prefix)
                                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
                    (mpd_max_markov_prob prefix)).
  { apply (req_trans
      (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                     (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
            (mult (mpd_max_markov_prob prefix)
                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
      (mult (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_max_markov_prob prefix))
            (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
      (mpd_max_markov_prob prefix)).
    - apply mult_assoc.
    - apply (req_trans
        (mult (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                             (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                    (mpd_max_markov_prob prefix))
              (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
        (mult (mult (mpd_max_markov_prob prefix)
                    (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                             (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
              (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
        (mpd_max_markov_prob prefix)).
      + apply req_mult_compat.
        * apply mult_comm.
        * apply req_refl.
      + apply (req_trans
          (mult (mult (mpd_max_markov_prob prefix)
                      (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
          (mult (mpd_max_markov_prob prefix)
                (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
          (mpd_max_markov_prob prefix)).
        * apply (req_sym
            (mult (mpd_max_markov_prob prefix)
                  (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                 (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                        (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
            (mult (mult (mpd_max_markov_prob prefix)
                        (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                 (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))).
          apply mult_assoc.
        * apply (req_trans
            (mult (mpd_max_markov_prob prefix)
                  (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                 (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                        (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
            (mult (mpd_max_markov_prob prefix) one)
            (mpd_max_markov_prob prefix)).
          -- apply req_mult_compat.
             ++ apply req_refl.
             ++ apply (req_trans
                 (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                       (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                 (mult (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                       (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                 one).
                ** apply mult_comm.
                ** apply inv_pos_correct.
          -- apply mult_one. }
  assert (H1 : le (mult (mpd_max_markov_prob prefix)
                        (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                  (mpd_minp_temp_sum prefix)).
  { exact (le_id_l (mult (mpd_max_markov_prob prefix)
                         (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                   (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                   (mpd_minp_temp_sum prefix)
                   (req_sym (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                            (mult (mpd_max_markov_prob prefix)
                                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                            (mpd_temp_factor_max_eq prefix))
                   (mpd_pick_max_tf_le_minp_sum prefix)). }
  apply (le_id_l (mpd_max_markov_prob prefix)
                 (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                       (mult (mpd_max_markov_prob prefix)
                             (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
                 (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                       (mpd_minp_temp_sum prefix))).
  - apply (req_sym (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                  (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                         (mult (mpd_max_markov_prob prefix)
                               (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
                   (mpd_max_markov_prob prefix)).
    exact Hid.
  - apply (req_le_mult_compat_r
             (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
             (mult (mpd_max_markov_prob prefix)
                   (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
             (mpd_minp_temp_sum prefix)).
    + apply (lt_le_iff zero
               (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                        (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
      left. apply (inv_pos_pos
                     (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                     (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
    + exact H1.
Qed.

(* dropped <= 1 - max (the proof shape of RestB req_minp_dropped_mass_le_one_minus_max:
   opp reversal plus a shift) *)
Lemma mpd_minp_dropped_mass_le_one_minus_max : forall prefix : list Token,
  le (mpd_minp_dropped_mass prefix) (req_minus one (mpd_max_markov_prob prefix)).
Proof.
  intro prefix. unfold mpd_minp_dropped_mass.
  apply (le_plus_compat one one
           (opp (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_minp_temp_sum prefix)))
           (opp (mpd_max_markov_prob prefix))).
  - apply le_refl.
  - apply opp_le_compat.
    exact (mpd_minp_scaled_sum_ge_max prefix).
Qed.

(* 6 <- minp_dropped_mass_le_inv_vocab_size (S06, chain 2):
   dropped <= 1 - max <= 1 - inv(|S|); the second half is the opp reversal plus chain 1. *)
Theorem mpd_minp_dropped_mass_le_inv_vocab_size : forall prefix : list Token,
  le (mpd_minp_dropped_mass prefix)
     (req_minus one
                (inv_pos (reqd_of_nat (length vocab))
                         (reqd_mp_of_nat_pos Token vocab vocab_nonempty))).
Proof.
  intro prefix.
  apply (le_trans _ (req_minus one (mpd_max_markov_prob prefix)) _).
  - exact (mpd_minp_dropped_mass_le_one_minus_max prefix).
  - apply (le_plus_compat one one
                           (opp (mpd_max_markov_prob prefix))
                           (opp (inv_pos (reqd_of_nat (length vocab))
                                         (reqd_mp_of_nat_pos Token vocab vocab_nonempty)))).
    + apply le_refl.
    + apply (opp_le_compat (inv_pos (reqd_of_nat (length vocab))
                                    (reqd_mp_of_nat_pos Token vocab vocab_nonempty))
                           (mpd_max_markov_prob prefix)).
      exact (mpd_minp_max_ge_inv_vocab_size prefix).
Qed.

End ReqMpKernelWorld2.

(* The remaining-items list at the file tail (above) is closed in full by this section; recorded here. *)

(* The remaining items: 1 single-item bound counterpart ruling plus the p-antitone cluster of 5 newly built items). *)
(* ------------------------------------------------------------
       The helper statement mpd_pick_max_tf_le_minp_sum (ReqMpKernelWorld2)
       is pointwise of the same shape (le (tf pick_max) (minp_temp_sum)); the counterpart holds, and with this
     1 mpd_minp_keep_p_antitone <- minp_keep_p_antitone
       the max >= 0 branch comes free from mpd_markov_pos through the delta unfolding)
     2 mpd_temp_factor_nonneg_p <- temp_factor_nonneg_p
     3 mpd_minp_term_nonneg_p <- minp_term_nonneg_p
     4 mpd_minp_temp_sum_p_antitone <- minp_temp_sum_p_antitone
       the keep2 implies keep1 antitonicity plus the pointwise two-branch shape of term_nonneg)
     5 mpd_minp_dropped_mass_p_monotone <- minp_dropped_mass_p_monotone
       a three-branch assembly of the opp_le_compat reversal plus the le_plus_compat shift)
   Definition clusters (the S06-6751 counterpart; the p-cluster threshold carries an explicit mp : R in place of the fixed
   min_p, so the section premises of this section do not carry min_p/min_p_lt_one -- leaner than the S06 section;
   the discharged definitions are used with closures in full; the six-item shape of mpd_pick_max_token /
   the ten-item shape of mpd_max_markov_prob verified written out by the -vos check):
     mpd_minp_threshold_p / mpd_minp_keep_p / mpd_minp_keep_dec_p /
     mpd_minp_temp_sum_p / mpd_minp_dropped_mass_p
   Bridge premise: req_le_dec (position 1, the ReqMpKernelWorld2 counterpart); the p cluster does not touch
   the argmin three-way step, so position 2 is not needed.
   ============================================================ *)
Section ReqMpKernelWorld3.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* B6W adaptation point (AA13 #13): the same deep adaptation as #11 -- the use point of the old shape lifted to the sigT witness form. *)
Definition mpd_vocab_ne_witness_s3 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.

(* Bridge premise at position 1 (the ReqMpKernelWorld2 position 1 counterpart) *)
Hypothesis req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* ---- The p-cluster definitions (the S06 L6726-6751 counterpart; the threshold carries the explicit mp : R) ---- *)
Definition mpd_minp_threshold_p (mp : R) (prefix : list Token) : R :=
  mult mp (mpd_max_markov_prob Token vocab vocab_nonempty total_loss temperature
                                  temperature_pos default_token req_le_dec prefix).

Definition mpd_minp_keep_p (mp : R) (prefix : list Token) (w : Token) : Set :=
  le (mpd_minp_threshold_p mp prefix)
     (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                        temperature_pos prefix w).

Definition mpd_minp_keep_dec_p (mp : R) (prefix : list Token) (w : Token) :
  Or (mpd_minp_keep_p mp prefix w) (Not (mpd_minp_keep_p mp prefix w)) :=
  req_le_dec (mpd_minp_threshold_p mp prefix)
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix w).

Definition mpd_minp_temp_sum_p (mp : R) (prefix : list Token) : R :=
  rsum Token (fun w : Token =>
           match mpd_minp_keep_dec_p mp prefix w with
           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
           | inr _ => zero
           end) vocab.

Definition mpd_minp_dropped_mass_p (mp : R) (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_minp_temp_sum_p mp prefix)).

(* 2 <- temp_factor_nonneg_p (S06):
   tf >= 0 (exp_neg is always positive, lifted by lt_le_iff) *)
Lemma mpd_temp_factor_nonneg_p : forall (prefix : list Token) (w : Token),
  le zero (mpd_temp_factor Token total_loss temperature temperature_pos prefix w).
Proof.
  intros prefix w.
  apply (lt_le_iff zero (mpd_temp_factor Token total_loss temperature temperature_pos prefix w)).
  left. unfold mpd_temp_factor. apply exp_neg_pos.
Qed.

(* 3 <- minp_term_nonneg_p (S06):
   the item of the parametrized keeper is >= 0 (the inl branch has tf >= 0, the inr branch 0) *)
Lemma mpd_minp_term_nonneg_p : forall (mp : R) (prefix : list Token) (w : Token),
  le zero (match mpd_minp_keep_dec_p mp prefix w with
           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
           | inr _ => zero
           end).
Proof.
  intros mp prefix w. destruct (mpd_minp_keep_dec_p mp prefix w) as [Hk | Hd].
  - exact (mpd_temp_factor_nonneg_p prefix w).
  - apply le_refl.
Qed.

(* 1 <- minp_keep_p_antitone (S06, T4a):
   mp1 <= mp2 gives keep_p mp2 w implies keep_p mp1 w (a larger threshold shrinks the keep set).
   The max >= 0 branch: the delta unfolding of mpd_max_markov_prob == kernel(pick_max),
   so mpd_markov_pos comes free; the monotone branch uses the le_mult_compat_weak interface field directly. *)
Lemma mpd_minp_keep_p_antitone : forall (mp1 mp2 : R),
  le mp1 mp2 ->
  forall (prefix : list Token) (w : Token),
    mpd_minp_keep_p mp2 prefix w -> mpd_minp_keep_p mp1 prefix w.
Proof.
  intros mp1 mp2 Hmp prefix w Hk2.
  assert (Hmax : le zero (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                temperature temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix))).
  { apply (lt_le_iff zero (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                temperature temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix))).
    left. exact (mpd_markov_pos Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix)). }
  apply (le_trans (mult mp1 (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                  temperature temperature_pos prefix
                                  (mpd_pick_max_token Token vocab total_loss default_token
                                                         req_le_dec prefix)))
                  (mult mp2 (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                  temperature temperature_pos prefix
                                  (mpd_pick_max_token Token vocab total_loss default_token
                                                         req_le_dec prefix)))
                  (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                     temperature_pos prefix w)).
  - apply (le_mult_compat_weak mp1 mp2
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix)) Hmax Hmp).
  - exact Hk2.
Qed.

(* 4 <- minp_temp_sum_p_antitone (S06, T4b):
   mp1 <= mp2 gives the antitonicity of the truncated sum (sum_p mp2 <= sum_p mp1).
   The two pointwise branches: keep2 gives keep1 (item 1), so the terms agree (le_refl);
   keep2 expelling w gives term 2 = 0 <= term 1 (item 3). *)
Lemma mpd_minp_temp_sum_p_antitone : forall (mp1 mp2 : R),
  le mp1 mp2 ->
  forall prefix : list Token,
    le (mpd_minp_temp_sum_p mp2 prefix) (mpd_minp_temp_sum_p mp1 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold mpd_minp_temp_sum_p.
  apply (rls_le_c Token
           (fun w : Token =>
              match mpd_minp_keep_dec_p mp2 prefix w with
              | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
              | inr _ => zero
              end)
           (fun w : Token =>
              match mpd_minp_keep_dec_p mp1 prefix w with
              | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
              | inr _ => zero
              end)).
  intro w. destruct (mpd_minp_keep_dec_p mp2 prefix w) as [Hk2 | Hd2].
  - assert (Hk1 : mpd_minp_keep_p mp1 prefix w)
      by exact (mpd_minp_keep_p_antitone mp1 mp2 Hmp prefix w Hk2).
    destruct (mpd_minp_keep_dec_p mp1 prefix w) as [Hk1' | Hd1'].
    + apply le_refl.
    + destruct (Hd1' Hk1).
  - exact (mpd_minp_term_nonneg_p mp1 prefix w).
Qed.

(* 5 <- minp_dropped_mass_p_monotone (S06, T4c):
   mp1 <= mp2 gives the monotonicity of the truncated mass (mass_p mp1 <= mass_p mp2).
   Three branches: the sum_p antitonicity (item 4), then the order kept under left multiplication by inv_p (req_le_mult_compat_r),
   then the 1-X reversal (opp_le_compat plus the le_plus_compat shift). *)
Lemma mpd_minp_dropped_mass_p_monotone : forall (mp1 mp2 : R),
  le mp1 mp2 ->
  forall prefix : list Token,
    le (mpd_minp_dropped_mass_p mp1 prefix) (mpd_minp_dropped_mass_p mp2 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold mpd_minp_dropped_mass_p.
  assert (Hsum : le (mpd_minp_temp_sum_p mp2 prefix) (mpd_minp_temp_sum_p mp1 prefix))
    by exact (mpd_minp_temp_sum_p_antitone mp1 mp2 Hmp prefix).
  assert (Hscaled : le (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                          (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                             (mpd_minp_temp_sum_p mp2 prefix))
                       (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                             (mpd_minp_temp_sum_p mp1 prefix))).
  { apply (req_le_mult_compat_r
             (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
    - apply (lt_le_iff zero (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                     (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
      left. apply (inv_pos_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
    - exact Hsum. }
  apply (le_plus_compat one one
           (opp (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_minp_temp_sum_p mp1 prefix)))
           (opp (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_minp_temp_sum_p mp2 prefix)))).
  - apply le_refl.
  - apply opp_le_compat. exact Hscaled.
Qed.

End ReqMpKernelWorld3.

(* mp-domain wrap-up: 6 items complete (1 counterpart ruling + the 5-item p cluster + definitions *)

(* the full statement-layer counterpart set is on file. *)
(* ================= Section 2. The rae_argmin_aux family ================= *)
Import ListNotations.

(* Engine section ReqArgminEngine: the global Real interface times an arbitrary Set carrier A *)
Section ReqArgminEngine.
Variable A : Set.
Variable key : A -> R.

(* Bridge premise at position 1: the two-way decision of le (the RestB/MpDomain position 1 counterpart) *)
Hypothesis rae_le_dec : forall a b : R, Or (le a b) (Not (le a b)).
(* Bridge premise at position 2: the three-way decision (used only by the not_le step of the min item) *)
Hypothesis rae_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* The argmin machine (the mpd_argmin_aux_token counterpart, keyed by key) *)
Fixpoint rae_argmin_aux (l : list A) (best : (A*R)%type) : (A*R)%type :=
  match l with
  | nil => best
  | a :: rest =>
      match rae_le_dec (key a) (snd best) with
      | inl _ => rae_argmin_aux rest (a, key a)
      | inr _ => rae_argmin_aux rest best
      end
  end.

(* The InT head insertion (the arbitrary-A generalization of mpd_InT_head_extend) *)
Lemma rae_InT_head_extend : forall (x y a : A) (l : list A),
  InT x (y :: l) -> InT x (y :: a :: l).
Proof.
  intros x y a l H. inversion H; subst.
  - apply InT_here.
  - apply InT_next. apply InT_next. assumption.
Qed.

(* 1 min: an And-two-branch traversal induction (tactic-by-tactic the shape of mpd_argmin_aux_token_min_mp;
   the not_le step split three ways by rae_lt_dec: inl lt goes to lt_le_iff; mid req goes to
   le_id_l + le_refl; inr lt contradicts Hnot and is discharged) *)
Lemma rae_argmin_aux_min : forall (l : list A) (best : (A*R)%type),
  And (forall w : A, InT w l ->
         le (snd (rae_argmin_aux l best)) (key w))
      (le (snd (rae_argmin_aux l best)) (snd best)).
Proof.
  induction l as [| a rest IH]; intro best.
  - assert (Hempty : forall w : A, InT w nil ->
      le (snd (rae_argmin_aux nil best)) (key w)).
    { intros w HIn. destruct (pls_inT_nil_empty _ w HIn). }
    exact (pair Hempty (le_refl _)).
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    destruct (rae_le_dec (key a) (snd best)) as [Hle | Hnot].
    + destruct (IH (a, key a)) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (key a) _ IH_le Hle).
    + destruct (IH best) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- destruct (rae_lt_dec (snd best) (key a)) as [Hlt | [Heq | Hgt]].
           ++ exact (le_trans _ (snd best) _ IH_le (lt_le_iff _ _ (inl Hlt))).
           ++ exact (le_trans _ (snd best) _ IH_le
                       (le_id_l _ _ _ Heq (le_refl (key a)))).
           ++ exact (match Hnot (lt_le_iff _ _ (inl Hgt)) with end).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* 2 The snd identity invariant (the shape of mpd_argmin_aux_token_snd_correct_mp) *)
Lemma rae_argmin_aux_snd_correct : forall (l : list A) (best : (A*R)%type),
  snd best = key (fst best) ->
  snd (rae_argmin_aux l best) =
  key (fst (rae_argmin_aux l best)).
Proof.
  induction l as [| a rest IH]; intros best Hinit.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. exact Hinit.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    destruct (rae_le_dec (key a) (snd best)) as [Hle | Hnot].
    + exact (IH (a, key a) eq_refl).
    + exact (IH best Hinit).
Qed.

(* The traversal membership helper (the shape of mpd_argmin_aux_token_mem) *)
Lemma rae_argmin_aux_mem : forall (l : list A) (best : (A*R)%type),
  InT (fst (rae_argmin_aux l best)) (fst best :: l).
Proof.
  induction l as [| a rest IH]; intro best.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply InT_here.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. destruct (rae_le_dec (key a) (snd best)) as [Hle | Hnot].
    + apply InT_next. apply IH.
    + apply rae_InT_head_extend. apply IH.
Qed.

(* The pick wrapper (the mpd_pick_best_token counterpart: nil gives default) *)
Definition rae_pick (l : list A) (default : A) : A :=
  match l with
  | nil => default
  | a0 :: rest => fst (rae_argmin_aux rest (a0, key a0))
  end.

(* pick is in l (the mpd_pick_best_in_vocab counterpart with the nonempty premise on the carrier side) *)
Lemma rae_pick_mem : forall (l : list A) (default : A),
  Not (Id l nil) -> InT (rae_pick l default) l.
Proof.
  intros l default Hne. destruct l as [| a0 rest].
  - exact (match Hne (@id_refl (list A) nil) with end).
  - unfold rae_pick. apply (rae_argmin_aux_mem rest (a0, key a0)).
Qed.

(* 3 pick optimality (the mpd_pick_best_optimal_mp counterpart; the assembly of 1+2;
   the snd identity companion transported by a pure eq_rect term, zero goal-reshaping tactics) *)
Theorem rae_pick_optimal : forall (l : list A) (default : A) (w : A),
  InT w l -> le (key (rae_pick l default)) (key w).
Proof.
  intros l default w Hw. unfold rae_pick.
  destruct l as [| a0 rest].
  - inversion Hw.
  - destruct (rae_argmin_aux_min rest (a0, key a0)) as [Hmin Hle].
    assert (Hsnd : snd (rae_argmin_aux rest (a0, key a0)) =
                   key (fst (rae_argmin_aux rest (a0, key a0))))
      by exact (rae_argmin_aux_snd_correct rest (a0, key a0) eq_refl).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + exact (eq_rect (snd (rae_argmin_aux rest (a0, key a0)))
               (fun r => le r (key a0)) Hle
               (key (fst (rae_argmin_aux rest (a0, key a0))))
               Hsnd).
    + exact (eq_rect (snd (rae_argmin_aux rest (a0, key a0)))
               (fun r => le r (key w)) (Hmin w Hwrest)
               (key (fst (rae_argmin_aux rest (a0, key a0))))
               Hsnd).
Qed.

End ReqArgminEngine.

(* The recovery check section MpRecycleProbe: the mp-domain argmin is an engine instance *)
(* (the configuration: the argmin machine of UpReqMpDomain Section ReqMpKernelWorld2, cut down to *)
(*  the premise positions it actually uses: Token / total_loss / the decisions 1+2; the remaining section variables *)
(*  vocab_nonempty/temperature/default_token/min_p stay outside the machine closure) *)
Section MpRecycleProbe.
Variable Token : Set.
Variable total_loss : list Token -> R.
Hypothesis probe_le_dec : forall a b : R, Or (le a b) (Not (le a b)).
Hypothesis probe_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* The mp-specific limb 1: the key function = total_loss (prefix ++ [w]) *)
Definition mp_key (prefix : list Token) : Token -> R :=
  fun w => total_loss (prefix ++ [w]).

(* The definitional transport: the mp-domain argmin machine and the engine instance agree pointwise (an induction plus
   a conversion-level argument: the mp machine recurses with the extra prefix item while the engine is keyed, and under the
   A:=Token, key:=mp_key prefix premise positions the two are branch-by-branch of the same shape -- the conversion-level
   evidence of the recovery claim: the mp machine is a special case of the engine) *)
Lemma mpd_argmin_engine_transport : forall (prefix l : list Token)
         (best : (Token*R)%type),
  mpd_argmin_aux_token Token total_loss probe_le_dec prefix l best =
  @rae_argmin_aux Token (mp_key prefix) probe_le_dec l best.
Proof.
  intros prefix l. induction l as [| a rest IH]; intro best.
  - reflexivity.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. unfold mp_key.
    destruct (probe_le_dec (total_loss (prefix ++ [a])) (snd best))
      as [Hc | Hc].
    + exact (IH (a, mp_key prefix a)).
    + exact (IH best).
Qed.

(* The pick-wrapper transport (the vocab/default limb 2: nil gives default, same positions) *)
Lemma mpd_pick_engine_transport : forall (vocab : list Token)
         (default_token : Token) (prefix : list Token),
  mpd_pick_best_token Token vocab total_loss default_token probe_le_dec prefix =
  @rae_pick Token (mp_key prefix) probe_le_dec vocab default_token.
Proof.
  intros vocab default_token prefix.
  destruct vocab as [| w0 rest].
  - reflexivity.
  - unfold mpd_pick_best_token, rae_pick. f_equal.
    exact (mpd_argmin_engine_transport prefix rest
             (w0, total_loss (prefix ++ [w0]))).
Qed.

(* The mp-domain item 1 is supplied directly by the engine (the statement at the resolved shape of mpd_argmin_aux_token_min_mp;
   the conversion-level core closure: transport plus the delta/beta of mp_key) *)
Theorem mpd_argmin_aux_token_min_via_engine : forall (prefix l : list Token)
         (best_token : Token) (best_loss : R),
  And (forall w : Token, InT w l ->
         le (snd (mpd_argmin_aux_token Token total_loss probe_le_dec
                    prefix l (best_token, best_loss)))
            (total_loss (prefix ++ [w])))
      (le (snd (mpd_argmin_aux_token Token total_loss probe_le_dec
                 prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l best_token best_loss.
  destruct (@rae_argmin_aux_min Token (mp_key prefix)
              probe_le_dec probe_lt_dec l (best_token, best_loss))
    as [Hmin Hle].
  assert (T : mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss) =
              @rae_argmin_aux Token (mp_key prefix) probe_le_dec
                l (best_token, best_loss))
    by exact (mpd_argmin_engine_transport prefix l (best_token, best_loss)).
  split.
  - intros w Hw.
    exact (eq_rect (@rae_argmin_aux Token (mp_key prefix) probe_le_dec
                      l (best_token, best_loss))
             (fun z => le (snd z) (mp_key prefix w)) (Hmin w Hw)
             (mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss))
             (eq_sym T)).
  - exact (eq_rect (@rae_argmin_aux Token (mp_key prefix) probe_le_dec
                      l (best_token, best_loss))
             (fun z => le (snd z) (snd (best_token, best_loss))) Hle
             (mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss))
             (eq_sym T)).
Qed.

(* The mp-domain item 2 is supplied directly by the engine (the snd identity invariant) *)
Theorem mpd_argmin_aux_token_snd_correct_via_engine :
  forall (prefix l : list Token) (best_token : Token) (best_loss : R),
  best_loss = total_loss (prefix ++ [best_token]) ->
  snd (mpd_argmin_aux_token Token total_loss probe_le_dec
         prefix l (best_token, best_loss)) =
  total_loss (prefix ++
    [fst (mpd_argmin_aux_token Token total_loss probe_le_dec
            prefix l (best_token, best_loss))]).
Proof.
  intros prefix l best_token best_loss Hinit.
  assert (T : mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss) =
              @rae_argmin_aux Token (mp_key prefix) probe_le_dec
                l (best_token, best_loss))
    by exact (mpd_argmin_engine_transport prefix l (best_token, best_loss)).
  exact (eq_rect (@rae_argmin_aux Token (mp_key prefix) probe_le_dec
                    l (best_token, best_loss))
           (fun z => snd z = total_loss (prefix ++ [fst z]))
           (@rae_argmin_aux_snd_correct Token (mp_key prefix)
              probe_le_dec l (best_token, best_loss) Hinit)
           (mpd_argmin_aux_token Token total_loss probe_le_dec
              prefix l (best_token, best_loss))
           (eq_sym T)).
Qed.

(* The mp-domain traversal membership item is supplied directly by the engine *)
Theorem mpd_argmin_aux_token_mem_via_engine :
  forall (prefix l : list Token) (best_token : Token) (best_loss : R),
  InT (fst (mpd_argmin_aux_token Token total_loss probe_le_dec
              prefix l (best_token, best_loss)))
      (best_token :: l).
Proof.
  intros prefix l best_token best_loss.
  assert (T : mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss) =
              @rae_argmin_aux Token (mp_key prefix) probe_le_dec
                l (best_token, best_loss))
    by exact (mpd_argmin_engine_transport prefix l (best_token, best_loss)).
  exact (eq_rect (@rae_argmin_aux Token (mp_key prefix) probe_le_dec
                    l (best_token, best_loss))
           (fun z => InT (fst z) (best_token :: l))
           (@rae_argmin_aux_mem Token (mp_key prefix)
              probe_le_dec l (best_token, best_loss))
           (mpd_argmin_aux_token Token total_loss probe_le_dec
              prefix l (best_token, best_loss))
           (eq_sym T)).
Qed.

(* The mp-domain item 3 (pick optimality) is supplied directly by the engine (limbs 1 and 2 converted through the transport) *)
Theorem mpd_pick_best_optimal_via_engine :
  forall (vocab : list Token) (default_token : Token)
         (prefix : list Token) (w : Token),
  InT w vocab ->
  le (total_loss (prefix ++
        [mpd_pick_best_token Token vocab total_loss default_token
                             probe_le_dec prefix]))
     (total_loss (prefix ++ [w])).
Proof.
  intros vocab default_token prefix w Hw.
  assert (PT : mpd_pick_best_token Token vocab total_loss default_token
                 probe_le_dec prefix =
               @rae_pick Token (mp_key prefix) probe_le_dec
                 vocab default_token)
    by exact (mpd_pick_engine_transport vocab default_token prefix).
  exact (eq_rect (@rae_pick Token (mp_key prefix) probe_le_dec
                    vocab default_token)
           (fun z => le (total_loss (prefix ++ [z]))
                        (total_loss (prefix ++ [w])))
           (@rae_pick_optimal Token (mp_key prefix) probe_le_dec
              probe_lt_dec vocab default_token w Hw)
           (mpd_pick_best_token Token vocab total_loss default_token
              probe_le_dec prefix)
           (eq_sym PT)).
Qed.

End MpRecycleProbe.
(* ================= Section 2. The traj_table family ================= *)
Import ListNotations.
Open Scope Q_scope.

(* Part 1: the finite sampled table of a descent trajectory (the B-side of the chain, with Q as the carrier) *)

(* The sampled table traj_table h t x n = [x; step x; ...; step^n x],
   whose item i is sf_grad_descent h t x i (n+1 points). *)
Fixpoint traj_table (h t x : Q) (n : nat) : list Q :=
  match n with
  | O => x :: nil
  | Datatypes.S n' => x :: traj_table h t (sf_grad_step h t x) n'
  end.

Lemma head_InT_traj_table : forall (h t x : Q) (n : nat),
  InT x (traj_table h t x n).
Proof.
  intros h t x n. revert x. induction n as [| n' IH]; intros x; cbn [traj_table].
  - apply InT_here.
  - apply InT_here.
Qed.

(* The table is nonempty (the nil case is closed by a constructor-mismatch inversion, the same-position precedent of the engine items) *)
Lemma traj_table_nonempty : forall (h t x : Q) (n : nat),
  Not (Id (traj_table h t x n) nil).
Proof.
  intros h t x n. revert t x. induction n as [| n' IH]; intros t x Hnil;
    cbn [traj_table] in Hnil.
  - inversion Hnil.
  - inversion Hnil.
Qed.

(* The traversal item: the j-th iterate point is always in the table (j <= n) -- the trajectory concretization of the main item face (a) *)
Lemma traj_table_iterate_mem : forall (h t x : Q) (n j : nat),
  (j <= n)%nat -> InT (sf_grad_descent h t x j) (traj_table h t x n).
Proof.
  intros h t x n. revert x. induction n as [| n' IH]; intros x j Hj.
  - assert (E : j = 0%nat) by lia.
    rewrite E. cbn [sf_grad_descent traj_table]. apply InT_here.
  - revert Hj. destruct j as [| j']; intros Hj.
    + cbn [sf_grad_descent traj_table]. apply InT_here.
    + cbn [sf_grad_descent traj_table]. apply InT_next.
      apply IH. lia.
Qed.

(* The eps-passage item (at the Q layer): u <= v and 0 <= eps give u <= v + eps (a QleT' export) *)
Lemma qlep_add_eps : forall (u v eps : Q),
  QleT' u v -> QleT' 0 eps -> QleT' u (v + eps).
Proof.
  intros u v eps Huv Heps.
  apply Qle_to_QleT'.
  apply (Qle_trans u v (v + eps)).
  - apply QleT'_to_Qle. exact Huv.
  - apply (Qle_trans v (v + 0) (v + eps)).
    + apply QleT'_to_Qle. apply sf_qeq_le. exact (Qeq_sym (v + 0) v (Qplus_0_r v)).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply QleT'_to_Qle. exact Heps.
Qed.

(* Part 2: the abstract argmin eps-optimality witness (the engine side of item A) *)
Section EpsOptimalReachCore.
Variable A : Set.
Variable key : A -> R.
(* Bridge premises at positions 1+2 (the UpReqArgminEngine Section counterparts: the two-way decision of le / the three-way decision) *)
Hypothesis hle_dec : forall a b : R, Or (le a b) (Not (le a b)).
Hypothesis hlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* The supporting item, eps-loosening: domination u <= v plus eps >= 0 gives eps-domination u <= v + eps.
   Assembly: le_trans times (req to le through the right branch of lt_le_iff) times le_plus_compat. *)
Lemma eps_loosen : forall (u v eps : R),
  le u v -> le zero eps -> le u (plus v eps).
Proof.
  intros u v eps Huv Heps.
  apply (le_trans u v (plus v eps)).
  - exact Huv.
  - apply (le_trans v (plus v zero) (plus v eps)).
    + apply lt_le_iff. apply inr.
      exact (req_sym (plus v zero) v (plus_zero v)).
    + apply le_plus_compat.
      * apply le_refl.
      * exact Heps.
Qed.

(* The eps-optimality reach witness shape (a Set-level sigT package: membership + domination + eps-domination) *)
Definition optimal_pick_witness (l : list A) (default : A) (eps : R) : Set :=
  sigT (fun xstar =>
    And (InT xstar l)
        (And (forall w : A, InT w l -> le (key xstar) (key w))
             (forall w : A, InT w l -> le (key xstar) (plus (key w) eps)))).

(* Main item: any finite nonempty table plus any nonnegative comparison threshold eps gives the sigT witness of
   domination/approximation at the argmin point. The certificates come directly from the item-A engine:
   membership = rae_pick_mem, domination = rae_pick_optimal, the eps form = eps_loosen. *)
Theorem finite_table_eps_optimal_witness :
  forall (l : list A) (default : A) (eps : R),
    Not (Id l nil) -> le zero eps ->
    optimal_pick_witness l default eps.
Proof.
  intros l default eps Hne Heps.
  refine (existT _ (rae_pick A key hle_dec l default) _).
  split.
  - exact (@rae_pick_mem A key hle_dec l default Hne).
  - split.
    + intros w Hw.
      exact (@rae_pick_optimal A key hle_dec hlt_dec l default w Hw).
    + intros w Hw.
      exact (eps_loosen (key (rae_pick A key hle_dec l default)) (key w) eps
               (@rae_pick_optimal A key hle_dec hlt_dec l default w Hw)
               Heps).
Qed.

End EpsOptimalReachCore.

(* Part 3: composition -- eps-optimal reachability over finite trajectories plus the first-tier quad_cost adaptation *)

(* The composition main item: the eps-optimal reach witness over the sampled descent-trajectory table.
   A := Q (the trajectory-point carrier of item B), the key abstract (any cost function),
   the domination certificates instantiated from the Part 2 main item at the interface slot l := traj_table h t x0 n.
   Exports: sigT + And + InT + interface le, a zero-Prop statement face. *)
Theorem trajectory_eps_optimal_reach :
  forall (keyQ : Q -> R)
         (hle_dec : forall a b : R, Or (le a b) (Not (le a b)))
         (hlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)))
         (h t x0 : Q) (eps : R) (n : nat),
    le zero eps ->
    sigT (fun xstar =>
      And (InT xstar (traj_table h t x0 n))
          (And (forall w : Q, InT w (traj_table h t x0 n)
                             -> le (keyQ xstar) (keyQ w))
               (forall w : Q, InT w (traj_table h t x0 n)
                             -> le (keyQ xstar) (plus (keyQ w) eps)))).
Proof.
  intros keyQ hle_dec hlt_dec h t x0 eps n Heps.
  exact (@finite_table_eps_optimal_witness Q keyQ hle_dec hlt_dec           (traj_table h t x0 n) x0 eps           (traj_table_nonempty h t x0 n) Heps).
Qed.

(* The item-B adaptation (first tier): an eps-upper-bound at the endpoint of the n-step descent.
   sf_grad_descent_convergence (the exact QleT' contraction bound) loosened by qlep_add_eps.
   Note: Q has no RIS instance (see the header), so the Q-layer key instantiation goes through the QleT' chain. *)
Theorem quad_cost_descent_eps_bound :
  forall (h t x0 eps : Q) (n : nat),
    QltT 0 h -> QltT h 2 -> QleT' 0 eps ->
    QleT' (sf_quad_cost t (sf_grad_descent h t x0 n))
          (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x0 + eps).
Proof.
  intros h t x0 eps n Hh H2 Heps.
  exact (qlep_add_eps (sf_quad_cost t (sf_grad_descent h t x0 n))           (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x0) eps           (sf_grad_descent_convergence h t x0 n Hh H2) Heps).
Qed.

(* The audit-trail face: G4 (at least 1 statement) *)
Print Assumptions finite_table_eps_optimal_witness.
Print Assumptions trajectory_eps_optimal_reach.
Print Assumptions quad_cost_descent_eps_bound.
Print Assumptions traj_table_iterate_mem.
