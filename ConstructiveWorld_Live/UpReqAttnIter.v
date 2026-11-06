(* ConstructiveWorld-Set -- req-layer attention iteration family. *)

(** * UpReqAttnIter: total-variation contraction of the req-layer attention iteration.

    Mission.  Formalizes the req-layer copy of the attention iteration operator: the Boltzmann
      side ([boltzmann_factor_i], [boltzmann_dist_i]), the q-kernel and one step ([q_kernel_i],
      [attention_step_i], [attention_iter_i]), the total-variation distance [tv_i], the spine of
      kernel identities ([agq_kernel_nonneg], [agq_kernel_row], [agq_step_norm],
      [agq_iter_norm]), the one-step contraction [agq_tv_contraction], the geometric iterate
      [agq_tv_iter], and the convergence theorem [agq_iterate_converges].

    Dependencies.  Stdlib [List] (with [ListNotations]) and [Lia].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqDist], [UpReqSampling] of this development.

    References.  This development, UpReqAttnIter.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here verbatim
      (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set] (decidable
      Q-carriers and boolean identity carriers); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].  The summation premises [sum_ext], [sum_linear],
      [sum_add], [sum_le], [sum_nonneg_h], [abs_sum_le_h] and [abs_nonneg_h] are declared as
      explicit [Hypothesis] slots of the enclosing [ReqAttnIter] section and remain assumptions
      of every statement stated inside it.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqAttnIter.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real
   (S07_RealSetoidExpLog.v zero-argument Class RealInterfaceEnhancedSetoid + global
   Instance RealEnhancedReal; Notation passthrough per the world's own UpReqAlign3.v
   precedent). *)
Notation R := Real.
(* The equality and order carriers of the statements below are bound to the concrete
   informative definitions real_eq / real_lt / real_le of the S-tree.  These are
   exactly the bindings that the global RealEnhancedReal instance assigns to the
   interface fields req / lt / le, so every statement elaborates to the same term as
   before; naming the carriers concretely keeps the extracted signatures informative
   and free of interface casts. *)
Notation lt := real_lt.
Notation req := real_eq.
Notation le := real_le.

(* ============================================================ *)
(* Section ReqAttnIter: req-layer migration of the q-kernel and    *)
(*   contraction iteration cluster (29 statements).                *)
(*   The summation interface carries the req copies of the Id      *)
(*   SumOver class fields, declared inside the section.            *)
(* ============================================================ *)
Section ReqAttnIter.
(* A-face adaptation (per UpReqAlign3.v precedent): the argument-bearing generation
   binders [Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.] are deleted; the
   carrier R is the global Real through the Require face, and the class fields
   (req/lt/le/zero/one/plus/mult/opp/abs/inv_pos/exp_neg) resolve through the global
   instance RealEnhancedReal.  Zero magic constructors, zero Prop casts, statement
   faces and premise positions preserved verbatim. *)

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- Summation interface: req copies of the Id SumOver fields, positionwise ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
(* Sums of nonnegative functions are nonnegative (req copy of the Id sum_over_S_nonneg field) *)
Hypothesis sum_nonneg_h :
  forall f : S -> R, (forall s : S, le zero (f s)) -> le zero (sumf f).
(* Triangle bound for sums (req copy of the Id abs_sum_le field) *)
Hypothesis abs_sum_le_h :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).
(* abs is nonnegative: req copy of the Id RealInterface abs_nonneg premise in
   the same position (the RIS class only carries the eps form, a constructive
   order cannot derive it, and the Real instance satisfies it) *)
Hypothesis abs_nonneg_h : forall a : R, le zero (abs a).

(* ---- Boltzmann side (upstream copy; the exp(-E/T) convention keeps its sign) ---- *)
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition boltzmann_factor_i (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo_i : R := sumf boltzmann_factor_i.

Variable Z_thermo_i_pos : lt zero Z_thermo_i.

Definition boltzmann_dist_i (s : S) : R :=
  mult (inv_pos Z_thermo_i Z_thermo_i_pos) (boltzmann_factor_i s).

(* ---- Markov side (upstream copy; the le-level statements migrate verbatim) ---- *)
Variable transition : S -> S -> R.
(* Row normalization (req copy of Id transition_normalization; the exit face switches Id to req) *)
Variable transition_row_i :
  forall s : S, req (sumf (fun s' : S => transition s s')) one.
Variable delta : R.
Variable delta_pos : lt zero delta.
Variable delta_lt_one : lt delta one.
(* Doeblin lower bound (le-level copy of Id minorization, positionwise) *)
Variable minorization :
  forall s s' : S, le (mult delta (boltzmann_dist_i s')) (transition s s').
(* Mixed plus-compatibility, the two premise positions as upstream *)
Variable lt_plus_compat_lt_le_i :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable lt_plus_compat_le_lt_i :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
(* Double-sum exchange (req form of Id sum_swap_cc) *)
Variable sum_swap_i : forall f : S -> S -> R,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
(* abs witness premise (req copy of Id abs_ge_zero_id_cc; the exit face switches Id to req, as in UpReqSampling) *)
Variable abs_ge_zero_i : forall a : R, le zero a -> req (abs a) a.
(* Steady state: req-form premise copy of Id steady_state_boltzmann_attn
   (upstream proves it from detailed_balance and the base setoid statements;
   here it is held as a section premise, positionwise) *)
Variable p_steady_i :
  forall s' : S,
    req (sumf (fun s : S => mult (boltzmann_dist_i s) (transition s s')))
        (boltzmann_dist_i s').
(* Geometric decay premise (req form of the Id r_arch_pow_attn honest interface; the power base becomes req_r_pow) *)
Variable arch_pow_i :
  forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => lt (mult a (req_r_pow (req_minus one delta) N)) eps).

Let omd := req_minus one delta.

(* 1 - delta > 0 (adjacent upstream statement; counterpart rsq_u_omd_pos_next) *)
Lemma agq_omd_pos : lt zero omd.
Proof.
  exact (@rsq_u_omd_pos_next delta delta_lt_one lt_plus_compat_lt_le_i).
Qed.

Let inv_omd := inv_pos omd agq_omd_pos.

Definition inv_two_i : R := inv_pos (plus one one) req_two_pos.

Definition tv_i (mu nu : S -> R) : R :=
  mult inv_two_i (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).

Definition attention_step_i (mu : S -> R) (s' : S) : R :=
  sumf (fun s : S => mult (mu s) (transition s s')).

(* The q-kernel (req form of Id q_kernel): a definitional binding of the fully
   applied rsq_u_r_kernel of ReqUContraction.  The inverse is a proof-relevant
   witness and the body is req (mult inv_omd
   (req_minus (transition s s') (mult delta (boltzmann_dist_i s')))) up to
   the same unfolding; binding the kernel directly keeps the witness position
   conversion-stable. *)
Definition q_kernel_i (s s' : S) : R :=
  @rsq_u_r_kernel S boltzmann_dist_i delta delta_lt_one transition
    lt_plus_compat_lt_le_i s s'.

Fixpoint attention_iter_i (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => attention_step_i (attention_iter_i m mu)
  end.

(* ---- The two remaining statements about 1 - delta ---- *)

(* 1 - delta <= 1: combine aux_delta_plus_omd (exported by UpReqSampling)
   with req_le_plus_nonneg_r *)
Lemma agq_omd_le_one : le omd one.
Proof.
  apply (le_id_r omd (plus omd delta) one).
  - exact (req_trans (plus omd delta) (plus delta omd) one
             (plus_comm omd delta) (aux_delta_plus_omd delta)).
  - exact (req_le_plus_nonneg_r omd delta (lt_le_iff _ _ (inl delta_pos))).
Qed.

(* 1 - delta < 1: unfold omd at delta and apply the mixed plus-compatibility premise *)
Lemma agq_omd_lt_one : lt omd one.
Proof.
  exact (lt_id_r omd (plus one zero) one (plus_zero one)
           (lt_plus_compat_le_lt_i one one (opp delta) zero
              (le_refl one) (lt_zero_opp delta delta_pos))).
Qed.

(* ---- The two steady-state targets ---- *)

(* Normalization of p: the base setoid statement has the Id SumOver form; the section sumf carries it here *)
Lemma agq_p_norm : req (sumf boltzmann_dist_i) one.
Proof.
  unfold boltzmann_dist_i.
  apply (req_trans _ (mult (inv_pos Z_thermo_i Z_thermo_i_pos)
                           (sumf boltzmann_factor_i)) _).
  - exact (sum_linear (inv_pos Z_thermo_i Z_thermo_i_pos) boltzmann_factor_i).
  - exact (req_trans (mult (inv_pos Z_thermo_i Z_thermo_i_pos) Z_thermo_i)
                     (mult Z_thermo_i (inv_pos Z_thermo_i Z_thermo_i_pos)) one
             (mult_comm (inv_pos Z_thermo_i Z_thermo_i_pos) Z_thermo_i)
             (inv_pos_correct Z_thermo_i Z_thermo_i_pos)).
Qed.

(* p is pointwise positive: mult_positive matches directly *)
Lemma agq_p_pos : forall s : S, lt zero (boltzmann_dist_i s).
Proof.
  intro s. unfold boltzmann_dist_i.
  apply mult_positive.
  - exact (inv_pos_pos Z_thermo_i Z_thermo_i_pos).
  - unfold boltzmann_factor_i. apply exp_neg_pos.
Qed.

(* ---- Four independent algebra lemmas (no matching form in UpReqAlgebra; proved directly) ---- *)

(* Additive cancellation: a + b == c gives b == c - a (req_minus_plus_cancel
   with req_add_cancel_l) *)
Lemma agq_plus_cancel :
  forall a b c : R, req (plus a b) c -> req b (req_minus c a).
Proof.
  intros a b c H.
  exact (req_trans _ _ _ (req_sym _ _ (req_minus_plus_cancel_r a b))
           (reqd_minus_compat (plus a b) c a a H (req_refl a))).
Qed.

(* inv absorption: inv(c) * (c * a) == a (associativity with inv_pos_correct and the unit laws) *)
Lemma agq_absorb_inv :
  forall (c : R) (Hc : lt zero c) (a : R),
    req (mult (inv_pos c Hc) (mult c a)) a.
Proof.
  intros c Hc a.
  apply (req_trans (mult (inv_pos c Hc) (mult c a))
                   (mult (mult (inv_pos c Hc) c) a) a).
  - exact (mult_assoc (inv_pos c Hc) c a).
  - apply (req_trans (mult (mult (inv_pos c Hc) c) a) (mult one a) a).
    + exact (req_mult_compat (mult (inv_pos c Hc) c) one a a
               (req_trans (mult (inv_pos c Hc) c)
                          (mult c (inv_pos c Hc)) one
                          (mult_comm (inv_pos c Hc) c)
                          (inv_pos_correct c Hc))
               (req_refl a)).
    + exact (req_mult_one_l a).
Qed.

(* (a + b) - c == b + (a - c): four associativity and commutativity rewrites;
   UpReqAlgebra req_minus_plus_r states (a - (b + c)) instead, so a separate
   lemma is built here *)
Lemma agq_minus_plus_swap_cc :
  forall a b c : R, req (req_minus (plus a b) c) (plus b (req_minus a c)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus (plus a b) (opp c))
                   (plus a (plus b (opp c))) _).
  - exact (req_sym _ _ (plus_assoc a b (opp c))).
  - apply (req_trans (plus a (plus b (opp c)))
                     (plus a (plus (opp c) b)) _).
    + exact (req_plus_compat a a (plus b (opp c)) (plus (opp c) b)
               (req_refl a) (plus_comm b (opp c))).
    + apply (req_trans (plus a (plus (opp c) b))
                       (plus (plus a (opp c)) b) _).
      * exact (plus_assoc a (opp c) b).
      * exact (plus_comm (plus a (opp c)) b).
Qed.

(* (a * b) - b == -((1 - a) * b): unit rewrites, the pointwise subtraction factor, and a sign chain *)
Lemma agq_minus_scal_opp_cc :
  forall a b : R,
    req (req_minus (mult a b) b) (opp (mult (req_minus one a) b)).
Proof.
  intros a b.
  assert (Hs : req (req_minus a one) (opp (req_minus one a))).
  { unfold req_minus.
    apply (req_trans (plus a (opp one)) (plus (opp one) a) _).
    - exact (plus_comm a (opp one)).
    - apply (req_trans (plus (opp one) a)
                       (plus (opp one) (opp (opp a))) _).
      + exact (req_plus_compat (opp one) (opp one) a (opp (opp a))
                  (req_refl (opp one)) (req_sym _ _ (req_double_neg a))).
      + exact (req_sym _ _ (req_opp_plus one (opp a))). }
  apply (req_trans (req_minus (mult a b) b)
                   (req_minus (mult a b) (mult one b)) _).
  - exact (reqd_minus_compat (mult a b) (mult a b) b (mult one b)
             (req_refl (mult a b))
             (req_trans _ _ _ (req_sym _ _ (mult_one b)) (mult_comm b one))).
  - apply (req_trans (req_minus (mult a b) (mult one b))
                     (mult (req_minus a one) b) _).
    + exact (req_minus_factor_pt a one b).
    + apply (req_trans (mult (req_minus a one) b)
                       (mult (opp (req_minus one a)) b) _).
      * exact (req_mult_compat (req_minus a one) (opp (req_minus one a))
                  b b Hs (req_refl b)).
      * exact (req_opp_mult_r (req_minus one a) b).
Qed.

(* |c * b| <= c * |b| for c >= 0: abs_mult with the abs witness premise *)
Lemma agq_abs_mult_nonneg :
  forall a b : R, le zero a -> le (abs (mult a b)) (mult a (abs b)).
Proof.
  intros a b Ha.
  apply (le_id_l (abs (mult a b)) (mult a (abs b)) (mult a (abs b))
                 (req_trans (abs (mult a b)) (mult (abs a) (abs b))
                            (mult a (abs b))
                            (abs_mult a b)
                            (req_mult_compat (abs a) a (abs b) (abs b)
                               (abs_ge_zero_i a Ha) (req_refl (abs b))))
                 (le_refl _)).
Qed.

(* ---- The ten spine statements (each follows from an exported
   ReqUContraction statement of UpReqSampling, with u := boltzmann_dist_i;
   q_kernel_i, attention_step_i and tv_i unify transparently at delta) ---- *)

(* The q-kernel is pointwise nonnegative (counterpart rsq_u_r_nonneg) *)
Lemma agq_kernel_nonneg : forall s s' : S, le zero (q_kernel_i s s').
Proof.
  intros s s'.
  exact (@rsq_u_r_nonneg S boltzmann_dist_i delta delta_lt_one transition
           minorization lt_plus_compat_lt_le_i s s').
Qed.

(* Row normalization of the q-kernel (counterpart rsq_u_r_norm) *)
Lemma agq_kernel_row :
  forall s : S, req (sumf (fun s' : S => q_kernel_i s s')) one.
Proof.
  intro s.
  exact (@rsq_u_r_norm S sumf sum_ext sum_linear sum_add boltzmann_dist_i
           agq_p_norm delta delta_lt_one transition transition_row_i
           lt_plus_compat_lt_le_i s).
Qed.

(* The transition is delta * p + (1 - delta) * Q (counterpart rsq_u_tr_decomp) *)
Lemma agq_tr_decomp : forall s s' : S,
  req (transition s s')
      (plus (mult delta (boltzmann_dist_i s'))
            (mult omd (q_kernel_i s s'))).
Proof.
  intros s s'.
  exact (@rsq_u_tr_decomp S boltzmann_dist_i delta delta_lt_one transition
           lt_plus_compat_lt_le_i s s').
Qed.

(* delta * a + (1 - delta) * a == a (counterpart rsq_delta_absorb_u) *)
Lemma agq_delta_absorb : forall a : R,
  req (plus (mult delta a) (mult omd a)) a.
Proof.
  intro a. exact (rsq_delta_absorb_u delta a).
Qed.

(* One-step decomposition: T mu == delta * p + (1 - delta) * Q mu (counterpart rsq_u_step_decomp) *)
Lemma agq_step_decomp : forall (mu : S -> R) (s' : S),
  req (sumf mu) one ->
  req (attention_step_i mu s')
      (plus (mult delta (boltzmann_dist_i s'))
            (mult omd (sumf (fun s : S => mult (mu s) (q_kernel_i s s'))))).
Proof.
  intros mu s' Hmu.
  exact (@rsq_u_step_decomp S sumf sum_ext sum_linear sum_add
           boltzmann_dist_i delta delta_lt_one transition
           lt_plus_compat_lt_le_i mu s' Hmu).
Qed.

(* One step preserves normalization (counterpart rsq_u_step_norm) *)
Lemma agq_step_norm : forall mu : S -> R,
  req (sumf mu) one -> req (sumf (fun s' : S => attention_step_i mu s')) one.
Proof.
  intros mu Hmu.
  exact (@rsq_u_step_norm S sumf sum_ext sum_linear sum_add boltzmann_dist_i
           agq_p_norm delta delta_lt_one transition transition_row_i
           sum_swap_i lt_plus_compat_lt_le_i mu Hmu).
Qed.

(* |sum (f * Q)| <= sum (|f| * Q) (counterpart rsq_u_abs_row) *)
Lemma agq_abs_kernel_bound : forall (f : S -> R) (s' : S),
  le (abs (sumf (fun s : S => mult (f s) (q_kernel_i s s'))))
     (sumf (fun s : S => mult (abs (f s)) (q_kernel_i s s'))).
Proof.
  intros f s'.
  exact (@rsq_u_abs_row S sumf sum_ext abs_sum_le_h boltzmann_dist_i delta
           delta_lt_one transition minorization abs_ge_zero_i
           lt_plus_compat_lt_le_i f s').
Qed.

(* Iteration preserves normalization (counterpart rsq_u_titer_norm);
   attention_iter_i and rsq_u_titer have convertible Fixpoint structure once
   transition is fixed *)
Lemma agq_iter_norm : forall (n : nat) (mu : S -> R),
  req (sumf mu) one -> req (sumf (attention_iter_i n mu)) one.
Proof.
  intros n mu Hmu.
  exact (@rsq_u_titer_norm S sumf sum_ext sum_linear sum_add boltzmann_dist_i
           agq_p_norm delta delta_lt_one transition transition_row_i
           sum_swap_i lt_plus_compat_lt_le_i n mu Hmu).
Qed.

(* Compatibility of tv in its right argument: nu1 == nu2 pointwise gives
   tv(f, nu1) == tv(f, nu2), by compat at the mult, sum, abs and minus
   layers *)
Lemma agq_tv_compat_r : forall (f nu1 nu2 : S -> R),
  (forall s : S, req (nu1 s) (nu2 s)) -> req (tv_i f nu1) (tv_i f nu2).
Proof.
  intros f nu1 nu2 H. unfold tv_i.
  exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
           (sum_ext _ _ (fun s : S =>
              req_abs_compat _ _
                (reqd_minus_compat _ _ _ _ (req_refl _) (H s))))).
Qed.

(* ========== Main theorem 1: one-step TV contraction ==========
   Follows from the two-point rsq_u_tv_contraction at nu := p with the target
   side rewritten through the steady-state premise p_steady_i (step(p) == p
   pointwise).  The req form drops the nonnegativity premise, as judged for
   rsq_u_tv_contraction. *)
Lemma agq_tv_contraction : forall mu : S -> R,
  req (sumf mu) one ->
  le (tv_i (attention_step_i mu) boltzmann_dist_i)
     (mult omd (tv_i mu boltzmann_dist_i)).
Proof.
  intros mu Hmu.
  apply (le_id_l _ _ _
           (req_sym _ _
              (agq_tv_compat_r (attention_step_i mu)
                 (attention_step_i boltzmann_dist_i) boltzmann_dist_i
                 p_steady_i))).
  exact (@rsq_u_tv_contraction S sumf sum_ext sum_linear sum_add sum_le
           abs_sum_le_h boltzmann_dist_i agq_p_norm delta delta_lt_one
           transition transition_row_i minorization sum_swap_i abs_ge_zero_i
           lt_plus_compat_lt_le_i mu boltzmann_dist_i Hmu agq_p_norm).
Qed.

(* ---- Statements specific to the one-point setting (proved or assembled here) ---- *)

(* Products of nonnegative factors are nonnegative, weak le * le form: a req
   rebuild of Id le_mult_nonneg_t12 by mult_comm and mult_zero rewrites with
   le_mult_compat_weak; UpReqAlgebra and UpReqDist have no ready le * le
   statement, so it is built inside the section *)
Lemma agq_le_mult_nonneg :
  forall a b : R, le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_r zero (mult b a) (mult a b) (mult_comm b a)).
  apply (le_id_l zero (mult zero a) (mult b a)).
  - exact (req_sym (mult zero a) zero
             (req_trans (mult zero a) (mult a zero) zero
                        (mult_comm zero a) (mult_zero a))).
  - exact (le_mult_compat_weak zero b a Ha Hb).
Qed.

(* One step preserves nonnegativity: the two branches X and Y with le_plus_compat *)
Lemma agq_step_nonneg : forall mu : S -> R,
  req (sumf mu) one -> (forall s : S, le zero (mu s)) ->
  forall s' : S, le zero (attention_step_i mu s').
Proof.
  intros mu Hmu Hnn s'.
  assert (HX : le zero (mult delta (boltzmann_dist_i s'))).
  { apply (aux_le_mult_nonneg_t12 delta (boltzmann_dist_i s')).
    - exact delta_pos.
    - exact (lt_le_iff _ _ (inl (agq_p_pos s'))). }
  assert (HY : le zero (mult omd (sumf (fun s : S =>
                  mult (mu s) (q_kernel_i s s'))))).
  { apply (aux_le_mult_nonneg_t12 omd
              (sumf (fun s : S => mult (mu s) (q_kernel_i s s')))).
    - exact agq_omd_pos.
    - apply sum_nonneg_h. intro s.
      exact (agq_le_mult_nonneg (mu s) (q_kernel_i s s')
               (Hnn s) (agq_kernel_nonneg s s')). }
  assert (Hstep : le zero (plus (mult delta (boltzmann_dist_i s'))
                                (mult omd (sumf (fun s : S =>
                                   mult (mu s) (q_kernel_i s s')))))).
  { apply (le_id_l zero (plus zero zero) _ (req_sym _ _ (plus_zero zero))).
    exact (le_plus_compat zero (mult delta (boltzmann_dist_i s')) zero
             (mult omd (sumf (fun s : S => mult (mu s) (q_kernel_i s s'))))
             HX HY). }
  apply (le_id_r zero (plus (mult delta (boltzmann_dist_i s'))
                            (mult omd (sumf (fun s : S =>
                               mult (mu s) (q_kernel_i s s')))))
                   (attention_step_i mu s')).
  - exact (req_sym _ _ (agq_step_decomp mu s' Hmu)).
  - exact Hstep.
Qed.

(* Iteration preserves nonnegativity: induction on the pointwise nonnegativity *)
Lemma agq_iter_nonneg : forall (n : nat) (mu : S -> R),
  req (sumf mu) one -> (forall s : S, le zero (mu s)) ->
  forall s : S, le zero (attention_iter_i n mu s).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu Hnn s.
  - exact (Hnn s).
  - exact (agq_step_nonneg (attention_iter_i n mu)
             (agq_iter_norm n mu Hmu) (IH mu Hmu Hnn) s).
Qed.

(* Steady-state invariance: p * Q == p (the p_steady premise with the
   one-step decomposition, agq_plus_cancel, agq_minus_scal_opp_cc and
   agq_absorb_inv) *)
Lemma agq_p_kernel_fixed : forall s' : S,
  req (sumf (fun s : S => mult (boltzmann_dist_i s) (q_kernel_i s s')))
      (boltzmann_dist_i s').
Proof.
  intro s'.
  assert (H3 : req (plus (mult delta (boltzmann_dist_i s'))
                         (mult omd (sumf (fun s : S =>
                            mult (boltzmann_dist_i s) (q_kernel_i s s')))))
                   (boltzmann_dist_i s')).
  { exact (req_trans _ _ _
             (req_sym _ _ (agq_step_decomp boltzmann_dist_i s' agq_p_norm))
             (p_steady_i s')). }
  assert (H7 : req (mult omd (sumf (fun s : S =>
                      mult (boltzmann_dist_i s) (q_kernel_i s s'))))
                   (mult omd (boltzmann_dist_i s'))).
  { assert (H4 : req (mult omd (sumf (fun s : S =>
                        mult (boltzmann_dist_i s) (q_kernel_i s s'))))
                     (req_minus (boltzmann_dist_i s')
                                (mult delta (boltzmann_dist_i s'))))
      by exact (agq_plus_cancel (mult delta (boltzmann_dist_i s')) _
                  (boltzmann_dist_i s') H3).
    assert (H6 : req (req_minus (boltzmann_dist_i s')
                                (mult delta (boltzmann_dist_i s')))
                     (mult omd (boltzmann_dist_i s'))).
    { apply (req_trans _ (req_minus (mult one (boltzmann_dist_i s'))
                                    (mult delta (boltzmann_dist_i s'))) _).
      - exact (reqd_minus_compat (boltzmann_dist_i s')
                  (mult one (boltzmann_dist_i s'))
                  (mult delta (boltzmann_dist_i s'))
                  (mult delta (boltzmann_dist_i s'))
                  (req_trans _ _ _
                     (req_sym _ _ (mult_one (boltzmann_dist_i s')))
                     (mult_comm (boltzmann_dist_i s') one))
                  (req_refl _)).
      - exact (req_sym _ _ (req_mult_minus_distr_r one delta
                  (boltzmann_dist_i s'))). }
    exact (req_trans _ _ _ H4 H6). }
  assert (HA : req (mult inv_omd (mult omd (sumf (fun s : S =>
                      mult (boltzmann_dist_i s) (q_kernel_i s s')))))
                   (sumf (fun s : S =>
                      mult (boltzmann_dist_i s) (q_kernel_i s s'))))
    by exact (agq_absorb_inv omd agq_omd_pos
                (sumf (fun s : S => mult (boltzmann_dist_i s) (q_kernel_i s s')))).
  assert (HC : req (mult inv_omd (mult omd (boltzmann_dist_i s')))
                   (boltzmann_dist_i s'))
    by exact (agq_absorb_inv omd agq_omd_pos (boltzmann_dist_i s')).
  apply (req_trans _ (mult inv_omd (mult omd (sumf (fun s : S =>
         mult (boltzmann_dist_i s) (q_kernel_i s s'))))) _).
  - exact (req_sym _ _ HA).
  - apply (req_trans _ (mult inv_omd (mult omd (boltzmann_dist_i s'))) _).
    + exact (req_mult_compat _ _ _ _ (req_refl _) H7).
    + exact HC.
Qed.

(* Pointwise difference decomposition: T mu - p == (1 - delta) * sum (mu - p) * Q
   (a chain through reqd_minus_compat, agq_minus_plus_swap_cc,
   agq_minus_scal_opp_cc, req_mult_minus_distr_r, agq_p_kernel_fixed,
   reqd_sum_minus and req_minus_factor_pt) *)
Lemma agq_diff_decomp : forall (mu : S -> R) (s' : S),
  req (sumf mu) one ->
  req (req_minus (attention_step_i mu s') (boltzmann_dist_i s'))
      (mult omd
            (sumf (fun s : S =>
               mult (req_minus (mu s) (boltzmann_dist_i s))
                    (q_kernel_i s s')))).
Proof.
  intros mu s' Hmu.
  assert (S1 : req (req_minus (attention_step_i mu s') (boltzmann_dist_i s'))
                   (req_minus (plus (mult delta (boltzmann_dist_i s'))
                                    (mult omd (sumf (fun s : S =>
                                       mult (mu s) (q_kernel_i s s')))))
                              (boltzmann_dist_i s')))
    by exact (reqd_minus_compat (attention_step_i mu s')
                (plus (mult delta (boltzmann_dist_i s'))
                      (mult omd (sumf (fun s : S =>
                         mult (mu s) (q_kernel_i s s')))))
                (boltzmann_dist_i s') (boltzmann_dist_i s')
                (agq_step_decomp mu s' Hmu) (req_refl _)).
  assert (S23 : req (req_minus (plus (mult delta (boltzmann_dist_i s'))
                                     (mult omd (sumf (fun s : S =>
                                        mult (mu s) (q_kernel_i s s')))))
                                (boltzmann_dist_i s'))
                   (plus (mult omd (sumf (fun s : S =>
                            mult (mu s) (q_kernel_i s s'))))
                         (opp (mult omd (boltzmann_dist_i s'))))).
  { apply (req_trans _ _ _
             (agq_minus_plus_swap_cc (mult delta (boltzmann_dist_i s'))
                (mult omd (sumf (fun s : S => mult (mu s) (q_kernel_i s s'))))
                (boltzmann_dist_i s'))).
    exact (req_plus_compat _ _ _ _ (req_refl _)
             (agq_minus_scal_opp_cc delta (boltzmann_dist_i s'))). }
  assert (S4 : req (req_minus (mult omd (sumf (fun s : S =>
                                  mult (mu s) (q_kernel_i s s'))))
                              (mult omd (boltzmann_dist_i s')))
                   (mult omd (req_minus (sumf (fun s : S =>
                                           mult (mu s) (q_kernel_i s s')))
                                        (boltzmann_dist_i s'))))
    by exact (req_sym _ _ (req_mult_minus_distr_l omd
                (sumf (fun s : S => mult (mu s) (q_kernel_i s s')))
                (boltzmann_dist_i s'))).
  assert (S5 : req (req_minus (sumf (fun s : S =>
                                  mult (mu s) (q_kernel_i s s')))
                              (boltzmann_dist_i s'))
                   (sumf (fun s : S =>
                      mult (req_minus (mu s) (boltzmann_dist_i s))
                           (q_kernel_i s s')))).
  { apply (req_trans _ (req_minus
           (sumf (fun s : S => mult (mu s) (q_kernel_i s s')))
           (sumf (fun s : S => mult (boltzmann_dist_i s) (q_kernel_i s s')))) _).
    - exact (reqd_minus_compat (sumf (fun s : S =>
                  mult (mu s) (q_kernel_i s s')))
                  (sumf (fun s : S =>
                     mult (mu s) (q_kernel_i s s')))
                  (boltzmann_dist_i s')
                  (sumf (fun s : S =>
                     mult (boltzmann_dist_i s) (q_kernel_i s s')))
                  (req_refl _)
                  (req_sym _ _ (agq_p_kernel_fixed s'))).
    - apply (req_trans _ (sumf (fun s : S =>
           req_minus (mult (mu s) (q_kernel_i s s'))
                     (mult (boltzmann_dist_i s) (q_kernel_i s s')))) _).
      + exact (req_sym _ _
                   (@reqd_sum_minus S sumf sum_ext sum_add sum_linear
                      (fun s : S => mult (mu s) (q_kernel_i s s'))
                      (fun s : S =>
                         mult (boltzmann_dist_i s) (q_kernel_i s s')))).
      + apply (sum_ext _ _).
        intro s. exact (req_minus_factor_pt (mu s) (boltzmann_dist_i s)
                          (q_kernel_i s s')). }
  apply (req_trans _ _ _ S1
           (req_trans _ _ _ S23
              (req_trans _ _ _ S4
                 (req_mult_compat _ _ _ _ (req_refl _) S5)))).
Qed.

(* The TV distance is nonnegative: inv_pos on two positives with the sum_nonneg_h and abs_nonneg_h premises *)
Lemma agq_tv_nonneg : forall mu nu : S -> R, le zero (tv_i mu nu).
Proof.
  intros mu nu. unfold tv_i.
  apply (aux_le_mult_nonneg_t12 inv_two_i
            (sumf (fun s : S => abs (req_minus (mu s) (nu s))))).
  - exact (inv_pos_pos (plus one one) req_two_pos).
  - apply sum_nonneg_h. intro s.
    exact (abs_nonneg_h (req_minus (mu s) (nu s))).
Qed.

(* Double-sum reduction: (1/2) * sum over s' of (1 - delta) * sum over s of
   f * Q == (1 - delta) * (1/2) * sum f (assembled from sum_linear,
   sum_swap_i, pointwise row normalization and associative rewrites) *)
Lemma agq_tv_reduce : forall f : S -> R,
  req (mult inv_two_i (sumf (fun s' : S => mult omd
         (sumf (fun s : S => mult (f s) (q_kernel_i s s'))))))
      (mult omd (mult inv_two_i (sumf f))).
Proof.
  intro f.
  apply (req_trans _ (mult inv_two_i (mult omd
         (sumf (fun s' : S => sumf (fun s : S =>
            mult (f s) (q_kernel_i s s')))))) _).
  - exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
             (sum_linear omd (fun s' : S =>
                sumf (fun s : S => mult (f s) (q_kernel_i s s'))))).
  - apply (req_trans _ (mult inv_two_i (mult omd
           (sumf (fun s : S => sumf (fun s' : S =>
              mult (f s) (q_kernel_i s s')))))) _).
    + exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
               (req_mult_compat omd omd _ _ (req_refl omd)
                  (req_sym _ _ (sum_swap_i (fun s s' : S =>
                     mult (f s) (q_kernel_i s s')))))).
    + assert (Hpt : forall s : S,
               req (sumf (fun s' : S => mult (f s) (q_kernel_i s s'))) (f s)).
      { intro s.
        apply (req_trans _ (mult (f s) (sumf (fun s' : S => q_kernel_i s s')))).
        - exact (sum_linear (f s) (fun s' : S => q_kernel_i s s')).
        - apply (req_trans _ (mult (f s) one)).
          + exact (req_mult_compat (f s) (f s)
                     (sumf (fun s' : S => q_kernel_i s s')) one
                     (req_refl (f s)) (agq_kernel_row s)).
          + exact (mult_one (f s)). }
      assert (Hsum : req (sumf (fun s : S =>
                          sumf (fun s' : S => mult (f s) (q_kernel_i s s'))))
                         (sumf f))
        by exact (sum_ext _ _ Hpt).
      apply (req_trans _ (mult inv_two_i (mult omd (sumf f))) _).
      * exact (req_mult_compat inv_two_i inv_two_i _ _ (req_refl inv_two_i)
                  (req_mult_compat omd omd _ _ (req_refl omd) Hsum)).
      * exact (req_trans (mult inv_two_i (mult omd (sumf f)))
                  (mult (mult inv_two_i omd) (sumf f))
                  (mult omd (mult inv_two_i (sumf f)))
                  (mult_assoc inv_two_i omd (sumf f))
                  (req_trans (mult (mult inv_two_i omd) (sumf f))
                     (mult (mult omd inv_two_i) (sumf f))
                     (mult omd (mult inv_two_i (sumf f)))
                     (req_mult_compat (mult inv_two_i omd) (mult omd inv_two_i)
                        (sumf f) (sumf f)
                        (mult_comm inv_two_i omd) (req_refl (sumf f)))
                     (req_sym _ _ (mult_assoc omd inv_two_i (sumf f))))).

Qed.

(* ---- Power monotonicity and geometric iteration ---- *)

(* Powers decrease by one step: omd^(S n) <= omd^n (the special case of Id
   r_pow_dec with base 1 - delta; a unit rewrite at the base case and
   le_mult_compat at the recursive step; UpReqSampling has no monotonicity
   statement for req_r_pow, so it is built here) *)
Lemma agq_r_pow_dec : forall n : nat,
  le (req_r_pow omd (Datatypes.S n)) (req_r_pow omd n).
Proof.
  intro n. induction n as [| m IH].
  - exact (le_id_l (mult omd one) omd one (mult_one omd) agq_omd_le_one).
  - apply (le_id_l _ (mult (req_r_pow omd (Datatypes.S m)) omd) _).
    + exact (mult_comm omd (req_r_pow omd (Datatypes.S m))).
    + apply (le_id_r _ (mult (req_r_pow omd m) omd) _).
      * exact (mult_comm (req_r_pow omd m) omd).
      * apply (le_mult_compat _ _ _ agq_omd_pos).
        exact IH.
Qed.

(* Powers decrease with the exponent: m <= n gives omd^n <= omd^m (assembled
   from the nat-level lia/Nat.leb argument, of the same order as the
   upstream statement, with agq_r_pow_dec) *)
Lemma agq_r_pow_dec_iter : forall m n : nat,
  (m <= n)%nat -> le (req_r_pow omd n) (req_r_pow omd m).
Proof.
  intros m n Hmn. revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - assert (Hm0 : m = 0%nat) by lia. subst m. apply le_refl.
  - destruct (Nat.leb m n) eqn:Emn.
    + apply (le_trans _ (req_r_pow omd n) _).
      * exact (agq_r_pow_dec n).
      * exact (IH m (proj1 (PeanoNat.Nat.leb_le m n) Emn)).
    + apply PeanoNat.Nat.leb_gt in Emn.
      assert (Hm : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* ========== Main theorem 2: geometric iteration TV contraction ==========
   Induction: the base case rewrites through the scalar unit laws; the
   recursive step chains agq_tv_contraction with req_le_mult_compat_r and
   associativity; the target side stays at the steady state. *)
Lemma agq_tv_iter : forall (n : nat) (mu : S -> R),
  req (sumf mu) one ->
  le (tv_i (attention_iter_i n mu) boltzmann_dist_i)
     (mult (req_r_pow omd n) (tv_i mu boltzmann_dist_i)).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu.
  - exact (le_id_l _ _ _
             (req_trans _ _ _
                (req_sym _ _ (mult_one (tv_i mu boltzmann_dist_i)))
                (mult_comm (tv_i mu boltzmann_dist_i) one))
             (le_refl _)).
  - assert (Hn : req (sumf (attention_iter_i n mu)) one)
      by exact (agq_iter_norm n mu Hmu).
    assert (Hge : le zero omd)
      by exact (req_le_minus_nonneg delta one
                  (lt_le_iff _ _ (inl delta_lt_one))).
    apply (le_trans _ (mult omd
             (tv_i (attention_iter_i n mu) boltzmann_dist_i)) _).
    + apply (le_id_l _ (tv_i (attention_step_i (attention_iter_i n mu))
                             boltzmann_dist_i) _).
      * exact (req_refl (tv_i (attention_step_i (attention_iter_i n mu))
                              boltzmann_dist_i)).
      * exact (agq_tv_contraction (attention_iter_i n mu) Hn).
    + apply (le_trans _ (mult omd
             (mult (req_r_pow omd n) (tv_i mu boltzmann_dist_i))) _).
      * exact (req_le_mult_compat_r omd
                  (tv_i (attention_iter_i n mu) boltzmann_dist_i)
                  (mult (req_r_pow omd n) (tv_i mu boltzmann_dist_i))
                  Hge (IH mu Hmu)).
      * apply (le_id_l _ (mult (mult omd (req_r_pow omd n))
                               (tv_i mu boltzmann_dist_i))).
        -- exact (mult_assoc omd (req_r_pow omd n)
                              (tv_i mu boltzmann_dist_i)).
        -- apply le_refl.
Qed.

(* ========== Main theorem 3: convergence of the iteration ==========
   The arch_pow_i premise is resolved directly, then agq_tv_iter,
   agq_tv_nonneg, agq_r_pow_dec_iter, le_mult_compat_weak and lt_id_l chain
   to the goal.  The req form drops the initial nonnegativity premise: the
   agq_tv_iter chain does not use it, as in main theorem 1. *)
Theorem agq_iterate_converges :
  forall mu0 : S -> R,
    req (sumf mu0) one ->
    forall eps : R, lt zero eps ->
      lt zero (tv_i mu0 boltzmann_dist_i) ->
      sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
        lt (tv_i (attention_iter_i n mu0) boltzmann_dist_i) eps).
Proof.
  intros mu0 Hmu eps Hep Htv0.
  destruct (arch_pow_i (tv_i mu0 boltzmann_dist_i) Htv0 eps Hep) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (req_r_pow omd n)
                             (tv_i mu0 boltzmann_dist_i)) _).
  - exact (agq_tv_iter n mu0 Hmu).
  - apply (le_lt_trans _ (mult (req_r_pow omd N)
                               (tv_i mu0 boltzmann_dist_i)) _).
    + apply (le_mult_compat_weak _ _ _).
      * exact (agq_tv_nonneg mu0 boltzmann_dist_i).
      * exact (agq_r_pow_dec_iter N n Hn).
    + exact (lt_id_l _ _ _
               (mult_comm (req_r_pow omd N) (tv_i mu0 boltzmann_dist_i))
               HN).
Qed.

End ReqAttnIter.
Print Assumptions agq_omd_lt_one.
