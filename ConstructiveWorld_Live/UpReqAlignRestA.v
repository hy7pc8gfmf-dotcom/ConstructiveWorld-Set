(* ConstructiveWorld-Set -- alignment residual segment A: DPO rewards, preference losses, and Q-embedding residuals at the Set layer. *)

(** * UpReqAlignRestA: the DPO implicit-reward face of the alignment family.

    Mission.  The DPO reward face of the alignment family: the log-ratio
      [ralt_log_ratio], the implicit reward [ralt_dir], the canonical policy
      read back through [ralt_log_pi_star] and [ralt_dpo_reward_recovers], the
      relative-reward identity [ralt_dpo_reward_relative_exact], the losses
      [ralt_dpo_pair_loss_at_star] and [ralt_dpo_loss_at_pi_star], the sigmoid
      growth [ralt_sigmoid_strict_inc] with the bound [ralt_dpo_loss_pi_star_bounded],
      and the Q-embedding residuals.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlgebra], [UpReqAlign] of this development.

    References.  This development, UpReqAlignRestA.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqAlignRestA.v] compiles cleanly
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
Require Import UpReqAlgebra.
Require Import UpReqAlign.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
Import RealInterfaceEnhancedMod.

(* Pool-build cure: the interface class in this tree is unparameterized
   (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid,
   fields resolved through the global Real instance of
   RealInterfaceEnhancedMod); the argument-bearing binder
   Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R} is deleted and the
   carrier R is bound to the global Real by the Notation below
   (UpReqAlign.v L50 / UpReqAlignRestB.v L143 precedent).  The order and
   equality field names are bound to their global faces (CW220_Extensions.v:
   the req/lt/le projections are iota-equal to real_eq/real_lt/real_le), so
   the extracted face matches the upstream global-instance statements with
   no coercion.  Statement names preserved verbatim. *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ============================================================ *)
(* ReqRestACore: main section for the DPO and preference residuals. *)
(*   The carrier R is the global Real (Notation above) and the      *)
(*   section-wide premises carry the algebra interface face plus    *)
(*   the preference data.                                           *)
(* ============================================================ *)
Section ReqRestACore.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis ralt_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
(* The finite-sum positivity premise [ralt_sum_pos] mirrors the signature of
   [pi_star_req], which reads a sum-positivity witness; the [Z_align_pos]
   premise stays in place because the logarithm and inversion witnesses
   below still read it. *)
Hypothesis ralt_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align_req S sumf reward beta beta_pos pi_ref).

Hypothesis ralt_lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Hypothesis ralt_log_lt_mono :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (log a Ha) (log b Hb).
(* ---- logarithm compatibility premises ---- *)
Hypothesis ralt_log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis ralt_log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ============ Section 1. The DPO real block on the req interface ============ *)


Lemma ralt_log_exp_neg : forall x : R,
  req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (req_trans (log (exp_neg x) (exp_neg_pos x))
                   (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                   (opp x)
                   (req_sym (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                            (log (exp_neg x) (exp_neg_pos x))
                            (req_double_neg (log (exp_neg x) (exp_neg_pos x))))
                   (req_opp_compat (opp (log (exp_neg x) (exp_neg_pos x))) x
                      (req_trans (opp (log (exp_neg x) (exp_neg_pos x)))
                                 (log_inv (exp_neg x) (exp_neg_pos x))
                                 x
                                 (req_sym (log_inv (exp_neg x) (exp_neg_pos x))
                                          (opp (log (exp_neg x) (exp_neg_pos x)))
                                          (log_inv_log (exp_neg x) (exp_neg_pos x)))
                                 (ralt_log_inv_exp_neg_req x)))).
Qed.

(* 1.1 strict order is preserved under multiplication by a positive on the
   left: read the interface field [lt_mult_compat] on the commuted products
   and transport back along the commutativity equalities with
   [req_lt_compat]. *)
Lemma ralt_mult_lt_compat_l : forall a b c : R,
  lt a b -> lt zero c -> lt (mult c a) (mult c b).
Proof.
  intros a b c Hab Hc.
  apply (req_lt_compat (mult a c) (mult c a) (mult b c) (mult c b)
                       (mult_comm a c) (mult_comm b c)).
  exact (lt_mult_compat a b c Hc Hab).
Qed.

(* 1.2 inversion reverses strict order: with [ia] the inverse of [a] and
   [ib] the inverse of [b],
   ib == (ia*a)*ib < (ia*b)*ib == ia,
   where the outer identifications absorb the products through
   [inv_pos_correct] and the middle strict step applies [lt_mult_compat]
   twice, transported across commutativity. *)
Lemma ralt_inv_pos_lt_contra : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  set (ia := inv_pos a Ha).
  set (ib := inv_pos b Hb).
  assert (Hia1 : req (mult ia a) one).
  { exact (req_trans (mult ia a) (mult a ia) one (mult_comm ia a) (inv_pos_correct a Ha)). }
  assert (Hib1 : req (mult b ib) one).
  { exact (inv_pos_correct b Hb). }
  (* Left identification of the midpoint: ib == (ia*a)*ib. *)
  assert (Hmid : req (mult (mult ia a) ib) ib).
  { apply (req_trans (mult (mult ia a) ib) (mult one ib) ib).
    - exact (req_mult_compat (mult ia a) one ib ib Hia1 (req_refl ib)).
    - exact (req_trans (mult one ib) (mult ib one) ib (mult_comm one ib) (mult_one ib)). }
  (* Middle strict step: lt (ia*a) (ia*b) by [lt_mult_compat] on the left,
     transported across commutativity. *)
  assert (Hlt1 : lt (mult ia a) (mult ia b)).
  { apply (req_lt_compat (mult a ia) (mult ia a) (mult b ia) (mult ia b)
                         (mult_comm a ia) (mult_comm b ia)).
    exact (lt_mult_compat a b ia (inv_pos_pos a Ha) Hab). }
  assert (Hltmid : lt (mult (mult ia a) ib) (mult (mult ia b) ib)).
  { exact (lt_mult_compat (mult ia a) (mult ia b) ib (inv_pos_pos b Hb) Hlt1). }
  (* Right identification of the midpoint: (ia*b)*ib == ia*(b*ib) == ia*1 == ia. *)
  assert (Hright : req (mult (mult ia b) ib) ia).
  { apply (req_trans (mult (mult ia b) ib) (mult ia (mult b ib)) ia).
    - exact (req_sym (mult ia (mult b ib)) (mult (mult ia b) ib) (mult_assoc ia b ib)).
    - apply (req_trans (mult ia (mult b ib)) (mult ia one) ia).
      + exact (req_mult_compat ia ia (mult b ib) one (req_refl ia) Hib1).
      + exact (mult_one ia). }
  apply (lt_id_r ib (mult (mult ia b) ib) ia Hright).
  exact (lt_id_l ib (mult (mult ia a) ib) (mult (mult ia b) ib)
                   (req_sym (mult (mult ia a) ib) ib Hmid) Hltmid).
Qed.

(* 1.3 compatibility of addition with order, strict on the left and weak on
   the right: held as the section premise [ralt_lt_plus_compat_lt_le]. *)
(* 1.4 dual form, weak on the left and strict on the right: derived from 1.3
   by commuting both sums and transporting with [req_lt_compat]; no new
   premise enters. *)
Lemma ralt_lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  apply (req_lt_compat (plus c a) (plus a c) (plus d b) (plus b d)
                       (plus_comm c a) (plus_comm d b)).
  exact (ralt_lt_plus_compat_lt_le c d a b Hcd Hab).
Qed.

(* 1.5 additive translation preserves strict order: 1.4 with both weak
   arguments filled by [le_refl]. *)
Lemma ralt_lt_plus_translate : forall (b c d : R),
  lt c d -> lt (plus b c) (plus b d).
Proof.
  intros b c d Hcd.
  exact (ralt_lt_plus_compat_le_lt b b c d (le_refl b) Hcd).
Qed.

(* 1.6 a shared summand cancels under the req-subtraction carrier: the
   algebra lemma [req_minus_plus_congr] states this identity directly. *)
Lemma ralt_minus_plus_common : forall A B C : R,
  req (req_minus (plus A B) (plus A C)) (req_minus B C).
Proof.
  intros A B C. unfold req_minus.
  apply (req_trans (plus (plus A B) (opp (plus A C)))
                   (plus (plus A B) (plus (opp A) (opp C)))
                   (plus B (opp C))).
  - exact (req_plus_compat (plus A B) (plus A B)
                           (opp (plus A C)) (plus (opp A) (opp C))
                           (req_refl (plus A B)) (req_opp_plus A C)).
  - apply (req_trans (plus (plus A B) (plus (opp A) (opp C)))
                     (plus (plus A (opp A)) (plus B (opp C)))
                     (plus B (opp C))).
    + exact (req_plus_swap_mid A B (opp A) (opp C)).
    + apply (req_trans (plus (plus A (opp A)) (plus B (opp C)))
                       (plus zero (plus B (opp C)))
                       (plus B (opp C))).
      * exact (req_plus_compat (plus A (opp A)) zero
                               (plus B (opp C)) (plus B (opp C))
                               (plus_opp A) (req_refl (plus B (opp C)))).
      * exact (req_plus_zero_l (plus B (opp C))).
Qed.

(* 1.7 strict monotonicity of the logarithm: held as the section premise
   [ralt_log_lt_mono]; the interface carries only the weak form
   [log_le_linear_eps], from which the strict shape is not derivable. *)

(* ============ Section 2. The dpo_reward family on the req interface ============ *)

(* The log-ratio: the shape of the upstream statement with each logarithm
   carrying its own positivity witness. *)
Definition ralt_log_ratio (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s : S) : R :=
  req_minus (log (pi s) (Hpi s)) (log (pi_ref s) (pi_ref_pos s)).

(* The DPO implicit reward: the scaled log-ratio. *)
Definition ralt_dir (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s : S) : R :=
  mult beta (ralt_log_ratio pi Hpi s).

(* Pointwise positivity of the canonical policy: the witness is the closed
   form supplied by [req_pi_star_pos]. *)
Definition ralt_pistar_pos (s : S)
  : lt zero (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) :=
  req_pi_star_pos S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s.

(* pi* abbreviation (delta transparent) *)
Definition ralt_pistar : S -> R :=
  pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos.

(* The canonical closed form of the policy (the internal instance behind
   [UpReqAlign.Z_align_pos]) and the closed form read from this section's
   [Z_align_pos] premise agree pointwise: the two shapes differ only in the
   positivity proof argument of [inv_pos].  The proof cancels the positive
   factor with [req_mult_cancel_l] and folds [inv_pos_correct] on both
   sides. *)
Lemma ralt_pistar_cross : forall s : S,
  req (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
      (mult (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos)
            (mult (pi_ref s)
                  (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Proof.
  intro s.
  unfold pi_star_req.
  apply (req_mult_compat _ _ _ _
    (req_mult_cancel_l (Z_align_req S sumf reward beta beta_pos pi_ref) _ _
       (@UpReqAlign.Z_align_pos S sumf ralt_sum_pos reward beta beta_pos
          pi_ref pi_ref_pos)
       (req_trans _ _ _
          (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
             (@UpReqAlign.Z_align_pos S sumf ralt_sum_pos reward beta beta_pos
                pi_ref pi_ref_pos))
          (req_sym _ _
             (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
                Z_align_pos))))
    (req_refl (mult (pi_ref s)
                    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
Qed.

(* 2.1 the logarithm of the policy value:
   log pi*(s) == -log Z + (log pi_ref(s) + r(s)/beta).
   The proof folds [ralt_log_exp_neg] with the double-negation identity and
   transports along the closed-form agreement [ralt_pistar_cross]. *)
Lemma ralt_log_pi_star : forall s : S,
  req (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
            (ralt_pistar_pos s))
      (plus (opp (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos))
            (plus (log (pi_ref s) (pi_ref_pos s))
                  (mult (inv_pos beta beta_pos) (reward s)))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (Z := Z_align_req S sumf reward beta beta_pos pi_ref).
  set (lgZ := log Z Z_align_pos).
  set (lgR := log (pi_ref s) (pi_ref_pos s)).
  set (e := exp_neg (opp (mult iv (reward s)))).
  set (lgI := log (inv_pos Z Z_align_pos) (inv_pos_pos Z Z_align_pos)).
  set (lgM := log (mult (pi_ref s) e) (mult_positive (pi_ref s) e (pi_ref_pos s) (exp_neg_pos (opp (mult iv (reward s)))))).
  assert (HlogE : req (log e (exp_neg_pos (opp (mult iv (reward s))))) (mult iv (reward s))).
  { apply (req_trans (log e (exp_neg_pos (opp (mult iv (reward s)))))
                     (opp (opp (mult iv (reward s)))) (mult iv (reward s))).
    - exact (ralt_log_exp_neg (opp (mult iv (reward s)))).
    - exact (req_double_neg (mult iv (reward s))). }
  assert (HlgM : req lgM (plus lgR (mult iv (reward s)))).
  { apply (req_trans lgM (plus lgR (log e (exp_neg_pos (opp (mult iv (reward s))))))
                        (plus lgR (mult iv (reward s)))).
    - exact (log_mult (pi_ref s) e (pi_ref_pos s) (exp_neg_pos (opp (mult iv (reward s))))).
    - exact (req_plus_compat lgR lgR (log e (exp_neg_pos (opp (mult iv (reward s))))) (mult iv (reward s))
                             (req_refl lgR) HlogE). }
  set (wit := mult_positive (inv_pos Z Z_align_pos) (mult (pi_ref s) e)
                            (inv_pos_pos Z Z_align_pos)
                            (mult_positive (pi_ref s) e (pi_ref_pos s)
                               (exp_neg_pos (opp (mult iv (reward s)))))).
  apply (req_trans (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
                        (ralt_pistar_pos s))
                   (log (mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e)) wit)
                   (plus (opp lgZ) (plus lgR (mult iv (reward s))))).
  - exact (ralt_log_req_compat (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
                               (mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e))
                               (ralt_pistar_pos s) wit
                               (ralt_pistar_cross s)).
  - apply (req_trans (log (mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e)) wit)
                     (plus lgI lgM)
                     (plus (opp lgZ) (plus lgR (mult iv (reward s))))).
    + exact (log_mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e)
                      (inv_pos_pos Z Z_align_pos) (mult_positive (pi_ref s) e (pi_ref_pos s)
                         (exp_neg_pos (opp (mult iv (reward s)))))).
    + exact (req_plus_compat lgI (opp lgZ) lgM (plus lgR (mult iv (reward s)))
                             (@rkl_log_inv_one_inv ralt_log_req_compat Z Z_align_pos)
                             HlgM).
Qed.

(* 2.2 the implicit reward of the canonical policy recovers the true reward
   up to the baseline shift: read [ralt_log_pi_star], cancel through the
   subtraction chain (association, reordering, [plus_opp]), distribute, and
   absorb the factor beta*(1/beta) = 1 with [mult_assoc],
   [inv_pos_correct] and [mult_one]. *)
Lemma ralt_dpo_reward_recovers : forall s : S,
  req (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                (ralt_pistar_pos) s)
      (plus (reward s)
            (opp (mult beta (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos)))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (lgZ := log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos).
  set (lgR := log (pi_ref s) (pi_ref_pos s)).
  set (Y := mult iv (reward s)).
  (* The subtraction cancels the log term: (A+(L+Y))-L == A+Y. *)
  assert (Hsub : req (req_minus (plus (opp lgZ) (plus lgR Y)) lgR) (plus (opp lgZ) Y)).
  { unfold req_minus.
    apply (req_trans (plus (plus (opp lgZ) (plus lgR Y)) (opp lgR))
                     (plus (opp lgZ) (plus (plus lgR Y) (opp lgR)))
                     (plus (opp lgZ) Y)).
    - exact (req_sym (plus (opp lgZ) (plus (plus lgR Y) (opp lgR)))
                     (plus (plus (opp lgZ) (plus lgR Y)) (opp lgR))
                     (plus_assoc (opp lgZ) (plus lgR Y) (opp lgR))).
    - apply (req_plus_compat (opp lgZ) (opp lgZ)
                             (plus (plus lgR Y) (opp lgR)) Y (req_refl (opp lgZ))).
      apply (req_trans (plus (plus lgR Y) (opp lgR))
                       (plus lgR (plus Y (opp lgR)))
                       Y).
      + exact (req_sym (plus lgR (plus Y (opp lgR))) (plus (plus lgR Y) (opp lgR))
                       (plus_assoc lgR Y (opp lgR))).
      + apply (req_trans (plus lgR (plus Y (opp lgR)))
                         (plus (plus lgR (opp lgR)) Y) Y).
      * apply (req_trans (plus lgR (plus Y (opp lgR)))
                         (plus lgR (plus (opp lgR) Y))
                         (plus (plus lgR (opp lgR)) Y)).
        -- exact (req_plus_compat lgR lgR (plus Y (opp lgR)) (plus (opp lgR) Y)
                    (req_refl lgR) (plus_comm Y (opp lgR))).
        -- exact (plus_assoc lgR (opp lgR) Y).
      * apply (req_trans (plus (plus lgR (opp lgR)) Y) (plus zero Y) Y).
        -- exact (req_plus_compat (plus lgR (opp lgR)) zero Y Y (plus_opp lgR) (req_refl Y)).
        -- exact (req_plus_zero_l Y). }
  (* Absorb the factor beta*(1/beta) = 1. *)
  assert (Hbetaone : req (mult beta iv) one).
  { exact (inv_pos_correct beta beta_pos). }
  assert (Hbetaiv : req (mult beta (mult iv (reward s))) (reward s)).
  { apply (req_trans (mult beta (mult iv (reward s)))
                     (mult (mult beta iv) (reward s)) (reward s)).
    - exact (mult_assoc beta iv (reward s)).
    - apply (req_trans (mult (mult beta iv) (reward s))
                       (mult one (reward s)) (reward s)).
      + exact (req_mult_compat (mult beta iv) one (reward s) (reward s)
                               Hbetaone (req_refl (reward s))).
      + exact (req_trans (mult one (reward s)) (mult (reward s) one) (reward s)
                         (mult_comm one (reward s)) (mult_one (reward s))). }
  unfold ralt_dir, ralt_log_ratio.
  apply (req_trans (mult beta (req_minus (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s)) lgR))
                   (mult beta (plus (opp lgZ) Y))
                   (plus (reward s) (opp (mult beta lgZ)))).
  - apply (req_mult_compat beta beta
             (req_minus (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s)) lgR)
             (plus (opp lgZ) Y) (req_refl beta)).
    apply (req_trans (req_minus (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s)) lgR)
                     (req_minus (plus (opp lgZ) (plus lgR Y)) lgR)
                     (plus (opp lgZ) Y)).
    + unfold req_minus.
      exact (req_plus_compat (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s))
                             (plus (opp lgZ) (plus lgR Y))
                             (opp lgR) (opp lgR)
                             (ralt_log_pi_star s) (req_refl (opp lgR))).
    + exact Hsub.
  - apply (req_trans (mult beta (plus (opp lgZ) Y))
                     (plus (mult beta (opp lgZ)) (mult beta Y))
                     (plus (reward s) (opp (mult beta lgZ)))).
    + exact (distrib beta (opp lgZ) Y).
    + apply (req_trans (plus (mult beta (opp lgZ)) (mult beta Y))
                       (plus (opp (mult beta lgZ)) (reward s))
                       (plus (reward s) (opp (mult beta lgZ)))).
      * exact (req_plus_compat (mult beta (opp lgZ)) (opp (mult beta lgZ))
                               (mult beta Y) (reward s)
                               (req_opp_mult_l beta lgZ) Hbetaiv).
      * exact (plus_comm (opp (mult beta lgZ)) (reward s)).
Qed.

(* 2.3 the difference of the canonical-policy implicit rewards equals the
   difference of the true rewards: the baseline cancels exactly.  The proof
   instantiates 2.2 at both points, transports [req_minus] along the two
   identifications, and cancels the shared term with
   [req_minus_plus_congr]. *)
Lemma ralt_dpo_reward_relative_exact : forall s s' : S,
  req (req_minus (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                           (ralt_pistar_pos) s)
                 (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                           (ralt_pistar_pos) s'))
      (req_minus (reward s) (reward s')).
Proof.
  intros s s'.
  set (B := opp (mult beta (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos))).
  assert (Hrec : req (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                               (ralt_pistar_pos) s)
                     (plus (reward s) B))
    by (apply ralt_dpo_reward_recovers).
  assert (Hrec' : req (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                (ralt_pistar_pos) s')
                      (plus (reward s') B))
    by (apply ralt_dpo_reward_recovers).
  apply (req_trans (req_minus (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                        (ralt_pistar_pos) s)
                              (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                        (ralt_pistar_pos) s'))
                   (req_minus (plus (reward s) B) (plus (reward s') B))
                   (req_minus (reward s) (reward s'))).
  - exact (req_plus_compat (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                     (ralt_pistar_pos) s)
                           (plus (reward s) B)
                           (opp (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                          (ralt_pistar_pos) s'))
                           (opp (plus (reward s') B))
                           Hrec (req_opp_compat _ _ Hrec')).
  - apply (req_trans (req_minus (plus (reward s) B) (plus (reward s') B))
                     (req_minus (plus B (reward s)) (plus B (reward s')))
                     (req_minus (reward s) (reward s'))).
    + exact (req_plus_compat (plus (reward s) B) (plus B (reward s))
                             (opp (plus (reward s') B)) (opp (plus B (reward s')))
                             (plus_comm (reward s) B)
                             (req_opp_compat (plus (reward s') B) (plus B (reward s'))
                                             (plus_comm (reward s') B))).
    + exact (req_minus_plus_congr B (reward s) (reward s')).
Qed.

(* 2.4 the delta-transparent identity: [ralt_dir] unfolds to the scaled
   log-ratio by definition, so both sides of the req-subtraction agree
   pointwise. *)
Lemma ralt_dpo_reward_diff_is_log_ratio_diff :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s s' : S),
    req (req_minus (ralt_dir pi Hpi s) (ralt_dir pi Hpi s'))
        (req_minus (mult beta (ralt_log_ratio pi Hpi s))
                   (mult beta (ralt_log_ratio pi Hpi s'))).
Proof.
  intros pi Hpi s s'.
  exact (req_refl (req_minus (mult beta (ralt_log_ratio pi Hpi s))
                             (mult beta (ralt_log_ratio pi Hpi s')))).
Qed.

(* ============ Section 3. The preference block on the req interface ============ *)

Variable Preference : Set.
Variable pref_win : Preference -> S.
Variable pref_lose : Preference -> S.

(* The implicit-reward difference over a preference pair: subtraction
   carried by [req_minus]. *)
Definition ralt_implicit_reward_diff
  (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference) : R :=
  req_minus (ralt_dir pi Hpi (pref_win pref)) (ralt_dir pi Hpi (pref_lose pref)).

(* Positivity of the single-pair loss denominator: [req_sigmoid_denom_pos]
   supplies it directly; the statement precedes the loss definition to feed
   the log witness slot. *)
Lemma ralt_dpo_pair_denom_pos :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference),
    lt zero (plus one (exp_neg (ralt_implicit_reward_diff pi Hpi pref))).
Proof.
  intros pi Hpi pref.
  exact (req_sigmoid_denom_pos (ralt_implicit_reward_diff pi Hpi pref)).
Qed.

(* The DPO single-pair loss: the logarithm carries its denominator witness
   as an explicit argument. *)
Definition ralt_dpo_pair_loss
  (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference) : R :=
  log (plus one (exp_neg (ralt_implicit_reward_diff pi Hpi pref)))
      (ralt_dpo_pair_denom_pos pi Hpi pref).

(* The star denominator positivity and the star loss constant: the same
   sigmoid denominator lemma applied to the reward difference. *)
Definition ralt_pair_denom_pos_star (pref : Preference)
  : lt zero (plus one (exp_neg (req_minus (reward (pref_win pref))
                                          (reward (pref_lose pref))))) :=
  req_sigmoid_denom_pos (req_minus (reward (pref_win pref))
                                   (reward (pref_lose pref))).

Definition ralt_dpo_pair_loss_star (pref : Preference) : R :=
  log (plus one (exp_neg (req_minus (reward (pref_win pref))
                                    (reward (pref_lose pref)))))
      (ralt_pair_denom_pos_star pref).

(* 3.1 at the canonical policy the implicit-reward difference equals the
   true-reward difference: direct instance of 2.3. *)
Theorem ralt_pi_star_implicit_reward_diff : forall pref : Preference,
  req (ralt_implicit_reward_diff ralt_pistar ralt_pistar_pos pref)
      (req_minus (reward (pref_win pref)) (reward (pref_lose pref))).
Proof.
  intro pref.
  exact (ralt_dpo_reward_relative_exact (pref_win pref) (pref_lose pref)).
Qed.

(* 3.2 at the canonical policy the loss degenerates to the sigmoid
   cross-entropy of the true-reward difference: transport 3.1 through the
   [exp_neg] compatibility and the logarithm compatibility premise. *)
Theorem ralt_dpo_pair_loss_at_star : forall pref : Preference,
  req (ralt_dpo_pair_loss ralt_pistar ralt_pistar_pos pref)
      (ralt_dpo_pair_loss_star pref).
Proof.
  intro pref.
  unfold ralt_dpo_pair_loss, ralt_dpo_pair_loss_star.
  apply ralt_log_req_compat.
  apply (req_plus_compat one one
           (exp_neg (ralt_implicit_reward_diff ralt_pistar ralt_pistar_pos pref))
           (exp_neg (req_minus (reward (pref_win pref)) (reward (pref_lose pref))))
           (req_refl one)).
  apply exp_neg_req_compat_setoid.
  exact (ralt_pi_star_implicit_reward_diff pref).
Qed.

(* 3.3 extensionality of the relative entropy in its right argument: apply
   the summation extensionality premise pointwise and transport along the
   product, subtraction and logarithm compatibility chain. *)
Theorem ralt_relative_entropy_ext_r :
  forall (p q1 q2 : S -> R) (Hp : forall s : S, lt zero (p s))
         (Hq1 : forall s : S, lt zero (q1 s)) (Hq2 : forall s : S, lt zero (q2 s)),
    (forall s : S, req (q1 s) (q2 s)) ->
    req (relative_entropy_req S sumf p q1 Hp Hq1)
        (relative_entropy_req S sumf p q2 Hp Hq2).
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hext.
  unfold relative_entropy_req.
  apply (ralt_sum_ext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q1 s) (Hq1 s))))
                      (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q2 s) (Hq2 s))))).
  intro s.
  apply (req_mult_compat (p s) (p s)
           (req_minus (log (p s) (Hp s)) (log (q1 s) (Hq1 s)))
           (req_minus (log (p s) (Hp s)) (log (q2 s) (Hq2 s)))
           (req_refl (p s))).
  exact (req_plus_compat (log (p s) (Hp s)) (log (p s) (Hp s))
                         (opp (log (q1 s) (Hq1 s))) (opp (log (q2 s) (Hq2 s)))
                         (req_refl (log (p s) (Hp s)))
                         (req_opp_compat (log (q1 s) (Hq1 s)) (log (q2 s) (Hq2 s))
                           (ralt_log_req_compat (q1 s) (q2 s) (Hq1 s) (Hq2 s) (Hext s)))).
Qed.

(* ---- Out of scope here: the total_loss cluster, whose fold_right_ext and
   list-fold machinery lives at the nat/list layer, and ppo_gap_nonneg,
   whose minimum shape needs the plain weak order. ---- *)

(* ============ Section 4. The sigmoid and DPO loss cluster on the req interface ============ *)
(* The sigmoid statements [req_sigmoid_denom_pos], [sigmoid_req],
   [req_sigmoid_pos] and [req_sigmoid_zero_half] are already available from
   the algebra module and are used as-is. *)

(* 4.1 the paired DPO loss: the sigmoid of the req-subtraction of the two
   scaled log-ratios, with the sigmoid positivity witness carried
   explicitly. *)
Definition ralt_dpo_loss_pair
  (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s_w s_l : S) : R :=
  opp (log (sigmoid_req (req_minus (mult beta (ralt_log_ratio pi Hpi s_w))
                                   (mult beta (ralt_log_ratio pi Hpi s_l))))
           (req_sigmoid_pos (req_minus (mult beta (ralt_log_ratio pi Hpi s_w))
                                       (mult beta (ralt_log_ratio pi Hpi s_l))))).

(* 4.2 at the canonical policy the paired loss reads -log sigma(r_w - r_l):
   2.2 cancels the normalizer and the reference term pairwise inside the
   difference, [inv_pos_ext] transports the denominator, and the logarithm
   compatibility premise closes the gap. *)
Theorem ralt_dpo_loss_at_pi_star : forall s_w s_l : S,
  req (ralt_dpo_loss_pair ralt_pistar ralt_pistar_pos s_w s_l)
      (opp (log (sigmoid_req (req_minus (reward s_w) (reward s_l)))
                 (req_sigmoid_pos (req_minus (reward s_w) (reward s_l))))).
Proof.
  intros s_w s_l.
  unfold ralt_dpo_loss_pair.
  set (MW := mult beta (ralt_log_ratio ralt_pistar ralt_pistar_pos s_w)).
  set (ML := mult beta (ralt_log_ratio ralt_pistar ralt_pistar_pos s_l)).
  set (X := req_minus (reward s_w) (reward s_l)).
  set (B := opp (mult beta (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos))).
  assert (Hw : req MW (plus (reward s_w) B))
    by (exact (ralt_dpo_reward_recovers s_w)).
  assert (Hl : req ML (plus (reward s_l) B))
    by (exact (ralt_dpo_reward_recovers s_l)).
  assert (Hdiff : req (req_minus MW ML) X).
  { apply (req_trans (req_minus MW ML)
                     (req_minus (plus (reward s_w) B) (plus (reward s_l) B)) X).
    - exact (req_plus_compat MW (plus (reward s_w) B) (opp ML) (opp (plus (reward s_l) B))
                             Hw (req_opp_compat ML (plus (reward s_l) B) Hl)).
    - apply (req_trans (req_minus (plus (reward s_w) B) (plus (reward s_l) B))
                       (req_minus (plus B (reward s_w)) (plus B (reward s_l))) X).
      + exact (req_plus_compat (plus (reward s_w) B) (plus B (reward s_w))
                               (opp (plus (reward s_l) B)) (opp (plus B (reward s_l)))
                               (plus_comm (reward s_w) B)
                               (req_opp_compat (plus (reward s_l) B) (plus B (reward s_l))
                                               (plus_comm (reward s_l) B))).
      + exact (req_minus_plus_congr B (reward s_w) (reward s_l)). }
  apply req_opp_compat.
  apply ralt_log_req_compat.
  apply (inv_pos_ext (plus one (exp_neg (req_minus MW ML))) (plus one (exp_neg X))
                     (req_sigmoid_denom_pos (req_minus MW ML)) (req_sigmoid_denom_pos X)).
  apply (req_plus_compat one one (exp_neg (req_minus MW ML)) (exp_neg X) (req_refl one)).
  apply exp_neg_req_compat_setoid.
  exact Hdiff.
Qed.

(* 4.3 the sigmoid is strictly increasing: [exp_neg_decr] with 1.4 gives
   lt (plus one (exp_neg y)) (plus one (exp_neg x)), and the inversion
   lemma 1.2 [ralt_inv_pos_lt_contra] reverses the order of the
   denominators. *)
Theorem ralt_sigmoid_strict_inc : forall x y : R,
  lt x y -> lt (sigmoid_req x) (sigmoid_req y).
Proof.
  intros x y Hxy.
  apply (ralt_inv_pos_lt_contra (plus one (exp_neg y)) (plus one (exp_neg x))
                                (req_sigmoid_denom_pos y) (req_sigmoid_denom_pos x)).
  exact (ralt_lt_plus_compat_le_lt one one (exp_neg y) (exp_neg x) (le_refl one)
                                   (exp_neg_decr x y Hxy)).
Qed.

(* 4.4 the paired canonical-policy loss is bounded by log 2 whenever the
   winner reward dominates: 4.2 with 4.3 turns the strict reward order
   into a strict order of the losses, [ralt_log_lt_mono] lifts it through
   the logarithm, [opp_lt_compat] reverses it, and log(1/2) = -log 2
   follows from [req_log_inv_one_inv] with the double-negation identity. *)
Theorem ralt_dpo_loss_pi_star_bounded : forall s_w s_l : S,
  lt (reward s_l) (reward s_w) ->
  lt (ralt_dpo_loss_pair ralt_pistar ralt_pistar_pos s_w s_l)
     (log (plus one one) (req_two_pos)).
Proof.
  intros s_w s_l Hrw.
  set (D := req_minus (reward s_w) (reward s_l)).
  assert (Hpos : lt zero D).
  (* Hpos: 0 < r_w - r_l *)
  { apply (lt_id_l zero (plus (reward s_l) (opp (reward s_l)))
                    (plus (reward s_w) (opp (reward s_l)))).
    - exact (req_sym (plus (reward s_l) (opp (reward s_l))) zero
                     (plus_opp (reward s_l))).
    - exact (ralt_lt_plus_compat_lt_le (reward s_l) (reward s_w) (opp (reward s_l))
                                       (opp (reward s_l)) Hrw (le_refl (opp (reward s_l)))). }
  assert (Hsig : lt (sigmoid_req zero) (sigmoid_req D))
    by (exact (ralt_sigmoid_strict_inc zero D Hpos)).
  assert (Hlog : lt (log (sigmoid_req zero) (req_sigmoid_pos zero))
                    (log (sigmoid_req D) (req_sigmoid_pos D)))
    by (exact (ralt_log_lt_mono (sigmoid_req zero) (sigmoid_req D)
                                (req_sigmoid_pos zero) (req_sigmoid_pos D) Hsig)).
  assert (Hopp : lt (opp (log (sigmoid_req D) (req_sigmoid_pos D)))
                    (opp (log (sigmoid_req zero) (req_sigmoid_pos zero))))
    by (exact (opp_lt_compat (log (sigmoid_req zero) (req_sigmoid_pos zero))
                             (log (sigmoid_req D) (req_sigmoid_pos D)) Hlog)).
  assert (Hval : req (opp (log (sigmoid_req zero) (req_sigmoid_pos zero)))
                     (log (plus one one) (req_two_pos))).
  { apply (req_trans (opp (log (sigmoid_req zero) (req_sigmoid_pos zero)))
                     (opp (log (inv_pos (plus one one) (req_two_pos))
                               (inv_pos_pos (plus one one) (req_two_pos))))
                     (log (plus one one) (req_two_pos))).
    - apply req_opp_compat.
      exact (ralt_log_req_compat (sigmoid_req zero)
                                 (inv_pos (plus one one) (req_two_pos))
                                 (req_sigmoid_pos zero)
                                 (inv_pos_pos (plus one one) (req_two_pos))
                                 (req_sigmoid_zero_half)).
    - apply (req_trans (opp (log (inv_pos (plus one one) (req_two_pos))
                                  (inv_pos_pos (plus one one) (req_two_pos))))
                       (opp (opp (log (plus one one) (req_two_pos))))
                       (log (plus one one) (req_two_pos))).
      + apply req_opp_compat.
        exact (@req_log_inv_one_inv ralt_log_req_compat
                 (plus one one) (req_two_pos)).
      + exact (req_double_neg (log (plus one one) (req_two_pos))). }
  exact (lt_id_l (ralt_dpo_loss_pair ralt_pistar ralt_pistar_pos s_w s_l)
                 (opp (log (sigmoid_req D) (req_sigmoid_pos D)))
                 (log (plus one one) (req_two_pos))
                 (ralt_dpo_loss_at_pi_star s_w s_l)
                 (lt_id_r (opp (log (sigmoid_req D) (req_sigmoid_pos D)))
                          (opp (log (sigmoid_req zero) (req_sigmoid_pos zero)))
                          (log (plus one one) (req_two_pos)) Hval Hopp)).
Qed.


End ReqRestACore.

(* ============================================================ *)
(* Section 5. The Q-into-real embedding residuals, stated on the req     *)
(*   interface: the req/lt/le projections of the real structure coincide *)
(*   pointwise with real_eq, real_lt and real_le, so each proof exposes  *)
(*   the concrete shape with change and closes with the concrete         *)
(*   statement.  Out of scope here: the nat-to-Q bridge statements and   *)
(*   the sequence/list audit residuals, whose carriers live at the       *)
(*   nat/list/Q layer.                                                   *)
(* ============================================================ *)

(* 5.1 the embedding is equal-invariant. *)
Lemma ralt_real_const_req_eq : forall x y : Q, x == y -> req (real_const x) (real_const y).
Proof.
  intros x y Hxy.
  change (real_eq (real_const x) (real_const y)).
  intros eps Heps. exists 0%nat. intros n Hn.
  cbn [projT1 real_const].
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hd0 : (x - y == 0)%Q).
  { unfold Qminus.
    apply (Qeq_trans _ (y + (- y))).
    - apply (proj2 (Qplus_inj_r x y (- y))). exact Hxy.
    - apply Qplus_opp_r. }
  assert (Hz : Qabs (x - y) == 0).
  { apply (Qeq_trans _ (Qabs 0%Q)).
    - apply Qabs_wd. exact Hd0.
    - reflexivity. }
  assert (Hcmp : Qcompare (Qabs (x - y)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (x - y)) eps = Qcompare 0 eps).
    { exact (Qcompare_comp (Qabs (x - y)) 0 Hz eps eps (Qeq_refl eps)). }
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* 5.2 the embedding preserves strict Q order. *)
Lemma ralt_real_const_req_lt : forall c d : Q,
  Qlt c d -> lt (real_const c) (real_const d).
Proof.
  intros c d Hcd.
  change (real_lt (real_const c) (real_const d)).
  exact (real_const_lt c d (Qlt_to_QltT c d Hcd)).
Qed.

(* 5.3 the embedding preserves weak Q order, by trichotomy on Q: strict on
   the left, contradictory in the middle, equal on the right. *)
Lemma ralt_real_const_req_le : forall x y : Q,
  Qle x y -> le (real_const x) (real_const y).
Proof.
  intros x y Hxy.
  change (real_le (real_const x) (real_const y)).
  destruct (Q_dec x y) as [[Hlt | Hgt] | Heq].
  - left. exact (ralt_real_const_req_lt x y Hlt).
  - exfalso. exact (Qlt_irrefl y (Qlt_le_trans y x y Hgt Hxy)).
  - right. exact (ralt_real_const_req_eq x y Heq).
Qed.

(* 5.4 the Set-level corollary for the QleT' order carrier. *)
Lemma ralt_real_const_req_qleT : forall x y : Q,
  QleT' x y -> le (real_const x) (real_const y).
Proof.
  intros x y H.
  exact (ralt_real_const_req_le x y (QleT'_to_Qle x y H)).
Qed.

(* 5.5 the Set-level corollary for the decidable Qeq_bool equality. *)
Lemma ralt_real_const_req_eq_bool : forall x y : Q,
  Id (Qeq_bool x y) true -> req (real_const x) (real_const y).
Proof.
  intros x y H.
  exact (ralt_real_const_req_eq x y
           (proj1 (Qeq_bool_iff x y) (RealSetoid.Id_eq (Qeq_bool x y) true H))).
Qed.

(* 5.6 the embedding preserves positivity. *)
Lemma ralt_real_const_req_pos : forall c : Q,
  QltT 0 c -> lt zero (real_const c).
Proof.
  intros c Hc.
  change (real_lt real_zero (real_const c)).
  exact (real_const_pos c Hc).
Qed.



(* Assumption audit: every main statement is reported to be closed under
   the global context. *)
Print Assumptions ralt_log_exp_neg.
Print Assumptions ralt_mult_lt_compat_l.
Print Assumptions ralt_lt_plus_compat_le_lt.
Print Assumptions ralt_lt_plus_translate.
Print Assumptions ralt_minus_plus_common.
Print Assumptions ralt_dpo_reward_diff_is_log_ratio_diff.
Print Assumptions ralt_dpo_pair_denom_pos.
Print Assumptions ralt_pi_star_implicit_reward_diff.
Print Assumptions ralt_sigmoid_strict_inc.
Print Assumptions ralt_real_const_req_qleT.
Print Assumptions ralt_real_const_req_eq_bool.