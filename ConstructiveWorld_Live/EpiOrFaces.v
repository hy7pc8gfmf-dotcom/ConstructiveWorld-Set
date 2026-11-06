(* ConstructiveWorld-Set — statement-face spectrum for the classical disjunction that e*pi or e+pi is irrational. *)

(** * EpiOrFaces: Set-carried statement faces for the irrationality of e*pi and e+pi.

    Mission.  The Set-carried statement-face spectrum of the classical
      statement that at least one of e*pi and e+pi is irrational:
      strong irrationality [epiIrr], algebraic root certificates [AlgWit],
      the disjunctive form [epi_or_face], the conditional form
      [epi_cond_face], their mutual exclusion with rationality
      [epi_irr_not_ratface], weakening and branch-data faces
      [epi_or_not_both_rat], [epi_or_face_down_dm], [epi_or_branch_data],
      and the named-premise closure [epi_trans_weak_quad_exit].

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [List],
      [Extraction], [QArith.Qabs].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [SumInvFactEscape],
      [S10_KVQuantTrig], [UpReqIrrationalCriterion] of this development.

    References.  This development, EpiOrFaces.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" EpiOrFaces.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import QArith.QArith ZArith.ZArith List.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import S10_KVQuantTrig.
Require Import UpReqIrrationalCriterion.

(* Section 1. The real-number records of e, pi, e*pi and e+pi (direct
   references to definitions already in the library) *)

Definition eR : Real :=
  existT (fun u : Qseq => cauchy u) (fun n => exp_series n 1)
    (lic_seq_cauchy (fun n => exp_series n 1) (fun n => 1%Q / q_fact n)
       lic_tail_e lic_vanish_e).

Definition piR : Real := cauchy_real_pi_leibniz.

Definition prodR : Real := real_mult eR piR.
Definition sumR  : Real := real_plus eR piR.

(* Section 2. The strong-irrationality statement face (the same
   conclusion face as the lic criterion) *)

Definition epiIrr (X : Real) : Set :=
  forall q : Q, sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c) (real_metric X (real_const q)))).

(* the e-side certificate: converted directly from
   lic_e_irrational_criterion. *)
Lemma epi_irr_e : epiIrr eR.
Proof.
  intro q. exact (lic_e_irrational_criterion q).
Qed.

(* Section 3. The strong disjunctive data form (a Set-level Or, the same
   statement-face encoding as rLPO) *)

Definition epi_or_face : Set := Or (epiIrr prodR) (epiIrr sumR).

(* Section 4. The integer-coefficient polynomial evaluator: the
   coefficient list is lowest order first, P = a0 + a1*x + a2*x^2 + ... *)

Fixpoint rpoly_eval (cs : list Z) (x : Real) : Real :=
  match cs with
  | nil => real_const 0%Q
  | a :: rest => real_plus (real_const (Qmake a 1))
                           (real_mult x (rpoly_eval rest x))
  end.

(* AlgWit(X): an integer-coefficient list cs, a nonzero position k (the
   Z.eqb decision face), and a real_eq root certificate for
   rpoly_eval cs X = 0. *)
Definition AlgWit (X : Real) : Set :=
  sigT (fun cs : list Z =>
    sigT (fun k : nat =>
      And (Id (Z.eqb (nth k cs 0%Z) 0%Z) false)
          (real_eq (rpoly_eval cs X) real_zero))).

(* Section 5. The strong conditional witness form *)

Definition epi_cond_face : Set := forall w : AlgWit prodR, epiIrr sumR.

(* Section 6. The currying bridge: not(A and B) and A -> not B are
   inter-derivable by pure logic, with no mathematical content.  The
   negative forms are carried as refutation statements exiting into the
   Set-level empty type Empty_set (the same exit form as TransWit_weak
   below).  AlgP(X) carries the algebraic
   witness data itself: the Set-carrier completion of the inhabitedness
   lift of AlgWit(X). *)

Definition AlgP (X : Real) : Set := AlgWit X.

Lemma epi_curry_forward : forall X Y : Real,
  (And (AlgP X) (AlgP Y) -> Empty_set) -> AlgP X -> AlgP Y -> Empty_set.
Proof.
  intros X Y Hconj Hx Hy. apply Hconj. split; assumption.
Qed.

Lemma epi_curry_backward : forall X Y : Real,
  (AlgP X -> AlgP Y -> Empty_set) -> And (AlgP X) (AlgP Y) -> Empty_set.
Proof.
  intros X Y Hcurry [Hx Hy]. exact (Hcurry Hx Hy).
Qed.

Lemma epi_neg_equiv_weak_cond :
  And ((And (AlgP prodR) (AlgP sumR) -> Empty_set)
       -> (AlgP prodR -> AlgP sumR -> Empty_set))
      ((AlgP prodR -> AlgP sumR -> Empty_set)
       -> (And (AlgP prodR) (AlgP sumR) -> Empty_set)).
Proof.
  split.
  - apply epi_curry_forward.
  - apply epi_curry_backward.
Qed.

(* Section 7. Extraction and axiom face *)

Separate Extraction eR piR prodR sumR epiIrr epi_or_face rpoly_eval
  AlgWit epi_cond_face.

Print Assumptions epi_irr_e.
Print Assumptions epi_or_face.
Print Assumptions epi_cond_face.
Print Assumptions epi_neg_equiv_weak_cond.

(* ==================== Section 8. Mutual exclusion of the rational face and the strong-irrationality face ==================== *)

(* Supply of Qabs (the absolute value) and of its Qeq congruence lemma
   Qabs_wd: QArith.QArith does not include the Qabs module, so this file
   imports it explicitly in its continuation region (pure Q arithmetic,
   no axiom increment). *)
From Stdlib Require Import QArith.Qabs.

(* RatP(X): X equals some rational number (the real_eq rational-constant
   form, a Set-level sigT). *)
Definition RatP (X : Real) : Set :=
  sigT (fun q : Q => real_eq X (real_const q)).

(* RatP_h carries the rationality witness data itself: the Set-carrier
   completion of the inhabitedness lift of RatP, of the same form as
   AlgP. *)
Definition RatP_h (X : Real) : Set := RatP X.

Lemma ratp_lift_forward : forall X : Real, RatP X -> RatP_h X.
Proof.
  intros X [q Hq]. exact (existT _ q Hq).
Qed.

(* Note: since the witness data is carried directly, the former lift face
   is an identity on data; the weakening from the disjunctive form to the
   lifted negative face eliminates the witness data directly inside the
   Prop goal. *)

(* Mutual-exclusion core: strong irrationality (a positive separation
   constant certificate for every rational number) and equality with some
   rational number cannot both hold.  Argument: with c/2 as the
   approximation accuracy, the separation certificate gives
   e0 < |u_N - q| - c, the approximation gives |u_N - q| < c/2, and the
   chain yields c < c*(1/2), contradicting c > 0. *)
Lemma epi_irr_not_ratface : forall X : Real, epiIrr X -> RatP X -> Empty_set.
Proof.
  intros X Hirr [q Hq].
  destruct (Hirr q) as [c [Hc [e0 [He0 [N0 Hsep]]]]].
  assert (Hpos2 : Qlt 0 (1 # 2)%Q) by (unfold Qlt; cbn; reflexivity).
  assert (Hhalf : QltT 0 (c * (1 # 2))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat c (1 # 2)%Q).
    - apply QltT_to_Qlt. exact Hc.
    - exact Hpos2. }
  destruct (Hq (c * (1 # 2))%Q Hhalf) as [N1 H1].
  assert (Hle0 : NatLe N0 (max N0 N1)).
  { apply NatLe_lift. apply Nat.le_max_l. }
  assert (Hle1 : NatLe N1 (max N0 N1)).
  { apply NatLe_lift. apply Nat.le_max_r. }
  pose proof (Hsep _ Hle0) as HsN.
  pose proof (H1 _ Hle1) as H1N.
  (* Qeq rewriting does not enter the QltT context (no Proper instance;
     the same body shape as the lic source theorem): the projection
     reshaping goes through lic_qltt_comp_r on the Qeq plane. *)
  assert (HsT : QltT e0 ((Qabs ((projT1 X (max N0 N1) - q)%Q) - c)%Q)).
  { apply (lic_qltt_comp_r
             ((projT1 (real_metric X (real_const q)) (max N0 N1))
              - projT1 (real_const c) (max N0 N1))%Q
             ((Qabs ((projT1 X (max N0 N1) - q)%Q) - c)%Q)
             e0).
    - pose proof (lic_metric_proj X q (max N0 N1)) as HQ.
      rewrite (qeqT_imp_qeq _ _ (real_const_proj c (max N0 N1))).
      rewrite HQ.
      reflexivity.
    - exact HsN. }
  assert (H1T : QltT (Qabs ((projT1 X (max N0 N1) - q)%Q)) (c * (1 # 2))%Q).
  { pose proof (real_const_proj q (max N0 N1)) as HQ0.
    assert (HabsEq : (Qabs (projT1 X (max N0 N1) - projT1 (real_const q) (max N0 N1)))%Q
                     == (Qabs ((projT1 X (max N0 N1) - q)%Q))%Q).
    { apply Qabs_wd. rewrite (qeqT_imp_qeq _ _ HQ0). reflexivity. }
    pose proof (QltT_to_Qlt _ _ H1N) as H1Q.
    setoid_rewrite HabsEq in H1Q.
    apply (Qlt_to_QltT _ _ H1Q). }
  set (A := Qabs ((projT1 X (max N0 N1) - q)%Q)) in *.
  pose proof (QltT_to_Qlt _ _ HsT) as HsN'.
  pose proof (QltT_to_Qlt _ _ H1T) as H1N'.
  pose proof (QltT_to_Qlt _ _ He0) as He0'.
  pose proof (QltT_to_Qlt _ _ Hhalf) as Hpos'.
  (* e0 + c < A: the right end translates through ((A - c) + c == A) *)
  assert (Hshift : Qlt (e0 + c)%Q A).
  { apply (lic_qlt_comp_r ((A - c)%Q + c)%Q A (e0 + c)%Q).
    - apply lic_qlt_minus_add_r.
    - apply lic_qlt_add_r. exact HsN'. }
  pose proof (Qlt_trans _ _ _ Hshift H1N') as Hbad.
  (* c < e0 + c: adding c to 0 < e0 *)
  assert (Hce : Qlt c (e0 + c)%Q).
  { pose proof (lic_qlt_add_r 0%Q e0 c He0') as H0.
    rewrite Qplus_0_l in H0.
    exact H0. }
  pose proof (Qlt_trans _ _ _ Hce Hbad) as Hbad2.
  (* c < c*(1/2) contradicts 0 < c*(1/2) *)
  assert (Hmid : Qlt (c * (1 # 2))%Q 0%Q).
  { pose proof Hbad2 as H0.
    apply (lic_qlt_add_l (- (c * (1 # 2)))%Q c (c * (1 # 2))%Q) in H0.
    assert (Hr2 : ((- (c * (1 # 2)))%Q + c * (1 # 2))%Q == 0%Q) by ring.
    rewrite Hr2 in H0.
    assert (Hr1 : ((- (c * (1 # 2)))%Q + c)%Q == (c * (1 # 2))%Q) by ring.
    rewrite Hr1 in H0.
    exact H0. }
  destruct (Qlt_irrefl 0%Q (Qlt_trans _ _ _ Hpos' Hmid)).
Qed.

(* The weakening from the disjunctive form to the two-sided rationality
   negation (the downgrade of the strong disjunctive face). *)
Lemma epi_or_not_both_rat : epi_or_face -> RatP prodR -> RatP sumR -> Empty_set.
Proof.
  intros [f | g] hr hs.
  - exact (epi_irr_not_ratface prodR f hr).
  - exact (epi_irr_not_ratface sumR g hs).
Qed.

Lemma epi_or_face_down_dm :
  epi_or_face -> And (RatP_h prodR) (RatP_h sumR) -> Empty_set.
Proof.
  intros hor [hr hs].
  destruct (epi_or_not_both_rat hor hr hs).
Qed.

(* ==================== Section 9. The weakening implication faces of the conditional witness form and the disjunctive exits ==================== *)

(* Application face: with a witness given, the strong conditional form
   produces the strong irrationality certificate for e+pi (a
   well-formedness note). *)
Lemma epi_cond_face_apply : epi_cond_face -> AlgWit prodR -> epiIrr sumR.
Proof.
  intros ec w. exact (ec w).
Qed.

(* Exit face: the strong conditional form together with an algebraic
   witness for e*pi yields the right branch of the strong disjunctive
   form. *)
Lemma epi_cond_or_intror : epi_cond_face -> AlgWit prodR -> epi_or_face.
Proof.
  intros ec w. exact (inr (ec w)).
Qed.

(* The maximal closable weakening of the strong conditional form: the
   witness and a rationality certificate for e+pi cannot both hold
   (through the mutual-exclusion core). *)
Lemma epi_cond_down_ratweak : epi_cond_face -> AlgWit prodR -> RatP sumR -> Empty_set.
Proof.
  intros ec w hr. destruct (epi_irr_not_ratface sumR (ec w) hr).
Qed.

(* The Set-level statement forms of the remaining implication faces.
   The mathematical status of their inhabitedness, recorded explicitly:
   both faces are currently memberless.  The strong disjunctive to strong
   conditional direction needs a strong irrationality certificate for
   e+pi out of an arbitrary algebraic witness; the strong conditional to
   strong disjunctive direction is vacuous when e*pi has no algebraic
   witness and produces no branch data.  Strong irrationality is
   compatible with algebraicity (the square root of 2 has both), and the
   existence of a witness is itself an open problem. *)
Definition epi_or_implies_cond : Set := epi_or_face -> epi_cond_face.
Definition epi_cond_implies_or : Set := epi_cond_face -> epi_or_face.

(* The implication face from the strong conditional form to the weak
   algebraicity-negation form.  Its inhabitedness needs the
   transcendence of e as mathematical input: if e*pi and e+pi were both
   algebraic, then e would be a root of the quadratic with rational
   coefficients x^2 - (e+pi)*x + e*pi, hence algebraic, contradicting
   the Hermite transcendence; the existing irrationality of e in the
   library (the lic criterion) does not suffice to close this face. *)
Definition epi_cond_implies_weak : Set :=
  epi_cond_face -> AlgP prodR -> AlgP sumR -> Empty_set.

(* ==================== Section 10. The computational form of branch witnesses ==================== *)

(* A disjunctive witness solves for the branch index and the strong
   irrationality certificate: a computational face extractable along the
   whole chain. *)
Lemma epi_or_branch_extract : forall (P : Real -> Set),
  (forall Z : Real, epiIrr Z -> P Z) -> epi_or_face -> sigT (fun u : Real => P u).
Proof.
  intros P HP [f | g].
  - exists prodR. apply HP. exact f.
  - exists sumR. apply HP. exact g.
Qed.

(* The distribution face of Or through branch maps. *)
Lemma epi_or_face_map : forall (A B : Set),
  (epiIrr prodR -> A) -> (epiIrr sumR -> B) -> epi_or_face -> Or A B.
Proof.
  intros A B f g [h | h].
  - exact (inl (f h)).
  - exact (inr (g h)).
Qed.

(* Boolean branch-index recoding: mutually solvable with Or (branches as
   data). *)
Definition epi_or_branch_data : Set :=
  sigT (fun b : bool => epiIrr (if b then prodR else sumR)).

Lemma epi_or_face_to_branch_data : epi_or_face -> epi_or_branch_data.
Proof.
  intros [f | g].
  - exists true. exact f.
  - exists false. exact g.
Qed.

Lemma branch_data_to_epi_or_face : epi_or_branch_data -> epi_or_face.
Proof.
  intros [b h]. destruct b.
  - exact (inl h).
  - exact (inr h).
Qed.

(* Deciding the branch (asserting which branch holds without a witness)
   is out of scope for this file: the inhabitedness of epi_or_face itself
   is a current open problem, and the two exit lemmas introduce no
   decision mechanism. *)

(* ==================== Section 11. Extraction and axiom face (continued) ==================== *)

Separate Extraction RatP epi_or_branch_data epi_or_face_map
  epi_or_branch_extract epi_cond_face_apply epi_cond_or_intror.

Print Assumptions epi_irr_not_ratface.
Print Assumptions epi_or_not_both_rat.
Print Assumptions epi_or_face_down_dm.
Print Assumptions ratp_lift_forward.
Print Assumptions epi_cond_face_apply.
Print Assumptions epi_cond_or_intror.
Print Assumptions epi_cond_down_ratweak.
Print Assumptions epi_or_branch_extract.
Print Assumptions epi_or_face_map.
Print Assumptions epi_or_face_to_branch_data.
Print Assumptions branch_data_to_epi_or_face.

(* ==================== Section 12. Explicit premise carrying for the dependency faces (named premise faces before the low-form engines enter the library) ==================== *)

(* The mathematical inputs for two faces of the spectrum are not yet in
   the library: the weak algebraicity-negation face needs an effective
   transcendence engine for e (of the Hermite 1873 type; the classical
   proof of that face only uses Trans(e), and transcendence on the pi
   side is not needed), and the strong conditional face additionally
   needs an effective irrationality measure of the Mahler 1953 type.
   This section casts the two dependency faces as named Set-level premise
   types: what is missing, and in which form it is carried, is on record
   verbatim, and each Print Assumptions line records one closure item.
   Once the mathematical inputs enter the library, replacing the premises
   by their instances closes the final forms with the statement faces
   untouched. *)

(* TransWit_weak(X): the L1 interface -- a refutation machine for the
   certificate "a nonzero integer-coefficient polynomial P with
   P(X) = 0", exiting into the Set-level empty type Empty_set (refutation
   data eliminates into any target, with no Prop in any position).  The
   Niven-Hermite generic skeleton (interpolation kernel, integrality,
   bounds, limit, exit) is already in the library; instantiating it on
   the e side decomposes into five follow-up items: the interpolation
   kernel, integrality, bounds, the exit conversion, and resultant
   clearance. *)
Definition TransWit_weak (X : Real) : Set :=
  forall cs : list Z,
    sigT (fun k : nat =>
      And (Id (Z.eqb (nth k cs 0%Z) 0%Z) false)
          (real_eq (rpoly_eval cs X) real_zero)) ->
    Empty_set.

(* TransWit_meas(X): the L2 interface -- an effective irrationality
   measure of the Mahler type: every nonzero integer-coefficient
   polynomial P comes with an explicit delta > 0 such that
   real_const delta < |P(X)| (the separation face of the same shape as
   epiIrr).  This is the engine-level input for the strong conditional
   conclusion face, heavier in scale, to advance once L1 is in the
   library. *)
Definition TransWit_meas (X : Real) : Set :=
  forall cs : list Z,
    sigT (fun k : nat => Id (Z.eqb (nth k cs 0%Z) 0%Z) false) ->
    sigT (fun d : Q => And (QltT 0 d)
      (real_lt (real_const d) (real_metric (rpoly_eval cs X) real_zero))).

(* The generic premise block (all premise positions of Set type):
   premise one is the resultant-clearance layer, the algebraic
   elimination from the two root certificates for e*pi and e+pi to one
   root certificate on the e side (under the two root certificates e is a
   root of x^2 - (e+pi)*x + e*pi, as noted in Section 9); premise two is
   the instance of TransWit_weak on e. *)
Section EpiTransWitClosure.

Variable res_cl : AlgWit prodR -> AlgWit sumR -> AlgWit eR.
Variable twk_e  : TransWit_weak eR.

(* The main closure (Set exit form): the two root certificates, through
   clearance and the engine, yield contradiction data -- the classical
   form of the weak algebraicity-negation face closes under the two
   premises, using only e-side inputs throughout. *)
Theorem epi_trans_weak_quad_exit : AlgWit prodR -> AlgWit sumR -> Empty_set.
Proof.
  intros w1 w2.
  destruct (res_cl w1 w2) as [cs cert].
  exact (twk_e cs cert).
Qed.

End EpiTransWitClosure.

(* The channel face from the L2 premise to the strong conditional final
   form (carried explicitly; this face has no members yet): the channel
   body is the transport from a linear polynomial certificate to the
   real_metric separation face (content of the same shape as
   lic_e_irrational_criterion), to close together with the L2
   input; the final form epi_cond_face stays untouched verbatim. *)
Definition epi_cond_from_meas : Set :=
  TransWit_meas sumR -> epi_cond_face.

(* The closure of the weak algebraicity-negation form (as the application
   face of Section 6): both premises are of Set type, and the
   eliminations of the conjunction and of the witness data complete
   inside the Empty_set goal. *)
Theorem epi_trans_weak_closure_conj :
  (AlgWit prodR -> AlgWit sumR -> AlgWit eR) ->
  TransWit_weak eR -> And (AlgP prodR) (AlgP sumR) -> Empty_set.
Proof.
  intros res_cl twk_e Hconj.
  destruct Hconj as [Hx Hy].
  destruct (epi_trans_weak_quad_exit res_cl twk_e Hx Hy).
Qed.

(* The closure of the weak conditional form: delivered one-way from the
   weak algebraicity-negation form through the Section 6 currying bridge
   (the pure-logic equivalence of the two is in the library). *)
Theorem epi_trans_weak_closure_curry :
  (AlgWit prodR -> AlgWit sumR -> AlgWit eR) ->
  TransWit_weak eR -> AlgP prodR -> AlgP sumR -> Empty_set.
Proof.
  intros res_cl twk_e.
  exact (epi_curry_forward prodR sumR
           (epi_trans_weak_closure_conj res_cl twk_e)).
Qed.

(* Obstacle note for the reverse direction of the branch-selection face:
   the supply-to-solution direction is closed by full machine
   verification -- a disjunctive witness is a fully effective
   irrationality proof of one branch (the direct connection to the
   Section 10 branch extraction).  The constructive membership of the
   supply face itself is a current open problem: both branches, the
   irrationality of e*pi and of e+pi, are open, and the family of
   decision principles does not go through in either direction for a
   single-instance disjunction (a single instance contains no
   substitution slot for a universal principle; the escape window is
   supplied by the open problem itself).  Machine verification is
   unreachable because of this mathematical status, not through any
   failure of technique.  The open status is re-evaluated under three
   trigger conditions: first, an irrationality proof for e*pi or e+pi (a
   classical proof suffices and gives the constructive entry point);
   second, an effective measure of the Mahler type in the library;
   third, the discovery that e*pi is rational (compatible with the
   transcendence of e through the quadratic escape), in which case the
   disjunction closes by its right branch and the global status is
   re-evaluated. *)
Theorem epi_or_supply_channel : epi_or_face -> epi_or_branch_data.
Proof. exact epi_or_face_to_branch_data. Qed.

(* Extraction and axiom face (continued) *)

Separate Extraction TransWit_weak TransWit_meas epi_cond_from_meas
  epi_trans_weak_quad_exit.

Print Assumptions epi_trans_weak_quad_exit.
Print Assumptions epi_trans_weak_closure_conj.
Print Assumptions epi_trans_weak_closure_curry.
Print Assumptions epi_or_supply_channel.
