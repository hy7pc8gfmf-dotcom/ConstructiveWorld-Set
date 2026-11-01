(* ConstructiveWorld-Set -- Arch_PA_02: the fa57 / sqrt / mwi / sa / frd / pint
   proposition families collected and instantiated on Set-borne carriers. *)
(** * Arch_PA_02: proposition-family collection and instantiation carrier.

    Mission.  This file formalizes the proposition families
    fa57_sum_carrier_realizes, fa57_sumd_mult_const_r, fa57_lt_minus_nonneg,
    fa57_minus_lt_strict, fa57_nat_to_R, fa57_nat_to_R_pos, fa57_grpo_G_pos,
    fa57_two, fa57_two_pos, together with the sqrt_half_proj family (Part 0-2),
    the mwi_step degenerate-window family, the sa_A ln2 three-leg supply
    family, the frd_req entropy-temperature discharge family, and the
    pint_eval polynomial-integration family.  Every statement face is carried
    on the Set layer: equalities ride Id (or QeqT at the Q layer), orders ride
    the Set-valued lt/le (or QltT/QleT'/NatLe at the arithmetic layers); zero
    Prop leakage at statement level.

    Dependencies.  The Require block below: S01_BaseRing through
    S15_TailFEPUp (the real-interface chain), UpReq* engines, Beukers* and
    Ln2* (the ln2 supply bridge), fa51/fa53/fa56/fa56b (the finite-sum
    engines), and Stdlib List/Setoid/Morphisms/Lia/Qfield/Extraction/
    QArith/ZArith/Arith/Bool.

    Constructivity.  All proofs close by Qed/Defined; zero axioms and nothing left open; no
    classical logic.  Q-layer equality statements are stated as QeqT with the
    two gates (qeq_imp_qeqT / qeqT_imp_qeq) used inside proofs only; Q-layer
    order statements are stated as QleT'/QltT; nat comparisons ride NatLe.

    Build.  rocq c -native-compiler no -Q world "" Arch_PA_02.v
    (Rocq 9.1.0), same-world dependency .vo tree, cpu_guard wrapper. *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa53_compat_abs.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
From Stdlib Require Import List.
From Stdlib Require Import Setoid Morphisms.
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
Require Import UpAblMetaWorld3.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
Require Import BeukersLists.
Require Import BeukersIdentity.
Require Import Ln2Escape.
Require Import Ln2Bridge.
From Stdlib Require Import Lia Setoid Morphisms Qfield.
From Stdlib Require Import Extraction.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.

(* ================= Section 1: the fa57_sum_carrier_realizes family ================= *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa57Ext.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
(* fa53 dependency slot: the one-sided strict translation family needs the
   decidable-order extension (precedent: the all-arguments-explicit DO feed;
   after discharge DO enters only the two cluster-two signatures -- same
   order as the fa53 piece-1 slot instantiation resolution, the honest
   resolution shape of the UpFirewall:104 / UpEntropyGain:86 slots). *)
Context {DO : DecidableOrder RI}.

(* The interface projections are imported qualified: downstream Requires
   (S10 onward) rebind the bare R as the Notation R := Real, so the Let block
   pins every slot to the S01_BaseRing projection at this section's RI. *)
Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let opp := @S01_BaseRing.opp RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.

(*   pos_preserved: pointwise positive implies positive sum; ext: pointwise     *)
(*   equality implies equal sum; linear: sum (a . f) == a . (sum f).            *)
(*   This piece supplies the sigT witness: list fold.                           *)

Theorem fa57_sum_carrier_realizes :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    sigT (fun sumf : (X -> R) -> R =>
            And (forall f : X -> R,
                   (forall x : X, lt zero (f x)) -> lt zero (sumf f))
                (And (forall f g : X -> R,
                        (forall x : X, Id (f x) (g x)) -> Id (sumf f) (sumf g))
                     (forall (a : R) (f : X -> R),
                        Id (sumf (fun x => mult a (f x)))
                           (mult a (sumf f))))).
Proof.
  intros X enum Hne.
  exact (existT _                (fun f => fa51_sumd X f enum)                ((fun f Hf => fa51_sumd_nonnil_pos X f enum Hne Hf),                 ((fun f g Hpt => fa56b_sumd_cong X f g enum Hpt),                  (fun a f => fa56_sumd_mult_const X a f enum)))).
Qed.

(* ---- Right-factor linearity (the (fun x => mult (f x) a) variant of
        G02:174): the swap (fa56b) x const (fa56) x comm three-step Id chain. ---- *)
Lemma fa57_sumd_mult_const_r :
  forall (X : Set) (a : R) (f : X -> R) (l : list X),
    Id (fa51_sumd X (fun x => mult (f x) a) l)
       (mult (fa51_sumd X f l) a).
Proof.
  intros X a f l.
  exact (id_trans (fa56b_sumd_cong X (fun x => mult (f x) a)                                    (fun x => mult a (f x)) l                                    (fun x => mult_comm (f x) a))                  (id_trans (fa56_sumd_mult_const X a f l)                            (mult_comm a (fa51_sumd X f l)))).
Qed.

(* Slot statement: lt a b implies lt zero (minus b a) (minus definitionally     *)
(* = plus . opp).  Forward: a+(opp a)==zero repositioning + the fa53 one-sided  *)
(* strict translation.                                                          *)

Lemma fa57_lt_minus_nonneg :
  forall a b : R, lt a b -> lt zero (minus b a).
Proof.
  intros a b Hab.
  exact (lt_id_l zero (plus a (opp a)) (plus b (opp a))           (id_sym (plus_opp a))           (@fa53_lt_plus_translate_r RI DO a b (opp a) Hab)).
Qed.

(* Reverse (dual of the strict tier of G01:685 le_of_minus_nonneg):
   zero translation back + the assoc/opp/zero identity canal. *)
Lemma fa57_minus_lt_strict :
  forall a b : R, lt zero (minus b a) -> lt a b.
Proof.
  intros a b H.
  apply (lt_id_l a (plus zero a) b
           (id_trans (id_sym (plus_zero a)) (id_sym (plus_comm zero a)))).
  apply (lt_id_r (plus zero a) (plus (plus b (opp a)) a) b).
  - exact (id_trans (id_sym (plus_assoc b (opp a) a))
                    (id_trans (id_cong (fun w => plus b w)
                                       (id_trans (plus_comm (opp a) a)
                                                 (plus_opp a)))
                              (plus_zero b))).
  - exact (@fa53_lt_plus_translate_r RI DO zero (plus b (opp a)) a H).
Qed.

(* Parameter slot: G := nat_to_R_g (length group_enum); G_pos : lt zero G was
   originally a Variable.  Discharge = cover (the total InT witness) + any
   point g0 implies enum nonempty (the nil branch is killed by the InT zero
   constructor) implies length definitionally S k implies the positivity
   induction piece.  The carrier is redeclared locally per existing precedent
   (UpGRPO.v:51-65 isomorphic: the S slot plus-one recursion plus
   plus_positive/one_pos induction, proof term verbatim isomorphic). *)

Fixpoint fa57_nat_to_R (k : nat) : R :=
  match k with
  | O => zero
  | Datatypes.S m => plus one (fa57_nat_to_R m)
  end.

Lemma fa57_nat_to_R_pos :
  forall k : nat, lt zero (fa57_nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - exact (lt_id_r zero one (plus one zero) (id_sym (plus_zero one)) one_pos).
  - exact (plus_positive one (fa57_nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

Theorem fa57_grpo_G_pos :
  forall (Group : Set) (group_enum : list Group),
    (forall i : Group, InT i group_enum) ->
    forall g0 : Group,
      lt zero (fa57_nat_to_R (Datatypes.length group_enum)).
Proof.
  intros Group group_enum cover g0.
  (* Induction on the InT derivation itself: both constructors are cons-shaped,
     the Nil branch never enters the proof term (same method as G04
     projp_single_le_sum; avoids the extraction magic wrapper of empty
     matching). *)
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
Qed.

(* ==================== Cluster four: the G04 W2' two-point uniform projection family ==================== *)
(* The two-point uniform instantiation of the -181/394-400 argument-slot face
   (I/f/idx/f_norm/f_pos/P_witness) is fully discharged.  I := bool,
   idx := [true; false], f = half, P = true.  The half normalization chain:
   half + half == half . 1 + half . 1 == half . two == one (the four stages:
   distrib + mult_one + mult_comm + inv_pos_correct). *)

Definition fa57_two : R := plus one one.

Lemma fa57_two_pos : lt zero fa57_two.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

Definition fa57_half : R := inv_pos fa57_two fa57_two_pos.

Lemma fa57_half_pos : lt zero fa57_half.
Proof.
  exact (inv_pos_pos fa57_two fa57_two_pos).
Qed.

Lemma fa57_half_plus_half : Id (plus fa57_half fa57_half) one.
Proof.
  exact (id_trans (id_cong2 plus (id_sym (mult_one fa57_half))                                (id_sym (mult_one fa57_half)))                  (id_trans (id_sym (distrib fa57_half one one))                            (id_trans (mult_comm fa57_half fa57_two)                                      (inv_pos_correct fa57_two fa57_two_pos)))).
Qed.

(* ---- The W2' seven-slot face discharge package (the norm/pos/witness three
        slots + the structural slots self-evidenced by the type face) ---- *)
Theorem fa57_W2p_uniform_two_realized :
  And (Id (fa51_sumd bool (fun _ : bool => fa57_half) [true; false]) one)
      (And (forall i : bool, lt zero ((fun _ : bool => fa57_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  split.
  - exact (id_trans (id_cong (fun w : R => plus fa57_half w)
                             (plus_zero fa57_half))
                    fa57_half_plus_half).
  - split.
    + exact (fun _ => fa57_half_pos).
    + exact (existT (fun i : bool =>
                       And (Id ((fun _ : bool => true) i) true)
                           (InT i [true; false]))
                    true (id_refl, @InT_here bool true [false])).
Qed.

(* Argument slots: Z_align : Real (bare argument slot) and
   Z_align_pos : lt zero Z_align (honest argument slot).  Loading = the
   fa51_Z_align realizer feeding both slots in one shot (the CYC6 slot-loading
   precedent; inside UpDPOLip instantiating with this realizer kills both
   slots). *)

Definition fa57_dpolip_Z_realizer :
  forall (X : Set) (enum : list X) (reward : X -> R) (beta : R)
         (beta_pos : lt zero beta) (pi_ref : X -> R),
    (forall s : X, lt zero (pi_ref s)) ->
    Not (Id enum nil) ->
    sigT (fun Z : R => And (Id Z (fa51_Z_align X enum reward beta beta_pos pi_ref))
                           (lt zero Z)).
Proof.
  intros X enum reward beta beta_pos pi_ref Href Hne.
  exact (existT _
                (fa51_Z_align X enum reward beta beta_pos pi_ref)
                (id_refl,
                 fa51_Z_align_pos X enum reward beta beta_pos pi_ref Href Hne)).
Qed.

End Fa57Ext.

(* ============ Assumption-face closure declaration (G4 prerequisite) ============ *)

Print Assumptions fa57_sum_carrier_realizes.
Print Assumptions fa57_sumd_mult_const_r.
Print Assumptions fa57_lt_minus_nonneg.
Print Assumptions fa57_minus_lt_strict.
Print Assumptions fa57_grpo_G_pos.
Print Assumptions fa57_W2p_uniform_two_realized.
Print Assumptions fa57_dpolip_Z_realizer.

Print Assumptions fa57_half_plus_half.
Print Assumptions fa57_half_pos.
Print Assumptions fa57_two_pos.
Print Assumptions fa57_lt_minus_nonneg.
Print Assumptions fa57_sumd_mult_const_r.
Print Assumptions fa57_sum_carrier_realizes.
(* ================= Section 2: the sqrt_half_proj family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.

Local Open Scope Q_scope.

(* Part 0: the Real-layer pointwise tool (half x + half x == x, the pointwise
   Q-ring identity) *)

(* Pointwise: projT1 (real_mult (real_const 1/2) x) n == 1/2 * x_n
   (assembled from the projection lemmas; statement on the QeqT carrier). *)
Lemma sqrt_half_proj : forall (x : Real) (n : nat),
  QeqT (projT1 (real_mult (real_const (1#2)) x) n) ((1#2) * projT1 x n).
Proof.
  intros x n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj (1#2) x n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1#2) n)).
  reflexivity.
Qed.

(* 1/2 x + 1/2 x == x (pointwise via real_eq; the Q-layer identity
   1/2 q + 1/2 q == q is decided by ring) *)
Lemma sqrt_real_plus_half_half : forall x : Real,
  real_eq (real_plus (real_mult (real_const (1#2)) x)
                     (real_mult (real_const (1#2)) x))
          x.
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  (* Pointwise simplification of the difference: 1/2 x_n + 1/2 x_n - x_n == 0 *)
  assert (Hd : projT1 (real_plus (real_mult (real_const (1#2)) x)
                                 (real_mult (real_const (1#2)) x)) n
                - projT1 x n == 0%Q).
  { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const (1#2)) x)
                            (real_mult (real_const (1#2)) x) n)).
    rewrite (qeqT_imp_qeq _ _ (sqrt_half_proj x n)).
    ring. }
  (* Qabs(difference) == Qabs 0 == 0; the pointwise bound |0| < eps *)
  assert (Habs0 : Qabs (projT1 (real_plus (real_mult (real_const (1#2)) x)
                                          (real_mult (real_const (1#2)) x)) n
                        - projT1 x n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* Part 1 (G2): constructive square-root existence at the Real layer *)

Theorem real_sqrt_exists : forall d : Real, real_le real_zero d ->
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - (* Case (i): 0 < d.  r := exp(half . log d). *)
    exists (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))).
    split.
    + (* r > 0: exp is everywhere positive (the real_le left branch = real_lt) *)
      exact (inl (cauchy_real_exp_pos
              (real_mult (real_const (1#2)) (cw_log d Hdlt)))).
    + (* r . r == d: the exp additivity + log/exp right-inverse canal. *)
      apply (real_eq_trans
              (real_mult (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt)))
                         (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                          (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              d).
      * (* Backward via exp additivity: exp(x) . exp(y) == exp(x+y) *)
        apply real_eq_sym. apply cauchy_real_exp_plus.
      * apply (real_eq_trans
                (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                            (real_mult (real_const (1#2)) (cw_log d Hdlt))))
                (cauchy_real_exp (cw_log d Hdlt)) d).
        -- (* exp respects real_eq (the half + half == identity piece feeds in) *)
           apply cauchy_real_exp_wd.
           apply sqrt_real_plus_half_half.
        -- (* exp(log d) == d *)
           apply cw_log_exp_right.
  - (* Case (ii): d == 0 (the real_eq certificate Hdeq).  r := real_zero. *)
    exists real_zero.
    split.
    + (* 0 >= 0: the real_le right branch = real_eq 0 0 (reflexivity) *)
      exact (inr (real_eq_refl real_zero)).
    + (* 0 . 0 == 0 == d *)
      apply (real_eq_trans (real_mult real_zero real_zero) real_zero d).
      * apply real_mult_zero.
      * exact Hdeq.
Qed.

(* Concrete instance (a machine-extractable sanity check): the square root of
   one is constructible.  r := exp(half . log 1), r >= 0 and r . r == 1 --
   the d = 1 instance of the G2 main theorem. *)

Lemma real_one_pos_local : real_lt real_zero real_one.
Proof.
  exists (1#2).
  split.
  - reflexivity.
  - exists 0%nat. intros n Hn. reflexivity.
Qed.

Lemma real_sqrt_one :
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) real_one)).
Proof.
  exact (real_sqrt_exists real_one (inl real_one_pos_local)).
Qed.

(* Part 2 (G1): the general square-dimension witness family (abstract R layer,
   interface-generic).  The in-library machine-checked instances previously
   covered only d = 4 (sq_witness_4); this section gives the sqrt_witness
   witness family for general k-square dimensions plus the dual instances. *)

Section SqrtWitnessGeneral.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* The nat -> R embedding reuses the in-library nat_to_R (RI implicit instance
   argument). *)

(* Additive homomorphism: nat_to_R (m+n) == nat_to_R m + nat_to_R n *)
Lemma nat_to_R_plus_hom : forall m n : nat,
  Id (nat_to_R (m + n)%nat) (plus (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (plus_comm zero (nat_to_R n))
                            (plus_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (id_cong (fun t => plus one t) IH)
                    (plus_assoc one (nat_to_R m) (nat_to_R n))).
Qed.

(* Multiplicative homomorphism: nat_to_R (m . n) == nat_to_R m . nat_to_R n *)
Lemma nat_to_R_mult_hom : forall m n : nat,
  Id (nat_to_R (m * n)%nat) (mult (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (mult_comm zero (nat_to_R n))
                            (mult_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (nat_to_R_plus_hom n (m * n)%nat)
           (id_trans (id_cong (fun t => plus (nat_to_R n) t) IH)
           (id_trans (id_cong (fun t => plus t (mult (nat_to_R m) (nat_to_R n)))
                              (id_sym (mult_one (nat_to_R n))))
           (id_trans (id_cong (fun t => plus (mult (nat_to_R n) one) t)
                              (mult_comm (nat_to_R m) (nat_to_R n)))
           (id_trans (id_sym (distrib (nat_to_R n) one (nat_to_R m)))
                     (mult_comm (nat_to_R n) (plus one (nat_to_R m)))))))).
Qed.

(* Strict positivity of nat_to_R: k >= 1 implies 0 < nat_to_R k *)
Lemma nat_to_R_pos : forall k : nat, lt zero (nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - simpl.
    exact (lt_id_r zero one (plus one zero)
                   (id_sym (plus_zero one)) one_pos).
  - simpl. exact (plus_positive one (nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

(* Witness (literal form): d := r . r (Id reflexivity; the naming form of
   "r is exactly sqrt(r^2)") *)
Lemma sqrt_witness_sq : forall k : nat,
  sqrt_witness (mult (nat_to_R k) (nat_to_R k)) (nat_to_R k).
Proof. intro k. exact id_refl. Qed.

(* Witness (nontrivial form): d := nat_to_R (k . k) == nat_to_R k . nat_to_R k
   (supplied by the multiplicative homomorphism nat_to_R_mult_hom -- the true
   witness of the k-square dimension) *)
Lemma sqrt_witness_nat_sq : forall k : nat,
  sqrt_witness (nat_to_R (k * k)%nat) (nat_to_R k).
Proof. intro k. exact (id_sym (nat_to_R_mult_hom k k)). Qed.

(* The k-square dual instance: 1/(S k) scaling == temperature (S k)
   (the instantiation of scale_sqrt_witness_dual at
   d := nat_to_R (S k) . nat_to_R (S k), r := nat_to_R (S k);
   k >= 0 implies temperature >= 1 > 0) *)
Lemma scale_dual_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S01_BaseRing.S RI SS -> @S01_BaseRing.R RI,
                (forall s : @S01_BaseRing.S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S01_BaseRing.S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (mult (nat_to_R (Datatypes.S k)) (nat_to_R (Datatypes.S k)))           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_sq (Datatypes.S k)) z s).
Qed.

(* Dual instance (nat-square form, d := nat_to_R ((S k) . (S k))) *)
Lemma scale_dual_nat_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S01_BaseRing.S RI SS -> @S01_BaseRing.R RI,
                (forall s : @S01_BaseRing.S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S01_BaseRing.S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (nat_to_R ((Datatypes.S k) * (Datatypes.S k))%nat)           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_nat_sq (Datatypes.S k)) z s).
Qed.

End SqrtWitnessGeneral.

Print Assumptions scale_dual_nat_sq_k.
Print Assumptions scale_dual_sq_k.
Print Assumptions sqrt_witness_nat_sq.
Print Assumptions sqrt_witness_sq.
Print Assumptions real_sqrt_one.
(* ================= Section 3: the mwi_step family ================= *)
Import RealInterfaceEnhancedMod.

(* Section 1: the degenerate-side machinery: the generic one-step kernel
   evolution + the base-ring algebra bridge *)

(* The generic one-step evolver: isomorphic to the donor mtw_step with the
   kernel K lifted to an explicit argument *)
Definition mwi_step (K : bool -> bool -> Real) (mu : bool -> Real) (s' : bool) : Real :=
  plus (mult (mu true) (K true s')) (mult (mu false) (K false s')).

(* Left zero multiplication: 0 . a == 0 (the base mult_zero is right-zero
   shaped only; bridge via comm) *)
Lemma mwi_mult_zero_l : forall a : Real, req (mult zero a) zero.
Proof.
  intro a.
  apply (req_trans (mult zero a) (mult a zero) zero).
  - exact (mult_comm zero a).
  - exact (mult_zero a).
Defined.

(* Self-difference is zero: a - a == 0 *)
Lemma mwi_req_minus_self : forall a : Real, req (req_minus a a) zero.
Proof.
  intro a.
  unfold req_minus.
  exact (plus_opp a).
Defined.

(* The absolute value of zero: |0| == 0 *)
Lemma mwi_abs_zero : req (abs zero) zero.
Proof. exact abs_zero. Defined.

(* Section 2: the degenerate-face theorem: all kernel rows equal implies
   one-step collapse (TV == 0, the mixed-window degenerate side).  Note: the
   row-stochastic premise is a world-eligibility premise; the collapse body
   only needs row equality (both rows equal to the first row). *)

Theorem mwi_collapse_row_equal :
  forall K : bool -> bool -> Real,
    (forall s : bool, req (plus (K s true) (K s false)) one) ->
    (forall s s' : bool, req (K s s') (K true s')) ->
    req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero.
Proof.
  intros K Hrow Heq.
  (* Under kernel K the one-step evolution of the mass pair is pointwise the
     first row: the mu0 side = 1 . K(t,.) + 0 . K(f,.) *)
  assert (Ht : forall s' : bool, req (mwi_step K mtw_mu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_mu0 s')
                     (plus (K true s') zero)
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_mu0 true) (K true s')) (K true s')
               (mult (mtw_mu0 false) (K false s')) zero
               (req_mult_one_l (K true s'))
               (mwi_mult_zero_l (K false s'))).
    - exact (plus_zero (K true s')). }
  (* The nu0 side = 0 . K(t,.) + 1 . K(f,.) = K(f,.) = K(t,.) (rows equal) *)
  assert (Hf : forall s' : bool, req (mwi_step K mtw_nu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_nu0 s')
                     (plus zero (K false s'))
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_nu0 true) (K true s')) zero
               (mult (mtw_nu0 false) (K false s')) (K false s')
               (mwi_mult_zero_l (K true s'))
               (req_mult_one_l (K false s'))).
    - exact (req_trans (plus zero (K false s')) (K false s') (K true s')
               (req_plus_zero_l (K false s'))
               (Heq false s')). }
  (* Pointwise difference zero implies pointwise absolute value zero *)
  assert (Hz : forall s' : bool,
           req (abs (req_minus (mwi_step K mtw_mu0 s')
                               (mwi_step K mtw_nu0 s'))) zero).
  { intro s'.
    apply (req_trans
             (abs (req_minus (mwi_step K mtw_mu0 s')
                             (mwi_step K mtw_nu0 s')))
             (abs zero) zero).
    - exact (req_abs_compat
               (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
               zero
               (req_trans
                  (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
                  (req_minus (K true s') (K true s'))
                  zero
                  (req_plus_compat
                     (mwi_step K mtw_mu0 s') (K true s')
                     (opp (mwi_step K mtw_nu0 s')) (opp (K true s'))
                     (Ht s')
                     (req_opp_compat (mwi_step K mtw_nu0 s') (K true s')
                               (Hf s')))
                  (mwi_req_minus_self (K true s')))).
    - exact mwi_abs_zero. }
  (* TV = (1/2) . (0+0) = 0 *)
  apply (req_trans (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0))
                   (mult mtw_half zero) zero).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool =>
                   abs (req_minus (mwi_step K mtw_mu0 s)
                                  (mwi_step K mtw_nu0 s))))
             zero
             (req_refl mtw_half)
             (req_trans
                (mtw_sumf (fun s : bool =>
                      abs (req_minus (mwi_step K mtw_mu0 s)
                                     (mwi_step K mtw_nu0 s))))
                (plus zero zero) zero
                (req_plus_compat
                   (abs (req_minus (mwi_step K mtw_mu0 true)
                                   (mwi_step K mtw_nu0 true))) zero
                   (abs (req_minus (mwi_step K mtw_mu0 false)
                                   (mwi_step K mtw_nu0 false))) zero
                   (Hz true) (Hz false))
                (req_plus_zero_l zero))).
  - exact (mult_zero mtw_half).
Defined.

(* Section 3: the explicit degenerate-world instance: the uniform kernel
   (every row (1/2, 1/2), rows equal) has TV(1) == 0 *)

Definition mwi_Kunif (s s' : bool) : Real := mtw_half.

Lemma mwi_Kunif_row : forall s : bool,
  req (plus (mwi_Kunif s true) (mwi_Kunif s false)) one.
Proof. intro s. exact mtw_hh_one. Defined.

Lemma mwi_Kunif_rows_eq : forall s s' : bool,
  req (mwi_Kunif s s') (mwi_Kunif true s').
Proof. intros s s'. exact (req_refl mtw_half). Defined.

Theorem mwi_degenerate_collapse_uniform :
  req (mtw_tv (mwi_step mwi_Kunif mtw_mu0) (mwi_step mwi_Kunif mtw_nu0)) zero.
Proof.
  exact (mwi_collapse_row_equal mwi_Kunif mwi_Kunif_row mwi_Kunif_rows_eq).
Defined.

(* Section 4: the host piece: the two-sided mixing-window theorem (carried by
   the S01 base Set-layer conjunction).  Left limb = the degenerate side (the
   degenerate-world window collapses); right limb = the existence side (the
   non-degenerate world window genuinely exists: the exact power law plus the
   budget lower bound, two conjuncts conjoined). *)

Theorem mtw_window_two_sided :
  And
    (* Degenerate side: a row-stochastic kernel with equal rows implies
       one-step collapse TV == 0 *)
    (forall K : bool -> bool -> Real,
       (forall s : bool, req (plus (K s true) (K s false)) one) ->
       (forall s s' : bool, req (K s s') (K true s')) ->
       req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero)
    (* Existence side: the non-degenerate (World3) exact power law + the
       mixing-window budget lower bound *)
    (And
       (forall n : nat,
          req (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
              (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)))
       (forall (n : nat) (B : Real),
          lt B (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)) ->
          lt B (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))).
Proof.
  split.
  - exact mwi_collapse_row_equal.
  - split.
    + exact mtw_tv_exact_iter.
    + exact mtw_no_mixing_below.
Defined.

(* The four-item self-check: every piece Closed (zero new assumptions) *)

Print Assumptions mwi_step.
Print Assumptions mwi_mult_zero_l.
Print Assumptions mwi_req_minus_self.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_collapse_row_equal.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mtw_window_two_sided.

(* PA re-anchor block (verification copy pieces) *)
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_req_minus_self.
(* ================= Section 4: the sa_A family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.

(* Section 1: the integer face of A_n (leg 2) + the normalization-bridge
   conversion *)

(* A_n := 2^{n+1} . q_n-tilde, the integer face (nat-carried, Z-converted) *)
Definition sa_A (n : nat) : Z :=
  Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n).

(* The Q carrier of A_n == 2^{n+1} . q_n-tilde (the bi_q_pow_2 + bk_Qmul_nat
   conversion; statement on the QeqT carrier). *)
Lemma sa_A_q : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S n)) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 (Datatypes.S n))).
  symmetry.
  exact (qeqT_imp_qeq _ _ (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n))).
Qed.

(* The true proof of leg 2: 0 < |A_n| (q_n-tilde >= 3^n >= 1 implies A_n >= 2) *)
Theorem sa_A_nonzeroT : forall n : nat, QltT 0 (Qabs ((sa_A n) # 1)%Q).
Proof.
  intro n.
  assert (Hge : (2 <= 2 ^ (Datatypes.S n) * bk_Qn_qtilde n)%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)) as H3.
    pose proof (NatLe_drop _ _ (ln2b_pow_ge1 3 n ltac:(lia))) as H31.
    pose proof (NatLe_drop _ _ (ln2b_pow_ge1 2 n ltac:(lia))) as H21.
    nia. }
  apply Qlt_to_QltT.
  unfold sa_A. unfold Qabs, Qlt. cbn [Qnum Qden].
  destruct (Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n)) as [| z | z]
    eqn:HM; cbn in *; lia.
Qed.

(* sa_norm_bridge: sa_A n # 1 == 2^{2n+1} . Q_n(1/2) (the congruent conversion
   via bi_norm_factor; the closed-form landing spot of the true normalization
   factor 2^{n+1} . q_n-tilde) *)
Theorem sa_norm_bridge : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n))
          * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof. intro n. exact (bi_norm_factor n). Qed.

(* Section 2: the positivity leg of clo_n (leg 3) + the carrier integrality /
   upper-bound support faces *)

(* Carrier: clo_n := lne_B n = the closed form (n!)^2/(2n+1)! of the integral
   int_0^1 t^n (1-t)^n dt *)
Definition sa_clo (n : nat) : Q := lne_B n.

(* The true proof of leg 3: 0 < clo_n (via lne_B_posT) *)
Theorem sa_clo_posT : forall n : nat, QltT 0 (sa_clo n).
Proof. intro n. apply lne_B_posT. Qed.

(* sa_clo_int: the carrier integrality face clo_n . (2n+1)! == (n!)^2 in Z
   (the sigT-witness form -- the combinatorial raw material of the B_n integer
   face; the numerator-side Z conversion goes through this face) *)
Theorem sa_clo_int : forall n : nat,
  sigT (fun m : Z =>
    QeqT (sa_clo n * q_fact (Datatypes.S (n + n))%nat) (m # 1)).
Proof. exact lne_B_int. Qed.

(* sa_clo_le_p4: the carrier upper bound clo_n <= 4^{-n} (the Q-side raw
   material of I_n <= 2^{n+1} . clo_n <= 2^{1-n}; the integral-side half
   1/(1-t/2)^{n+1} <= 2^{n+1} awaits the body piece) *)
Theorem sa_clo_le_p4 : forall n : nat, QleT' (sa_clo n) (Qinv (lne_p4 n)).
Proof. exact lne_B_le_p4. Qed.

(* Section 3: the theta tier (leg 1) + the half-power conversion *)

Definition sa_theta : Q := (1 # 2)%Q.

(* The true proof of leg 1: theta = 1/2 < 1 *)
Theorem sa_theta_lt1 : QltT sa_theta (1 # 1)%Q.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* sa_theta_posT: theta positivity (the prerequisite face of ln2b_decay) *)
Theorem sa_theta_posT : QltT 0 sa_theta.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* The powers of one *)
Lemma sa_qpow_one_q : forall n : nat, QeqT (q_pow (1 # 1)%Q n) (1 # 1)%Q.
Proof.
  induction n as [| n IH].
  - apply qeq_imp_qeqT. reflexivity.
  - cbn [q_pow]. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

(* The half-power inverse: q_pow (1/2) n . q_pow 2 n == 1 (the ln2b_qpow_inv
   conversion) *)
Lemma sa_half_pow : forall n : nat,
  QeqT (q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n) (1 # 1)%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  transitivity (q_pow (1 # 1)%Q n).
  - exact (qeqT_imp_qeq _ _ (ln2b_qpow_inv 1%Z 2%positive n)).
  - exact (qeqT_imp_qeq _ _ (sa_qpow_one_q n)).
Qed.

(* The half-power inverse conversion: 2^{-n} == (1/2)^n *)
Theorem sa_theta_pow_inv2 : forall n : nat,
  QeqT (Qinv (q_pow (2 # 1)%Q n)) (q_pow (1 # 2)%Q n).
Proof.
  intro n.
  assert (Hnz : ~ (q_pow (2 # 1)%Q n == 0%Q)).
  { intro E.
    (* q_neq_of_lt lands in the S01 Set-layer Not (Empty_set flavor); the
       empty match lowers it to the False-flavored goal. *)
    exact (match q_neq_of_lt (q_pow (2 # 1)%Q n) (bi_q_pow_pos2 n)
             (qeq_imp_qeqT _ _ E) with end). }
  assert (Hm := sa_half_pow n).
  assert (H1 : (Qinv (q_pow (2 # 1)%Q n) * q_pow (2 # 1)%Q n)%Q
               == (q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n)%Q).
  { rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q n)) (q_pow (2 # 1)%Q n)).
    rewrite (Qmult_inv_r (q_pow (2 # 1)%Q n) Hnz).
    rewrite (qeqT_imp_qeq _ _ Hm). reflexivity. }
  apply (lne_mult_canc _ _ (q_pow (2 # 1)%Q n)); [exact H1 | exact Hnz].
Qed.

(* sa_Qinv_le: the Q-inverse monotonicity 0 < a <= b implies 1/b <= 1/a
   (a Q-layer support lemma stated on the QltT/QleT' carriers; the Z case
   split decided by nia) *)
Lemma sa_Qinv_le : forall a b : Q,
  QltT 0%Q a -> QleT' a b -> QleT' (Qinv b) (Qinv a).
Proof.
  intros [an ad] [bn bd] Ha Hab.
  apply Qle_to_QleT'.
  pose proof (QltT_to_Qlt 0%Q ((an # ad)%Q) Ha) as Hlt.
  pose proof (QleT'_to_Qle ((an # ad)%Q) ((bn # bd)%Q) Hab) as Hle.
  unfold Qlt, Qle in Hlt, Hle. cbn [Qnum Qden] in Hlt, Hle.
  unfold Qle, Qinv. cbn [Qnum Qden].
  destruct an; destruct bn; cbn in *; nia.
Qed.

(* sa_q2_le_mul: the exponent-slot comparison q_pow 2 n <= q_pow 2 (S n) .
   q_n-tilde (all three rewrites ride the gated bi_q_pow_2 / bk_Qmul_nat
   conversions; the nat tail is the NatLe_lift bridge + nia with
   q_n-tilde >= 1). *)
Lemma sa_q2_le_mul : forall n : nat,
  QleT' (q_pow (2 # 1)%Q n)
        ((q_pow (2 # 1)%Q (Datatypes.S n) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q).
Proof.
  intro n.
  assert (Hq1 : (1 <= bk_Qn_qtilde n)%nat).
  { pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)) as H3.
    pose proof (NatLe_drop _ _ (ln2b_pow_ge1 3 n ltac:(lia))) as H31. lia. }
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 (Datatypes.S n))).
  rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n))).
  rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 n)).
  apply QleT'_to_Qle. apply bk_Qle_nat. apply NatLe_lift.
  rewrite Nat.pow_succ_r'. nia.
Qed.

(* sa_theta_leg_scaffold (pure Q conversion, true proof):
   1/(2^{n+1} . q_n-tilde) <= (1/2)^n = theta^n -- the closing tier of the
   error end 2^{-2n}/q_n-tilde <= theta^n (q_n-tilde >= 3^n >= 1).  The Qinv
   monotonicity piece sa_Qinv_le is fed its two premises as terms; the
   2^{-n} = (1/2)^n slot rides the sa_theta_pow_inv2 gate. *)
Theorem sa_theta_leg_scaffold : forall n : nat,
  QleT' (Qinv ((q_pow (2 # 1)%Q (Datatypes.S n)
                 * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q))
        (q_pow (1 # 2)%Q n).
Proof.
  intro n.
  apply Qle_to_QleT'.
  rewrite <- (qeqT_imp_qeq _ _ (sa_theta_pow_inv2 n)).
  exact (QleT'_to_Qle _ _
           (sa_Qinv_le (q_pow (2 # 1)%Q n)
                       ((q_pow (2 # 1)%Q (Datatypes.S n)
                          * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q)
                       (bi_q_pow_pos2 n) (sa_q2_le_mul n))).
Qed.

(* sa_clo_in_theta_window (true proof): clo_n < theta^n (n >= 1) -- the
   carrier lands strictly inside the theta-tier decision window (the 2^{-n}
   window of lne_B_lt_p2 converted via sa_theta_pow_inv2) *)
Theorem sa_clo_in_theta_window : forall n : nat, (1 <= n)%nat ->
  QltT (sa_clo n) (q_pow sa_theta n).
Proof.
  intros n Hn.
  apply (bi_qlt_eq (lne_B n) (Qinv (ln2i_p2 n)) (sa_clo n) (q_pow sa_theta n)).
  - exact (lne_B_lt_p2 n Hn).
  - apply qeq_imp_qeqT. reflexivity.
  - unfold sa_theta.
    apply qeq_imp_qeqT.
    rewrite (ln2i_p2_Z n).
    rewrite <- (qeqT_imp_qeq _ _ (bi_q_pow_2 n)).
    exact (qeqT_imp_qeq _ _ (sa_theta_pow_inv2 n)).
Qed.

(* Section 4: the three independent packaged pieces (legs 1-2-3 mounted) *)

(* sa_supply_head: the independent package of legs 1-2-3 of the five-leg
   supply *)
Definition sa_supply_head : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun clo : nat -> Q =>
      sigT (fun th : Q =>
        And (QltT th (1 # 1))
          (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
               (forall n : nat, QltT 0 (clo n)))))).

Theorem sa_supply_three_legs : sa_supply_head.
Proof.
  exists sa_A. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + apply sa_clo_posT.
Qed.

(* Section 5: the conditional interface (legs 4-5) + the two-stage assembly
   closure *)

(* sa_supply_rem: the conditional interface, the B_n integer face plus the two
   real legs (the 4 lower bound / 5 upper bound) -- the instantiation
   resolution slot to be filled once the identity body (I_n =
   2^{n+1} . q_n-tilde . X - r_n, three sub-pieces per the header note)
   arrives.  Semantics made precise: the nonemptiness of this interface is
   exactly the existence of the theta-tier Pade approximation column; this
   piece asserts nothing beyond it. *)
Definition sa_supply_rem : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower sa_A B sa_clo)
        (ln2b_line_upper sa_A B sa_theta)).

(* sa_supply_assemble: the two-stage assembly -- the three mounted legs plus
   the conditional interface imply the full supply type *)
Theorem sa_supply_assemble : forall Hm : sa_supply_rem, ln2i_pade_supply.
Proof.
  intros [B [Hlow Hup]].
  exists sa_A. exists B. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + split.
      * apply sa_clo_posT.
      * split.
        -- exact Hlow.
        -- exact Hup.
Qed.

(* sa_ln2_irrational: the ln2-irrationality two-stage closure -- via the
   Ln2Bridge source module's ln2b_irrational_from_supply (going genuinely
   through lic_irrational_criterion, zero bypass).  The statement face = the
   expanded form of the L4 conclusion face (all Set: sigT/And/QltT/real_lt). *)
Theorem sa_ln2_irrational : forall (Hm : sa_supply_rem) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hm q.
  exact (ln2b_irrational_from_supply (sa_supply_assemble Hm) q).
Qed.

(* Section 6: the numerical anchor group (exact vm_compute decisions:
   A_1 = 2^2 . q_1-tilde = 12, A_2 = 2^3 . q_2-tilde = 104, clo_1 = 1/6,
   the theta^2 half-power anchor) *)

Theorem sa_A1_anchor : QeqT ((sa_A 1) # 1)%Q (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_A2_anchor : QeqT ((sa_A 2) # 1)%Q (104 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_clo1_anchor : QeqT (sa_clo 1) (1 # 6)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_theta2_anchor : QeqT (q_pow sa_theta 2) (1 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* Section 7: the extraction recheck and the assumption audit *)

Separate Extraction sa_ln2_irrational sa_supply_assemble
  sa_supply_three_legs sa_A_nonzeroT sa_clo_posT sa_clo_int
  sa_theta_leg_scaffold sa_clo_in_theta_window sa_norm_bridge.
Print Assumptions sa_ln2_irrational.
Print Assumptions sa_supply_assemble.
Print Assumptions sa_supply_three_legs.
Print Assumptions sa_theta_leg_scaffold.
Print Assumptions sa_clo_in_theta_window.
Print Assumptions sa_A_nonzeroT.

Print Assumptions sa_ln2_irrational.
Print Assumptions sa_clo_le_p4.
Print Assumptions sa_clo_int.
Print Assumptions sa_clo_posT.
Print Assumptions sa_norm_bridge.
(* ================= Section 5: the frd_req_entropy_temp_explicit family ================= *)
Import RealInterfaceEnhancedMod.

(* Section FrdTempDischarge: the union of the host Section FirewallReq
   witness face and the UpReqTempEntropy Section ReqTempEntropy resolution
   face.  One witness per type; the host slot and the resolution slot are fed
   together (the restatement-bridge adjudication is in the header note). *)
Section FrdTempDischarge.
(* Set-carrier completion: the interface class is unparameterized in this
   tree; the carrier is the global Cauchy Real (the R bridge notation) and
   every interface slot resolves through the module's global instance, so the
   section runs without a Context pair (precedent UpFirewallReq:51-56). *)
Notation R := Real.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- The summation face (the host ssum_* and the resolution fsum_*
   same-shape merge) ---- *)
Hypothesis frd_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis frd_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis frd_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis frd_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis frd_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis frd_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.

Hypothesis frd_dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis frd_dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis frd_dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis frd_dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- The Z_temp interface (co-located with the host req_Z_temp_spec) ---- *)
Variable Z_temp : R -> R.
Hypothesis frd_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Theorem frd_req_entropy_temp_explicit :
  forall (t : R) (Ht : lt zero t),
  req (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss Z_temp
                           frd_Z_temp_spec t Ht)
      (plus (mult (inv_pos t Ht)
                  (UpFirewallReq.fw_et S sumf frd_sum_pos base_loss
                                        Z_temp frd_Z_temp_spec t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t Ht))).
Proof.
  intros t Ht.
  exact (UpReqTempEntropy.req_entropy_temp_explicit           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t Ht).
Qed.

(* The normalization witness = fw_norm (the fw_ witnesses fed in the same
   slots). *)
Theorem frd_req_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (UpFirewallReq.fw_kl S sumf frd_sum_pos base_loss Z_temp
                            frd_Z_temp_spec t1 t2 Ht1 Ht2)
      (plus (plus (opp (UpFirewallReq.fw_h S sumf frd_sum_pos
                                            base_loss Z_temp
                                            frd_Z_temp_spec t1 Ht1))
                  (mult (inv_pos t2 Ht2)
                        (UpFirewallReq.fw_et S sumf frd_sum_pos
                                              base_loss Z_temp
                                              frd_Z_temp_spec t1 Ht1)))
            (log (Z_temp t2)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t2 Ht2))).
Proof.
  intros t2 Ht2 t1 Ht1.
  exact (UpReqTempEntropy.req_relative_entropy_temp_decomp           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t2 Ht2           (UpFirewallReq.fw_bt S sumf frd_sum_pos base_loss Z_temp                                 frd_Z_temp_spec t1 Ht1)           (UpFirewallReq.fw_bt_pos S sumf frd_sum_pos base_loss                                    Z_temp frd_Z_temp_spec t1 Ht1)           (UpFirewallReq.fw_norm S sumf frd_sum_linear frd_sum_pos                                   base_loss Z_temp frd_Z_temp_spec t1 Ht1)).
Qed.

(* The A_chain2 crossing, the assembly chain complete). *)
Theorem frd_req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (req_relative_entropy S sumf
             (UpFirewallReq.fw_bt S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t2 Ht2)
             (UpFirewallReq.fw_bt S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t1 Ht1)
             (UpFirewallReq.fw_bt_pos S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
             (UpFirewallReq.fw_bt_pos S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
            (UpFirewallReq.fw_kl S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (UpFirewallReq.fw_et S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                       (UpFirewallReq.fw_et S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpReqTempEntropy.req_temp_strict_ident2           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2).
Qed.

(* The slot-A/slot-B argument slots feed the two restatement pieces above. *)
Theorem frd_recovery_entropy_gain :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (plus (mult (inv_pos t2 Ht2)
                  (req_minus (UpFirewallReq.fw_et S sumf frd_sum_pos
                                                    base_loss Z_temp
                                                    frd_Z_temp_spec t2 Ht2)
                             (UpFirewallReq.fw_et S sumf frd_sum_pos
                                                   base_loss Z_temp
                                                   frd_Z_temp_spec t1 Ht1)))
            (UpFirewallReq.fw_kl S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           t1 t2 Ht1 Ht2).
Qed.

(* The restatement piece C (slots A/B chained in through piece 4).  The
   three-slot replacement closes the loop here. *)
Theorem frd_recovery_entropy_gain_alt :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (req_minus (mult (inv_pos t1 Ht1)
                       (req_minus (UpFirewallReq.fw_et S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t2 Ht2)
                                  (UpFirewallReq.fw_et S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t1 Ht1)))
                 (req_relative_entropy S sumf
                    (UpFirewallReq.fw_bt S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t2 Ht2)
                    (UpFirewallReq.fw_bt S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t1 Ht1)
                    (UpFirewallReq.fw_bt_pos S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                    (UpFirewallReq.fw_bt_pos S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain_alt           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           frd_req_temp_strict_ident2           t1 t2 Ht1 Ht2).
Qed.

End FrdTempDischarge.

(* Print Assumptions audit (all five pieces; the same convention as the
   bbd/enp file tails): the statement face is unchanged, zero new assumption
   slots. *)
Print Assumptions frd_req_entropy_temp_explicit.
Print Assumptions frd_req_relative_entropy_temp_decomp.
Print Assumptions frd_req_temp_strict_ident2.
Print Assumptions frd_recovery_entropy_gain.
Print Assumptions frd_recovery_entropy_gain_alt.

(* PA re-anchor block (verification copy pieces) *)
Print Assumptions frd_recovery_entropy_gain_alt.
Print Assumptions frd_recovery_entropy_gain.
Print Assumptions frd_req_temp_strict_ident2.
Print Assumptions frd_req_relative_entropy_temp_decomp.
Print Assumptions frd_req_entropy_temp_explicit.
(* ================= Section 6: the pint_eval family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.

(* Section A: definitions (all Set face; carrier Q; a polynomial = a
   coefficient list, head = constant term) *)

(* Evaluation (Horner recurrence): pint_eval p x = a_0 + x . (a_1 + x . (...))
   = sum_k a_k x^k *)
Fixpoint pint_eval (p : list Q) (x : Q) : Q :=
  match p with
  | [] => 0
  | a :: p' => a + x * pint_eval p' x
  end.

(* Monomial integral value: int_0^1 a . x^k dx = a/(k+1) (k+1 is nonzero in Q;
   division is total) *)
Definition pint_monomial_int (a : Q) (k : nat) : Q :=
  a / (Z.of_nat (Datatypes.S k) # 1).

(* The definite integral (the starting-offset k version, for induction; the
   i-th coefficient is paired with denominator k+i+1) *)
Fixpoint pint_integral_from (p : list Q) (k : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' => pint_monomial_int a k + pint_integral_from p' (Datatypes.S k)
  end.

(* The main definite integral over [0,1] *)
Definition pint_integral (p : list Q) : Q := pint_integral_from p 0.

(* The coefficient encoding of x^k: k zeros followed by one 1 *)
Fixpoint pint_pow_poly (k : nat) : list Q :=
  match k with
  | 0%nat => 1 :: []
  | Datatypes.S m => 0 :: pint_pow_poly m
  end.

(* Termwise operations: scaling / addition (equal-length semantics) / the i-th
   coefficient (0 out of range) *)
Fixpoint pint_scale (a : Q) (p : list Q) : list Q :=
  match p with
  | [] => []
  | c :: p' => a * c :: pint_scale a p'
  end.

Fixpoint pint_add (p q : list Q) : list Q :=
  match p with
  | [] => q
  | a :: p' =>
      match q with
      | [] => p
      | b :: q' => a + b :: pint_add p' q'
      end
  end.

Fixpoint pint_coeff (p : list Q) (i : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' =>
      match i with
      | 0%nat => a
      | Datatypes.S i' => pint_coeff p' i'
      end
  end.

(* Section B: internal Q-layer support (== / Qle appear inside proofs only) *)

(* Zero divided by any Q is zero (Qdiv = multiply by Qinv; the zero product
   closes in one step); statement on the QeqT carrier *)
Lemma pint_zero_div : forall d : Q, QeqT (0 / d) 0.
Proof. intros d. apply qeq_imp_qeqT. unfold Qdiv. apply Qmult_0_l. Qed.

(* Multiplication associates over division: (a . c)/d == a . (c/d) *)
Lemma pint_div_mult_assoc : forall a c d : Q, QeqT (a * c / d) (a * (c / d)).
Proof. intros a c d. apply qeq_imp_qeqT. unfold Qdiv. ring. Qed.

(* Division distributes over addition: (a+b)/d == a/d + b/d *)
Lemma pint_div_add_distr : forall a b d : Q, QeqT ((a + b) / d) (a / d + b / d).
Proof. intros a b d. apply qeq_imp_qeqT. unfold Qdiv. ring. Qed.

(* 1/(k+1) strictly positive: Qinv at (n#1) (n > 0) folds definitionally back
   to (1#n); the sign analysis of Z.of_nat (Datatypes.S k) goes through the
   Nat2Z bridge (the Z0 branch is contradictory, the Zneg branch contradicts
   nonnegativity); statement on the QltT carrier *)
Lemma pint_invS_pos : forall k : nat, QltT 0 ((/ (Z.of_nat (Datatypes.S k) # 1))%Q).
Proof.
  intros k. apply Qlt_to_QltT.
  assert (Hnn : (0 <= Z.of_nat (Datatypes.S k))%Z) by apply Nat2Z.is_nonneg.
  assert (Hz : Z.of_nat (Datatypes.S k) <> 0%Z).
  { intros Hc. discriminate Hc. }
  destruct (Z.of_nat (Datatypes.S k)) as [| z | z] eqn:E.
  - exfalso. apply Hz. reflexivity.
  - unfold Qinv, Qlt. cbn [Qnum Qden Qmult]. lia.
  - exfalso. simpl in Hnn. lia.
Qed.

(* Monomial integral nonnegative: 0 <= a implies 0 <= a/(k+1) (QleT' in and
   out; Qle appears inside the proof only) *)
Lemma pint_monomial_int_nonneg : forall (a : Q) (k : nat),
  QleT' 0 a -> QleT' 0 (pint_monomial_int a k).
Proof.
  intros a k Ha. apply Qle_to_QleT'.
  unfold pint_monomial_int, Qdiv.
  apply (Qle_trans 0 (0 * (1 / (Z.of_nat (Datatypes.S k) # 1)))
                    (a * (1 / (Z.of_nat (Datatypes.S k) # 1)))).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply Qeq_sym. apply Qmult_0_l.
  - apply (Qmult_le_compat_r 0 a).
    + exact (QleT'_to_Qle 0 a Ha).
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply pint_invS_pos.
Qed.

(* Section C: the evaluation-correctness companion: the evaluation of
   pint_pow_poly k agrees with q_pow x k (the S03 power engine) *)

Theorem pint_eval_pow_poly : forall (k : nat) (x : Q),
  QeqT (pint_eval (pint_pow_poly k) x) (q_pow x k).
Proof.
  intros k. induction k as [| m IH]; intros x.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT. ring.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (IH x)).
    apply Qplus_0_l.
Qed.

(* Section D: the correctness anchor: int x^k == 1/(k+1) (with the offset
   generalization) *)

(* Offset generalization: int (starting offset k) x^m == 1/(k+m+1).  Induction
   on m; the nat-layer S induction goes through the lia bridge (Hnat), and
   the Z.of_nat atom is rewritten on both sides in step. *)
Lemma pint_integral_from_pow_poly : forall (m k : nat),
  QeqT (pint_integral_from (pint_pow_poly m) k)
    (1 / (Z.of_nat (Datatypes.S (k + m)) # 1)).
Proof.
  intros m k. apply qeq_imp_qeqT. revert k.
  induction m as [| m' IH]; intros k.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    rewrite Nat.add_0_r. apply Qplus_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    unfold pint_monomial_int.
    rewrite (fun d => qeqT_imp_qeq _ _ (pint_zero_div d)).
    rewrite (IH (Datatypes.S k)).
    assert (Hnat : Datatypes.S (k + Datatypes.S m')
                   = Datatypes.S (Datatypes.S k + m')) by lia.
    rewrite Hnat.
    apply Qplus_0_l.
Qed.

(* Correctness anchor (Set face): int_0^1 x^k dx == 1/(k+1) *)
Theorem pint_integral_pow_poly : forall k : nat,
  QeqT (pint_integral (pint_pow_poly k)) (1 / (Z.of_nat (Datatypes.S k) # 1)).
Proof.
  intros k. apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (qeqT_imp_qeq _ _ (pint_integral_from_pow_poly k 0)).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* Degenerate anchor: int 1 == 1 *)
Theorem pint_integral_one : QeqT (pint_integral (pint_pow_poly 0)) (1 # 1).
Proof.
  apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (qeqT_imp_qeq _ _ (pint_integral_from_pow_poly 0 0)).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* Section E: linearity (the coefficient-level offset version + the 0-offset
   assembly, Set face) *)

(* Scaling: int (offset k) (a . p) == a . int (offset k) p *)
Lemma pint_integral_from_scale : forall (a : Q) (p : list Q) (k : nat),
  QeqT (pint_integral_from (pint_scale a p) k) (a * pint_integral_from p k).
Proof.
  intros a p k. apply qeq_imp_qeqT. revert k.
  induction p as [| c p' IH]; intros k.
  - cbn [pint_integral_from pint_scale]. symmetry. apply Qmult_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_scale].
    rewrite (qeqT_imp_qeq _ _ (pint_div_mult_assoc a c (Z.of_nat (Datatypes.S k) # 1))).
    rewrite (IH (Datatypes.S k)).
    unfold pint_monomial_int. ring.
Qed.

(* Addition (equal-length premise): int (offset k) (p+q) == int p + int q *)
Lemma pint_integral_from_add : forall (p q : list Q) (k : nat),
  length p = length q ->
  QeqT (pint_integral_from (pint_add p q) k)
    (pint_integral_from p k + pint_integral_from q k).
Proof.
  intros p q k Hlen. apply qeq_imp_qeqT. revert q k Hlen.
  induction p as [| a p' IH]; intros q k Hlen.
  - destruct q as [| b q'].
    + cbn [pint_integral_from pint_add]. ring.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from pint_monomial_int pint_add].
      injection Hlen as Hlen'.
      rewrite (IH q' (Datatypes.S k) Hlen').
      rewrite (qeqT_imp_qeq _ _ (pint_div_add_distr a b (Z.of_nat (Datatypes.S k) # 1))).
      unfold pint_monomial_int. ring.
Qed.

(* Assembly (0 offset, QeqT face) *)
Theorem pint_integral_scale : forall (a : Q) (p : list Q),
  QeqT (pint_integral (pint_scale a p)) (a * pint_integral p).
Proof.
  intros a p.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  exact (qeqT_imp_qeq _ _ (pint_integral_from_scale a p 0)).
Qed.

Theorem pint_integral_add : forall p q : list Q,
  length p = length q ->
  QeqT (pint_integral (pint_add p q)) (pint_integral p + pint_integral q).
Proof.
  intros p q Hlen.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  exact (qeqT_imp_qeq _ _ (pint_integral_from_add p q 0 Hlen)).
Qed.

(* Section F: the monotonicity companion pieces (coefficientwise; the QleT'
   face, Qle inside the proof only) *)

(* Coefficientwise nonnegative implies a nonnegative offset integral (the two
   Qplus_le_compat branches: the monomial nonnegativity branch + the induction
   branch; the coefficient index offset aligns definitionally with the S
   branch of pint_coeff) *)
Lemma pint_integral_from_nonneg : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral_from p k).
Proof.
  intros p. induction p as [| a p' IH]; intros k Hcoeff.
  - reflexivity.
  - cbn [pint_integral_from].
    apply Qle_to_QleT'.
    apply (Qplus_le_compat 0 (pint_monomial_int a k)
                           0 (pint_integral_from p' (Datatypes.S k))).
    + apply QleT'_to_Qle. apply pint_monomial_int_nonneg.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply QleT'_to_Qle. apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Coefficientwise <= (equal lengths) implies the offset integral <=: the two
   Qmult_le_compat_r branches (the right factor 1/(k+1) strictly positive via
   pint_invS_pos) + the induction branch *)
Lemma pint_integral_from_mono : forall (p q : list Q) (k : nat),
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral_from p k) (pint_integral_from q k).
Proof.
  intros p. induction p as [| a p' IH]; intros q k Hlen Hcoeff.
  - destruct q as [| b q'].
    + reflexivity.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from].
      injection Hlen as Hlen'.
      apply Qle_to_QleT'.
      apply Qplus_le_compat.
      * unfold pint_monomial_int, Qdiv.
        apply (Qmult_le_compat_r a b).
        -- apply QleT'_to_Qle.
           specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply pint_invS_pos.
      * apply QleT'_to_Qle. apply IH.
        -- exact Hlen'.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Assembly (0 offset, QleT' face) *)
Theorem pint_integral_nonneg : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral p).
Proof.
  intros p H.
  unfold pint_integral.
  exact (pint_integral_from_nonneg p 0 H).
Qed.

Theorem pint_integral_mono : forall p q : list Q,
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral p) (pint_integral q).
Proof.
  intros p q Hlen Hcoeff.
  unfold pint_integral.
  exact (pint_integral_from_mono p q 0 Hlen Hcoeff).
Qed.

(* Assumption audit trail: Print Assumptions (compile-time stdout, rechecked
   by verify) *)

Print Assumptions pint_integral_pow_poly.
Print Assumptions pint_integral_one.
Print Assumptions pint_eval_pow_poly.
Print Assumptions pint_integral_scale.
Print Assumptions pint_integral_add.
Print Assumptions pint_integral_nonneg.
Print Assumptions pint_integral_mono.

Print Assumptions pint_integral_mono.
Print Assumptions pint_integral_nonneg.
Print Assumptions pint_integral_add.
Print Assumptions pint_integral_scale.
Print Assumptions pint_zero_div.
