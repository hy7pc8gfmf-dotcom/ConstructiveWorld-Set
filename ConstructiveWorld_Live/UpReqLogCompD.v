(* ConstructiveWorld-Set -- temperature log-free-energy composite family of the generalized mainline. *)

(** * UpReqLogCompD: the log-free-energy and temperature composite surface.

    Mission.  Formalizes the composite family of the generalized mainline:
      Boltzmann weights, partition normalization, free energy over explicit
      sums and the temperature identities, with main statements
      [logc_boltz_log_decomp], [logc_free_energy_boltzmann],
      [logc_fe_kl_decomp], [logc_relative_entropy_temp_decomp],
      [logc_t_sum_plogp].

    Dependencies.  Stdlib [List].  Requires of this development
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpRealLeB], [G05_LogSmall].

    References.  This development, UpReqLogCompD.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqLogCompD.v] compiles cleanly
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
Require Import UpRealLeB.
Require Import G05_LogSmall.
From Stdlib Require Import List.
(* NOTE: no [Import RealInterfaceEnhancedMod] here -- a re-import after
   [G05_LogSmall] would push the boxed class-field projections (plus/mult/...)
   on top of G05_LogSmall's re-pinned field Notations and split the algebra
   face into two heads ([RealInterfaceEnhancedMod.plus] vs [real_plus]) that
   the unifier cannot reconcile; the G05_LogSmall canonical scope is exactly
   the one its own header installs. *)
(* Carrier pinning (the [UpReqAlign3]/[AlignIdUnclosed] precedent): the
   interface class [RealInterfaceEnhancedSetoid] is a zero-argument Class in
   this tree ([S07_RealSetoidExpLog]); the Main-baseline section binder pair
   {R : Set} / {RIS : RealInterfaceEnhancedSetoid R} is carrier-ized away --
   the carrier R is pinned to the global Real by the Notation below and the
   interface fields resolve through the global instance [RealEnhancedReal]
   (concretely via the field Notations re-exported by [G05_LogSmall], here
   completed with the six field names G05 does not re-export, each bound to
   its top-level [real_]* global).  Zero Obj.magic, zero Prop casts;
   statement names verbatim unchanged. *)
Notation R := Real.
Notation req_mult_compat := RealSetoid.real_eq_mult_compat_adapt.
Notation mult_assoc := real_mult_assoc.
Notation mult_one := real_mult_one.
Notation mult_zero := real_mult_zero.
Notation distrib := real_distrib.
Notation inv_pos_pos := real_inv_pos_pos.

(* ============================================================ *)
(* Part 0: the shared req algebra toolkit (generic RIS; shared by all sections).                              *)
(* ============================================================ *)

Section LogcAlg.
(* binder pair {R : Set} {RIS : RealInterfaceEnhancedSetoid R} carrier-ized
   away (zero-argument Class in this tree; R := Real pinned file-top). *)

(* A1: the left form of mult one, from the right-form field [mult_one] plus commutativity. *)
Lemma logc_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

(* A2: [mult a (opp b)] equals [opp (mult a b)] by distributivity, [mult_zero] and zero cancellation. *)
Lemma logc_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (logd_req_plus_zero_r (mult a b) (mult a (opp b))).
  apply (req_trans (plus (mult a b) (mult a (opp b)))
                   (mult a (plus b (opp b))) zero).
  - apply req_sym. exact (distrib a b (opp b)).
  - apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
    + apply (req_mult_compat a a (plus b (opp b)) zero (req_refl a) (plus_opp b)).
    + exact (mult_zero a).
Qed.

(* A3: [mult (opp a) b] equals [opp (mult a b)], dual to A2 plus commutativity. *)
Lemma logc_mult_opp_r : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - exact (mult_comm (opp a) b).
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + exact (logc_mult_opp_l b a).
    + apply req_opp_compat. exact (mult_comm b a).
Qed.

(* A4: negation distributes over addition, [opp (plus a b)] equals [plus (opp a) (opp b)], by a zero-cancellation construction. *)
Lemma logc_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply req_sym.
  apply (logd_req_plus_zero_r (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (plus a b) (plus (opp a) (opp b)))
                   (plus a (plus b (plus (opp a) (opp b)))) zero).
  - apply req_sym. exact (plus_assoc a b (plus (opp a) (opp b))).
  - apply (req_trans (plus a (plus b (plus (opp a) (opp b))))
                     (plus a (plus (plus b (opp a)) (opp b))) zero).
    + apply (req_plus_compat a a (plus b (plus (opp a) (opp b)))
                              (plus (plus b (opp a)) (opp b))).
      * apply req_refl.
      * exact (plus_assoc b (opp a) (opp b)).
    + apply (req_trans (plus a (plus (plus b (opp a)) (opp b)))
                       (plus (plus a (plus b (opp a))) (opp b)) zero).
      * exact (plus_assoc a (plus b (opp a)) (opp b)).
      * apply (req_trans (plus (plus a (plus b (opp a))) (opp b))
                         (plus (plus a (plus (opp a) b)) (opp b)) zero).
        -- apply (req_plus_compat (plus a (plus b (opp a)))
                     (plus a (plus (opp a) b)) (opp b) (opp b)).
           ++ apply (req_plus_compat a a (plus b (opp a)) (plus (opp a) b)).
              ** apply req_refl.
              ** exact (plus_comm b (opp a)).
           ++ apply req_refl.
        -- apply (req_trans (plus (plus a (plus (opp a) b)) (opp b))
                            (plus (plus (plus a (opp a)) b) (opp b)) zero).
           ++ apply (req_plus_compat (plus a (plus (opp a) b))
                        (plus (plus a (opp a)) b) (opp b) (opp b)).
              ** exact (plus_assoc a (opp a) b).
              ** apply req_refl.
           ++ apply (req_trans (plus (plus (plus a (opp a)) b) (opp b))
                               (plus (plus a (opp a)) (plus b (opp b))) zero).
              ** apply req_sym. exact (plus_assoc (plus a (opp a)) b (opp b)).
              ** apply (req_trans (plus (plus a (opp a)) (plus b (opp b)))
                                  (plus zero zero) zero).
                 --- apply (req_plus_compat (plus a (opp a)) zero
                               (plus b (opp b)) zero (plus_opp a) (plus_opp b)).
                 --- exact (plus_zero zero).
Qed.

(* A5: [plus u (plus w (opp u))] equals [w] by commutativity, associativity and cancellation. *)
Lemma logc_plus_assoc_cancel : forall u w : R, req (plus u (plus w (opp u))) w.
Proof.
  intros u w.
  apply (req_trans (plus u (plus w (opp u))) (plus (plus u w) (opp u)) w).
  - exact (plus_assoc u w (opp u)).
  - apply (req_trans (plus (plus u w) (opp u)) (plus (plus w u) (opp u)) w).
    + apply (req_plus_compat (plus u w) (plus w u) (opp u) (opp u)
                (plus_comm u w) (req_refl (opp u))).
    + apply (req_trans (plus (plus w u) (opp u)) (plus w (plus u (opp u))) w).
      * apply req_sym. exact (plus_assoc w u (opp u)).
      * apply (req_trans (plus w (plus u (opp u))) (plus w zero) w).
        -- apply (req_plus_compat w w (plus u (opp u)) zero
                     (req_refl w) (plus_opp u)).
        -- exact (plus_zero w).
Qed.

(* A6: if [v] equals [plus u w] then [plus (opp u) v] equals [w], cancellation of the subtracted term and the numeric core of slot 7. *)
Lemma logc_cancel_left : forall u v w : R,
  req v (plus u w) -> req (plus (opp u) v) w.
Proof.
  intros u v w H.
  apply (req_trans (plus (opp u) v)
                   (plus (opp u) (plus w (opp (opp u)))) w).
  - apply (req_plus_compat (opp u) (opp u) v (plus w (opp (opp u)))
              (req_refl (opp u))).
    apply (req_trans v (plus u w) (plus w (opp (opp u)))).
    + exact H.
    + apply (req_trans (plus u w) (plus w u) (plus w (opp (opp u)))).
      * exact (plus_comm u w).
      * apply (req_plus_compat w w u (opp (opp u)) (req_refl w)).
        apply req_sym. exact (logd_req_opp_opp u).
  - exact (logc_plus_assoc_cancel (opp u) w).
Qed.

End LogcAlg.

(* ============================================================ *)
(* Part 1: the FEP composite section (slots 1/2/4; supplied in the same form as the UpSigMigrate section).                  *)
(* ============================================================ *)

Section LogcFEP.
(* binder pair {R : Set} {RIS : RealInterfaceEnhancedSetoid R} carrier-ized
   away (zero-argument Class in this tree; R := Real pinned file-top). *)
Variable S : Type.

(* the three sum-algebra slots, at the same position as the UpSigMigrate SumOver setoid interface. *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
(* the partition condition, an explicit supply slot with N an explicit argument, verbatim from the G5 conclusion table. *)
Hypothesis fep_partition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* the B1/B2 supply slots (G5 conclusion table; the Real-level closures are           *)
(*   [logd_log_compat_real] and [logd_log_exp_neg_real]). *)
Hypothesis sup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis sup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* section-local definitions, in the conventional UpSigMigrate form. *)
Definition logc_posd (p : S -> R) : Type := forall s : S, lt zero (p s).
Definition logc_boltz (s : S) : R :=
  mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Lemma logc_boltz_pos : logc_posd logc_boltz.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.
Definition logc_fe (p : S -> R) (Hp : logc_posd p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).

(* F1: right linearity of the sum, the dual of [sum_linear] in the [mult (f s) a] form. *)
Lemma logc_sum_linear_r : forall (a : R) (f : S -> R),
  req (sumf (fun s => mult (f s) a)) (mult (sumf f) a).
Proof.
  intros a f.
  apply (req_trans (sumf (fun s => mult (f s) a))
                   (sumf (fun s => mult a (f s))) (mult (sumf f) a)).
  - apply sum_ext. intro s. exact (mult_comm (f s) a).
  - apply (req_trans (sumf (fun s => mult a (f s)))
                     (mult a (sumf f)) (mult (sumf f) a)).
    + exact (sum_linear a f).
    + exact (mult_comm a (sumf f)).
Qed.

(* F2: negation commutes with the sum, the sum of [opp f] equals [opp (sumf f)], via the [opp one] numeric route. *)
Lemma logc_sum_opp : forall f : S -> R,
  req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s))) (opp (sumf f))).
  - apply sum_ext. intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply req_opp_compat.
      exact (req_sym (mult one (f s)) (f s) (logc_mult_one_l (f s))).
    + apply req_sym. exact (logc_mult_opp_r one (f s)).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f)) (opp (sumf f))).
    + exact (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f))
                       (opp (mult one (sumf f))) (opp (sumf f))).
      * exact (logc_mult_opp_r one (sumf f)).
      * apply req_opp_compat. exact (logc_mult_one_l (sumf f)).
Qed.


Lemma logc_boltz_log_decomp : forall s : S,
  req (log (logc_boltz s) (logc_boltz_pos s))
      (plus (opp (log Z Z_pos))
            (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intro s.
  apply (req_trans (log (logc_boltz s) (logc_boltz_pos s))
                   (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                         (log (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                              (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                   (plus (opp (log Z Z_pos))
                         (opp (mult (inv_pos D D_pos) (base_loss s))))).
  - exact (log_mult (inv_pos Z Z_pos)
                    (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                    (inv_pos_pos Z Z_pos)
                    (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))).
  - apply req_plus_compat.
    + exact (logd_log_inv_one_inv_of_compat sup_compat Z Z_pos
               (inv_pos_pos Z Z_pos)).
    + exact (sup_log_exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* F4: Boltzmann normalization, the sum of the weights equals one, from the partition condition, [sum_linear] and [inv_pos_correct]. *)
Lemma logc_boltzmann_normalized : req (sumf logc_boltz) one.
Proof.
  apply (req_trans (sumf logc_boltz)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg
                                   (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
             (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg
                                      (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z) one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
               (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z
               (req_refl (inv_pos Z Z_pos))).
      apply req_sym. exact fep_partition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z)
                       (mult Z (inv_pos Z Z_pos)) one).
      * exact (mult_comm (inv_pos Z Z_pos) Z).
      * exact (inv_pos_correct Z Z_pos).
Qed.


(*   the req signature assembled independently of the Id-carried original [energy_in_log_boltzmann]    *)
Lemma logc_energy_in_log_boltzmann : forall s : S,
  req (base_loss s)
      (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                         (log Z Z_pos)))).
Proof.
  intro s.
  assert (Hsum : req (plus (log (logc_boltz s) (logc_boltz_pos s)) (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
  { apply (req_trans (plus (log (logc_boltz s) (logc_boltz_pos s)) (log Z Z_pos))
                     (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
    - apply (req_plus_compat (log (logc_boltz s) (logc_boltz_pos s))
               (plus (opp (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s))))
               (log Z Z_pos) (log Z Z_pos)).
      + exact (logc_boltz_log_decomp s).
      + apply req_refl.
    - apply (req_trans (plus (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos))
                       (plus (opp (log Z Z_pos))
                             (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                   (log Z Z_pos)))
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
      + apply req_sym.
        exact (plus_assoc (opp (log Z Z_pos))
               (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z Z_pos)).
      + apply (req_trans (plus (opp (log Z Z_pos))
                               (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                     (log Z Z_pos)))
                         (plus (opp (log Z Z_pos))
                               (plus (log Z Z_pos)
                                     (opp (mult (inv_pos D D_pos) (base_loss s)))))
                         (opp (mult (inv_pos D D_pos) (base_loss s)))).
        * apply (req_plus_compat (opp (log Z Z_pos)) (opp (log Z Z_pos))
                   (plus (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z Z_pos))
                   (plus (log Z Z_pos) (opp (mult (inv_pos D D_pos) (base_loss s))))).
          -- apply req_refl.
          -- exact (plus_comm (opp (mult (inv_pos D D_pos) (base_loss s)))
                              (log Z Z_pos)).
        * apply (req_trans (plus (opp (log Z Z_pos))
                                 (plus (log Z Z_pos)
                                       (opp (mult (inv_pos D D_pos) (base_loss s)))))
                           (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (opp (mult (inv_pos D D_pos) (base_loss s)))).
          -- apply (req_trans (plus (opp (log Z Z_pos))
                                    (plus (log Z Z_pos)
                                          (opp (mult (inv_pos D D_pos)
                                                     (base_loss s)))))
                              (plus (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                    (opp (mult (inv_pos D D_pos) (base_loss s))))
                              (plus zero (opp (mult (inv_pos D D_pos)
                                                   (base_loss s))))).
             ++ exact (plus_assoc (opp (log Z Z_pos)) (log Z Z_pos)
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
             ++ apply (req_plus_compat (plus (opp (log Z Z_pos)) (log Z Z_pos))
                        zero
                        (opp (mult (inv_pos D D_pos) (base_loss s)))
                        (opp (mult (inv_pos D D_pos) (base_loss s)))).
                ** exact (req_trans (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                    (plus (log Z Z_pos) (opp (log Z Z_pos)))
                                    zero
                                    (plus_comm (opp (log Z Z_pos))
                                               (log Z Z_pos))
                                    (plus_opp (log Z Z_pos))).
                ** apply req_refl.
          -- exact (logd_req_plus_zero_l
                      (opp (mult (inv_pos D D_pos) (base_loss s)))). }
  apply (req_sym (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                     (log Z Z_pos))))
                 (base_loss s)).
  apply (req_trans (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                      (log Z Z_pos))))
                   (opp (opp (base_loss s))) (base_loss s)).
  - apply req_opp_compat.
    apply (req_trans (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                   (log Z Z_pos)))
                     (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                     (opp (base_loss s))).
    + apply (req_mult_compat D D
               (plus (log (logc_boltz s) (logc_boltz_pos s)) (log Z Z_pos))
               (opp (mult (inv_pos D D_pos) (base_loss s)))
               (req_refl D) Hsum).
    + apply (req_trans (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (base_loss s))).
      * exact (logc_mult_opp_l D (mult (inv_pos D D_pos) (base_loss s))).
      * apply req_opp_compat.
        apply (req_trans (mult D (mult (inv_pos D D_pos) (base_loss s)))
                         (mult (mult D (inv_pos D D_pos)) (base_loss s))
                         (base_loss s)).
        -- exact (mult_assoc D (inv_pos D D_pos) (base_loss s)).
        -- apply (req_trans (mult (mult D (inv_pos D D_pos)) (base_loss s))
                            (mult one (base_loss s)) (base_loss s)).
           ++ apply (req_mult_compat (mult D (inv_pos D D_pos)) one
                        (base_loss s) (base_loss s)
                        (inv_pos_correct D D_pos) (req_refl (base_loss s))).
           ++ exact (logc_mult_one_l (base_loss s)).
  - exact (logd_req_opp_opp (base_loss s)).
Qed.

(* F6: the pointwise two-term decomposition of q times energy, valid for any positive distribution [q], with [D] transported unchanged throughout. *)
Lemma logc_pt_energy_point : forall (q : S -> R) (Hq : logc_posd q) (s : S),
  req (mult (q s) (base_loss s))
      (opp (plus (mult D (mult (q s) (log (logc_boltz s) (logc_boltz_pos s))))
                 (mult D (mult (q s) (log Z Z_pos))))).
Proof.
  intros q Hq s.
  apply (req_trans (mult (q s) (base_loss s))
                   (mult (q s) (opp (mult D (plus (log (logc_boltz s)
                                                    (logc_boltz_pos s))
                                                   (log Z Z_pos)))))
                   (opp (plus (mult D (mult (q s)
                                             (log (logc_boltz s)
                                                  (logc_boltz_pos s))))
                              (mult D (mult (q s) (log Z Z_pos)))))).
  - apply (req_mult_compat (q s) (q s) (base_loss s)
             (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                (log Z Z_pos))))
             (req_refl (q s))).
    exact (logc_energy_in_log_boltzmann s).
  - apply (req_trans (mult (q s) (opp (mult D (plus (log (logc_boltz s)
                                                      (logc_boltz_pos s))
                                                     (log Z Z_pos)))))
                     (opp (mult (q s) (mult D (plus (log (logc_boltz s)
                                                      (logc_boltz_pos s))
                                                     (log Z Z_pos)))))
                     (opp (plus (mult D (mult (q s)
                                               (log (logc_boltz s)
                                                    (logc_boltz_pos s))))
                                (mult D (mult (q s) (log Z Z_pos)))))).
    + exact (logc_mult_opp_l (q s)
               (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                             (log Z Z_pos)))).
    + apply (req_trans (opp (mult (q s) (mult D (plus (log (logc_boltz s)
                                                        (logc_boltz_pos s))
                                                       (log Z Z_pos)))))
                       (opp (mult D (mult (q s)
                                           (plus (log (logc_boltz s)
                                                  (logc_boltz_pos s))
                                                 (log Z Z_pos)))))
                       (opp (plus (mult D (mult (q s)
                                                 (log (logc_boltz s)
                                                      (logc_boltz_pos s))))
                                  (mult D (mult (q s) (log Z Z_pos)))))).
      * apply req_opp_compat.
        apply (req_trans (mult (q s) (mult D (plus (log (logc_boltz s)
                                                     (logc_boltz_pos s))
                                                    (log Z Z_pos))))
                         (mult (mult (q s) D)
                               (plus (log (logc_boltz s) (logc_boltz_pos s))
                                     (log Z Z_pos)))
                         (mult D (mult (q s)
                                       (plus (log (logc_boltz s)
                                                  (logc_boltz_pos s))
                                                 (log Z Z_pos))))).
        -- exact (mult_assoc (q s) D
                       (plus (log (logc_boltz s) (logc_boltz_pos s))
                             (log Z Z_pos))).
        -- apply (req_trans (mult (mult (q s) D)
                                  (plus (log (logc_boltz s)
                                             (logc_boltz_pos s))
                                        (log Z Z_pos)))
                            (mult (mult D (q s))
                                  (plus (log (logc_boltz s)
                                             (logc_boltz_pos s))
                                        (log Z Z_pos)))
                            (mult D (mult (q s)
                                          (plus (log (logc_boltz s)
                                                     (logc_boltz_pos s))
                                                (log Z Z_pos))))).
           ++ apply (req_mult_compat (mult (q s) D) (mult D (q s))
                        (plus (log (logc_boltz s) (logc_boltz_pos s))
                              (log Z Z_pos))
                        (plus (log (logc_boltz s) (logc_boltz_pos s))
                              (log Z Z_pos))
                        (mult_comm (q s) D)
                        (req_refl (plus (log (logc_boltz s)
                                          (logc_boltz_pos s))
                                        (log Z Z_pos)))).
           ++ apply req_sym. exact (mult_assoc D (q s)
                        (plus (log (logc_boltz s) (logc_boltz_pos s))
                              (log Z Z_pos))).
      * apply req_opp_compat.
        apply (req_trans (mult D (mult (q s)
                                        (plus (log (logc_boltz s)
                                                   (logc_boltz_pos s))
                                                  (log Z Z_pos))))
                         (mult D (plus (mult (q s)
                                             (log (logc_boltz s)
                                                  (logc_boltz_pos s)))
                                       (mult (q s) (log Z Z_pos))))
                         (plus (mult D (mult (q s)
                                             (log (logc_boltz s)
                                                  (logc_boltz_pos s))))
                               (mult D (mult (q s) (log Z Z_pos))))).
        -- apply (req_mult_compat D D
                       (mult (q s) (plus (log (logc_boltz s)
                                                  (logc_boltz_pos s))
                                                (log Z Z_pos)))
                       (plus (mult (q s) (log (logc_boltz s)
                                                (logc_boltz_pos s)))
                             (mult (q s) (log Z Z_pos)))
                       (req_refl D)
                       (distrib (q s) (log (logc_boltz s) (logc_boltz_pos s))
                          (log Z Z_pos))).
        -- exact (distrib D (mult (q s) (log (logc_boltz s) (logc_boltz_pos s)))
                    (mult (q s) (log Z Z_pos))).
Qed.


Lemma logc_boltz_energy_sum :
  req (sumf (fun s => mult (logc_boltz s) (base_loss s)))
      (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                (log (logc_boltz s) (logc_boltz_pos s))))))
            (opp (mult D (log Z Z_pos)))).
Proof.
  set (LB := fun s : S => log (logc_boltz s) (logc_boltz_pos s)).
  set (A := fun s : S => mult D (mult (logc_boltz s) (LB s))).
  set (Bs := fun s : S => mult D (mult (logc_boltz s) (log Z Z_pos))).
  apply (req_trans (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                   (opp (sumf (fun s : S => plus (A s) (Bs s))))
                   (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                             (LB s)))))
                         (opp (mult D (log Z Z_pos))))).
  - apply (req_trans (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                     (sumf (fun s : S => opp (plus (A s) (Bs s))))
                     (opp (sumf (fun s : S => plus (A s) (Bs s))))).
    + apply sum_ext. intro s.
      exact (logc_pt_energy_point logc_boltz logc_boltz_pos s).
    + exact (logc_sum_opp (fun s : S => plus (A s) (Bs s))).
  - apply (req_trans (opp (sumf (fun s : S => plus (A s) (Bs s))))
                     (opp (plus (sumf A) (sumf Bs)))
                     (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                               (LB s)))))
                           (opp (mult D (log Z Z_pos))))).
    + apply req_opp_compat. exact (sum_add A Bs).
    + apply (req_trans (opp (plus (sumf A) (sumf Bs)))
                       (plus (opp (sumf A)) (opp (sumf Bs)))
                       (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                                 (LB s)))))
                             (opp (mult D (log Z Z_pos))))).
        * exact (logc_opp_plus (sumf A) (sumf Bs)).
        * apply req_plus_compat.
          -- apply req_opp_compat.
             exact (sum_linear D (fun s : S => mult (logc_boltz s) (LB s))).
          -- apply req_opp_compat.
             apply (req_trans (sumf Bs)
                              (mult D (sumf (fun s : S => mult (logc_boltz s)
                                                (log Z Z_pos))))
                              (mult D (log Z Z_pos))).
             ++ exact (sum_linear D
                          (fun s : S => mult (logc_boltz s) (log Z Z_pos))).
             ++ apply (req_mult_compat D D
                          (sumf (fun s => mult (logc_boltz s) (log Z Z_pos)))
                          (log Z Z_pos) (req_refl D)).
                ** apply (req_trans (sumf (fun s => mult (logc_boltz s)
                                            (log Z Z_pos)))
                                    (mult (sumf logc_boltz) (log Z Z_pos))
                                    (log Z Z_pos)).
                   --- exact (logc_sum_linear_r (log Z Z_pos) logc_boltz).
                   --- apply (req_trans (mult (sumf logc_boltz) (log Z Z_pos))
                                        (mult one (log Z Z_pos))
                                        (log Z Z_pos)).
                      +++ apply (req_mult_compat (sumf logc_boltz) one
                                    (log Z Z_pos) (log Z Z_pos)
                                    logc_boltzmann_normalized
                                    (req_refl (log Z Z_pos))).
                      +++ exact (logc_mult_one_l (log Z Z_pos)).
Qed.


(*   the req signature assembled independently of the Id-carried original [free_energy_boltzmann]      *)
Lemma logc_free_energy_boltzmann :
  req (logc_fe logc_boltz logc_boltz_pos) (mult (opp D) (log Z Z_pos)).
Proof.
  set (LB := fun s : S => log (logc_boltz s) (logc_boltz_pos s)).
  set (S1 := mult D (sumf (fun s : S => mult (logc_boltz s) (LB s)))).
  assert (HoppS1 : req (plus (opp S1) S1) zero).
  { apply (req_trans (plus (opp S1) S1) (plus S1 (opp S1)) zero).
    - exact (plus_comm (opp S1) S1).
    - exact (plus_opp S1). }
  assert (HFE : req (logc_fe logc_boltz logc_boltz_pos)
                    (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)).
  { apply (req_trans (logc_fe logc_boltz logc_boltz_pos)
                     (plus (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                           S1)
                     (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)).
    - apply req_refl.
    - apply (req_plus_compat (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                (opp (plus S1 (mult D (log Z Z_pos)))) S1 S1).
      + apply (req_trans (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                         (plus (opp S1) (opp (mult D (log Z Z_pos))))
                         (opp (plus S1 (mult D (log Z Z_pos))))).
        * exact logc_boltz_energy_sum.
        * apply req_sym. exact (logc_opp_plus S1 (mult D (log Z Z_pos))).
      + apply req_refl. }
  apply (req_trans (logc_fe logc_boltz logc_boltz_pos)
                   (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)
                   (mult (opp D) (log Z Z_pos))).
  - exact HFE.
  - apply (req_trans (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)
                     (plus (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1)
                     (mult (opp D) (log Z Z_pos))).
    + apply (req_plus_compat (opp (plus S1 (mult D (log Z Z_pos))))
                (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1 S1).
      * exact (logc_opp_plus S1 (mult D (log Z Z_pos))).
      * apply req_refl.
    + apply (req_trans (plus (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1)
                       (plus (opp (mult D (log Z Z_pos))) zero)
                       (mult (opp D) (log Z Z_pos))).
      * apply (req_trans (plus (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1)
                         (plus (opp S1) (plus (opp (mult D (log Z Z_pos))) S1))
                         (plus (opp (mult D (log Z Z_pos))) zero)).
        -- apply req_sym.
           exact (plus_assoc (opp S1) (opp (mult D (log Z Z_pos))) S1).
        -- apply (req_trans (plus (opp S1)
                                  (plus (opp (mult D (log Z Z_pos))) S1))
                            (plus (opp S1)
                                  (plus S1 (opp (mult D (log Z Z_pos)))))
                            (plus (opp (mult D (log Z Z_pos))) zero)).
           ++ apply (req_plus_compat (opp S1) (opp S1)
                        (plus (opp (mult D (log Z Z_pos))) S1)
                        (plus S1 (opp (mult D (log Z Z_pos))))
                        (req_refl (opp S1))
                        (plus_comm (opp (mult D (log Z Z_pos))) S1)).
           ++ apply (req_trans (plus (opp S1)
                                     (plus S1 (opp (mult D (log Z Z_pos)))))
                               (plus (plus (opp S1) S1)
                                     (opp (mult D (log Z Z_pos))))
                               (plus (opp (mult D (log Z Z_pos))) zero)).
              ** exact (plus_assoc (opp S1) S1 (opp (mult D (log Z Z_pos)))).
              ** apply (req_trans (plus (plus (opp S1) S1)
                                          (opp (mult D (log Z Z_pos))))
                                  (plus zero (opp (mult D (log Z Z_pos))))
                                  (plus (opp (mult D (log Z Z_pos))) zero)).
                 --- apply (req_plus_compat (plus (opp S1) S1) zero
                           (opp (mult D (log Z Z_pos)))
                           (opp (mult D (log Z Z_pos)))
                           HoppS1 (req_refl (opp (mult D (log Z Z_pos))))).
                 --- exact (plus_comm zero (opp (mult D (log Z Z_pos)))).
      * apply (req_trans (plus (opp (mult D (log Z Z_pos))) zero)
                         (opp (mult D (log Z Z_pos)))
                         (mult (opp D) (log Z Z_pos))).
        -- exact (plus_zero (opp (mult D (log Z Z_pos)))).
        -- apply req_sym. exact (logc_mult_opp_r D (log Z Z_pos)).
Qed.



(* F9, the slot-4 resolution at the req layer: the FEP decomposition F[p] equals F[p_b] plus D times the summed KL terms, in minus form.       *)
Lemma logc_fe_kl_decomp : forall (p : S -> R) (Hp : logc_posd p)
    (Hnormp : req (sumf p) one),
  req (logc_fe p Hp)
      (plus (logc_fe logc_boltz logc_boltz_pos)
            (mult D (sumf (fun s => mult (p s)
                             (plus (log (p s) (Hp s))
                                   (opp (log (logc_boltz s)
                                             (logc_boltz_pos s)))))))).
Proof.
  intros p Hp Hnormp.
  set (Lb := fun s : S => log (logc_boltz s) (logc_boltz_pos s)).
  set (Lp := fun s : S => log (p s) (Hp s)).
  set (U := mult D (sumf (fun s => mult (p s) (Lp s)))).
  set (V := mult D (sumf (fun s => mult (p s) (Lb s)))).
  set (W := mult D (log Z Z_pos)).
  (* Hpe: the summed energy equals [opp (plus V W)], from pointwise F6, the three sum bridges and Hnormp as a premise. *)
  assert (Hpe : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp V) (opp W))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (opp (sumf (fun s => plus (mult D (mult (p s) (Lb s)))
                                                (mult D (mult (p s)
                                                           (log Z Z_pos))))))
                     (plus (opp V) (opp W))).
    - apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                       (sumf (fun s => opp (plus (mult D (mult (p s) (Lb s)))
                                                 (mult D (mult (p s)
                                                            (log Z Z_pos))))))
                       (opp (sumf (fun s => plus (mult D (mult (p s) (Lb s)))
                                                  (mult D (mult (p s)
                                                             (log Z Z_pos))))))).
      + apply sum_ext. intro s. exact (logc_pt_energy_point p Hp s).
      + exact (logc_sum_opp (fun s => plus (mult D (mult (p s) (Lb s)))
                                (mult D (mult (p s) (log Z Z_pos))))).
    - apply (req_trans (opp (sumf (fun s => plus (mult D (mult (p s) (Lb s)))
                                  (mult D (mult (p s) (log Z Z_pos))))))
                       (opp (plus (sumf (fun s => mult D (mult (p s) (Lb s))))
                                  (sumf (fun s => mult D (mult (p s)
                                                             (log Z Z_pos))))))
                       (plus (opp V) (opp W))).
      + apply req_opp_compat.
        exact (sum_add (fun s => mult D (mult (p s) (Lb s)))
                       (fun s => mult D (mult (p s) (log Z Z_pos)))).
      + apply (req_trans (opp (plus (sumf (fun s => mult D (mult (p s) (Lb s))))
                                    (sumf (fun s => mult D (mult (p s)
                                                           (log Z Z_pos))))))
                         (plus (opp (sumf (fun s => mult D (mult (p s) (Lb s)))))
                               (opp (sumf (fun s => mult D (mult (p s)
                                                          (log Z Z_pos))))))
                         (plus (opp V) (opp W))).
        * exact (logc_opp_plus (sumf (fun s => mult D (mult (p s) (Lb s))))
                    (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))).
        * apply req_plus_compat.
          -- apply req_opp_compat.
             exact (sum_linear D (fun s => mult (p s) (Lb s))).
          -- apply req_opp_compat.
             apply (req_trans (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                              (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                              (mult D (log Z Z_pos))).
             ++ exact (sum_linear D (fun s => mult (p s) (log Z Z_pos))).
             ++ apply (req_mult_compat D D
                          (sumf (fun s => mult (p s) (log Z Z_pos)))
                          (log Z Z_pos) (req_refl D)).
                ** apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                    (mult (sumf p) (log Z Z_pos)) (log Z Z_pos)).
                   --- exact (logc_sum_linear_r (log Z Z_pos) p).
                   --- apply (req_trans (mult (sumf p) (log Z Z_pos))
                                        (mult one (log Z Z_pos))
                                        (log Z Z_pos)).
                      +++ apply (req_mult_compat (sumf p) one
                                    (log Z Z_pos) (log Z Z_pos)
                                    Hnormp (req_refl (log Z Z_pos))).
                      +++ exact (logc_mult_one_l (log Z Z_pos)). }
  (* F[p] ≡ (opp V + opp W) + U *)
  assert (HFEp : req (logc_fe p Hp) (plus (plus (opp V) (opp W)) U)).
  { apply (req_trans (logc_fe p Hp)
                     (plus (sumf (fun s => mult (p s) (base_loss s)))
                           (mult D (sumf (fun s => mult (p s) (Lp s)))))
                     (plus (plus (opp V) (opp W)) U)).
    - apply req_refl.
    - apply (req_trans (plus (sumf (fun s => mult (p s) (base_loss s)))
                             (mult D (sumf (fun s => mult (p s) (Lp s)))))
                       (plus (plus (opp V) (opp W))
                             (mult D (sumf (fun s => mult (p s) (Lp s)))))
                       (plus (plus (opp V) (opp W)) U)).
      + apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s)))
                  (plus (opp V) (opp W))
                  (mult D (sumf (fun s => mult (p s) (Lp s))))
                  (mult D (sumf (fun s => mult (p s) (Lp s))))).
        * exact Hpe.
        * apply req_refl.
      + apply req_refl. }
  
  assert (Hkl : req (mult D (sumf (fun s => mult (p s) (plus (Lp s) (opp (Lb s))))))
                    (plus U (opp V))).
  { set (K := fun s : S => mult (p s) (plus (Lp s) (opp (Lb s)))).
    set (K2 := fun s : S => plus (mult (p s) (Lp s))
                                 (opp (mult (p s) (Lb s)))).
    assert (Hper : forall s : S, req (K s) (K2 s)).
    { intro s.
      apply (req_trans (K s)
                       (plus (mult (p s) (Lp s)) (mult (p s) (opp (Lb s))))
                       (K2 s)).
      - exact (distrib (p s) (Lp s) (opp (Lb s))).
      - apply (req_plus_compat (mult (p s) (Lp s)) (mult (p s) (Lp s))
                  (mult (p s) (opp (Lb s))) (opp (mult (p s) (Lb s)))
                  (req_refl (mult (p s) (Lp s)))).
        exact (logc_mult_opp_l (p s) (Lb s)). }
    apply (req_trans (mult D (sumf K)) (mult D (sumf K2)) (plus U (opp V))).
    - apply (req_mult_compat D D (sumf K) (sumf K2) (req_refl D)).
      apply sum_ext. intro s. exact (Hper s).
    - apply (req_trans (mult D (sumf K2))
                       (plus (mult D (sumf (fun s => mult (p s) (Lp s))))
                             (mult D (sumf (fun s => opp (mult (p s) (Lb s))))))
                       (plus U (opp V))).
      + apply (req_trans (mult D (sumf K2))
                         (mult D (plus (sumf (fun s => mult (p s) (Lp s)))
                                       (sumf (fun s => opp (mult (p s) (Lb s))))))
                         (plus (mult D (sumf (fun s => mult (p s) (Lp s))))
                               (mult D (sumf (fun s => opp (mult (p s) (Lb s))))))).
        * apply (req_mult_compat D D (sumf K2)
                    (plus (sumf (fun s => mult (p s) (Lp s)))
                          (sumf (fun s => opp (mult (p s) (Lb s)))))
                    (req_refl D)).
          exact (sum_add (fun s => mult (p s) (Lp s))
                         (fun s => opp (mult (p s) (Lb s)))).
        * exact (distrib D (sumf (fun s => mult (p s) (Lp s)))
                    (sumf (fun s => opp (mult (p s) (Lb s))))).
      + apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (Lp s))))
                  U
                  (mult D (sumf (fun s => opp (mult (p s) (Lb s)))))
                  (opp (mult D (sumf (fun s => mult (p s) (Lb s)))))).
        * apply req_refl.
        * apply (req_trans (mult D (sumf (fun s => opp (mult (p s) (Lb s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (Lb s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (Lb s)))))).
          -- apply (req_mult_compat D D
                        (sumf (fun s => opp (mult (p s) (Lb s))))
                        (opp (sumf (fun s => mult (p s) (Lb s))))
                        (req_refl D)).
             exact (logc_sum_opp (fun s => mult (p s) (Lb s))).
          -- exact (logc_mult_opp_l D (sumf (fun s => mult (p s) (Lb s)))).
}
  (* assembly: F[p] equals (oppV + oppW) + U, regrouped as oppW + (U + oppV), which equals F[b] plus D times KL. *)
  apply (req_trans (logc_fe p Hp) (plus (plus (opp V) (opp W)) U)
                   (plus (logc_fe logc_boltz logc_boltz_pos)
                         (mult D (sumf (fun s => mult (p s)
                                          (plus (Lp s) (opp (Lb s)))))))).
  - exact HFEp.
  - apply (req_trans (plus (plus (opp V) (opp W)) U)
                     (plus (opp W) (plus U (opp V)))
                     (plus (logc_fe logc_boltz logc_boltz_pos)
                           (mult D (sumf (fun s => mult (p s)
                                            (plus (Lp s) (opp (Lb s)))))))).
    + (* the five-step permutation from (oppV + oppW) + U to oppW + (U + oppV). *)
      apply (req_trans (plus (plus (opp V) (opp W)) U)
                       (plus (opp V) (plus (opp W) U))
                       (plus (opp W) (plus U (opp V)))).
      * apply req_sym. exact (plus_assoc (opp V) (opp W) U).
      * apply (req_trans (plus (opp V) (plus (opp W) U))
                         (plus (opp V) (plus U (opp W)))
                         (plus (opp W) (plus U (opp V)))).
        -- apply (req_plus_compat (opp V) (opp V) (plus (opp W) U)
                     (plus U (opp W)) (req_refl (opp V))
                     (plus_comm (opp W) U)).
        -- apply (req_trans (plus (opp V) (plus U (opp W)))
                            (plus (plus (opp V) U) (opp W))
                            (plus (opp W) (plus U (opp V)))).
           ++ exact (plus_assoc (opp V) U (opp W)).
           ++ apply (req_trans (plus (plus (opp V) U) (opp W))
                               (plus (opp W) (plus (opp V) U))
                               (plus (opp W) (plus U (opp V)))).
              ** exact (plus_comm (plus (opp V) U) (opp W)).
              ** apply (req_trans (plus (opp W) (plus (opp V) U))
                                  (plus (opp W) (plus U (opp V)))
                                  (plus (opp W) (plus U (opp V)))).
                 --- apply (req_plus_compat (opp W) (opp W) (plus (opp V) U)
                              (plus U (opp V)) (req_refl (opp W))
                              (plus_comm (opp V) U)).
                 --- apply req_refl.
    + apply (req_plus_compat (opp (mult D (log Z Z_pos)))
               (logc_fe logc_boltz logc_boltz_pos)
               (plus U (opp V))
               (mult D (sumf (fun s => mult (p s)
                                (plus (Lp s) (opp (Lb s))))))).
      * (* F[b] equals [opp W], the interior form of slot 2. *)
        apply (req_trans (opp (mult D (log Z Z_pos)))
                         (mult (opp D) (log Z Z_pos))
                         (logc_fe logc_boltz logc_boltz_pos)).
        -- apply req_sym. exact (logc_mult_opp_r D (log Z Z_pos)).
        -- apply req_sym. exact logc_free_energy_boltzmann.
      * apply req_sym. exact Hkl.
Qed.

End LogcFEP.

(* ============================================================ *)
(* Part 2, the slot-4 resolution at the Real layer, in [real_kl_term] form ([real_list_sum] instantiation;     *)
(*   supplied by the explicit Hpart slot, the G5 B1/B2 closures and the G6 D1 literal-form bridge).                 *)
(* ============================================================ *)

Lemma logc_real_kl_decomp_full :
  forall (X : Type) (l : list X) (e : X -> Real) (D : Real)
    (D_pos : real_lt real_zero D) (Z : Real) (Z_pos : real_lt real_zero Z)
    (Hpart : real_eq Z (real_list_sum X
                        (fun s => real_exp_neg
                                   (real_mult (real_inv_pos D D_pos) (e s))) l))
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p l) real_one),
  real_eq
    (real_free_energy X (fun f => real_list_sum X f l) e D p Hp)
    (real_plus
       (real_free_energy X (fun f => real_list_sum X f l) e D
          (fun s => real_mult (real_inv_pos Z Z_pos)
                              (real_exp_neg
                                 (real_mult (real_inv_pos D D_pos) (e s))))
          (fun s => real_mult_positive (real_inv_pos Z Z_pos)
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))
                       (real_inv_pos_pos Z Z_pos)
                       (real_exp_neg_pos
                          (real_mult (real_inv_pos D D_pos) (e s)))))
       (real_mult D
          (real_list_sum X
             (fun s => real_kl_term (p s)
                         (real_mult (real_inv_pos Z Z_pos)
                                    (real_exp_neg
                                       (real_mult (real_inv_pos D D_pos)
                                                  (e s))))
                         (Hp s)
                         (real_mult_positive (real_inv_pos Z Z_pos)
                            (real_exp_neg
                               (real_mult (real_inv_pos D D_pos) (e s)))
                            (real_inv_pos_pos Z Z_pos)
                            (real_exp_neg_pos
                               (real_mult (real_inv_pos D D_pos) (e s))))) l))).
Proof.
  intros X l e D D_pos Z Z_pos Hpart p Hp Hnormp.
  set (B := fun s : X => real_mult (real_inv_pos Z Z_pos)
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))).
  set (Bpos := fun s : X => real_mult_positive (real_inv_pos Z Z_pos)
                  (real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))
                  (real_inv_pos_pos Z Z_pos)
                  (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (e s)))).
  pose proof (@logc_fe_kl_decomp X
                (fun f => real_list_sum X f l)
                (fun f g H => real_list_sum_ext X f g l H)
                (fun f g => real_list_sum_add X f g l)
                (fun a f => real_list_sum_linear X a f l)
                e D D_pos Z Z_pos Hpart
                logd_log_compat_real logd_log_exp_neg_real p Hp Hnormp) as Hd.
  apply (real_eq_trans
           (real_free_energy X (fun f => real_list_sum X f l) e D p Hp)
           (real_plus
              (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
              (real_mult D
                 (real_list_sum X
                    (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (B s)
                                                       (Bpos s))))) l)))
           (real_plus
              (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
              (real_mult D
                 (real_list_sum X
                    (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l)))).
  - exact Hd.
  - apply (RealSetoid.real_eq_plus_compat
             (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
             (real_mult D
                (real_list_sum X
                   (fun s => real_mult (p s)
                              (real_plus (real_log (p s) (Hp s))
                                         (real_opp (real_log (B s)
                                                     (Bpos s))))) l))
             (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
             (real_mult D
                (real_list_sum X
                   (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_mult_compat D
               (real_list_sum X
                  (fun s => real_mult (p s)
                             (real_plus (real_log (p s) (Hp s))
                                        (real_opp (real_log (B s)
                                                    (Bpos s))))) l)
               D
               (real_list_sum X
                  (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l)).
      * apply real_eq_refl.
      * apply (real_eq_sym
                 (real_list_sum X
                    (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l)
                 (real_list_sum X
                    (fun s => real_mult (p s)
                               (real_plus (real_log (p s) (Hp s))
                                          (real_opp (real_log (B s)
                                                      (Bpos s))))) l)).
         exact (real_list_sum_ext X
                  (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s))
                  (fun s => real_mult (p s)
                             (real_plus (real_log (p s) (Hp s))
                                        (real_opp (real_log (B s)
                                                    (Bpos s))))) l
                  (fun s => logd_kl_term_minus_form (p s) (B s) (Hp s)
                              (Bpos s))).
Qed.

(* ============================================================ *)
(* Part 3: the temperature composite section (slots 5/6/7; supplied in the same form as the UpFirewallReq section).                  *)
(* ============================================================ *)

Section LogcTemp.
(* binder pair {R : Set} {RIS : RealInterfaceEnhancedSetoid R} carrier-ized
   away (zero-argument Class in this tree; R := Real pinned file-top). *)
Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis tsum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis tsum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tsum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

Variable energy : S -> R.
Variable Z_temp : R -> R.
(* req_Z_temp_spec, the premise slot matching its counterpart at line 93 of the source module. *)
Hypothesis zt_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (energy s)))).
Hypothesis zt_pos : forall (t : R) (Ht : lt zero t), lt zero (Z_temp t).
(* the B1/B2 supply slots, as in LogcFEP. *)
Hypothesis tsup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis tsup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* the temperature-parameterized definition family, at the same position as the UpFirewallReq fw_* family;               *)
(*   rebuilt with the same bodies as entropy_dist and req_relative_entropy of UpReqDist. *)
Definition logc_t_bt (t : R) (Ht : lt zero t) (s : S) : R :=
  mult (inv_pos (Z_temp t) (zt_pos t Ht))
       (exp_neg (mult (inv_pos t Ht) (energy s))).
Definition logc_t_bt_pos (t : R) (Ht : lt zero t) :
  forall s : S, lt zero (logc_t_bt t Ht s).
Proof.
  intros s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.
Definition logc_t_et (t : R) (Ht : lt zero t) : R :=
  sumf (fun s => mult (logc_t_bt t Ht s) (energy s)).
Definition logc_t_h (t : R) (Ht : lt zero t) : R :=
  sumf (fun s => mult (logc_t_bt t Ht s)
                      (opp (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s)))).
Definition logc_t_kl (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2) : R :=
  sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                      (plus (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s))
                            (opp (log (logc_t_bt t2 Ht2 s)
                                      (logc_t_bt_pos t2 Ht2 s))))).

(* T1: negation and right linearity of the sum, the LogcFEP arguments replayed on the section fields of this section. *)
Lemma logc_t_sum_opp : forall f : S -> R,
  req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s))) (opp (sumf f))).
  - apply tsum_ext. intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply req_opp_compat.
      exact (req_sym (mult one (f s)) (f s) (logc_mult_one_l (f s))).
    + apply req_sym. exact (logc_mult_opp_r one (f s)).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f)) (opp (sumf f))).
    + exact (tsum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f))
                       (opp (mult one (sumf f))) (opp (sumf f))).
      * exact (logc_mult_opp_r one (sumf f)).
      * apply req_opp_compat. exact (logc_mult_one_l (sumf f)).
Qed.

Lemma logc_t_sum_linear_r : forall (a : R) (f : S -> R),
  req (sumf (fun s => mult (f s) a)) (mult (sumf f) a).
Proof.
  intros a f.
  apply (req_trans (sumf (fun s => mult (f s) a))
                   (sumf (fun s => mult a (f s))) (mult (sumf f) a)).
  - apply tsum_ext. intro s. exact (mult_comm (f s) a).
  - apply (req_trans (sumf (fun s => mult a (f s)))
                     (mult a (sumf f)) (mult (sumf f) a)).
    + exact (tsum_linear a f).
    + exact (mult_comm a (sumf f)).
Qed.

(* T2: normalization, the sum of the temperature weights equals one, from zt_spec, [tsum_linear] and [inv_pos_correct]. *)
Lemma logc_t_normalized : forall (t : R) (Ht : lt zero t),
  req (sumf (logc_t_bt t Ht)) one.
Proof.
  intros t Ht.
  apply (req_trans (sumf (logc_t_bt t Ht))
                   (mult (inv_pos (Z_temp t) (zt_pos t Ht))
                         (sumf (fun s => exp_neg
                                   (mult (inv_pos t Ht) (energy s)))))
                   one).
  - exact (tsum_linear (inv_pos (Z_temp t) (zt_pos t Ht))
             (fun s => exp_neg (mult (inv_pos t Ht) (energy s)))).
  - apply (req_trans (mult (inv_pos (Z_temp t) (zt_pos t Ht))
                           (sumf (fun s => exp_neg
                                      (mult (inv_pos t Ht) (energy s)))))
                     (mult (inv_pos (Z_temp t) (zt_pos t Ht)) (Z_temp t)) one).
    + apply (req_mult_compat (inv_pos (Z_temp t) (zt_pos t Ht))
               (inv_pos (Z_temp t) (zt_pos t Ht))
               (sumf (fun s => exp_neg (mult (inv_pos t Ht) (energy s))))
               (Z_temp t)
               (req_refl (inv_pos (Z_temp t) (zt_pos t Ht)))).
      apply req_sym. exact (zt_spec t Ht).
    + apply (req_trans (mult (inv_pos (Z_temp t) (zt_pos t Ht)) (Z_temp t))
                       (mult (Z_temp t) (inv_pos (Z_temp t) (zt_pos t Ht)))
                       one).
      * exact (mult_comm (inv_pos (Z_temp t) (zt_pos t Ht)) (Z_temp t)).
      * exact (inv_pos_correct (Z_temp t) (zt_pos t Ht)).
Qed.


Lemma logc_t_log_decomp : forall (t : R) (Ht : lt zero t) (s : S),
  req (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))
      (plus (opp (log (Z_temp t) (zt_pos t Ht)))
            (opp (mult (inv_pos t Ht) (energy s)))).
Proof.
  intros t Ht s.
  apply (req_trans (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))
                   (plus (log (inv_pos (Z_temp t) (zt_pos t Ht))
                              (inv_pos_pos (Z_temp t) (zt_pos t Ht)))
                         (log (exp_neg (mult (inv_pos t Ht) (energy s)))
                              (exp_neg_pos (mult (inv_pos t Ht) (energy s)))))
                   (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                         (opp (mult (inv_pos t Ht) (energy s))))).
  - exact (log_mult (inv_pos (Z_temp t) (zt_pos t Ht))
                    (exp_neg (mult (inv_pos t Ht) (energy s)))
                    (inv_pos_pos (Z_temp t) (zt_pos t Ht))
                    (exp_neg_pos (mult (inv_pos t Ht) (energy s)))).
  - apply req_plus_compat.
    + exact (logd_log_inv_one_inv_of_compat tsup_compat (Z_temp t)
               (zt_pos t Ht) (inv_pos_pos (Z_temp t) (zt_pos t Ht))).
    + exact (tsup_log_exp_neg (mult (inv_pos t Ht) (energy s))).
Qed.


Lemma logc_t_sum_plogp : forall (t : R) (Ht : lt zero t),
  req (sumf (fun s => mult (logc_t_bt t Ht s)
                           (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))))
      (plus (opp (log (Z_temp t) (zt_pos t Ht)))
            (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
Proof.
  intros t Ht.
  apply (req_trans (sumf (fun s => mult (logc_t_bt t Ht s)
                            (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))))
                   (sumf (fun s => plus
                               (opp (mult (logc_t_bt t Ht s)
                                          (log (Z_temp t) (zt_pos t Ht))))
                               (opp (mult (logc_t_bt t Ht s)
                                          (mult (inv_pos t Ht) (energy s))))))
                   (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                         (opp (mult (inv_pos t Ht) (logc_t_et t Ht))))).
  - apply tsum_ext. intro s.
    
    apply (req_trans (mult (logc_t_bt t Ht s)
                           (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s)))
                     (mult (logc_t_bt t Ht s)
                           (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                 (opp (mult (inv_pos t Ht) (energy s)))))
                     (plus (opp (mult (logc_t_bt t Ht s)
                                      (log (Z_temp t) (zt_pos t Ht))))
                           (opp (mult (logc_t_bt t Ht s)
                                      (mult (inv_pos t Ht) (energy s)))))).
    + apply (req_mult_compat (logc_t_bt t Ht s) (logc_t_bt t Ht s)
               (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))
               (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                     (opp (mult (inv_pos t Ht) (energy s))))
               (req_refl (logc_t_bt t Ht s))).
      exact (logc_t_log_decomp t Ht s).
    + apply (req_trans (mult (logc_t_bt t Ht s)
                             (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                   (opp (mult (inv_pos t Ht) (energy s)))))
                       (plus (mult (logc_t_bt t Ht s)
                                   (opp (log (Z_temp t) (zt_pos t Ht))))
                             (mult (logc_t_bt t Ht s)
                                   (opp (mult (inv_pos t Ht) (energy s)))))
                       (plus (opp (mult (logc_t_bt t Ht s)
                                        (log (Z_temp t) (zt_pos t Ht))))
                             (opp (mult (logc_t_bt t Ht s)
                                        (mult (inv_pos t Ht) (energy s)))))).
      * exact (distrib (logc_t_bt t Ht s) (opp (log (Z_temp t) (zt_pos t Ht)))
                  (opp (mult (inv_pos t Ht) (energy s)))).
      * apply (req_plus_compat (mult (logc_t_bt t Ht s)
                                   (opp (log (Z_temp t) (zt_pos t Ht))))
                  (opp (mult (logc_t_bt t Ht s) (log (Z_temp t) (zt_pos t Ht))))
                  (mult (logc_t_bt t Ht s)
                        (opp (mult (inv_pos t Ht) (energy s))))
                  (opp (mult (logc_t_bt t Ht s)
                             (mult (inv_pos t Ht) (energy s))))).
        -- exact (logc_mult_opp_l (logc_t_bt t Ht s)
                    (log (Z_temp t) (zt_pos t Ht))).
        -- exact (logc_mult_opp_l (logc_t_bt t Ht s)
                    (mult (inv_pos t Ht) (energy s))).
  - apply (req_trans (sumf (fun s => plus
                               (opp (mult (logc_t_bt t Ht s)
                                          (log (Z_temp t) (zt_pos t Ht))))
                               (opp (mult (logc_t_bt t Ht s)
                                          (mult (inv_pos t Ht) (energy s))))))
                     (plus (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                                 (log (Z_temp t)
                                                      (zt_pos t Ht)))))
                           (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                                 (mult (inv_pos t Ht)
                                                       (energy s))))))
                     (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                           (opp (mult (inv_pos t Ht) (logc_t_et t Ht))))).
    + exact (tsum_add (fun s => opp (mult (logc_t_bt t Ht s)
                             (log (Z_temp t) (zt_pos t Ht))))
                      (fun s => opp (mult (logc_t_bt t Ht s)
                                (mult (inv_pos t Ht) (energy s))))).
    + apply (req_plus_compat
               (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (log (Z_temp t) (zt_pos t Ht)))))
               (opp (log (Z_temp t) (zt_pos t Ht)))
               (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (mult (inv_pos t Ht) (energy s)))))
               (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
      * apply (req_trans (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (log (Z_temp t) (zt_pos t Ht)))))
                         (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                     (log (Z_temp t) (zt_pos t Ht)))))
                         (opp (log (Z_temp t) (zt_pos t Ht)))).
        -- exact (logc_t_sum_opp (fun s => mult (logc_t_bt t Ht s)
                                    (log (Z_temp t) (zt_pos t Ht)))).
        -- apply (req_trans (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                         (log (Z_temp t) (zt_pos t Ht)))))
                            (opp (mult (log (Z_temp t) (zt_pos t Ht))
                                       (sumf (logc_t_bt t Ht))))
                            (opp (log (Z_temp t) (zt_pos t Ht)))).
           ++ apply req_opp_compat.
              apply (req_trans (sumf (fun s : S => mult (logc_t_bt t Ht s)
                                         (log (Z_temp t) (zt_pos t Ht))))
                               (mult (sumf (logc_t_bt t Ht))
                                     (log (Z_temp t) (zt_pos t Ht)))
                               (mult (log (Z_temp t) (zt_pos t Ht))
                                     (sumf (logc_t_bt t Ht)))).
              ** exact (logc_t_sum_linear_r (log (Z_temp t) (zt_pos t Ht))
                            (logc_t_bt t Ht)).
              ** exact (mult_comm (sumf (logc_t_bt t Ht))
                            (log (Z_temp t) (zt_pos t Ht))).
           ++ apply req_opp_compat.
              apply (req_trans (mult (log (Z_temp t) (zt_pos t Ht))
                                     (sumf (logc_t_bt t Ht)))
                               (mult (log (Z_temp t) (zt_pos t Ht)) one)
                               (log (Z_temp t) (zt_pos t Ht))).
              ** apply (req_mult_compat (log (Z_temp t) (zt_pos t Ht))
                            (log (Z_temp t) (zt_pos t Ht))
                            (sumf (logc_t_bt t Ht)) one
                            (req_refl (log (Z_temp t) (zt_pos t Ht)))
                            (logc_t_normalized t Ht)).
              ** exact (mult_one (log (Z_temp t) (zt_pos t Ht))).
      * apply (req_trans (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (mult (inv_pos t Ht) (energy s)))))
                         (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                     (mult (inv_pos t Ht) (energy s)))))
                         (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
        -- exact (logc_t_sum_opp (fun s => mult (logc_t_bt t Ht s)
                                    (mult (inv_pos t Ht) (energy s)))).
        -- apply (req_trans (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                         (mult (inv_pos t Ht) (energy s)))))
                            (opp (mult (inv_pos t Ht)
                                       (sumf (fun s => mult (logc_t_bt t Ht s)
                                                (energy s)))))
                            (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
           ++ apply req_opp_compat.
              apply (req_trans (sumf (fun s => mult (logc_t_bt t Ht s)
                                        (mult (inv_pos t Ht) (energy s))))
                               (sumf (fun s => mult (inv_pos t Ht)
                                        (mult (logc_t_bt t Ht s) (energy s))))
                               (mult (inv_pos t Ht)
                                 (sumf (fun s => mult (logc_t_bt t Ht s)
                                           (energy s))))).
              ** apply tsum_ext. intro s.
                 apply (req_trans (mult (logc_t_bt t Ht s)
                                    (mult (inv_pos t Ht) (energy s)))
                                  (mult (mult (logc_t_bt t Ht s)
                                          (inv_pos t Ht))
                                    (energy s))
                                  (mult (inv_pos t Ht)
                                    (mult (logc_t_bt t Ht s) (energy s)))).
                 --- exact (mult_assoc (logc_t_bt t Ht s) (inv_pos t Ht)
                              (energy s)).
                 --- apply (req_trans (mult (mult (logc_t_bt t Ht s)
                                          (inv_pos t Ht))
                                    (energy s))
                                      (mult (mult (inv_pos t Ht)
                                              (logc_t_bt t Ht s))
                                        (energy s))
                                      (mult (inv_pos t Ht)
                                        (mult (logc_t_bt t Ht s)
                                          (energy s)))).
                     +++ apply (req_mult_compat
                                  (mult (logc_t_bt t Ht s) (inv_pos t Ht))
                                  (mult (inv_pos t Ht) (logc_t_bt t Ht s))
                                  (energy s) (energy s)
                                  (mult_comm (logc_t_bt t Ht s)
                                             (inv_pos t Ht))
                                  (req_refl (energy s))).
                     +++ apply req_sym.
                         exact (mult_assoc (inv_pos t Ht)
                                  (logc_t_bt t Ht s) (energy s)).
              ** exact (tsum_linear (inv_pos t Ht)
                          (fun s => mult (logc_t_bt t Ht s) (energy s))).
           ++ apply req_opp_compat. apply req_refl.
Qed.


Lemma logc_entropy_temp_explicit : forall (t : R) (Ht : lt zero t),
  req (logc_t_h t Ht)
      (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
            (log (Z_temp t) (zt_pos t Ht))).
Proof.
  intros t Ht.
  apply (req_trans (logc_t_h t Ht)
                   (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                   (log (logc_t_bt t Ht s)
                                        (logc_t_bt_pos t Ht s)))))
                   (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                         (log (Z_temp t) (zt_pos t Ht)))).
  - apply (req_trans (logc_t_h t Ht)
                     (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                 (log (logc_t_bt t Ht s)
                                      (logc_t_bt_pos t Ht s)))))
                     (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                     (log (logc_t_bt t Ht s)
                                          (logc_t_bt_pos t Ht s)))))).
    + apply tsum_ext. intro s.
      exact (logc_mult_opp_l (logc_t_bt t Ht s)
                (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))).
    + exact (logc_t_sum_opp (fun s => mult (logc_t_bt t Ht s)
                                (log (logc_t_bt t Ht s)
                                     (logc_t_bt_pos t Ht s)))).
  - apply (req_trans (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                 (log (logc_t_bt t Ht s)
                                      (logc_t_bt_pos t Ht s)))))
                     (opp (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                (opp (mult (inv_pos t Ht)
                                           (logc_t_et t Ht)))))
                     (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                           (log (Z_temp t) (zt_pos t Ht)))).
    + apply req_opp_compat.
      exact (logc_t_sum_plogp t Ht).
    + apply (req_trans (opp (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                  (opp (mult (inv_pos t Ht)
                                             (logc_t_et t Ht)))))
                       (plus (opp (opp (log (Z_temp t) (zt_pos t Ht))))
                             (opp (opp (mult (inv_pos t Ht)
                                             (logc_t_et t Ht)))))
                       (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                             (log (Z_temp t) (zt_pos t Ht)))).
      * exact (logc_opp_plus (opp (log (Z_temp t) (zt_pos t Ht)))
                 (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
      * apply (req_trans (plus (opp (opp (log (Z_temp t) (zt_pos t Ht))))
                               (opp (opp (mult (inv_pos t Ht)
                                           (logc_t_et t Ht)))))
                         (plus (log (Z_temp t) (zt_pos t Ht))
                               (mult (inv_pos t Ht) (logc_t_et t Ht)))
                         (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                               (log (Z_temp t) (zt_pos t Ht)))).
        -- apply (req_plus_compat (opp (opp (log (Z_temp t) (zt_pos t Ht))))
                      (log (Z_temp t) (zt_pos t Ht))
                      (opp (opp (mult (inv_pos t Ht) (logc_t_et t Ht))))
                      (mult (inv_pos t Ht) (logc_t_et t Ht))).
           ++ exact (logd_req_opp_opp (log (Z_temp t) (zt_pos t Ht))).
           ++ exact (logd_req_opp_opp
                      (mult (inv_pos t Ht) (logc_t_et t Ht))).
        -- exact (plus_comm (log (Z_temp t) (zt_pos t Ht))
                  (mult (inv_pos t Ht) (logc_t_et t Ht))).
Qed.


Lemma logc_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (logc_t_kl t1 t2 Ht1 Ht2)
      (plus (plus (opp (logc_t_h t1 Ht1))
                  (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
            (log (Z_temp t2) (zt_pos t2 Ht2))).
Proof.
  intros t2 Ht2 t1 Ht1.
  
  assert (Hleft : req (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                (log (logc_t_bt t1 Ht1 s)
                                     (logc_t_bt_pos t1 Ht1 s))))
                     (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                           (opp (mult (inv_pos t1 Ht1)
                                      (logc_t_et t1 Ht1))))).
  { exact (logc_t_sum_plogp t1 Ht1). }
  assert (Hright : req (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                 (opp (log (logc_t_bt t2 Ht2 s)
                                           (logc_t_bt_pos t2 Ht2 s)))))
                     (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                           (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
  { apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                              (opp (log (logc_t_bt t2 Ht2 s)
                                        (logc_t_bt_pos t2 Ht2 s)))))
                     (sumf (fun s => plus (mult (logc_t_bt t1 Ht1 s)
                                            (log (Z_temp t2) (zt_pos t2 Ht2)))
                                          (mult (logc_t_bt t1 Ht1 s)
                                            (mult (inv_pos t2 Ht2)
                                                  (energy s)))))
                     (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                           (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
    - apply tsum_ext. intro s.
      
      apply (req_trans (mult (logc_t_bt t1 Ht1 s)
                             (opp (log (logc_t_bt t2 Ht2 s)
                                       (logc_t_bt_pos t2 Ht2 s))))
                       (mult (logc_t_bt t1 Ht1 s)
                             (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                   (mult (inv_pos t2 Ht2) (energy s))))
                       (plus (mult (logc_t_bt t1 Ht1 s)
                                   (log (Z_temp t2) (zt_pos t2 Ht2)))
                             (mult (logc_t_bt t1 Ht1 s)
                                   (mult (inv_pos t2 Ht2) (energy s))))).
      + apply (req_mult_compat (logc_t_bt t1 Ht1 s) (logc_t_bt t1 Ht1 s)
                  (opp (log (logc_t_bt t2 Ht2 s) (logc_t_bt_pos t2 Ht2 s)))
                  (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                        (mult (inv_pos t2 Ht2) (energy s)))
                  (req_refl (logc_t_bt t1 Ht1 s))).
        
        apply (req_trans (opp (log (logc_t_bt t2 Ht2 s)
                                   (logc_t_bt_pos t2 Ht2 s)))
                         (opp (plus (opp (log (Z_temp t2) (zt_pos t2 Ht2)))
                                    (opp (mult (inv_pos t2 Ht2)
                                               (energy s)))))
                         (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                               (mult (inv_pos t2 Ht2) (energy s)))).
        -- apply req_opp_compat.
           exact (logc_t_log_decomp t2 Ht2 s).
        -- apply (req_trans (opp (plus (opp (log (Z_temp t2) (zt_pos t2 Ht2)))
                                       (opp (mult (inv_pos t2 Ht2)
                                                  (energy s)))))
                            (plus (opp (opp (log (Z_temp t2)
                                                 (zt_pos t2 Ht2))))
                                  (opp (opp (mult (inv_pos t2 Ht2)
                                                  (energy s)))))
                            (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                  (mult (inv_pos t2 Ht2) (energy s)))).
           ++ exact (logc_opp_plus (opp (log (Z_temp t2) (zt_pos t2 Ht2)))
                       (opp (mult (inv_pos t2 Ht2) (energy s)))).
           ++ apply (req_plus_compat
                        (opp (opp (log (Z_temp t2) (zt_pos t2 Ht2))))
                        (log (Z_temp t2) (zt_pos t2 Ht2))
                        (opp (opp (mult (inv_pos t2 Ht2) (energy s))))
                        (mult (inv_pos t2 Ht2) (energy s))).
              ** exact (logd_req_opp_opp
                          (log (Z_temp t2) (zt_pos t2 Ht2))).
              ** exact (logd_req_opp_opp
                          (mult (inv_pos t2 Ht2) (energy s))).
      + exact (distrib (logc_t_bt t1 Ht1 s)
                  (log (Z_temp t2) (zt_pos t2 Ht2))
                  (mult (inv_pos t2 Ht2) (energy s))).
    - apply (req_trans (sumf (fun s => plus (mult (logc_t_bt t1 Ht1 s)
                                              (log (Z_temp t2)
                                                   (zt_pos t2 Ht2)))
                                            (mult (logc_t_bt t1 Ht1 s)
                                              (mult (inv_pos t2 Ht2)
                                                    (energy s)))))
                       (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                             (log (Z_temp t2)
                                                  (zt_pos t2 Ht2))))
                             (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                               (mult (inv_pos t2 Ht2)
                                                     (energy s)))))
                       (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                             (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
      + exact (tsum_add (fun s => mult (logc_t_bt t1 Ht1 s)
                                  (log (Z_temp t2) (zt_pos t2 Ht2)))
                        (fun s => mult (logc_t_bt t1 Ht1 s)
                                  (mult (inv_pos t2 Ht2) (energy s)))).
      + apply (req_plus_compat (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                         (log (Z_temp t2) (zt_pos t2 Ht2))))
                  (log (Z_temp t2) (zt_pos t2 Ht2))
                  (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                    (mult (inv_pos t2 Ht2) (energy s))))
                  (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))).
        * apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (log (Z_temp t2) (zt_pos t2 Ht2))))
                           (mult (sumf (logc_t_bt t1 Ht1))
                                  (log (Z_temp t2) (zt_pos t2 Ht2)))
                           (log (Z_temp t2) (zt_pos t2 Ht2))).
          -- exact (logc_t_sum_linear_r (log (Z_temp t2) (zt_pos t2 Ht2))
                       (logc_t_bt t1 Ht1)).
          -- apply (req_trans (mult (sumf (logc_t_bt t1 Ht1))
                                    (log (Z_temp t2) (zt_pos t2 Ht2)))
                              (mult one (log (Z_temp t2) (zt_pos t2 Ht2)))
                              (log (Z_temp t2) (zt_pos t2 Ht2))).
             ++ apply (req_mult_compat (sumf (logc_t_bt t1 Ht1)) one
                          (log (Z_temp t2) (zt_pos t2 Ht2))
                          (log (Z_temp t2) (zt_pos t2 Ht2))
                          (logc_t_normalized t1 Ht1)
                          (req_refl (log (Z_temp t2) (zt_pos t2 Ht2)))).
             ++ exact (logc_mult_one_l (log (Z_temp t2) (zt_pos t2 Ht2))).
        * apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (mult (inv_pos t2 Ht2) (energy s))))
                           (mult (inv_pos t2 Ht2)
                                  (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                                    (energy s))))
                           (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))).
          -- apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                        (mult (inv_pos t2 Ht2) (energy s))))
                              (sumf (fun s => mult (inv_pos t2 Ht2)
                                        (mult (logc_t_bt t1 Ht1 s) (energy s))))
                              (mult (inv_pos t2 Ht2)
                                (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                                  (energy s))))).
             ++ apply tsum_ext. intro s.
                 apply (req_trans (mult (logc_t_bt t1 Ht1 s)
                                    (mult (inv_pos t2 Ht2) (energy s)))
                                  (mult (mult (logc_t_bt t1 Ht1 s)
                                          (inv_pos t2 Ht2))
                                    (energy s))
                                  (mult (inv_pos t2 Ht2)
                                    (mult (logc_t_bt t1 Ht1 s) (energy s)))).
                 --- exact (mult_assoc (logc_t_bt t1 Ht1 s) (inv_pos t2 Ht2)
                              (energy s)).
                 --- apply (req_trans (mult (mult (logc_t_bt t1 Ht1 s)
                                          (inv_pos t2 Ht2))
                                    (energy s))
                                      (mult (mult (inv_pos t2 Ht2)
                                              (logc_t_bt t1 Ht1 s))
                                        (energy s))
                                      (mult (inv_pos t2 Ht2)
                                        (mult (logc_t_bt t1 Ht1 s)
                                          (energy s)))).
                     +++ apply (req_mult_compat
                                  (mult (logc_t_bt t1 Ht1 s) (inv_pos t2 Ht2))
                                  (mult (inv_pos t2 Ht2) (logc_t_bt t1 Ht1 s))
                                  (energy s) (energy s)
                                  (mult_comm (logc_t_bt t1 Ht1 s)
                                             (inv_pos t2 Ht2))
                                  (req_refl (energy s))).
                     +++ apply req_sym.
                         exact (mult_assoc (inv_pos t2 Ht2)
                                  (logc_t_bt t1 Ht1 s) (energy s)).
             ++ exact (tsum_linear (inv_pos t2 Ht2)
                         (fun s => mult (logc_t_bt t1 Ht1 s) (energy s))).
          -- apply req_refl. }
  
  apply (req_trans (logc_t_kl t1 t2 Ht1 Ht2)
                   (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                   (log (logc_t_bt t1 Ht1 s)
                                        (logc_t_bt_pos t1 Ht1 s))))
                         (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                   (opp (log (logc_t_bt t2 Ht2 s)
                                             (logc_t_bt_pos t2 Ht2 s))))))
                   (plus (plus (opp (logc_t_h t1 Ht1))
                               (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                         (log (Z_temp t2) (zt_pos t2 Ht2)))).
  - apply (req_trans (logc_t_kl t1 t2 Ht1 Ht2)
                     (sumf (fun s => plus (mult (logc_t_bt t1 Ht1 s)
                                            (log (logc_t_bt t1 Ht1 s)
                                                 (logc_t_bt_pos t1 Ht1 s)))
                                          (mult (logc_t_bt t1 Ht1 s)
                                            (opp (log (logc_t_bt t2 Ht2 s)
                                                      (logc_t_bt_pos t2 Ht2 s))))))
                     (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                   (log (logc_t_bt t1 Ht1 s)
                                        (logc_t_bt_pos t1 Ht1 s))))
                           (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (opp (log (logc_t_bt t2 Ht2 s)
                                               (logc_t_bt_pos t2 Ht2 s))))))).
    + apply tsum_ext. intro s.
      exact (distrib (logc_t_bt t1 Ht1 s)
                (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s))
                (opp (log (logc_t_bt t2 Ht2 s) (logc_t_bt_pos t2 Ht2 s)))).
    + exact (tsum_add (fun s => mult (logc_t_bt t1 Ht1 s)
                        (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s)))
                      (fun s => mult (logc_t_bt t1 Ht1 s)
                        (opp (log (logc_t_bt t2 Ht2 s)
                                  (logc_t_bt_pos t2 Ht2 s))))).
  - apply (req_trans (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                  (log (logc_t_bt t1 Ht1 s)
                                       (logc_t_bt_pos t1 Ht1 s))))
                           (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (opp (log (logc_t_bt t2 Ht2 s)
                                               (logc_t_bt_pos t2 Ht2 s))))))
                     (plus (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                                 (opp (mult (inv_pos t1 Ht1)
                                            (logc_t_et t1 Ht1))))
                           (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                 (mult (inv_pos t2 Ht2)
                                       (logc_t_et t1 Ht1))))
                     (plus (plus (opp (logc_t_h t1 Ht1))
                                 (mult (inv_pos t2 Ht2)
                                       (logc_t_et t1 Ht1)))
                           (log (Z_temp t2) (zt_pos t2 Ht2)))).
    + apply (req_plus_compat
                (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                          (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s))))
                (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                      (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1))))
                (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                          (opp (log (logc_t_bt t2 Ht2 s)
                                    (logc_t_bt_pos t2 Ht2 s)))))
                (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                      (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
      * exact Hleft.
      * exact Hright.
    + (* permutation concluded: (-logZ1 - E1/t1) + (logZ2 + E1/t2) equals (-H1 + E1/t2) + logZ2. *)
      assert (HoppH1 : req (opp (logc_t_h t1 Ht1))
                           (plus (opp (mult (inv_pos t1 Ht1)
                                           (logc_t_et t1 Ht1)))
                                 (opp (log (Z_temp t1) (zt_pos t1 Ht1))))).
      { apply (req_trans (opp (logc_t_h t1 Ht1))
                         (opp (plus (mult (inv_pos t1 Ht1)
                                          (logc_t_et t1 Ht1))
                                    (log (Z_temp t1) (zt_pos t1 Ht1))))
                         (plus (opp (mult (inv_pos t1 Ht1)
                                          (logc_t_et t1 Ht1)))
                               (opp (log (Z_temp t1) (zt_pos t1 Ht1))))).
        - apply req_opp_compat.
          exact (logc_entropy_temp_explicit t1 Ht1).
        - exact (logc_opp_plus (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1))
                  (log (Z_temp t1) (zt_pos t1 Ht1))). }
      apply (req_trans (plus (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                                   (opp (mult (inv_pos t1 Ht1)
                                              (logc_t_et t1 Ht1))))
                             (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                   (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1))))
                       (plus (plus (opp (mult (inv_pos t1 Ht1)
                                              (logc_t_et t1 Ht1)))
                                   (opp (log (Z_temp t1)
                                             (zt_pos t1 Ht1))))
                             (plus (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1))
                                   (log (Z_temp t2) (zt_pos t2 Ht2))))
                       (plus (plus (opp (logc_t_h t1 Ht1))
                                   (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1)))
                             (log (Z_temp t2) (zt_pos t2 Ht2)))).
      * apply (req_plus_compat
                  (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                    (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1))))
                  (plus (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1)))
                    (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                  (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                    (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                  (plus (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))
                    (log (Z_temp t2) (zt_pos t2 Ht2)))).
        -- exact (plus_comm (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                               (opp (mult (inv_pos t1 Ht1)
                                          (logc_t_et t1 Ht1)))).
        -- exact (plus_comm (log (Z_temp t2) (zt_pos t2 Ht2))
                               (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1))).
      * apply (req_trans (plus (plus (opp (mult (inv_pos t1 Ht1)
                                                 (logc_t_et t1 Ht1)))
                                       (opp (log (Z_temp t1)
                                                 (zt_pos t1 Ht1))))
                                  (plus (mult (inv_pos t2 Ht2)
                                              (logc_t_et t1 Ht1))
                                    (log (Z_temp t2) (zt_pos t2 Ht2))))
                         (plus (plus (plus (opp (mult (inv_pos t1 Ht1)
                                                        (logc_t_et t1 Ht1)))
                                              (opp (log (Z_temp t1)
                                                        (zt_pos t1 Ht1))))
                                        (mult (inv_pos t2 Ht2)
                                              (logc_t_et t1 Ht1)))
                                  (log (Z_temp t2) (zt_pos t2 Ht2)))
                         (plus (plus (opp (logc_t_h t1 Ht1))
                                     (mult (inv_pos t2 Ht2)
                                           (logc_t_et t1 Ht1)))
                               (log (Z_temp t2) (zt_pos t2 Ht2)))).
        -- exact (plus_assoc (plus (opp (mult (inv_pos t1 Ht1)
                                                  (logc_t_et t1 Ht1)))
                                   (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                             (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))
                             (log (Z_temp t2) (zt_pos t2 Ht2))).
        -- apply (req_plus_compat
                    (plus (plus (opp (mult (inv_pos t1 Ht1)
                                                (logc_t_et t1 Ht1)))
                                  (opp (log (Z_temp t1)
                                            (zt_pos t1 Ht1))))
                            (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                    (plus (opp (logc_t_h t1 Ht1))
                      (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                    (log (Z_temp t2) (zt_pos t2 Ht2))
                    (log (Z_temp t2) (zt_pos t2 Ht2))).
           ++ apply (req_plus_compat
                        (plus (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1)))
                          (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                        (opp (logc_t_h t1 Ht1))
                        (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))
                        (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))).
              ** exact (req_sym
                          (opp (logc_t_h t1 Ht1))
                          (plus (opp (mult (inv_pos t1 Ht1)
                                           (logc_t_et t1 Ht1)))
                                (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                          HoppH1).
              ** apply req_refl.
           ++ apply req_refl.
Qed.

End LogcTemp.

(* ============================================================ *)
(* closure audit: Print Assumptions on the main resolved statements.                          *)
(* ============================================================ *)
Print Assumptions logc_energy_in_log_boltzmann.
Print Assumptions logc_free_energy_boltzmann.
Print Assumptions logc_fe_kl_decomp.
Print Assumptions logc_real_kl_decomp_full.
Print Assumptions logc_entropy_temp_explicit.
Print Assumptions logc_relative_entropy_temp_decomp.
Print Assumptions logc_boltzmann_normalized.
Print Assumptions logc_boltz_log_decomp.
Print Assumptions logc_t_log_decomp.
Print Assumptions logc_t_sum_plogp.

Print Assumptions logc_mult_one_l.
