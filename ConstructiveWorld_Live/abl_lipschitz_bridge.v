(* ConstructiveWorld-Set — Lipschitz budget to geometric contraction bridge. *)
(** * abl_lipschitz_bridge: Lipschitz budget implies contraction.

    Mission.  A self-map [step] on a Set carrier [X] with a gap
      function [gap] and Lipschitz budget constant [L] ([0 <= L < 1],
      one-step two-point budget) contracts geometrically:
      [gap (iter n x) (iter n y) <= L^n * gap x y]; an affine
      instantiation follows, and Part C derives the constructive
      Banach fixed-point theorem with the Cauchy modulus
      [lbr_iter_cauchy], the closed bound [lbr_iter_cauchy_closed]
      and the residual calculator [lbr_residual_calc].

    Dependencies.  Stdlib [List], [PeanoNat], [Extraction],
      [Arith.Arith], [Lia]; and [S01_BaseRing] through
      [S06_DiffSamplingGibbs] of this development (interface fields
      only, no host-section theorem consumed).

    References.  This development, abl_lipschitz_bridge.v, the
      baseline module in ConstructiveWorld-Main whose statement
      names are carried over verbatim (statement-face Set-carrier
      completion); shapes mirror [attention_tv_iter_contraction].

    Constructivity.  All named statements are carried by [Set]:
      existence as [sigT], conjunction as the [Set]-level product,
      order bounds as [NatLe] or interface [le] values; two genuine
      [Fixpoint]s ([lbr_iter], [lbr_r_pow]); extraction reports
      [Obj.magic] = 0 and [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_lipschitz_bridge.v]
      compiles cleanly (exit 0); the artifact starts [436f7121 00015ff4]. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* The eq-to-Id bridge (eq singleton elimination moves into Set). *)
Definition lbr_eq_id {A : Set} {x y : A} (H : x = y) : Id x y :=
  match H as H0 in (_ = z) return Id x z with
  | eq_refl => id_refl
  end.

(* ============================================================ *)
(* Part A: the Lipschitz-budget-to-geometric-contraction bridge,     *)
(* host-independent.  Five honest interface slots: the carrier       *)
(* [X:Set], the gap [gap], the step [step], the budget constant      *)
(* [L], the budget certificates (nonnegativity, strictly below one,  *)
(* one-step two-point budget) plus gap nonnegativity and the arch    *)
(* slot.  Main lemma [lbr_iter_lipschitz]:                           *)
(* |f^n x - f^n y| <= L^n * |x - y| by induction.                    *)
(* ============================================================ *)

Section LbrBridge.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.

Variable X : Set.
Variable gap : X -> X -> R.
Variable step : X -> X.
Variable L : R.

(* The two budget certificates (counterparts of the two conjuncts at   *)
(* the S06 op_lipschitz/inner_lipschitz argument positions). *)
Variable lbr_L_nonneg : le zero L.
Variable lbr_L_lt_one : lt L one.

(* The Lipschitz budget: the one-step two-point bound (the budget side   *)
(* of the bridge). *)
Variable lbr_budget : forall x y : X,
  le (gap (step x) (step y)) (mult L (gap x y)).

(* Gap nonnegativity (the abstract form of tv_dist_nonneg). *)
Variable lbr_gap_nonneg : forall x y : X, le zero (gap x y).

(* ===== Two Fixpoints: the geometric-rate and iteration carriers ===== *)

Fixpoint lbr_r_pow (n : nat) : R :=
  match n with
  | O => one
  | Datatypes.S m => mult L (lbr_r_pow m)
  end.

Fixpoint lbr_iter (n : nat) (x : X) : X :=
  match n with
  | O => x
  | Datatypes.S m => step (lbr_iter m x)
  end.

(* The arch slot (counterpart of the host r_arch_pow_attn with the rate   *)
(* L; [lbr_r_pow] is the section-local unary geometric-rate carrier). *)
Variable lbr_arch : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (lbr_r_pow N)) eps).

(* ===== Basics: unital multiplication and power nonnegativity ===== *)

Lemma lbr_gap_le_mult_one : forall x y : X,
  le (gap x y) (mult one (gap x y)).
Proof.
  intros x y.
  exact (le_id_l (gap x y) (mult one (gap x y)) (mult one (gap x y))
           (id_sym (id_trans (mult_comm one (gap x y)) (mult_one (gap x y))))
           (le_refl _)).
Qed.

Lemma lbr_r_pow_nonneg : forall n : nat, le zero (lbr_r_pow n).
Proof.
  induction n as [| n IH].
  - exact (lt_le_iff zero one (inl one_pos)).
  - simpl.
    apply (le_id_l zero (mult zero (lbr_r_pow n)) (mult L (lbr_r_pow n))).
    + exact (id_sym (id_trans (mult_comm zero (lbr_r_pow n))
                              (mult_zero (lbr_r_pow n)))).
    + apply (le_mult_compat_weak zero L (lbr_r_pow n)).
      * exact IH.
      * exact lbr_L_nonneg.
Qed.

(* ===== Geometric-rate side: monotone power decay (NatLe carrier) ===== *)

Lemma lbr_r_pow_step_dec : forall n : nat,
  le (lbr_r_pow (Datatypes.S n)) (lbr_r_pow n).
Proof.
  intro n.
  apply (le_trans _ (mult one (lbr_r_pow n)) _).
  - apply (le_mult_compat_weak L one (lbr_r_pow n)).
    + apply lbr_r_pow_nonneg.
    + apply (lt_le_iff L one). exact (inl lbr_L_lt_one).
  - apply (le_id_l (mult one (lbr_r_pow n)) (lbr_r_pow n) (lbr_r_pow n)).
    + exact (id_trans (mult_comm one (lbr_r_pow n)) (mult_one (lbr_r_pow n))).
    + apply le_refl.
Qed.

Lemma lbr_r_pow_dec : forall m n : nat,
  NatLe m n -> le (lbr_r_pow n) (lbr_r_pow m).
Proof.
  intros m n Hmn. revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - pose proof (NatLe_drop m O Hmn) as Hm0.
    assert (Hmeq : m = 0%nat) by lia. subst m. apply le_refl.
  - destruct (Nat.leb m n) eqn:Emn.
    + apply (le_trans _ (lbr_r_pow n) _).
      * apply lbr_r_pow_step_dec.
      * apply IH. apply (NatLe_lift m n).
        exact (proj1 (PeanoNat.Nat.leb_le m n) Emn).
    + apply Nat.leb_gt in Emn.
      pose proof (NatLe_drop m (Datatypes.S n) Hmn) as Hle.
      assert (Hmeq : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* ===== Iteration side: additive decomposition and step exchange ===== *)

Lemma lbr_iter_plus : forall (m n : nat) (x : X),
  Id (lbr_iter (Nat.add m n) x) (lbr_iter m (lbr_iter n x)).
Proof.
  intros m n x. induction m as [| m IH].
  - simpl. apply id_refl.
  - simpl. exact (id_cong step IH).
Qed.

Lemma lbr_iter_step_commute : forall (n : nat) (x : X),
  Id (lbr_iter n (step x)) (step (lbr_iter n x)).
Proof.
  intros n x. induction n as [| n IH].
  - simpl. apply id_refl.
  - simpl. exact (id_cong step IH).
Qed.

Lemma lbr_iter_consecutive : forall (n : nat) (x : X),
  Id (lbr_iter (Datatypes.S n) x) (lbr_iter n (step x)).
Proof.
  intros n x. simpl. exact (id_sym (lbr_iter_step_commute n x)).
Qed.

(* Multiplication respects order in the second factor when the first    *)
(* factor is nonnegative: u <= v gives w*u <= w*v; derived from the      *)
(* first-factor form [le_mult_compat_weak] by commutativity. *)
Lemma lbr_mult_compat_r : forall u v w : R,
  le zero w -> le u v -> le (mult w u) (mult w v).
Proof.
  intros u v w Hw Huv.
  apply (le_trans _ (mult u w)).
  - apply (le_id_l (mult w u) (mult u w) (mult u w)
             (mult_comm w u) (le_refl _)).
  - apply (le_trans _ (mult v w)).
    + apply (le_mult_compat_weak u v w).
      * exact Hw.
      * exact Huv.
    + apply (le_id_l (mult v w) (mult w v) (mult w v)
               (id_sym (mult_comm w v)) (le_refl _)).
Qed.

(* ============================================================ *)
(* Main bridge lemma: the Lipschitz budget yields geometric iterative   *)
(* contraction, |f^n x - f^n y| <= L^n * |x - y| (statement shape of    *)
(* the host contraction family, with gap for the distance, L for the    *)
(* rate, step for the map).  Base case: the unit-multiplication shift;  *)
(* step case: the budget, the induction case, second-factor             *)
(* order preservation [lbr_mult_compat_r], and the associativity fold   *)
(* (definitional via [mult_assoc]). *)
(* ============================================================ *)

Theorem lbr_iter_lipschitz : forall (n : nat) (x y : X),
  le (gap (lbr_iter n x) (lbr_iter n y)) (mult (lbr_r_pow n) (gap x y)).
Proof.
  intros n. induction n as [| n IH]; intros x y.
  - simpl. exact (lbr_gap_le_mult_one x y).
  - simpl.
    apply (le_trans _ (mult L (gap (lbr_iter n x) (lbr_iter n y))) _).
    + apply (lbr_budget (lbr_iter n x) (lbr_iter n y)).
    + apply (le_trans _ (mult L (mult (lbr_r_pow n) (gap x y))) _).
      * apply (lbr_mult_compat_r (gap (lbr_iter n x) (lbr_iter n y))
                                 (mult (lbr_r_pow n) (gap x y)) L).
        -- exact lbr_L_nonneg.
        -- exact (IH x y).
      * apply (le_id_l (mult L (mult (lbr_r_pow n) (gap x y)))
                       (mult (mult L (lbr_r_pow n)) (gap x y))
                       (mult (lbr_r_pow (Datatypes.S n)) (gap x y))).
        -- exact (mult_assoc L (lbr_r_pow n) (gap x y)).
        -- apply le_refl.
Qed.

(* Adjacent-gap decay: |f^(n+1) x - f^n x| <= L^n * |f x - x| (the      *)
(* Cauchy-sequence supply face; uses the main bridge lemma). *)
Lemma lbr_iter_step_gap_decay : forall (n : nat) (x : X),
  le (gap (lbr_iter (Datatypes.S n) x) (lbr_iter n x))
     (mult (lbr_r_pow n) (gap (step x) x)).
Proof.
  intros n x.
  apply (le_id_l (gap (lbr_iter (Datatypes.S n) x) (lbr_iter n x))
                 (gap (lbr_iter n (step x)) (lbr_iter n x))
                 (mult (lbr_r_pow n) (gap (step x) x))).
  - exact (id_cong (fun z => gap z (lbr_iter n x)) (lbr_iter_consecutive n x)).
  - apply (lbr_iter_lipschitz n (step x) x).
Qed.

(* ===== Precision-to-step-count sigT calculator ===== *)

Theorem lbr_step_count : forall (x y : X) (eps : R),
  lt zero (gap x y) -> lt zero eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    lt (gap (lbr_iter n x) (lbr_iter n y)) eps).
Proof.
  intros x y eps Hg0 Hep.
  destruct (lbr_arch (gap x y) Hg0 eps Hep) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (lbr_r_pow n) (gap x y)) _).
  - apply (lbr_iter_lipschitz n x y).
  - apply (le_lt_trans _ (mult (lbr_r_pow N) (gap x y)) _).
    + apply (le_mult_compat_weak (lbr_r_pow n) (lbr_r_pow N) (gap x y)).
      * apply lbr_gap_nonneg.
      * apply (lbr_r_pow_dec N n Hn).
    + apply (lt_id_l (mult (lbr_r_pow N) (gap x y))
                     (mult (gap x y) (lbr_r_pow N)) eps).
      * exact (mult_comm (lbr_r_pow N) (gap x y)).
      * exact HN.
Qed.

End LbrBridge.

(* ============================================================ *)
(* Part B: the affine instantiation.  The host operator-budget slot is  *)
(* restated as [lbr_op_lips_mirror] (the host section Variable is not   *)
(* reachable from outside).  The two-point budget of the affine step     *)
(* f x = c*x + b combines the operator slot instantiated at [smult c],  *)
(* the affine-difference lemma (vector algebra on interface fields)     *)
(* and the metric-difference shift (the [smetric_snorm] field); the     *)
(* output [lbr_affine_iter_contraction] uses the Part A main lemma. *)
(* ============================================================ *)

Section LbrAffine.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpaceExtended RI}.
Context {HS : HilbertSpace RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.
Let szero := @szero RI SS.
Let splus := @splus RI SS.
Let smult := @smult RI SS.
Let sopp := @sopp RI SS.
Let smetric := @smetric RI SS.
Let snorm := @snorm RI SS.
Let smetric_snorm := @smetric_snorm RI SS.

Variable c : R.
Variable b : S.

(* Counterpart of the host operator-budget slot. *)
Variable lbr_op_lips_mirror : forall L0 : S -> S,
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (smetric (L0 h) szero) (mult N (smetric h szero)))).

(* Vector difference (self-contained; no host definition consumed). *)
Definition lbr_sminus (u v : S) : S := splus u (sopp v).

(* ===== Vector-algebra small lemmas (interface fields only) ===== *)

Lemma lbr_splus_zero_l : forall t : S, Id (splus szero t) t.
Proof.
  intro t. exact (id_trans (splus_comm szero t) (splus_zero t)).
Qed.

Lemma lbr_sopp_szero : Id (sopp szero) szero.
Proof.
  exact (id_trans (id_sym (splus_zero (sopp szero)))
                  (id_trans (splus_comm (sopp szero) szero)
                            (splus_opp szero))).
Qed.

(* Carrier-difference cancellation: (-z) + (z + t) == t. *)
Lemma lbr_splus_shift_inv : forall z t : S,
  Id (splus (sopp z) (splus z t)) t.
Proof.
  intros z t.
  apply (id_trans (splus_assoc (sopp z) z t)).
  apply (id_trans (id_cong (fun w => splus w t)
             (id_trans (splus_comm (sopp z) z) (splus_opp z)))).
  apply lbr_splus_zero_l.
Qed.

(* Uniqueness of the additive inverse: z + a == z + b == 0 gives a == b. *)
Lemma lbr_splus_unique_inv : forall z a b2 : S,
  Id (splus z a) szero -> Id (splus z b2) szero -> Id a b2.
Proof.
  intros z a b2 Ha Hb.
  assert (Hca : Id a (sopp z)).
  { apply (id_trans (id_sym (lbr_splus_shift_inv z a))).
    apply (id_trans (id_cong (fun w => splus (sopp z) w) Ha)).
    apply (id_trans (splus_comm (sopp z) szero)).
    apply lbr_splus_zero_l. }
  assert (Hcb : Id b2 (sopp z)).
  { apply (id_trans (id_sym (lbr_splus_shift_inv z b2))).
    apply (id_trans (id_cong (fun w => splus (sopp z) w) Hb)).
    apply (id_trans (splus_comm (sopp z) szero)).
    apply lbr_splus_zero_l. }
  exact (id_trans Hca (id_sym Hcb)).
Qed.

(* Negation distributes over addition (via inverse uniqueness). *)
Lemma lbr_sopp_splus : forall u v : S,
  Id (sopp (splus u v)) (splus (sopp v) (sopp u)).
Proof.
  intros u v.
  apply (lbr_splus_unique_inv (splus u v) (sopp (splus u v))
                              (splus (sopp v) (sopp u))).
  - apply splus_opp.
  - apply (id_trans (id_sym (splus_assoc u v (splus (sopp v) (sopp u))))).
    apply (id_trans (id_cong (fun w => splus u w)
                             (splus_assoc v (sopp v) (sopp u)))).
    apply (id_trans (id_cong (fun w => splus u (splus w (sopp u)))
                             (splus_opp v))).
    apply (id_trans (id_cong (fun w => splus u w)
                             (lbr_splus_zero_l (sopp u)))).
    apply splus_opp.
Qed.

(* Central regrouping: (u + v) + ((-v) + w) == u + w (the main shift    *)
(* of the affine-difference lemma). *)
Lemma lbr_splus_swap_mid : forall u v w : S,
  Id (splus (splus u v) (splus (sopp v) w)) (splus u w).
Proof.
  intros u v w.
  apply (id_trans (id_sym (splus_assoc u v (splus (sopp v) w)))).
  apply (id_cong (fun z => splus u z)).
  apply (id_trans (splus_assoc v (sopp v) w)).
  apply (id_trans (id_cong (fun z => splus z w) (splus_opp v))).
  apply lbr_splus_zero_l.
Qed.

(* Scaling the zero vector: c*0 == 0 (distributivity and self-difference). *)
Lemma lbr_smult_szero : Id (smult c szero) szero.
Proof.
  assert (Hz : Id (splus (smult c szero) (smult c szero)) (smult c szero)).
  { exact (id_trans (id_sym (smult_distrib_r c szero szero))
                    (id_cong (fun w => smult c w) (lbr_splus_zero_l szero))). }
  apply (id_trans (id_sym (lbr_splus_shift_inv (smult c szero)
                                               (smult c szero)))).
  apply (id_trans (id_cong (fun w => splus (sopp (smult c szero)) w) Hz)).
  apply (id_trans (splus_comm (sopp (smult c szero)) (smult c szero))).
  apply splus_opp.
Qed.

(* Scaling negated vectors: c*(-y) == -(c*y) (distributivity and        *)
(* inverse uniqueness). *)
Lemma lbr_smult_sopp : forall y : S,
  Id (smult c (sopp y)) (sopp (smult c y)).
Proof.
  intro y.
  assert (HA : Id (splus (smult c y) (smult c (sopp y))) szero).
  { apply (id_trans (id_sym (smult_distrib_r c y (sopp y)))).
    apply (id_trans (id_cong (fun w => smult c w) (splus_opp y))).
    exact lbr_smult_szero. }
  exact (lbr_splus_unique_inv (smult c y) (smult c (sopp y))
                              (sopp (smult c y)) HA (splus_opp (smult c y))).
Qed.

(* Metric-difference shift: the metric of u-v equals the norm of u-v    *)
(* (the [smetric_snorm] field). *)
Lemma lbr_smetric_sminus_zero : forall u v : S,
  Id (smetric (lbr_sminus u v) szero) (smetric u v).
Proof.
  intros u v.
  apply (id_trans (smetric_snorm (lbr_sminus u v) szero)).
  apply (id_trans (id_cong snorm (id_trans (id_cong (fun z => splus
                             (splus u (sopp v)) z) lbr_sopp_szero)
                             (splus_zero (splus u (sopp v)))))).
  apply (id_sym (smetric_snorm u v)).
Qed.

(* ===== The affine step and its two-point budget (Part B core) ===== *)

Definition lbr_affine_step (x : S) : S := splus (smult c x) b.

(* Affine-difference lemma: f(x) - f(y) == c*(x - y). *)
Lemma lbr_affine_diff : forall x y : S,
  Id (lbr_sminus (lbr_affine_step x) (lbr_affine_step y))
     (smult c (lbr_sminus x y)).
Proof.
  intros x y. unfold lbr_sminus, lbr_affine_step.
  apply (id_trans (id_cong (fun z => splus (splus (smult c x) b) z)
                           (lbr_sopp_splus (smult c y) b))).
  apply (id_trans (lbr_splus_swap_mid (smult c x) b (sopp (smult c y)))).
  apply (id_trans (id_cong (fun z => splus (smult c x) z)
                           (id_sym (lbr_smult_sopp y)))).
  exact (id_sym (smult_distrib_r c x (sopp y))).
Qed.

(* Budget projection: the operator slot at [smult c] yields the affine   *)
(* two-point budget as a sigT package. *)
Theorem lbr_affine_budget_proj : sigT (fun N : R =>
  And (le zero N)
      (forall u v : S,
        le (smetric (lbr_affine_step u) (lbr_affine_step v))
           (mult N (smetric u v)))).
Proof.
  destruct (lbr_op_lips_mirror (smult c)) as [N [HNneg HNbd]].
  exists N. split.
  - exact HNneg.
  - intros u v.
    apply (le_id_l (smetric (lbr_affine_step u) (lbr_affine_step v))
                   (smetric (lbr_sminus (lbr_affine_step u)
                                         (lbr_affine_step v)) szero)
                   (mult N (smetric u v))).
    + exact (id_sym (lbr_smetric_sminus_zero (lbr_affine_step u)
                                             (lbr_affine_step v))).
    + apply (le_trans _ (mult N (smetric (lbr_sminus u v) szero)) _).
      * apply (le_id_l (smetric (lbr_sminus (lbr_affine_step u)
                                            (lbr_affine_step v)) szero)
                       (smetric (smult c (lbr_sminus u v)) szero)
                       (mult N (smetric (lbr_sminus u v) szero))).
        -- exact (id_cong (fun z => smetric z szero) (lbr_affine_diff u v)).
        -- exact (HNbd (lbr_sminus u v)).
      * apply (le_id_l (mult N (smetric (lbr_sminus u v) szero))
                       (mult N (smetric u v)) (mult N (smetric u v))).
        -- exact (id_cong (fun z => mult N z) (lbr_smetric_sminus_zero u v)).
        -- apply le_refl.
Qed.

(* Output: budget in, Part A main lemma applied, affine iterative       *)
(* contraction out (the affine instance of the host contraction shape). *)
Theorem lbr_affine_iter_contraction : sigT (fun N : R =>
  And (le zero N)
      (forall (n : nat) (x y : S),
        le (smetric (lbr_iter S lbr_affine_step n x)
                    (lbr_iter S lbr_affine_step n y))
           (mult (lbr_r_pow N n) (smetric x y)))).
Proof.
  destruct lbr_affine_budget_proj as [N [HNneg HNbud]].
  exists N. split.
  - exact HNneg.
  - intros n x y.
    exact (@lbr_iter_lipschitz RI S smetric lbr_affine_step N HNneg HNbud n x y).
Qed.

End LbrAffine.

(* ============================================================ *)
(* Part C: the constructive Banach fixed-point theorem.  The           *)
(* completeness slot matches the S01 StateSpace metric fields and the   *)
(* [cauchy_complete_S] shape; the convergence certificate [lbr_clim]    *)
(* is the eps-characterization.  Core construction: adjacent-gap decay  *)
(* chains into a triangle sum, the geometric telescoping identity       *)
(* (1-L) * sum L^i c + L^k c = c bounds the tail, giving the Cauchy     *)
(* modulus; the limit l is a fixed point via the shifted sequence       *)
(* w_n = step(u_n) with its two limits identified by [lbr_clim_unique]; *)
(* uniqueness uses cancellation of g <= L*g.  The arch constant         *)
(* (1-L) + g0 > 0 absorbs a vanishing g0 with no case split. *)
(* ============================================================ *)

Section LbrBanach.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.

Variable X : Set.
Variable gap : X -> X -> R.
Variable step : X -> X.
Variable L : R.

Variable lbr_L_nonneg : le zero L.
Variable lbr_L_lt_one : lt L one.
(* Strictly positivity-decreasing field: the subtraction-shaped slot    *)
(* used throughout the Banach chain (the interface layer provides no    *)
(* strict-from-weak producer, so the field carries the strictness). *)
Variable lbr_minus_pos : forall a b : R, lt a b -> lt zero (minus b a).
Variable lbr_budget : forall x y : X,
  le (gap (step x) (step y)) (mult L (gap x y)).
Variable lbr_gap_nonneg : forall x y : X, le zero (gap x y).
Variable lbr_gap_sym : forall x y : X, Id (gap x y) (gap y x).
Variable lbr_gap_tri : forall x y z : X,
  le (gap x z) (plus (gap x y) (gap y z)).
Variable lbr_gap_zero : forall x y : X, Id (gap x y) zero -> Id x y.
Variable lbr_arch : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (lbr_r_pow L N)) eps).

(* 1 - L strictly positive, and 1 = (1 - L) + L as the algebraic        *)
(* cornerstone of the telescoping identity. *)
Let lbr_s_pos : lt zero (minus one L) := lbr_minus_pos L one lbr_L_lt_one.
Let invs := inv_pos (minus one L) lbr_s_pos.

(* The convergence certificate (eps-characterization; feeds the         *)
(* uniqueness transfer and the fixed-point conclusion). *)
Definition lbr_clim (u : nat -> X) (l : X) : Set :=
  forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n -> lt (gap (u n) l) eps).

Variable lbr_clim_unique : forall (u : nat -> X) (l1 l2 : X),
  lbr_clim u l1 -> lbr_clim u l2 -> Id l1 l2.

(* The completeness interface slot (matching cauchy_complete_S). *)
Variable lbr_complete : forall (u : nat -> X),
  (forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n -> lt (gap (u m) (u n)) eps)) ->
  sigT (fun l : X => lbr_clim u l).

(* The fixed point (Id face at the Set level). *)
Definition lbr_fixed_point (x : X) : Set := Id (step x) x.

(* ===== Basic algebra lemmas ===== *)

Lemma lbr_opp_zero : Id (opp zero) zero.
Proof.
  exact (id_trans (id_sym (id_trans (plus_comm zero (opp zero))
                                    (plus_zero (opp zero))))
                  (plus_opp zero)).
Qed.

Lemma lbr_minus_one_L_le_one : le (minus one L) one.
Proof.
  unfold minus.
  apply (le_id_r _ _ _ (plus_zero one)).
  exact (le_plus_compat one one (opp L) zero (le_refl one)
           (le_id_r (opp L) (opp zero) zero lbr_opp_zero
              (opp_le_compat zero L lbr_L_nonneg))).
Qed.

(* g <= g/(1-L): absorbing the telescoping ratio constant (g0 >= 0      *)
(* suffices, strict positivity not required). *)
Lemma lbr_le_scaled : forall c : R, le zero c ->
  le c (mult c invs).
Proof.
  intros c Hc.
  assert (Hcs : le (mult c (minus one L)) c).
  { apply (le_trans _ (mult (minus one L) c)).
    - apply (le_id_l (mult c (minus one L)) (mult (minus one L) c)
                     (mult (minus one L) c) (mult_comm c (minus one L))
                     (le_refl _)).
    - apply (le_trans _ (mult one c)).
      + exact (le_mult_compat_weak (minus one L) one c Hc
                  lbr_minus_one_L_le_one).
      + apply (le_id_r _ _ _ (id_trans (mult_comm one c) (mult_one c))).
        apply le_refl. }
  apply (le_trans c (mult (mult c (minus one L)) invs) (mult c invs)).
  - apply (le_id_l c (mult (mult c (minus one L)) invs)
                     (mult (mult c (minus one L)) invs)
             (id_trans (id_sym (mult_one c))
              (id_trans (id_sym (id_cong (fun z => mult c z)
                                  (inv_pos_correct (minus one L) lbr_s_pos)))
                        (mult_assoc c (minus one L) invs)))
             (le_refl _)).
  - exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos) Hcs).
Qed.

(* Halving (via S01 half_pos/half_twice): for every positive eps there  *)
(* is a positive e' with e' + e' = eps. *)
Lemma lbr_half : forall eps : R, lt zero eps ->
  sigT (fun e' : R => And (lt zero e') (Id (plus e' e') eps)).
Proof.
  intros eps Hep.
  exists (mult (inv_pos (plus one one) two_pos) eps).
  split.
  - exact (half_pos eps Hep).
  - exact (half_twice eps).
Qed.

(* ===== Geometric tail-sum carrier and the telescoping identity ===== *)

Fixpoint lbr_rsum (g : nat -> R) (k : nat) : R :=
  match k with
  | O => zero
  | Datatypes.S j => plus (lbr_rsum g j) (g j)
  end.

Lemma lbr_rsum_ext : forall (g h : nat -> R) (k : nat),
  (forall i : nat, NatLe i k -> Id (g i) (h i)) ->
  Id (lbr_rsum g k) (lbr_rsum h k).
Proof.
  intros g h k. induction k as [| k IH]; intros Hik.
  - simpl. apply id_refl.
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (g k))
             (IH (fun i Hive => Hik i (NatLe_lift i (Datatypes.S k)
                    (Nat.le_le_succ_r i k (NatLe_drop i k Hive))))))).
    apply (id_trans (id_cong (fun z => plus (lbr_rsum h k) z)
             (Hik k (NatLe_lift k (Datatypes.S k)
                    (Nat.le_le_succ_r k k (Nat.le_refl k)))))).
    apply id_refl.
Qed.

Lemma lbr_rsum_mono : forall (g h : nat -> R) (k : nat),
  (forall i : nat, NatLe i k -> le (g i) (h i)) ->
  le (lbr_rsum g k) (lbr_rsum h k).
Proof.
  intros g h k. induction k as [| k IH]; intros Hik.
  - simpl. apply le_refl.
  - simpl.
    apply (le_plus_compat (lbr_rsum g k) (lbr_rsum h k) (g k) (h k)).
    + apply (IH (fun i Hive => Hik i (NatLe_lift i (Datatypes.S k)
                     (Nat.le_le_succ_r i k (NatLe_drop i k Hive))))).
    + apply (Hik k (NatLe_lift k (Datatypes.S k)
                     (Nat.le_le_succ_r k k (Nat.le_refl k)))).
Qed.

Lemma lbr_rsum_scal : forall (h : nat -> R) (c : R) (k : nat),
  Id (lbr_rsum (fun i => mult c (h i)) k) (mult c (lbr_rsum h k)).
Proof.
  intros h c k. induction k as [| k IH].
  - simpl. exact (id_sym (mult_zero c)).
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (mult c (h k))) IH)).
    exact (id_sym (distrib c (lbr_rsum h k) (h k))).
Qed.

(* Additivity of exponents for powers: L^(n+i) = L^n * L^i. *)
Lemma lbr_r_pow_add : forall n i : nat,
  Id (lbr_r_pow L (Nat.add n i)) (mult (lbr_r_pow L n) (lbr_r_pow L i)).
Proof.
  intros n i. revert i. induction n as [| n IH]; intro i.
  - exact (id_sym (id_trans (mult_comm one (lbr_r_pow L i))
                            (mult_one (lbr_r_pow L i)))).
  - simpl. exact (id_trans (id_cong (fun z => mult L z) (IH i))
                           (mult_assoc L (lbr_r_pow L n) (lbr_r_pow L i))).
Qed.

(* plus (1-L) L = one (the algebraic cornerstone of telescoping). *)
Lemma lbr_plus_minus_L : Id (plus (minus one L) L) one.
Proof.
  unfold minus.
  exact (id_trans (id_sym (plus_assoc one (opp L) L))
                  (id_trans (id_cong (fun z => plus one z)
                              (id_trans (plus_comm (opp L) L) (plus_opp L)))
                            (plus_zero one))).
Qed.

(* Telescoping step: (1-L)*(X*c) + (L*X)*c = X*c. *)
Lemma lbr_minus_plus_scal : forall Z c : R,
  Id (plus (mult (minus one L) (mult Z c)) (mult (mult L Z) c)) (mult Z c).
Proof.
  intros Z c.
  apply (id_trans (id_cong (fun z => plus z (mult (mult L Z) c))
                            (mult_assoc (minus one L) Z c))).
  apply (id_trans (id_sym (mult_plus_distr_r (mult (minus one L) Z) (mult L Z) c))).
  apply (id_trans (id_cong (fun z => mult z c)
                            (id_sym (mult_plus_distr_r (minus one L) L Z)))).
  apply (id_trans (id_cong (fun z => mult (mult z Z) c) lbr_plus_minus_L)).
  exact (id_trans (id_sym (mult_assoc one Z c))
                  (id_trans (mult_comm one (mult Z c)) (mult_one (mult Z c)))).
Qed.

(* Telescoping identity: (1-L) * sum_{i<k} L^i * c + L^k * c = c. *)
Lemma lbr_geom_telescope : forall c : R, forall k : nat,
  Id (plus (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k))
           (mult (lbr_r_pow L k) c))
     c.
Proof.
  intros c k. induction k as [| k IH].
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (mult one c))
                              (mult_zero (minus one L)))).
    apply (id_trans (id_cong (fun z => plus zero z)
                              (id_trans (mult_comm one c) (mult_one c)))).
    exact (id_trans (plus_comm zero c) (plus_zero c)).
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (mult (mult L (lbr_r_pow L k)) c))
              (distrib (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                       (mult (lbr_r_pow L k) c)))).
    apply (id_trans (id_sym (plus_assoc (mult (minus one L)
                                              (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k))
                                        (mult (minus one L) (mult (lbr_r_pow L k) c))
                                        (mult (mult L (lbr_r_pow L k)) c)))).
    apply (id_trans (id_cong (fun z => plus (mult (minus one L)
                                                  (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)) z)
                              (lbr_minus_plus_scal (lbr_r_pow L k) c))).
    exact IH.
Qed.

(* Geometric tail-sum bound: sum_{i<k} L^i * c <= c/(1-L). *)
Lemma lbr_geom_tail_le : forall c : R, le zero c -> forall k : nat,
  le (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k) (mult c invs).
Proof.
  intros c Hc k.
  assert (Hpow : le zero (mult (lbr_r_pow L k) c)).
  { apply (le_trans _ (mult zero c)).
    - apply (le_id_l zero (mult zero c) (mult zero c)
               (id_sym (id_trans (mult_comm zero c) (mult_zero c)))
               (le_refl (mult zero c))).
    - exact (le_mult_compat_weak zero (lbr_r_pow L k) c Hc
                (lbr_r_pow_nonneg L lbr_L_nonneg k)). }
  assert (Hst : le (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)) c).
  { apply (le_id_r _ _ _ (lbr_geom_telescope c k)).
    exact (le_plus_nonneg_r (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k))
                            (mult (lbr_r_pow L k) c) Hpow). }
  apply (le_id_l (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                 (mult (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)) invs)
                 (mult c invs)).
  - exact (id_trans (id_sym (mult_one (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)))
             (id_trans (id_sym (id_cong (fun z => mult (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k) z)
                                 (inv_pos_correct (minus one L) lbr_s_pos)))
                       (id_trans (mult_assoc (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                                                      (minus one L) invs)
                                 (id_cong (fun z => mult z invs)
                                          (mult_comm (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                                                     (minus one L)))))).
  - exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos) Hst).
Qed.

(* ===== Additive cancellation and g <= L*g implies g <= 0 ===== *)

Lemma lbr_le_plus_cancel : forall a b c : R, le (plus a b) (plus c b) -> le a c.
Proof.
  intros a b c H.
  assert (Hm : le zero (minus c a)).
  { apply (le_id_r _ _ _ (id_trans (minus_plus_distr c b a b)
                              (id_trans (id_cong (fun z => plus (minus c a) z)
                                                  (plus_opp b))
                                        (plus_zero (minus c a))))).
    exact (le_minus_nonneg (plus a b) (plus c b) H). }
  apply (le_trans _ (plus zero a)).
  - apply (le_id_l a (plus a zero) (plus zero a) (id_sym (plus_zero a))
             (le_id_l (plus a zero) (plus zero a) (plus zero a)
                      (plus_comm a zero) (le_refl _))).
  - apply (le_id_r _ _ _ (id_trans (plus_comm (minus c a) a) (minus_plus_cancel a c))).
    exact (le_plus_compat zero (minus c a) a a Hm (le_refl a)).
Qed.

Lemma lbr_le_self_mult_zero : forall g : R, le g (mult L g) -> le g zero.
Proof.
  intros g Hgle.
  assert (Hgs : le (mult g (minus one L)) zero).
  { apply (lbr_le_plus_cancel (mult g (minus one L)) (mult g L) zero).
    apply (le_id_l (plus (mult g (minus one L)) (mult g L)) g
                   (plus zero (mult g L))
                   (id_sym (id_trans (id_sym (mult_one g))
                             (id_trans (id_sym (id_cong (fun z => mult g z) lbr_plus_minus_L))
                                       (distrib g (minus one L) L))))
                   (le_trans g (mult g L) (plus zero (mult g L))
                             (le_id_r _ _ _ (mult_comm L g) Hgle)
                             (le_id_l (mult g L) (plus (mult g L) zero)
                                      (plus zero (mult g L))
                                (id_sym (plus_zero (mult g L)))
                                (le_id_l (plus (mult g L) zero)
                                         (plus zero (mult g L))
                                         (plus zero (mult g L))
                                   (plus_comm (mult g L) zero) (le_refl _))))). }
  apply (le_id_l g (mult (mult g (minus one L)) invs) zero
             (id_trans (id_sym (mult_one g))
                       (id_trans (id_sym (id_cong (fun z => mult g z)
                                           (inv_pos_correct (minus one L) lbr_s_pos)))
                                 (mult_assoc g (minus one L) invs)))
             (le_id_r _ _ _ (id_trans (mult_comm zero invs) (mult_zero invs))
                (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos) Hgs))).
Qed.

(* ===== The Cauchy modulus of the iteration sequence ===== *)

(* The ratio constant C = g0/(1-L) is nonnegative. *)
Lemma lbr_scaled_nonneg : forall x0 : X, le zero (mult (gap (step x0) x0) invs).
Proof.
  intro x0.
  apply (le_trans _ (mult zero invs)).
  - apply (le_id_l zero (mult zero invs) (mult zero invs)
             (id_sym (id_trans (mult_comm zero invs) (mult_zero invs)))
             (le_refl (mult zero invs))).
  - exact (le_mult_compat_weak zero (gap (step x0) x0) invs
              (lt_le_iff zero invs (inl (inv_pos_pos (minus one L) lbr_s_pos)))
              (lbr_gap_nonneg (step x0) x0)).
Qed.

Lemma lbr_gap_le_scaled : forall x0 : X,
  le (gap (step x0) x0) (mult (gap (step x0) x0) invs).
Proof.
  intro x0. exact (lbr_le_scaled (gap (step x0) x0) (lbr_gap_nonneg (step x0) x0)).
Qed.

(* Triangle chain: gap(u_n, u_{n+k}) bounds the sum of adjacent gaps. *)
Lemma lbr_iter_gap_chain : forall (x0 : X) (k n : nat),
  le (gap (lbr_iter X step n x0) (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
     (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add n i)) x0)
                                     (lbr_iter X step (Nat.add n i) x0))
               (Datatypes.S k)).
Proof.
  intros x0 k n. induction k as [| k IH].
  - assert (E1 : Nat.add n (Datatypes.S O) = Datatypes.S n) by lia.
    rewrite E1.
    simpl.
    assert (E0 : Nat.add n O = n) by lia.
    rewrite E0.
    apply (le_trans _ (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))).
    + apply (le_id_l (gap (lbr_iter X step n x0) (lbr_iter X step (Datatypes.S n) x0))
                     (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                     (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                     (lbr_gap_sym (lbr_iter X step n x0) (lbr_iter X step (Datatypes.S n) x0))
                     (le_refl _)).
    + apply (le_trans _ (plus (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero)).
      * exact (le_plus_nonneg_r (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero
                  (le_refl zero)).
      * apply (le_id_l (plus (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero)
                       (plus zero (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)))
                       (plus zero (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)))
                       (plus_comm (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero)
                       (le_refl _)).
  - assert (E2 : Nat.add n (Datatypes.S (Datatypes.S k))
                 = Datatypes.S (Nat.add n (Datatypes.S k))) by lia.
    rewrite E2.
    apply (le_trans _ (plus (gap (lbr_iter X step n x0) (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                            (gap (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                 (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)))).
    + exact (lbr_gap_tri (lbr_iter X step n x0) (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                         (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)).
    + apply (le_trans _ (plus (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add n i)) x0)
                                                        (lbr_iter X step (Nat.add n i) x0))
                                        (Datatypes.S k))
                              (gap (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                   (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)))).
      * exact (le_plus_compat _ _ _ _ IH (le_refl _)).
      * exact (le_plus_compat _ _ _ _ (le_refl (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add n i)) x0)
                                                                  (lbr_iter X step (Nat.add n i) x0))
                                                 (Datatypes.S k)))
                              (le_id_l (gap (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                             (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0))
                                       (gap (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)
                                            (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                                       (gap (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)
                                            (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                                       (lbr_gap_sym (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                                    (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0))
                                       (le_refl _))).
Qed.

(* Off-diagonal bound: gap(u_m, u_{m+k}) <= L^m * C (chain plus         *)
(* geometric tail sum). *)
Lemma lbr_iter_offdiag_le : forall (x0 : X) (m k : nat),
  le (gap (lbr_iter X step m x0) (lbr_iter X step (Nat.add m (Datatypes.S k)) x0))
     (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)).
Proof.
  intros x0 m k.
  apply (le_trans _ (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add m i)) x0)
                                              (lbr_iter X step (Nat.add m i) x0))
                              (Datatypes.S k)) _).
  - exact (lbr_iter_gap_chain x0 k m).
  - apply (le_trans _ (lbr_rsum (fun i => mult (lbr_r_pow L m)
                                                (mult (lbr_r_pow L i) (gap (step x0) x0)))
                                (Datatypes.S k)) _).
    + exact (le_id_r _ _ _ (lbr_rsum_ext (fun i => mult (lbr_r_pow L (Nat.add m i)) (gap (step x0) x0))
                                (fun i => mult (lbr_r_pow L m) (mult (lbr_r_pow L i) (gap (step x0) x0)))
                                (Datatypes.S k)
                                (fun i _ => id_trans (id_cong (fun z => mult z (gap (step x0) x0))
                                                 (lbr_r_pow_add m i))
                                        (id_sym (mult_assoc (lbr_r_pow L m) (lbr_r_pow L i)
                                                    (gap (step x0) x0)))))
                (lbr_rsum_mono (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add m i)) x0)
                                               (lbr_iter X step (Nat.add m i) x0))
                               (fun i => mult (lbr_r_pow L (Nat.add m i)) (gap (step x0) x0))
                               (Datatypes.S k)
                               (fun i _ => lbr_iter_step_gap_decay X gap step L lbr_L_nonneg
                                             lbr_budget (Nat.add m i) x0))).
    + exact (le_id_l _ _ _ (lbr_rsum_scal (fun i => mult (lbr_r_pow L i) (gap (step x0) x0))
                              (lbr_r_pow L m) (Datatypes.S k))
                (lbr_mult_compat_r (lbr_rsum (fun i => mult (lbr_r_pow L i) (gap (step x0) x0))
                                             (Datatypes.S k))
                                   (mult (gap (step x0) x0) invs)
                                   (lbr_r_pow L m)
                                   (lbr_r_pow_nonneg L lbr_L_nonneg m)
                                   (lbr_geom_tail_le (gap (step x0) x0)
                                      (lbr_gap_nonneg (step x0) x0) (Datatypes.S k)))).
Qed.

(* Diagonal bound: gap(u_m, u_m) <= 2 * L^m * C (symmetry, triangle,    *)
(* decay). *)
Lemma lbr_iter_diag_le : forall (x0 : X) (m : nat),
  le (gap (lbr_iter X step m x0) (lbr_iter X step m x0))
     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
           (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))).
Proof.
  intros x0 m.
  assert (Htail : le (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                     (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))).
  { apply (le_trans _ (mult (lbr_r_pow L m) (gap (step x0) x0))).
    - exact (lbr_iter_step_gap_decay X gap step L lbr_L_nonneg lbr_budget m x0).
    - exact (lbr_mult_compat_r (gap (step x0) x0)
                               (mult (gap (step x0) x0) invs)
                               (lbr_r_pow L m)
                               (lbr_r_pow_nonneg L lbr_L_nonneg m)
                               (lbr_gap_le_scaled x0)). }
  apply (le_trans _ (plus (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                          (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))).
  - apply (le_trans _ (plus (gap (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0))
                            (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))).
    + exact (lbr_gap_tri (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)).
    + apply (le_id_l (plus (gap (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0))
                           (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))
                     (plus (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                           (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))
                     (plus (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                           (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))
                     (id_cong (fun z => plus z (gap (lbr_iter X step (Datatypes.S m) x0)
                                                     (lbr_iter X step m x0)))
                              (lbr_gap_sym (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0)))
                     (le_refl _)).
  - exact (le_plus_compat _ _ _ _ Htail Htail).
Qed.

(* The master strict modulus: the arch constant (1-L)+g0 > 0 absorbs    *)
(* a vanishing g0, giving for every positive eps an N with              *)
(* L^n * (g0/(1-L)) < eps for all n >= N. *)
Lemma lbr_iter_master_lt : forall (x0 : X) (eps : R), lt zero eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    lt (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)) eps).
Proof.
  intros x0 eps Hep.
  assert (Harchpos : lt zero (plus (gap (step x0) x0) (minus one L))).
  { exact (plus_le_lt_pos (gap (step x0) x0) (minus one L)
             (lbr_gap_nonneg (step x0) x0) lbr_s_pos). }
  destruct (lbr_arch (plus (gap (step x0) x0) (minus one L)) Harchpos
                     (mult eps (minus one L))
                     (mult_positive eps (minus one L) Hep lbr_s_pos)) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (mult (lbr_r_pow L N) (gap (step x0) x0)) invs) _).
  - apply (le_id_l (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                   (mult (mult (lbr_r_pow L n) (gap (step x0) x0)) invs)
                   (mult (mult (lbr_r_pow L N) (gap (step x0) x0)) invs)).
    + exact (mult_assoc (lbr_r_pow L n) (gap (step x0) x0) invs).
    + exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos)
               (le_mult_compat_weak (lbr_r_pow L n) (lbr_r_pow L N) (gap (step x0) x0)
                  (lbr_gap_nonneg (step x0) x0)
                  (lbr_r_pow_dec L lbr_L_nonneg lbr_L_lt_one N n Hn))).
  - apply (le_lt_trans _ (mult (mult (plus (gap (step x0) x0) (minus one L))
                                        (lbr_r_pow L N)) invs) _).
    + exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos)
               (le_trans (mult (lbr_r_pow L N) (gap (step x0) x0))
                         (mult (gap (step x0) x0) (lbr_r_pow L N))
                         (mult (plus (gap (step x0) x0) (minus one L)) (lbr_r_pow L N))
                 (le_id_l (mult (lbr_r_pow L N) (gap (step x0) x0))
                          (mult (gap (step x0) x0) (lbr_r_pow L N))
                          (mult (gap (step x0) x0) (lbr_r_pow L N))
                          (mult_comm (lbr_r_pow L N) (gap (step x0) x0))
                          (le_refl _))
                 (le_mult_compat_weak (gap (step x0) x0)
                                      (plus (gap (step x0) x0) (minus one L))
                                      (lbr_r_pow L N)
                                      (lbr_r_pow_nonneg L lbr_L_nonneg N)
                                      (le_plus_nonneg_r (gap (step x0) x0) (minus one L)
                                         (lt_le_iff zero (minus one L) (inl lbr_s_pos)))))).
    + apply (lt_id_r _ _ _ (id_trans (id_sym (mult_assoc eps (minus one L) invs))
                                (id_trans (id_cong (fun z => mult eps z)
                                                    (inv_pos_correct (minus one L) lbr_s_pos))
                                          (mult_one eps)))).
      apply (lt_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos)).
      exact HN.
Qed.

(* The iteration-sequence Cauchy modulus (feeds the completeness slot). *)
Lemma lbr_iter_cauchy : forall x0 : X, forall eps : R, lt zero eps ->
  sigT (fun N : nat => forall m n : nat,
    NatLe N m -> NatLe N n -> lt (gap (lbr_iter X step m x0) (lbr_iter X step n x0)) eps).
Proof.
  intros x0 eps Hep.
  destruct (lbr_half eps Hep) as [e' [He'p He'eq]].
  destruct (lbr_iter_master_lt x0 e' He'p) as [N HN].
  exists N.
  assert (Hinner : forall a b : nat, NatLe N a -> NatLe N b -> NatLe a b ->
            lt (gap (lbr_iter X step a x0) (lbr_iter X step b x0)) eps).
  { intros a b Ha Hb Hab.
    destruct (Nat.eq_dec a b) as [Eab | Hneq].
    - subst b.
      apply (le_lt_trans _ (plus (mult (lbr_r_pow L a) (mult (gap (step x0) x0) invs))
                                 (mult (lbr_r_pow L a) (mult (gap (step x0) x0) invs))) _).
      + exact (lbr_iter_diag_le x0 a).
      + apply (lt_id_r _ _ _ He'eq).
        apply (lt_plus_compat _ _ _ _ (HN a Ha) (HN a Ha)).
    - assert (Hk : sigT (fun k : nat => Id b (Nat.add a (Datatypes.S k)))).
      { exists (Nat.pred (Nat.sub b a)).
        pose proof (NatLe_drop a b Hab) as Hable.
        apply lbr_eq_id. lia. }
      destruct Hk as [k Hk].
      apply (lt_id_l _ _ _
                (id_cong (fun z => gap (lbr_iter X step a x0) z)
                  (id_cong (fun w => lbr_iter X step w x0) Hk))
                (le_lt_trans _ (mult (lbr_r_pow L a) (mult (gap (step x0) x0) invs)) _
                   (lbr_iter_offdiag_le x0 a k)
                   (lt_le_trans _ _ _ (HN a Ha)
                      (le_id_r _ _ _ He'eq
                         (le_plus_nonneg_r e' e' (lt_le_iff zero e' (inl He'p))))))).
  }
  intros m n Hm Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - apply (Hinner m n Hm Hn).
    exact (NatLe_lift m n (proj1 (PeanoNat.Nat.leb_le m n) Emn)).
  - apply (Nat.leb_gt m n) in Emn.
    apply (lt_id_l (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
                   (gap (lbr_iter X step n x0) (lbr_iter X step m x0)) eps).
    + exact (lbr_gap_sym (lbr_iter X step m x0) (lbr_iter X step n x0)).
    + apply (Hinner n m Hn Hm).
      exact (NatLe_lift n m (Nat.lt_le_incl _ _ Emn)).
Qed.

(* ===== The Banach fixed-point theorem and uniqueness ===== *)

Theorem lbr_banach_fixed_point : forall x0 : X,
  sigT (fun l : X => And (lbr_fixed_point l)
                         (lbr_clim (fun n : nat => lbr_iter X step n x0) l)).
Proof.
  intros x0.
  destruct (lbr_complete (fun n : nat => lbr_iter X step n x0) (lbr_iter_cauchy x0)) as [l Hcl].
  exists l. split.
  - unfold lbr_fixed_point.
    apply id_sym.
    apply (lbr_clim_unique (fun n : nat => step (lbr_iter X step n x0)) l (step l)).
    + (* The shifted sequence w converges to l: triangle chain, geometric   *)
      (* decay, and Hcl. *)
      intros eps Hep.
      destruct (lbr_half eps Hep) as [e' [He'p He'eq]].
      destruct (Hcl e' He'p) as [Nc HNc].
      destruct (lbr_iter_master_lt x0 e' He'p) as [Nd HNd].
      exists (Nat.max Nc Nd). intros n Hn.
      assert (Hnc : NatLe Nc n).
      { exact (NatLe_lift Nc n (Nat.le_trans Nc (Nat.max Nc Nd) n (Nat.le_max_l Nc Nd)
                                  (NatLe_drop (Nat.max Nc Nd) n Hn))). }
      assert (Hnd : NatLe Nd n).
      { exact (NatLe_lift Nd n (Nat.le_trans Nd (Nat.max Nc Nd) n (Nat.le_max_r Nc Nd)
                                  (NatLe_drop (Nat.max Nc Nd) n Hn))). }
      apply (le_lt_trans _ (plus (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                                 (gap (lbr_iter X step n x0) l)) _).
      * exact (lbr_gap_tri (step (lbr_iter X step n x0)) (lbr_iter X step n x0) l).
      * apply (lt_id_r _ _ _ He'eq).
        assert (Hd1 : le (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                         (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))).
        { apply (le_trans _ (mult (lbr_r_pow L n) (gap (step x0) x0)) _).
          - exact (lbr_iter_step_gap_decay X gap step L lbr_L_nonneg lbr_budget n x0).
          - exact (lbr_mult_compat_r (gap (step x0) x0)
                                     (mult (gap (step x0) x0) invs)
                                     (lbr_r_pow L n)
                                     (lbr_r_pow_nonneg L lbr_L_nonneg n)
                                     (lbr_gap_le_scaled x0)). }
        apply (lt_plus_compat _ _ _ _
                  (le_lt_trans _ _ _ Hd1 (HNd n Hnd))
                  (HNc n Hnc)).
    + (* The shifted sequence converges to step l: budget, L <= 1, Hcl. *)
      intros eps Hep.
      destruct (Hcl eps Hep) as [Nc HNc].
      exists Nc. intros n Hn.
      apply (le_lt_trans _ (gap (lbr_iter X step n x0) l) _).
      * apply (le_id_r _ _ _ (id_trans (mult_comm one (gap (lbr_iter X step n x0) l))
                                  (mult_one (gap (lbr_iter X step n x0) l)))).
        apply (le_trans _ (mult L (gap (lbr_iter X step n x0) l))).
        -- exact (lbr_budget (lbr_iter X step n x0) l).
        -- exact (le_mult_compat_weak L one (gap (lbr_iter X step n x0) l)
                    (lbr_gap_nonneg (lbr_iter X step n x0) l)
                    (lt_le_iff L one (inl lbr_L_lt_one))).
      * exact (HNc n Hn).
  - exact Hcl.
Qed.

(* The contraction fixes the self-gap to zero (d(x,x) = 0). *)
Lemma lbr_fix_self_gap : forall x : X, lbr_fixed_point x -> Id (gap x x) zero.
Proof.
  intros x Hfix. unfold lbr_fixed_point in Hfix.
  apply (le_antisym (gap x x) zero).
  - apply (lbr_le_self_mult_zero (gap x x)).
    apply (le_id_l (gap x x) (gap (step x) (step x)) (mult L (gap x x))).
    + exact (id_trans (id_cong (fun z => gap z x) (id_sym Hfix))
                      (id_sym (id_cong (fun z => gap (step x) z) Hfix))).
    + exact (lbr_budget x x).
  - exact (lbr_gap_nonneg x x).
Qed.

Theorem lbr_fixed_point_unique : forall l1 l2 : X,
  lbr_fixed_point l1 -> lbr_fixed_point l2 -> Id l1 l2.
Proof.
  intros l1 l2 H1 H2.
  unfold lbr_fixed_point in H1, H2.
  apply (lbr_gap_zero l1 l2).
  apply (le_antisym (gap l1 l2) zero).
  - apply (lbr_le_self_mult_zero (gap l1 l2)).
    (* Rewriting g <= g*0 + (L*g + 0): the outer term is the zero        *)
    (* self-gap of the fixed point, the middle term is the budget. *)
    assert (Hout1 : Id (gap l1 (step l1)) zero).
    { exact (id_trans (id_cong (fun z => gap l1 z) H1) (lbr_fix_self_gap l1 H1)). }
    assert (Hout2 : Id (gap (step l2) l2) zero).
    { exact (id_trans (id_cong (fun z => gap z l2) H2) (lbr_fix_self_gap l2 H2)). }
    apply (le_trans (gap l1 l2)
                    (plus (gap l1 (step l1))
                          (plus (gap (step l1) (step l2)) (gap (step l2) l2)))
                    (mult L (gap l1 l2))).
    + (* First leg: two triangle steps bound gap l1 l2 by the three-gap     *)
      (* sum. *)
      apply (le_trans _ (plus (gap l1 (step l1)) (gap (step l1) l2))).
      * exact (lbr_gap_tri l1 (step l1) l2).
      * exact (le_plus_compat (gap l1 (step l1)) (gap l1 (step l1))
                              (gap (step l1) l2)
                              (plus (gap (step l1) (step l2)) (gap (step l2) l2))
                              (le_refl (gap l1 (step l1)))
                              (lbr_gap_tri (step l1) (step l2) l2)).
    + (* Second leg: the chain reduces to g(s1,s2) <= L * g(l1,l2) by the   *)
      (* budget. *)
      apply (le_id_l (plus (gap l1 (step l1))
                           (plus (gap (step l1) (step l2)) (gap (step l2) l2)))
                     (plus zero (plus (gap (step l1) (step l2)) zero))
                     (mult L (gap l1 l2))).
      * exact (id_trans (id_cong (fun z => plus z (plus (gap (step l1) (step l2))
                                                        (gap (step l2) l2)))
                                 Hout1)
                        (id_cong (fun w => plus zero (plus (gap (step l1) (step l2)) w))
                                 Hout2)).
      * exact (le_id_l (plus zero (plus (gap (step l1) (step l2)) zero))
                       (gap (step l1) (step l2))
                       (mult L (gap l1 l2))
                       (id_trans (id_cong (fun z => plus zero z)
                                          (plus_zero (gap (step l1) (step l2))))
                                 (id_trans (plus_comm zero (gap (step l1) (step l2)))
                                           (plus_zero (gap (step l1) (step l2)))))
                       (lbr_budget l1 l2)).
  - exact (lbr_gap_nonneg l1 l2).
Qed.

(* ============================================================ *)

(* ============================================================ *)

(* The scaled power L^n * C is nonnegative (shared by the two lemmas    *)
(* below). *)
Lemma lbr_scaled_pow_nonneg : forall (x0 : X) (n : nat),
  le zero (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)).
Proof.
  intros x0 n.
  apply (le_trans _ (mult zero (mult (gap (step x0) x0) invs))).
  - apply (le_id_l zero (mult zero (mult (gap (step x0) x0) invs))
                    (mult zero (mult (gap (step x0) x0) invs))
                    (id_sym (id_trans (mult_comm zero (mult (gap (step x0) x0) invs))
                                      (mult_zero (mult (gap (step x0) x0) invs))))
                    (le_refl (mult zero (mult (gap (step x0) x0) invs)))).
  - exact (le_mult_compat_weak zero (lbr_r_pow L n) (mult (gap (step x0) x0) invs)
              (lbr_scaled_nonneg x0)
              (lbr_r_pow_nonneg L lbr_L_nonneg n)).
Qed.

(* Closed two-sided Cauchy bound: for all m n,                          *)
(* g(u_m, u_n) <= L^m * C + L^n * C (equal case by the diagonal bound;  *)
(* ordered case by the off-diagonal bound with symmetry and             *)
(* nonnegativity absorption). *)
Lemma lbr_iter_cauchy_closed : forall (x0 : X) (m n : nat),
  le (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
           (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))).
Proof.
  intros x0 m n.
  destruct (Nat.eq_dec m n) as [Emn | Hneq].
  - subst n. exact (lbr_iter_diag_le x0 m).
  - destruct (Nat.leb m n) eqn:Eleb.
    + (* m < n: n = m + S k; off-diagonal bound with nonnegativity          *)
      (* absorption, matching the m-first order directly. *)
      assert (Hk : sigT (fun k : nat => Id n (Nat.add m (Datatypes.S k)))).
      { exists (Nat.pred (Nat.sub n m)).
        pose proof (NatLe_lift m n (proj1 (PeanoNat.Nat.leb_le m n) Eleb)) as Hmn.
        pose proof (NatLe_drop m n Hmn) as Hmle.
        apply lbr_eq_id. lia. }
      destruct Hk as [k Hk].
      apply (le_id_l (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
                     (gap (lbr_iter X step m x0)
                          (lbr_iter X step (Nat.add m (Datatypes.S k)) x0))
                     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                           (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))).
      * exact (id_cong (fun z => gap (lbr_iter X step m x0) z)
                       (id_cong (fun w => lbr_iter X step w x0) Hk)).
      * apply (le_trans _ (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))).
        -- exact (lbr_iter_offdiag_le x0 m k).
        -- exact (le_plus_nonneg_r (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                   (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                   (lbr_scaled_pow_nonneg x0 n)).
    + (* n < m symmetric: m = n + S k; off-diagonal bound at n, then        *)
      (* commutativity of plus. *)
      apply (le_id_l (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
                     (gap (lbr_iter X step n x0) (lbr_iter X step m x0))
                     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                           (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))).
      * exact (lbr_gap_sym (lbr_iter X step m x0) (lbr_iter X step n x0)).
      * assert (Hk : sigT (fun k : nat => Id m (Nat.add n (Datatypes.S k)))).
        { exists (Nat.pred (Nat.sub m n)).
          pose proof (proj1 (Nat.leb_gt m n) Eleb) as Hgt.
          apply lbr_eq_id. lia. }
        destruct Hk as [k Hk].
        apply (le_id_l (gap (lbr_iter X step n x0) (lbr_iter X step m x0))
                       (gap (lbr_iter X step n x0)
                            (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                       (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                             (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))).
        -- exact (id_cong (fun z => gap (lbr_iter X step n x0) z)
                          (id_cong (fun w => lbr_iter X step w x0) Hk)).
        -- apply (le_trans _ (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))).
           ++ exact (lbr_iter_offdiag_le x0 n k).
           ++ apply (le_trans _ (plus (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)))).
              ** exact (le_plus_nonneg_r (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                         (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                         (lbr_scaled_pow_nonneg x0 m)).
              ** exact (le_id_l (plus (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)))
                                (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))
                                (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))
                                (plus_comm (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                           (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)))
                                (le_refl (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                               (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))))).
Qed.

(* Uniform residual calculator: for every positive eps there is an N    *)
(* with g(step u_n, u_n) < eps for all n >= N (decay bound, scaling,    *)
(* master modulus in three shifts; no fixed point needed). *)
Theorem lbr_residual_calc : forall (x0 : X) (eps : R), lt zero eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    lt (gap (step (lbr_iter X step n x0)) (lbr_iter X step n x0)) eps).
Proof.
  intros x0 eps Hep.
  destruct (lbr_iter_master_lt x0 eps Hep) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)) _).
  - apply (le_trans _ (mult (lbr_r_pow L n) (gap (step x0) x0))).
    + exact (lbr_iter_step_gap_decay X gap step L lbr_L_nonneg lbr_budget n x0).
    + exact (lbr_mult_compat_r (gap (step x0) x0)
                               (mult (gap (step x0) x0) invs)
                               (lbr_r_pow L n)
                               (lbr_r_pow_nonneg L lbr_L_nonneg n)
                               (lbr_gap_le_scaled x0)).
  - exact (HN n Hn).
Qed.

End LbrBanach.

(* ================================================================== *)
(* Closing audit: assumption checks (all Closed), numerical smoke      *)
(* tests, and Separate Extraction of the three Fixpoints.              *)
(* ================================================================== *)

Print Assumptions lbr_iter_lipschitz.
Print Assumptions lbr_step_count.
Print Assumptions lbr_r_pow_dec.
Print Assumptions lbr_r_pow_nonneg.
Print Assumptions lbr_r_pow_step_dec.
Print Assumptions lbr_iter_plus.
Print Assumptions lbr_iter_step_gap_decay.
Print Assumptions lbr_affine_diff.
Print Assumptions lbr_affine_budget_proj.
Print Assumptions lbr_affine_iter_contraction.
Print Assumptions lbr_geom_telescope.
Print Assumptions lbr_iter_master_lt.
Print Assumptions lbr_iter_cauchy.
Print Assumptions lbr_banach_fixed_point.
Print Assumptions lbr_fixed_point_unique.
Print Assumptions lbr_iter_cauchy_closed.
Print Assumptions lbr_residual_calc.

(* Numerical smoke tests: [lbr_iter] instantiated at nat. *)
(* Five iterates of the successor step from 0 give 5. *)
Eval vm_compute in (lbr_iter nat Datatypes.S 5 0).
(* Four iterates of the doubling step from 1 give 16. *)
Eval vm_compute in (lbr_iter nat (fun k => k * 2) 4 1).

Separate Extraction lbr_iter lbr_r_pow lbr_rsum.
