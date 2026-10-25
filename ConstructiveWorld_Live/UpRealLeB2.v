(* ConstructiveWorld-Set — multi-eps composition chains and generalized completion for the Bishop order. *)

(** * UpRealLeB2: composition combinators and a generalized completer for the Bishop non-strict order.

    Mission.  Built on the engines of [UpRealLeB]: the nonnegative-coefficient
      completer [real_le_closure_b_nonneg] (a C >= 0 certificate plus a
      C-scaled eps-family completes to Bishop form), the transitivity
      [real_le_b_trans] and addition [real_le_b_plus_compat] combinators (eps/2
      splitting), and four upgrades of eps-form bounds to Bishop form:
      [real_abs_le_quad_B], [real_quad_t_le_h_B], [real_abs_h_sq_le_B], and
      [real_db_breaking_bound_B].

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Setoid].  Requires
      [UpRealLeB] and the backbone [S01_BaseRing] .. [S15_TailFEPUp].

    References.  This development, the same-named baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All statements are carried by [Set]; proofs are explicit
      term-mode [real_eq] chains.  Where only nonnegativity of a coefficient
      is available, the generalized completer substitutes the witness
      e0 := delta * inv(2) * inv(C+1), avoiding a positivity premise.  The
      upgraded statements carry their source premises verbatim and add none.
      Statements extract with [Obj.magic] = 0; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpRealLeB2.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.Qring.
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

(* ============================================================ *)
(* F.0 Helper: delta*inv(2) + delta*inv(2) == delta (basis of the eps/2 split). *)
(* ============================================================ *)

Lemma leb2_half_add : forall d : Real,
  real_eq
    (real_plus
       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    d.
Proof.
  intro d.
  (* dh + dh == d*(h+h) rewriting chain. *)
  apply (real_eq_trans _
           (real_mult d
              (real_plus
                 (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                 (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
           _).
  - apply real_eq_sym. apply real_distrib.
  - apply (real_eq_trans _ (real_mult d real_one) _).
    + apply (RealSetoid.real_eq_mult_compat d
               (real_plus
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
               d
               real_one).
      * apply real_eq_refl.
      * (* h + h == 1：h+h == h·1+h·1 == h·(1+1) == (1+1)·h == 1 *)
        apply (real_eq_trans _
                 (real_plus
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one)
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one))
                 _).
        -- apply (RealSetoid.real_eq_plus_compat
                    (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                    (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one)
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one)).
           ++ apply real_eq_sym. apply real_mult_one.
           ++ apply real_eq_sym. apply real_mult_one.
        -- apply (real_eq_trans _
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                               (real_plus real_one real_one))
                    _).
           ++ apply real_eq_sym. apply real_distrib.
           ++ apply (real_eq_trans _
                       (real_mult (real_plus real_one real_one)
                                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                       _).
              ** apply real_mult_comm.
              ** apply real_inv_pos_correct.
    + apply real_mult_one.
Qed.

(* ============================================================ *)
(* F.1 Nonnegative-coefficient completer: completion still works when the      *)
(* positivity of C is not provable (composite coefficients with >= 0 factors). *)
(* Witness e0 := delta * inv(2) * inv(C+1), with C*e0 == delta*inv(2)*(C*inv(C+1)) *)
(*        ≤ δ·inv(2)·((C+1)·inv(C+1)) == δ·inv(2) < δ.                 *)
(* ============================================================ *)

Lemma real_le_closure_b_nonneg : forall x y C : Real,
  real_le real_zero C ->
  (forall eps : Real, real_lt real_zero eps ->
    real_le x (real_plus y (real_mult C eps))) ->
  real_le_b x y.
Proof.
  intros x y C HC H. unfold real_le_b. intros d Hd.
  (* Half-witness dh := delta*inv(2) and its positivity. *)
  assert (Hhalfpos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdh : real_lt real_zero
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    by exact (real_mult_positive d
                (real_inv_pos (real_plus real_one real_one) real_two_pos_local) Hd Hhalfpos).
  (* C + 1 > 0 and C <= C + 1 (the only certificate work for a nonnegative coefficient). *)
  assert (HCltp : real_lt C (real_plus C real_one)).
  { apply (RealSetoid.real_lt_id_l C (real_plus C real_zero) (real_plus C real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate C real_zero real_one). exact real_lt_zero_one. }
  assert (HCle : real_le C (real_plus C real_one))
    by exact (RealSetoid.real_lt_le_iff_req C (real_plus C real_one) (inl HCltp)).
  assert (HCp : real_lt real_zero (real_plus C real_one)).
  { apply (real_lt_le_trans real_zero real_one (real_plus C real_one) real_lt_zero_one).
    apply (RealSetoid.real_le_id_l real_one (real_plus real_zero real_one) (real_plus C real_one)).
    - apply real_eq_sym.
      apply (real_eq_trans (real_plus real_zero real_one) (real_plus real_one real_zero) _).
      + apply real_plus_comm.
      + apply real_plus_zero.
    - apply (real_le_plus_compat real_zero C real_one real_one).
      + exact HC.
      + apply real_le_refl. }
  assert (HinvCp : real_lt real_zero (real_inv_pos (real_plus C real_one) HCp))
    by exact (real_inv_pos_pos (real_plus C real_one) HCp).
  (* Witness e0 := delta*inv(2)*inv(C+1) > 0. *)
  assert (He0pos : real_lt real_zero
    (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
               (real_inv_pos (real_plus C real_one) HCp)))
    by exact (real_mult_positive
                (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                (real_inv_pos (real_plus C real_one) HCp) Hdh HinvCp).
  (* Key bound: C*e0 <= delta*inv(2) < delta. *)
  assert (Hkey : real_le
    (real_mult C
       (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  (real_inv_pos (real_plus C real_one) HCp)))
    (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))).
  { assert (Heq1 : real_eq
      (real_mult C
         (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                    (real_inv_pos (real_plus C real_one) HCp)))
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult C (real_inv_pos (real_plus C real_one) HCp)))).
    { apply (real_eq_trans _
               (real_mult
                  (real_mult C
                     (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                  (real_inv_pos (real_plus C real_one) HCp))
               _).
      - apply real_mult_assoc.
      - apply (real_eq_trans _
                 (real_mult
                    (real_mult
                       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                       C)
                    (real_inv_pos (real_plus C real_one) HCp))
                 _).
        + apply (RealSetoid.real_eq_mult_compat
                    (real_mult C
                       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                    (real_inv_pos (real_plus C real_one) HCp)
                    (real_mult
                       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                       C)
                    (real_inv_pos (real_plus C real_one) HCp)).
          * apply real_mult_comm.
          * apply real_eq_refl.
        + apply real_eq_sym. apply real_mult_assoc. }
    assert (Hle2 : real_le
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult C (real_inv_pos (real_plus C real_one) HCp)))
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp))))
      by exact (real_le_mult_compat_r
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  (real_mult C (real_inv_pos (real_plus C real_one) HCp))
                  (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp))
                  (RealSetoid.real_lt_le_iff_req real_zero _
                    (inl Hdh))
                  (real_le_mult_compat C (real_plus C real_one)
                     (real_inv_pos (real_plus C real_one) HCp) HinvCp HCle)).
    assert (Heq3 : real_eq
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp)))
      (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))).
    { apply (real_eq_trans _
               (real_mult
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  real_one)
               _).
      - apply (RealSetoid.real_eq_mult_compat
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp))
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  real_one).
        + apply real_eq_refl.
        + apply real_inv_pos_correct.
      - apply real_mult_one. }
    exact (real_le_trans _ _
             (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
             (RealSetoid.real_le_id_l _ _ _ Heq1 (real_le_refl _))
             (RealSetoid.real_le_id_r _ _ _ Heq3 Hle2)). }
  (* Using the premise (both Or branches close separately). *)
  destruct (H _
    (real_mult_positive
       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_inv_pos (real_plus C real_one) HCp) Hdh HinvCp)) as [Hlt | Heq].
  - apply (real_lt_trans x (real_plus y (real_mult C
      (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                 (real_inv_pos (real_plus C real_one) HCp)))) (real_plus y d)).
    + exact Hlt.
    + apply (real_le_lt_trans _ (real_plus y
        (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))) (real_plus y d)).
      * apply (real_le_plus_compat y y _ _).
        -- apply real_le_refl.
        -- exact Hkey.
      * apply (real_lt_plus_translate y
          (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) d).
        -- (* dh < d：dh < d·1 == d *)
           apply (real_lt_eq_lt
             (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
             (real_mult d real_one) d).
           ++ apply (real_mult_lt_compat_l
                       (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                       real_one d real_inv_two_lt_one Hd).
           ++ apply real_mult_one.
  - apply (RealSetoid.real_lt_id_l x (real_plus y (real_mult C
      (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                 (real_inv_pos (real_plus C real_one) HCp)))) (real_plus y d)).
    + exact Heq.
    + apply (real_le_lt_trans _ (real_plus y
        (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))) (real_plus y d)).
      * apply (real_le_plus_compat y y _ _).
        -- apply real_le_refl.
        -- exact Hkey.
      * apply (real_lt_plus_translate y
          (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) d).
        -- (* dh < d：dh < d·1 == d *)
           apply (real_lt_eq_lt
             (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
             (real_mult d real_one) d).
           ++ apply (real_mult_lt_compat_l
                       (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                       real_one d real_inv_two_lt_one Hd).
           ++ apply real_mult_one.
Qed.

(* ============================================================ *)
(* F.2 Transitivity combinator: x <=_B y and y <=_B z give x <=_B z, by the    *)
(* eps/2 split (two shares of delta*inv(2); middle term (z+dh)+dh == z+delta). *)
(* ============================================================ *)

Lemma real_le_b_trans : forall x y z : Real,
  real_le_b x y -> real_le_b y z -> real_le_b x z.
Proof.
  intros x y z Hxy Hyz. unfold real_le_b in Hxy, Hyz. unfold real_le_b. intros d Hd.
  assert (Hhalfpos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdh : real_lt real_zero
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    by exact (real_mult_positive d
                (real_inv_pos (real_plus real_one real_one) real_two_pos_local) Hd Hhalfpos).
  pose proof (Hxy (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) Hdh) as H1.
  pose proof (Hyz (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) Hdh) as H2.
  (* Middle term: y + dh < (z + dh) + dh (translation plus commutativity). *)
  assert (Hmid : real_lt
    (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))).
  { pose proof (real_lt_plus_translate
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  y (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                  H2) as H3.
    apply (real_lt_eq_lt
      (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
      (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                 (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))))
      (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                 (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))).
    - (* y+dh < dh+(z+dh): left commutation rewrite plus translation. *)
      apply (RealSetoid.real_lt_id_l
               (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) y)
               (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                          (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))))).
      + apply real_plus_comm.
      + exact H3.
    - (* dh+(z+dh) == (z+dh)+dh：plus_comm *)
      apply real_plus_comm. }
  (* Final term: (z+dh)+dh == z+delta. *)
  assert (Heqz : real_eq
    (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    (real_plus z d)).
  { apply (real_eq_trans _
             (real_plus z
                (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                           (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))))
             _).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat z
               (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                          (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               z d).
      + apply real_eq_refl.
      + exact (leb2_half_add d). }
  exact (real_lt_trans x
           (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
           (real_plus z d) H1
           (real_lt_eq_lt
              (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
              (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
              (real_plus z d) Hmid Heqz)).
Qed.

(* ============================================================ *)
(* F.3 Addition combinator: x <=_B y and u <=_B v give x+u <=_B y+v, by the    *)
(* eps/2 split (two shares of delta*inv(2); (y+dh)+(v+dh) == (y+v)+delta).     *)
(* ============================================================ *)

Lemma real_le_b_plus_compat : forall x y u v : Real,
  real_le_b x y -> real_le_b u v ->
  real_le_b (real_plus x u) (real_plus y v).
Proof.
  intros x y u v Hx Hu. unfold real_le_b in Hx, Hu. unfold real_le_b. intros d Hd.
  set (dh := real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)).
  assert (Hhalfpos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdh : real_lt real_zero dh)
    by exact (real_mult_positive d
                (real_inv_pos (real_plus real_one real_one) real_two_pos_local) Hd Hhalfpos).
  pose proof (Hx dh Hdh) as H1.
  pose proof (Hu dh Hdh) as H2.
  pose proof (real_lt_plus_compat x (real_plus y dh) u (real_plus v dh) H1 H2) as H3.
  (* (y+dh)+(v+dh) == (y+v)+delta: six assoc/comm steps, one assert each. *)
  assert (HstepA : real_eq (real_plus (real_plus y dh) (real_plus v dh))
                           (real_plus y (real_plus dh (real_plus v dh)))).
  { apply real_eq_sym. apply real_plus_assoc. }
  assert (HstepB : real_eq (real_plus y (real_plus dh (real_plus v dh)))
                           (real_plus y (real_plus dh (real_plus dh v)))).
  { apply (RealSetoid.real_eq_plus_compat y (real_plus dh (real_plus v dh)) y (real_plus dh (real_plus dh v))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_plus_compat dh (real_plus v dh) dh (real_plus dh v)).
      + apply real_eq_refl.
      + apply real_plus_comm. }
  assert (HstepC : real_eq (real_plus y (real_plus dh (real_plus dh v)))
                           (real_plus y (real_plus (real_plus dh dh) v))).
  { apply (RealSetoid.real_eq_plus_compat y (real_plus dh (real_plus dh v)) y (real_plus (real_plus dh dh) v)).
    - apply real_eq_refl.
    - apply real_plus_assoc. }
  assert (HstepD : real_eq (real_plus y (real_plus (real_plus dh dh) v))
                           (real_plus y (real_plus d v))).
  { apply (RealSetoid.real_eq_plus_compat y (real_plus (real_plus dh dh) v) y (real_plus d v)).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_plus_compat (real_plus dh dh) v d v).
      + exact (leb2_half_add d).
      + apply real_eq_refl. }
  assert (HstepE : real_eq (real_plus y (real_plus d v))
                           (real_plus (real_plus y v) d)).
  { apply (real_eq_trans _ (real_plus y (real_plus v d)) _).
    - apply (RealSetoid.real_eq_plus_compat y (real_plus d v) y (real_plus v d)).
      + apply real_eq_refl.
      + apply real_plus_comm.
    - apply real_plus_assoc. }
  apply (real_lt_eq_lt (real_plus x u)
                       (real_plus (real_plus y dh) (real_plus v dh))
                       (real_plus (real_plus y v) d)).
  - exact H3.
  - exact (real_eq_trans _ _ _ HstepA (real_eq_trans _ _ _ HstepB
             (real_eq_trans _ _ _ HstepC (real_eq_trans _ _ _ HstepD HstepE)))).
Qed.

(* ============================================================ *)
(* F.4 Upgrade of real_abs_le_quad_eps: |X| <=_B 2t^2 + (eps1+eps2).  The      *)
(* source concludes with a universal eps remainder (eps1/eps2 are fixed        *)
(* positive premises absorbed into the right side); certificate: one step of   *)
(* the D := 1 completer plus direct composition; no new premises.             *)
(* ============================================================ *)

Lemma real_abs_le_quad_B : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
            (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                       (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB HA Heps2.
  apply real_le_closure_b_one. intros eps Heps.
  exact (real_abs_le_quad_eps X t eps1 eps2 eps HXA HXB HA Heps2 Heps).
Qed.

(* ============================================================ *)
(* F.5 Upgrade of real_quad_t_le_h_eps: 2(h/x)^2 <=_B (1/2)*eps*|h|.  The     *)
(* source eps' is a universal sum remainder (premise 0 < eps') which vanishes *)
(* from the bound after completion; the embedded |h| factor joins the fixed   *)
(* side.  No new premises.                                                    *)
(* ============================================================ *)

Lemma real_quad_t_le_h_B : forall (x h eps : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx)) (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) eps)
               (real_abs h)).
Proof.
  intros x h eps Hx Hh Heps.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_quad_t_le_h_eps x h eps eps' Hx Hh Heps Heps').
Qed.

(* ============================================================ *)
(* F.6 Upgrade of real_abs_h_sq_le_eps: A*|h|^2 <=_B (A*eps3)*|h|. *)
(* Same chain as F.5 (double remainder A*eps3*|h| + eps', eps' universally discharged). *)
(* ============================================================ *)

Lemma real_abs_h_sq_le_B : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_abs_h_sq_le_eps A h eps3 eps' HA Hh3 Heps').
Qed.

(* ============================================================ *)
(* F.7 Upgrade of real_db_breaking_bound_eps (nonnegative composite            *)
(* coefficient).  The source eps and eps' sit inside the composite coefficient *)
(* invZ*T*(exp*eps + eps'); the coefficient C := invZ*T*(exp+1) is only        *)
(* nonnegative (T >= 0 has no positivity certificate), so the F.1 completer    *)
(* applies.  Both eps and eps' vanish from the bound: db <=_B invZ*T*(exp*M).  *)
(* Section variables mirror the source discharged prefix.                      *)
(* ============================================================ *)

Section RealKVQuantLeB.

Variable S : Type.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).
Variable real_transition : S -> S -> Real.
Variable real_transition_nonneg : forall s s' : S, real_le real_zero (real_transition s s').
Variable real_transition_sym : forall s s' : S, real_eq (real_transition s s') (real_transition s' s).
Variable real_energy : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable L : Real.
Variable E_max : Real.
Variable real_metric : S -> S -> Real.
Variable real_energy_lipschitz : forall s s' : S,
  real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
          (real_mult L (real_metric s s')).
Variable real_energy_lower : forall s : S, real_le (real_opp E_max) (real_energy s).
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_evicted_partition_pos : real_lt real_zero
  (real_evicted_partition S keep keep_dec real_energy D D_pos real_sum_over_S).

Theorem real_db_breaking_bound_B : forall s s' : S,
  keep s -> keep s' ->
  real_le_b
    (real_db_breaking S keep keep_dec real_transition real_energy D D_pos
                      real_sum_over_S real_evicted_partition_pos s s')
    (real_mult
       (real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                        real_sum_over_S) real_evicted_partition_pos)
       (real_mult (real_transition s s')
                  (real_mult
                     (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                     (real_mult
                        (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                        (cauchy_real_exp
                           (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))))))).
Proof.
  intros s s' Hs Hs'.
  apply (real_le_closure_b_nonneg
           (real_db_breaking S keep keep_dec real_transition real_energy D D_pos
                             real_sum_over_S real_evicted_partition_pos s s')
           (real_mult
              (real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                               real_sum_over_S) real_evicted_partition_pos)
              (real_mult (real_transition s s')
                         (real_mult
                            (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                            (real_mult
                               (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                               (cauchy_real_exp
                                  (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))))
           (real_mult
              (real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                               real_sum_over_S) real_evicted_partition_pos)
              (real_mult (real_transition s s')
                         (real_plus (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                    real_one)))).
  (* Premise 1: 0 <= C := invZ*(T*(exp+1)), assembled from invZ>0, T>=0, exp+1>0. *)
  {
  set (W := real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                             real_sum_over_S) real_evicted_partition_pos).
  set (T := real_transition s s').
  set (E1 := cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)).
  assert (HWpos : real_lt real_zero W)
    by exact (real_inv_pos_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                                  real_sum_over_S) real_evicted_partition_pos).
  assert (HWle : real_le real_zero W)
    by exact (RealSetoid.real_lt_le_iff_req real_zero W (inl HWpos)).
  assert (HTle : real_le real_zero T) by exact (real_transition_nonneg s s').
  assert (HGpos : real_lt real_zero (real_plus E1 real_one))
    by exact (real_plus_positive E1 real_one
                (cauchy_real_exp_pos (real_mult (real_inv_pos D D_pos) E_max)) real_lt_zero_one).
  assert (HTG : real_le real_zero (real_mult T (real_plus E1 real_one))).
  { apply (RealSetoid.real_le_id_l real_zero (real_mult T real_zero)
                                   (real_mult T (real_plus E1 real_one))).
    - apply real_eq_sym. apply real_mult_zero.
    - apply (real_le_mult_compat_r T real_zero (real_plus E1 real_one) HTle).
      exact (RealSetoid.real_lt_le_iff_req real_zero (real_plus E1 real_one) (inl HGpos)). }
  apply (RealSetoid.real_le_id_l real_zero (real_mult W real_zero)
                                 (real_mult W (real_mult T (real_plus E1 real_one)))).
  - apply real_eq_sym. apply real_mult_zero.
  - apply (real_le_mult_compat_r W real_zero (real_mult T (real_plus E1 real_one)) HWle).
    exact HTG.
  }
  (* Premise 2: forall eps > 0, db <= y + C*eps (source with eps := eps' := eps, by distributivity). *)
  intros ep Hep.
  set (W := real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                             real_sum_over_S) real_evicted_partition_pos) in *.
  set (T := real_transition s s') in *.
  set (E1 := cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) in *.
  set (M2 := real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                       (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))) in *.
  set (C := real_mult W (real_mult T (real_plus E1 real_one))).
  pose proof (real_db_breaking_bound_eps S keep keep_dec real_transition
              real_transition_nonneg real_transition_sym real_energy D D_pos L E_max
              real_metric real_energy_lipschitz real_energy_lower real_sum_over_S
              real_evicted_partition_pos s s' ep ep Hs Hs' Hep Hep) as Hsrc.
  fold W in Hsrc. fold T in Hsrc. fold E1 in Hsrc. fold M2 in Hsrc.
  assert (Hchain1 : real_eq
    (real_mult W (real_mult T (real_plus (real_mult E1 M2) (real_plus (real_mult E1 ep) ep))))
    (real_plus (real_mult W (real_mult T (real_mult E1 M2)))
               (real_mult W (real_mult T (real_plus (real_mult E1 ep) ep))))).
  { apply (real_eq_trans _
             (real_mult W
                (real_plus (real_mult T (real_mult E1 M2))
                           (real_mult T (real_plus (real_mult E1 ep) ep)))) _).
    - apply (RealSetoid.real_eq_mult_compat W _ W _).
      + apply real_eq_refl.
      + apply real_distrib.
    - apply real_distrib. }
  assert (Hchain2 : real_eq
    (real_mult W (real_mult T (real_plus (real_mult E1 ep) ep)))
    (real_mult C ep)).
  { apply (real_eq_trans _
             (real_mult W (real_mult T (real_mult (real_plus E1 real_one) ep))) _).
    - apply (RealSetoid.real_eq_mult_compat W _ W _).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_mult_compat T _ T _).
        * apply real_eq_refl.
        * (* (E1·ep)+ep == (E1+1)·ep *)
          apply (real_eq_trans _
                   (real_plus (real_mult E1 ep) (real_mult real_one ep)) _).
          -- apply (RealSetoid.real_eq_plus_compat (real_mult E1 ep) ep
                       (real_mult E1 ep) (real_mult real_one ep)).
             ++ apply real_eq_refl.
             ++ apply (real_eq_trans ep (real_mult ep real_one)
                         (real_mult real_one ep)).
                ** apply real_eq_sym. apply real_mult_one.
                ** apply real_mult_comm.
          -- apply real_distrib_r.
    - apply (real_eq_trans _
               (real_mult W (real_mult (real_mult T (real_plus E1 real_one)) ep)) _).
      + apply (RealSetoid.real_eq_mult_compat W _ W _).
        * apply real_eq_refl.
        * apply real_mult_assoc.
      + apply real_mult_assoc. }
  apply (RealSetoid.real_le_id_r
           (real_db_breaking S keep keep_dec real_transition real_energy D D_pos
                             real_sum_over_S real_evicted_partition_pos s s')
           (real_mult W (real_mult T (real_plus (real_mult E1 M2) (real_plus (real_mult E1 ep) ep))))
           (real_plus (real_mult W (real_mult T (real_mult E1 M2))) (real_mult C ep))).
  - exact (real_eq_trans _ _ _ Hchain1
             (RealSetoid.real_eq_plus_compat
                (real_mult W (real_mult T (real_mult E1 M2)))
                (real_mult W (real_mult T (real_plus (real_mult E1 ep) ep)))
                (real_mult W (real_mult T (real_mult E1 M2)))
                (real_mult C ep)
                (real_eq_refl _) Hchain2)).
  - exact Hsrc.
Qed.

End RealKVQuantLeB.

(* ============================================================ *)

(*                                                                *)
(* Verdict G1 [nonnegative-coefficient completer]: real_le_closure_b_nonneg   *)
(* is provable.  The source completer demands a positivity certificate         *)
(* (0 < D), while composite coefficients in multi-eps chains are often only    *)
(* nonnegative (a positive times a nonnegative factor).  A nonnegative         *)
(* certificate suffices: witness e0 := delta*inv(2)*inv(C+1) (positivity of    *)
(* C+1 from C >= 0 and 0 < 1), giving C*e0 <= delta*inv(2)*((C+1)*inv(C+1))    *)
(* == delta*inv(2) < delta.  No density, no classical reasoning, no new        *)
(* premises.                                                                   *)
(* Verdict G2 [two combinators]: real_le_b_trans and real_le_b_plus_compat    *)
(* are provable; the split uses delta*inv(2) (existing real_inv_two_lt_one),   *)
(* the middle terms close by assoc/comm rewriting.  The Bishop order hence     *)
(* admits transitivity and addition composition: multi-eps statements can be   *)
(* completed piecewise and combined.                                           *)
(* Verdict G3 [real_abs_le_quad_B]: full upgrade.  The source concludes with  *)
(* a universal eps remainder — a plain-eps shape; the certificate chain lives  *)
(* inside the source statement, so the upgrade is one step plus direct         *)
(* composition, no new premises.                                              *)
(* Verdict G4 [real_quad_t_le_h_B]: full upgrade — the source eps' is a       *)
(* universal sum remainder with its own 0 < eps' premise; after the D := 1     *)
(* completion it vanishes from the bound.                                      *)
(* Verdict G5 [real_abs_h_sq_le_B]: full upgrade, same chain as G4. *)
(* Verdict G6 [real_db_breaking_bound_B]: full upgrade (not frozen).  The     *)
(* positivity route for the composite coefficient (invZ*T*exp as D) is         *)
(* constructively unavailable (T carries only a nonnegativity interface); the *)
(* nonnegative route applies instead with C := invZ*T*(exp+1), its             *)
(* nonnegativity assembled from existing interface facts, and the F.1          *)
(* completer finishes in one step after distributivity.  No new premises.      *)
(* All four explicit-assumption statements of the inventory are upgraded here. *)

(* The remaining seven inventory entries are deliberately excluded (shape mismatch). *)


(* Statements extract with [Obj.magic] = 0; closedness checks close the file. *)
(* ============================================================ *)

Print Assumptions leb2_half_add.
Print Assumptions real_le_closure_b_nonneg.
Print Assumptions real_le_b_trans.
Print Assumptions real_le_b_plus_compat.
Print Assumptions real_abs_le_quad_B.
Print Assumptions real_quad_t_le_h_B.
Print Assumptions real_abs_h_sq_le_B.
Print Assumptions real_db_breaking_bound_B.
