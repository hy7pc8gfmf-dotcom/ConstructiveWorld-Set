(* ConstructiveWorld-Set -- absolute-value inequality family and the
   partition-function definition pin. *)
(** * AbsSqClose: abs basic inequality family, finite-sum triangle, and the
      Boltzmann-partition definition pin.

    Mission.
      Family 1 (abs basic inequalities, S01 carrier):
        asc_abs_lower_pos (|a| < c -> 0 < c + a),
        asc_abs_le_intro (u <= w -> -u <= w -> |u| <= w),
        asc_sq_nonneg (0 <= t^2), asc_sq_le_abs_sq (t^2 <= |t|^2),
        asc_nsq_square_nonneg, asc_abs_nonneg (0 <= |a|),
        asc_abs_sum_le_r (finite-sum triangle at the sumd_sumf instance).
      Family 2 (partition-function pin):
        czd12_fep_partition / czd12_fep_Z_pos -- the partition function Z
        pinned to the concrete finite sum sumd_sumf; positivity by head
        non-empty list induction plus the exp_neg positivity field.

    Dependencies.
      S01_BaseRing (carrier R, DecidableOrder class fields, Id),
      fa53_compat_abs (fa53_lt_plus_translate_r), UpReqSumD (sumd_list_sum,
      sumd_sumf, sumd_list_sum_pos_cons), S07_RealSetoidExpLog
      (RealInterfaceEnhancedSetoid fields at the concrete Real layer);
      Stdlib List.

    References.
      UpReqLogRDF (lrdf_abs_lower_pos / lrdf_abs_le_intro / lrdf_sq_nonneg /
      lrdf_sq_le_abs_sq), UpReqSqrtF (nsq_square_nonneg), UpReqAttnIter
      (abs_nonneg_h), UpReqAttnGibbs (abs_sum_le_r), UpReqLogCompD
      (fep_partition).

    Port notes (deviations from the frozen Main-tree draft, all forced by
      the same-world dependency generation).
      1. The frozen draft required TempSoftmaxInstantiation; that module is
         not landed in the Set-line tree or world and the file references
         none of its names, so the Require is dropped.
      2. The UpReqSumD generation in this world exports [Notation R :=
         Real]; the S01-idiom section re-pins the token via
         [Local Notation R := S01_BaseRing.R] so every statement face of
         the abs/sq family keeps its frozen token shape.
      3. The finite-sum pieces (asc_sumd_list_abs_triangle,
         asc_abs_sum_le_r) and the tail section are materialized at the
         concrete Real layer per the world convention (the former R/RIS
         head absorbed by the global instance; cf. the UpAblT1 discharge
         generation). The RIS abs_triangle field is the Bishop per-eps
         form, so the sum-triangle face carries a per-item positive budget
         e (the S11_TP3B5 b4_tri_sum precedent); the eps-free plain form is
         not derivable from that field without a collapse lemma.
      4. czd12_list_sum_pos_cons delegates to the world UpReqSumD
         sumd_list_sum_pos_cons (same statement shape at the Real layer).

    Constructivity.
      Every declaration Qed-closed, zero admits; statement faces Set-carried
      with zero Prop leakage (Or is the constructive disjunction over
      Set-valued lt/Id; the single negative face is the Id-form non-empty
      premise Not (Id enum nil) of czd12_fep_Z_pos, the in-register
      fa51-precedent datum shape; the induction pieces match no empty
      branch).

    Build.
      rocq c -native-compiler no -Q <same-world> "" AbsSqClose.v
      (Rocq 9.1.0) against the same-world dependency .vo tree, under the
      cpu_guard load wrapper. *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.

(* Carrier re-pin: the UpReqSumD generation above exports [Notation R :=
   Real] (the S07 Real); this file's S01-idiom section needs the S01
   carrier, so the token is re-pinned before the section opens. *)
Local Notation R := S01_BaseRing.R.

(* ============================================================ *)
(* Main section: S01 carrier + DO decidable-order reinforcement  *)
(* (fa53-style double Context)                                   *)
(* ============================================================ *)
Section AbsSqCloseMain.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* fa53 projection alias: the class field name lt_dec is shadowed by
   Stdlib Compare_dec *)
Definition asc_lt_dec_id :
  forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ _ lt_d _ _ _ => lt_d
  end.

(* ---- Support 1: -0 == 0 (both right inverses of zero, via
   plus_inv_unique) ---- *)
Lemma asc_opp_zero_id : Id (opp zero) zero.
Proof.
  exact (plus_inv_unique zero (opp zero) zero
           (plus_opp zero) (plus_zero zero)).
Qed.

(* ---- Support 2: opp involution --a == a (plus_inv_unique, left
   alignment) ---- *)
Lemma asc_opp_opp : forall a : R, Id (opp (opp a)) a.
Proof.
  intro a.
  exact (plus_inv_unique (opp a) (opp (opp a)) a
           (plus_opp (opp a))
           (id_trans (id_sym (plus_comm a (opp a))) (plus_opp a))).
Qed.

(* ---- Support 3: (-t)^2 == t^2 (ring support; opp_mult_l/r assembly) ---- *)
Lemma asc_sq_opp : forall t : R, Id (mult t t) (mult (opp t) (opp t)).
Proof.
  intro t.
  exact (id_sym (id_trans (opp_mult_r t (opp t))
                  (id_trans (id_cong opp (opp_mult_l t t))
                            (asc_opp_opp (mult t t))))).
Qed.

(* ---- Support 4 (new mathematical point, abs_neg bridge): a < 0 ->
   |a| == -a ----
   a<0 gives -a>0 (opp_lt_compat with the -0 == 0 reshape), hence the
   abs_pos branch at -a; the abs_opp field folds |a| back; combined with
   the fa53 item 3 (a >= 0 branch) this yields the two-way abs identity
   bridge. *)
Lemma asc_abs_neg_id : forall a : R, lt a zero -> Id (abs a) (opp a).
Proof.
  intros a Ha.
  exact (id_trans (id_sym (abs_opp a))
                  (abs_pos (opp a)
                     (lt_id_l zero (opp zero) (opp a)
                        (id_sym asc_opp_zero_id) (opp_lt_compat a zero Ha)))).
Qed.

(* ---- #40: |a| < c -> 0 < c + a (real_abs_lt_lower req-slot shape) ----
   Trichotomy on 0 ? a: positive branch |a|==a and both summands positive;
   zero branch |0|==0 collapses c; negative branch via the |a|==-a bridge
   and the fa53 one-sided strict translation. *)
Theorem asc_abs_lower_pos : forall a c : R, lt (abs a) c -> lt zero (plus c a).
Proof.
  intros a c H.
  destruct (asc_lt_dec_id zero a) as [H0a | [H0eq | Halt]].
  - (* 0 < a: |a|==a, c > a > 0 -> plus_positive *)
    assert (Hc : lt zero c).
    { exact (lt_trans zero a c H0a
               (lt_id_l a (abs a) c (id_sym (abs_pos a H0a)) H)). }
    exact (plus_positive c a Hc H0a).
  - (* 0 == a: c > |0| == 0; c + a collapses onto c *)
    assert (Hc : lt zero c).
    { exact (lt_id_l zero (abs a) c
               (id_sym (id_trans (id_cong abs (id_sym H0eq)) abs_zero)) H). }
    exact (lt_id_r zero c (plus c a)
             (id_sym (id_trans (id_cong (fun w => plus c w) (id_sym H0eq))
                               (plus_zero c)))
             Hc).
  - (* a < 0: |a|==-a bridge + fa53 one-sided strict translation *)
    exact (lt_id_l zero (plus (opp a) a) (plus c a)
             (id_sym (id_trans (id_sym (plus_comm a (opp a))) (plus_opp a)))
             (fa53_lt_plus_translate_r (opp a) c a
                (lt_id_l (opp a) (abs a) c
                   (id_sym (asc_abs_neg_id a Halt)) H))).
Qed.

(* ---- #41: u <= w /\ -u <= w -> |u| <= w (abs_le introduction shape) ----
   Trichotomy on 0 ? u: positive branch |u|==u gives it directly; zero
   branch normalizes |u| == 0 == u; negative branch rewrites through the
   |u|==-u bridge. *)
Theorem asc_abs_le_intro :
  forall u w : R, le u w -> le (opp u) w -> le (abs u) w.
Proof.
  intros u w Huw Hou.
  destruct (asc_lt_dec_id zero u) as [H0u | [H0eq | Hult]].
  - (* 0 < u: |u|==u *)
    exact (le_id_l (abs u) u w (abs_pos u H0u) Huw).
  - (* 0 == u: |u| == |0| == 0 == u normalization *)
    exact (le_id_l (abs u) u w
             (id_trans (id_trans (id_cong abs (id_sym H0eq)) abs_zero)
                       H0eq)
             Huw).
  - (* u < 0: |u|==-u bridge rewrite *)
    exact (le_id_l (abs u) (opp u) w (asc_abs_neg_id u Hult) Hou).
Qed.

(* ---- #42: 0 <= t^2 (Qsquare_nonneg pointwise-fact shape) ----
   Trichotomy on 0 ? t: positive branch via the 0*t == 0 chain and weak
   multiplication monotonicity on two le zero t; zero branch squares to
   zero; negative branch rewrites (-t)^2 == t^2 onto the positive branch. *)
Theorem asc_sq_nonneg : forall t : R, le zero (mult t t).
Proof.
  intro t.
  destruct (asc_lt_dec_id zero t) as [H0t | [H0eq | Htl]].
  - (* 0 < t: 0*t == 0 chain + weak multiplication on two le zero t *)
    assert (Hge : le zero t) by (exact (lt_le_iff zero t (inl H0t))).
    exact (le_id_l zero (mult zero t) (mult t t)
             (id_sym (id_trans (mult_comm zero t) (mult_zero t)))
             (le_mult_compat_weak zero t t Hge Hge)).
  - (* 0 == t: t^2 == 0^2 == 0 *)
    assert (Htz : Id (mult t t) zero).
    { exact (id_trans (id_cong (fun w => mult w t) (id_sym H0eq))
                      (id_trans (mult_comm zero t) (mult_zero t))). }
    exact (le_id_r zero zero (mult t t) (id_sym Htz) (le_refl zero)).
  - (* t < 0: -t > 0 branch + (-t)^2==t^2 reshape *)
    assert (Ht0 : lt zero (opp t)).
    { exact (lt_id_l zero (opp zero) (opp t) (id_sym asc_opp_zero_id)
               (opp_lt_compat t zero Htl)). }
    exact (le_id_r zero (mult (opp t) (opp t)) (mult t t)
             (id_sym (asc_sq_opp t))
             (le_id_l zero (mult zero (opp t)) (mult (opp t) (opp t))
                (id_sym (id_trans (mult_comm zero (opp t))
                                  (mult_zero (opp t))))
                (le_mult_compat_weak zero (opp t) (opp t)
                   (lt_le_iff zero (opp t) (inl Ht0))
                   (lt_le_iff zero (opp t) (inl Ht0))))).
Qed.

(* ---- #43: t^2 <= |t|^2 (q_sq_abs shape) ----
   Trichotomy on 0 ? t: non-negative branch |t|==t (fa53 item 3 covers both
   lt and eq), goal is a le_refl reshape; negative branch chains the
   |t|==-t bridge with the (-t)^2==t^2 support. *)
Theorem asc_sq_le_abs_sq :
  forall t : R, le (mult t t) (mult (abs t) (abs t)).
Proof.
  intro t.
  destruct (asc_lt_dec_id zero t) as [H0t | [H0eq | Htl]].
  - (* 0 < t: |t|==t *)
    exact (le_id_r (mult t t) (mult t t) (mult (abs t) (abs t))
             (id_sym (id_cong2 mult (abs_pos t H0t) (abs_pos t H0t)))
             (le_refl (mult t t))).
  - (* 0 == t: |t|==0==t normalization *)
    assert (Haid : Id (abs t) t).
    { exact (id_trans (id_trans (id_cong abs (id_sym H0eq)) abs_zero)
                      H0eq). }
    exact (le_id_r (mult t t) (mult t t) (mult (abs t) (abs t))
             (id_sym (id_cong2 mult Haid Haid)) (le_refl (mult t t))).
  - (* t < 0: |t|==-t bridge + (-t)^2==t^2 chain *)
    assert (Haid : Id (abs t) (opp t)) by (exact (asc_abs_neg_id t Htl)).
    exact (le_id_r (mult t t) (mult t t) (mult (abs t) (abs t))
             (id_sym (id_trans (id_cong2 mult Haid Haid)
                               (id_sym (asc_sq_opp t))))
             (le_refl (mult t t))).
Qed.

(* ---- #44: nsq slot (token-identical statement to #42; standalone for
   cross-checking) ---- *)
Theorem asc_nsq_square_nonneg : forall t : R, le zero (mult t t).
Proof.
  exact asc_sq_nonneg.
Qed.

(* ---- #45: 0 <= |a| (abs non-negativity slot) ----
   Positive branch lifts |a|==a to le; zero branch refl-off |a|==0;
   negative branch bridges |a|==-a and lifts -a>0 to le. *)
Theorem asc_abs_nonneg : forall a : R, le zero (abs a).
Proof.
  intro a.
  destruct (asc_lt_dec_id zero a) as [H0a | [H0eq | Halt]].
  - (* 0 < a: |a|==a lifted to le *)
    exact (le_id_r zero a (abs a) (id_sym (abs_pos a H0a))
             (lt_le_iff zero a (inl H0a))).
  - (* 0 == a: |a| == |0| == 0 *)
    assert (Haz : Id (abs a) zero).
    { exact (id_trans (id_cong abs (id_sym H0eq)) abs_zero). }
    exact (le_id_r zero zero (abs a) (id_sym Haz) (le_refl zero)).
  - (* a < 0: |a|==-a bridge + -a>0 lifted to le *)
    assert (Ht0 : lt zero (opp a)).
    { exact (lt_id_l zero (opp zero) (opp a) (id_sym asc_opp_zero_id)
               (opp_lt_compat a zero Halt)). }
    exact (le_id_r zero (opp a) (abs a) (id_sym (asc_abs_neg_id a Halt))
             (lt_le_iff zero (opp a) (inl Ht0))).
Qed.

End AbsSqCloseMain.

(* ============================================================ *)
(* Tail: Real-layer finite-sum triangle and the #47 partition    *)
(* definition pin (world generation: heads materialized at the   *)
(* concrete Real layer, RIS fields via the global instance).     *)
(* ============================================================ *)
(* Real / real_eq / real_lt are the S02 concrete-layer carriers; import
   S02 so the tail faces can name them, then open the RIS field module. *)
Require Import S02_CauchyComplete.
Require S07_RealSetoidExpLog.
Import S07_RealSetoidExpLog.RealInterfaceEnhancedMod.

(* Extraction-face re-pin (the same carrier re-pin idiom as the [Local
   Notation R := S01_BaseRing.R] block above): the class-field token
   [req] abstracts to the extractor's logical dummy (type req = __), so
   any Set-valued body of a req-face statement would need an Obj.magic
   cast. The Real-layer instance RealEnhancedReal pins req := real_eq;
   re-pinning the token to the concrete [real_eq] keeps every statement
   token, the definitional pin and the proof bodies intact while the
   extracted face carries the real per-eps equality type: zero
   Obj.magic, zero semantic change. *)
Local Notation req := real_eq.

(* ---- #46 helper: finite-sum triangle at the sumd instance ----
   Per-item positive budget e (S11_TP3B5 b4_tri_sum precedent): the RIS
   abs_triangle field is the Bishop per-eps form, so the eps-free plain
   face is not derivable here without a collapse lemma. List induction;
   the abs identity is by reflection on each item. *)
Lemma asc_sumd_list_abs_triangle :
  forall (S : Set) (f : S -> Real) (e : S -> Real) (l : list S),
    (forall s : S, real_lt zero (e s)) ->
    real_le (abs (sumd_list_sum S f l))
            (plus (sumd_list_sum S (fun s : S => abs (f s)) l)
                  (sumd_list_sum S e l)).
Proof.
  intros S f e l He. induction l as [| x t IH].
  - (* nil: |0| <= 0 + 0, both sums collapse onto zero *)
    exact (le_id_l (abs (sumd_list_sum S f nil)) zero
                   (plus (sumd_list_sum S (fun s : S => abs (f s)) nil)
                         (sumd_list_sum S e nil))
                   abs_zero
                   (le_id_r zero zero
                      (plus (sumd_list_sum S (fun s : S => abs (f s)) nil)
                            (sumd_list_sum S e nil))
                      (req_sym (plus zero zero) zero (plus_zero zero))
                      (le_refl zero))).
  - (* cons: abs_triangle step + le_plus_compat twice + AC ring shift *)
    assert (Htri : real_le
                     (abs (plus (f x) (sumd_list_sum S f t)))
                     (plus (plus (abs (f x)) (abs (sumd_list_sum S f t)))
                           (e x))).
    { exact (abs_triangle (f x) (sumd_list_sum S f t) (e x) (He x)). }
    assert (Hst1 : real_le
                     (plus (abs (f x)) (abs (sumd_list_sum S f t)))
                     (plus (abs (f x))
                           (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                 (sumd_list_sum S e t)))).
    { exact (le_plus_compat (abs (f x)) (abs (f x))
               (abs (sumd_list_sum S f t))
               (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                     (sumd_list_sum S e t))
               (le_refl (abs (f x))) IH). }
    assert (Hst2 : real_le
                     (plus (plus (abs (f x)) (abs (sumd_list_sum S f t)))
                           (e x))
                     (plus (plus (abs (f x))
                                 (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                       (sumd_list_sum S e t)))
                           (e x))).
    { exact (le_plus_compat
               (plus (abs (f x)) (abs (sumd_list_sum S f t)))
               (plus (abs (f x))
                     (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                           (sumd_list_sum S e t)))
               (e x) (e x) Hst1 (le_refl (e x))). }
    assert (Heq : real_eq
                     (plus (plus (abs (f x))
                                 (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                       (sumd_list_sum S e t)))
                           (e x))
                     (plus (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                           (plus (e x) (sumd_list_sum S e t)))).
    { exact (req_trans
               (plus (plus (abs (f x))
                           (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                 (sumd_list_sum S e t)))
                     (e x))
               (plus (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                     (plus (sumd_list_sum S e t) (e x)))
               (plus (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                     (plus (e x) (sumd_list_sum S e t)))
               (req_trans
                  (plus (plus (abs (f x))
                              (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                    (sumd_list_sum S e t)))
                        (e x))
                  (plus (plus (plus (abs (f x))
                                    (sumd_list_sum S (fun s : S => abs (f s)) t))
                              (sumd_list_sum S e t))
                        (e x))
                  (plus (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                        (plus (sumd_list_sum S e t) (e x)))
                  (req_plus_compat
                     (plus (abs (f x))
                           (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                 (sumd_list_sum S e t)))
                     (plus (plus (abs (f x))
                                 (sumd_list_sum S (fun s : S => abs (f s)) t))
                           (sumd_list_sum S e t))
                     (e x) (e x)
                     (plus_assoc (abs (f x))
                                 (sumd_list_sum S (fun s : S => abs (f s)) t)
                                 (sumd_list_sum S e t))
                     (req_refl (e x)))
                  (req_sym
                     (plus (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                           (plus (sumd_list_sum S e t) (e x)))
                     (plus (plus (plus (abs (f x))
                                       (sumd_list_sum S (fun s : S => abs (f s)) t))
                                 (sumd_list_sum S e t))
                           (e x))
                     (plus_assoc (plus (abs (f x))
                                       (sumd_list_sum S (fun s : S => abs (f s)) t))
                                 (sumd_list_sum S e t) (e x))))
               (req_plus_compat
                  (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                  (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                  (plus (sumd_list_sum S e t) (e x))
                  (plus (e x) (sumd_list_sum S e t))
                  (req_refl (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t)))
                  (plus_comm (sumd_list_sum S e t) (e x)))). }
    exact (le_trans (abs (plus (f x) (sumd_list_sum S f t)))
                    (plus (plus (abs (f x))
                                (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                      (sumd_list_sum S e t)))
                          (e x))
                    (plus (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                          (plus (e x) (sumd_list_sum S e t)))
                    (le_trans _ _ _ Htri Hst2)
                    (le_id_r
                       (plus (plus (abs (f x))
                                   (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                         (sumd_list_sum S e t)))
                             (e x))
                       (plus (plus (abs (f x))
                                   (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                         (sumd_list_sum S e t)))
                             (e x))
                       (plus (plus (abs (f x)) (sumd_list_sum S (fun s : S => abs (f s)) t))
                             (plus (e x) (sumd_list_sum S e t)))
                       Heq
                       (le_refl (plus (plus (abs (f x))
                                           (plus (sumd_list_sum S (fun s : S => abs (f s)) t)
                                                 (sumd_list_sum S e t)))
                                      (e x))))).
Qed.

(* #46 slot outlet (sumd_sumf specialization form) *)
Theorem asc_abs_sum_le_r :
  forall (S : Set) (enum : list S) (f : S -> Real) (e : S -> Real),
    (forall s : S, real_lt zero (e s)) ->
    real_le (abs (sumd_sumf S enum f))
            (plus (sumd_sumf S enum (fun s : S => abs (f s)))
                  (sumd_sumf S enum e)).
Proof.
  intros S enum f e H. exact (asc_sumd_list_abs_triangle S f e enum H).
Qed.

(* ============================================================ *)
(* Tail section: #47 partition-function definition pin            *)
(*   Precedents: the fa51_sumpos_id Z_temp_spec_def pin and the   *)
(*   G12_ZPosFam zposd_Z (Z moved from Variable to Definition).   *)
(* ============================================================ *)
Section FepPartitionPin.

Variable S : Set.
Variable enum : list S.
Variable base_loss : S -> Real.
Variable D : Real.
Variable D_pos : real_lt zero D.

(* #47 definition pin: Z as the concrete finite sum (sumd_sumf;
   Boltzmann form of the partition function) *)
Definition czd12_fep_Z : Real :=
  sumd_sumf S enum
    (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s))).

(* partition slot: definitional closure; after the pin the slot statement
   is req_refl (fa51 precedent) *)
Theorem czd12_fep_partition :
  req czd12_fep_Z
      (sumd_sumf S enum
         (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  exact (req_refl czd12_fep_Z).
Qed.

(* engine piece: head-non-empty list with pointwise positive summands has
   positive sum (constructive induction, zero empty-branch matching:
   non-emptiness is carried structurally by the (x :: l) head shape) --
   delegates to the world UpReqSumD piece of the same statement shape *)
Lemma czd12_list_sum_pos_cons :
  forall (f : S -> Real) (x : S) (l : list S),
    (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_list_sum S f (x :: l)).
Proof.
  intros f x l H. exact (sumd_list_sum_pos_cons S f x l H).
Qed.

(* #47 Z_pos: sumd positivity + pointwise exp_neg_pos (fa51_Z_temp_pos
   shape; premise is the fa51-style Id-form non-nil evidence, Set-layer
   zero Prop beyond the negative datum) *)
Theorem czd12_fep_Z_pos :
  Not (Id enum nil) -> real_lt zero czd12_fep_Z.
Proof.
  intro Hne. unfold czd12_fep_Z. destruct enum as [| x l].
  - destruct (Hne (@id_refl (list S) nil)).
  - exact (czd12_list_sum_pos_cons
             (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))
             x l
             (fun s : S => exp_neg_pos
                 (mult (inv_pos D D_pos) (base_loss s)))).
Qed.

End FepPartitionPin.

(* ---- In-file self-check (axiom-face audit): explicit PA block ---- *)
Print Assumptions asc_opp_zero_id.
Print Assumptions asc_opp_opp.
Print Assumptions asc_sq_opp.
Print Assumptions asc_abs_neg_id.
Print Assumptions asc_abs_lower_pos.
Print Assumptions asc_abs_le_intro.
Print Assumptions asc_sq_nonneg.
Print Assumptions asc_sq_le_abs_sq.
Print Assumptions asc_nsq_square_nonneg.
Print Assumptions asc_abs_nonneg.
Print Assumptions asc_abs_sum_le_r.
Print Assumptions czd12_fep_partition.
Print Assumptions czd12_fep_Z_pos.
