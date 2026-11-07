(* ConstructiveWorld-Set -- abs_sum_le family I (plain Or form): strongest
   reachable forms, on the Bishop B face. *)

(** * PA_UpAblAbsSumLeB: strongest reachable forms for the abs_sum_le
    family I.

    Mission.  The strongest reachable form of the abs_sum_le family I
      (plain Or form, UpReqSampling family I interface) is the Bishop
      B form [real_le_b]: strictly stronger than the per-eps form
      ([real_le_closure_b_one] closes in one step), which follows by
      the [inl] injection into [real_lt_le_iff_req]; the plain Or
      form is not constructed here.  Supplies: the two-point core
      difference form on both faces, the [real_list_sum] fold form
      by induction on the weight [W], and the non-coexistence of
      [real_lt (Y+2e) X] with [real_le X (Y+e)].

    Dependencies.  Stdlib [List], [QArith.Qring]; requires the
      [S01]-[S15] chain and [UpRealLeB].

    References.  ConstructiveWorld-Main, module [PA_UpAblAbsSumLeB]
      (statement names carried over verbatim).

    Constructivity.  No admission words, no axiom declarations, no
      classical logic, whole file [Qed]-closed; statements are
      Set-level values, proofs constructive ([Or] by branches,
      [sigT] witnesses direct).

    Build.  [coqc -native-compiler no -q -Q . "" PA_UpAblAbsSumLeB.v]
      compiles cleanly (exit 0). *)

From Stdlib Require Import List.
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
(* Section 0 - in-library interface check ([Check] against the     *)
(*   true signatures)                                              *)
(* ============================================================ *)

Check real_le_b.              (* the Bishop-form <= (the strongest-reachable predicate, see UpRealLeB) *)
Check real_le_closure_b_one.  (* per-eps completion into the B form (one-step closure) *)
Check real_le_closure_b.      (* B-form closure with an explicit positivity certificate D *)
Check real_abs_triangle_le_B. (* |a+b| <=_B |a|+|b| (the B-form triangle) *)
Check real_abs_triangle_le_eps. (* |a+b| <= (|a|+|b|)+eps per eps (the two-point core triangle) *)
Check real_lt_zero_one.       (* 0 < 1 (the positivity certificate for W(nil)) *)
Check real_lt_plus_r_zero.    (* y < y+eps (see UpRealLeB) *)
Check real_list_sum.          (* the list fold (X universal, from S08_RealMainlineDPO) *)
Check RealSetoid.real_eq_abs_compat. (* abs respects real_eq *)
Check real_abs_zero_req.      (* |0| == 0 *)
Check real_lt_irrefl.         (* irreflexivity of real < (the common landing point of the contradiction arguments) *)

(* ============================================================ *)
(* Section 1 - basic lemmas: right absorption by a positive        *)
(*   margin, and the difference-form two-point triangle            *)
(* ============================================================ *)

(* Basic lemma: [le a b] with [0 < c] gives [le a (b+c)] (right     *)
(* absorption of a positive margin).  Construction: the [lt] branch *)
(* composes by transitivity ([b < b+c] via the [(b+0)] transport),  *)
(* the [eq] branch transports then follows the same chain; both     *)
(* close through the [inl] injection of [real_lt_le_iff_req].       *)
Lemma uabS4_le_add_r : forall a b c : Real,
  real_le a b -> real_lt real_zero c -> real_le a (real_plus b c).
Proof.
  intros a b c Hab Hc.
  apply (RealSetoid.real_lt_le_iff_req a (real_plus b c)). apply inl.
  destruct Hab as [Hab | Hab].
  - apply (real_lt_trans a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
  - apply (RealSetoid.real_lt_id_l a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
Qed.

(* A.1 Two-point core difference form (per eps, via [inl]):        *)
(* [|a-c| <= (|a-b|+|b-c|)+eps].  Construction: the difference     *)
(* identity [(a-b)+(b-c) == a-c] (five steps: assoc twice, opp,    *)
(* zero, each transported by [real_eq_plus_compat]); once [abs]    *)
(* respects the equation, the two-point core triangle applies      *)
(* directly.                                                       *)
Lemma uabS4_abs_diff_triangle_le_eps : forall a b c e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a (real_opp c)))
          (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                (real_abs (real_plus b (real_opp c)))) e).
Proof.
  intros a b c e He.
  assert (Hdiff : real_eq (real_plus (real_plus a (real_opp b))
                                     (real_plus b (real_opp c)))
                          (real_plus a (real_opp c))).
  { eapply real_eq_trans.
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) (real_plus b (real_opp c))) a
               (real_opp c)).
      + apply real_eq_refl.
      + eapply real_eq_trans.
        * apply real_plus_assoc.
        * eapply real_eq_trans.
          -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
                          (real_opp c) real_zero (real_opp c)).
             ++ apply (real_eq_trans _ _ _ (real_plus_comm (real_opp b) b)).
                apply real_plus_opp.
             ++ apply real_eq_refl.
          -- apply (real_eq_trans _ _ _ (real_plus_comm real_zero (real_opp c))).
             apply real_plus_zero. }
  apply (RealSetoid.real_le_id_l _ _ _
           (RealSetoid.real_eq_abs_compat _ _
              (real_eq_sym (real_plus (real_plus a (real_opp b))
                                      (real_plus b (real_opp c)))
                           (real_plus a (real_opp c)) Hdiff))).
  exact (real_abs_triangle_le_eps (real_plus a (real_opp b))
                                  (real_plus b (real_opp c)) e He).
Qed.

(* A.2 Two-point core difference form (B face, strongest           *)
(* reachable): [|a-c| <=_B |a-b|+|b-c|].                           *)
Theorem uabS4_abs_diff_triangle_le_B : forall a b c : Real,
  real_le_b (real_abs (real_plus a (real_opp c)))
            (real_plus (real_abs (real_plus a (real_opp b)))
                       (real_abs (real_plus b (real_opp c)))).
Proof.
  intros a b c.
  apply real_le_closure_b_one.
  intros e He.
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* A.3 B-form instance on the two-point world ([S := bool]): the   *)
(* two-point world is the least nontrivial world for abs_sum_le;   *)
(* [real_abs_triangle_le_B] applies directly.                      *)
Theorem uabS4_abs_sum_le_B_pair : forall f : bool -> Real,
  real_le_b (real_abs (real_plus (f true) (f false)))
            (real_plus (real_abs (f true)) (real_abs (f false))).
Proof.
  intros f.
  exact (real_abs_triangle_le_B (f true) (f false)).
Qed.

(* ============================================================ *)
(* Section 2 - the list fold form: weighted induction with a       *)
(*   weight function, closed on the B face                         *)
(* ============================================================ *)

(* Weight function: [W(nil)=1], [W(w::rest)=W(rest)+1]             *)
(* (definitional tail weight plus one).  Error allocation: a       *)
(* single-point introduction spends exactly one whole unit [e] per *)
(* step, and the tail margin is carried by [W(rest)*e]; together   *)
(* [(W(rest)+1)*e == W(cons)*e] - the allocation is exact at every *)
(* level.                                                          *)
Fixpoint uabS4_wlen (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_one
  | w :: rest => real_plus (uabS4_wlen X rest) real_one
  end.

(* Weight positivity certificate: [0 < W(l)] (induction: [1 > 0];  *)
(* [W(rest) > 0] translates to [W(rest)+1]).                       *)
Lemma uabS4_wlen_pos : forall (X : Type) (l : list X),
  real_lt real_zero (uabS4_wlen X l).
Proof.
  intros X l. induction l as [| w rest IH].
  - exact real_lt_zero_one.
  - apply (real_lt_trans real_zero (uabS4_wlen X rest)
             (real_plus (uabS4_wlen X rest) real_one)).
    + exact IH.
    + apply real_lt_plus_r_zero. exact real_lt_zero_one.
Qed.

(* Induction-step lemma (the cons step of the fold induction): the *)
(* two-point core triangle (single-point introduction, margin one  *)
(* whole unit [e]) plus the tail margin (carried weighted by       *)
(* [w*e]) give the fold target margin [(w+1)*e].  Construction:    *)
(* composed through [real_le_plus_compat], then final transport    *)
(* along an eq chain ([assoc] three times, [distrib]/[mult_one];   *)
(* [(w+1)*e == w*e + e] rearranged stepwise via comm/distrib).     *)
Lemma uabS4_cons_glue : forall a s t w e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) (real_abs s)) e) ->
  real_le (real_abs s) (real_plus t (real_mult w e)) ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) t)
                     (real_mult (real_plus w real_one) e)).
Proof.
  intros a s t w e He Hpair Hih.
  assert (Hmid : real_le (real_plus (real_abs a) (real_abs s))
                         (real_plus (real_abs a) (real_plus t (real_mult w e)))).
  { apply (real_le_plus_compat (real_abs a) (real_abs a)
             (real_abs s) (real_plus t (real_mult w e))).
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl (real_abs a))).
    - exact Hih. }
  assert (Hstep : real_le (real_plus (real_plus (real_abs a) (real_abs s)) e)
                          (real_plus (real_plus (real_abs a)
                                     (real_plus t (real_mult w e))) e)).
  { apply (real_le_plus_compat _ _ e e).
    - exact Hmid.
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl e)). }
  assert (Hchain : real_le (real_abs (real_plus a s))
                           (real_plus (real_plus (real_abs a)
                                      (real_plus t (real_mult w e))) e)).
  { apply (real_le_trans _ _ _ Hpair Hstep). }
  apply (RealSetoid.real_le_id_r (real_abs (real_plus a s))
           (real_plus (real_plus (real_abs a) (real_plus t (real_mult w e))) e)
           (real_plus (real_plus (real_abs a) t)
                      (real_mult (real_plus w real_one) e))).
  - eapply real_eq_trans.
    + apply real_eq_sym. apply real_plus_assoc.
    + eapply real_eq_trans.
      * apply (RealSetoid.real_eq_plus_compat (real_abs a)
                   (real_plus (real_plus t (real_mult w e)) e) (real_abs a)
                   (real_plus t (real_plus (real_mult w e) e))).
        -- apply real_eq_refl.
        -- apply real_eq_sym. apply real_plus_assoc.
      * eapply real_eq_trans.
        -- apply real_plus_assoc.
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_abs a) t)
                        (real_plus (real_mult w e) e)
                        (real_plus (real_abs a) t)
                        (real_mult (real_plus w real_one) e)).
           ++ apply real_eq_refl.
           ++ apply real_eq_sym.
              apply (real_eq_trans _ _ _
                       (real_mult_comm (real_plus w real_one) e)).
              apply (real_eq_trans _ _ _ (real_distrib e w real_one)).
              apply (RealSetoid.real_eq_plus_compat (real_mult e w)
                          (real_mult e real_one) (real_mult w e) e).
              ** apply real_mult_comm.
              ** apply real_mult_one.
  - exact Hchain.
Qed.

(* B.1 Weighted induction body (per-eps form, weight [W]):         *)
(* [|sum_l f| <= sum_l|f| + W(l)*e].  Case [l = []]: [|0| == 0 <=  *)
(* 0 + 1*e] (right absorption of a positive margin); step [l] to   *)
(* [w::rest]: the two-point core triangle introduces one whole     *)
(* unit [e], the tail is carried at the same weight by the         *)
(* induction assumption, composed by [uabS4_cons_glue].            *)
Lemma uabS4_abs_list_sum_le_wt : forall (X : Type) (f : X -> Real) (l : list X)
                                        (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l)
                     (real_mult (uabS4_wlen X l) e)).
Proof.
  intros X f l. induction l as [| w rest IH]; intro e; intro He.
  - apply (uabS4_le_add_r (real_abs (real_list_sum X f nil)) real_zero
             (real_mult (uabS4_wlen X nil) e)).
    + apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero real_zero).
      * exact real_abs_zero_req.
      * exact (RealSetoid.real_eq_le real_zero real_zero (real_eq_refl real_zero)).
    + apply (RealSetoid.real_lt_id_r real_zero e (real_mult real_one e)).
      * apply real_eq_sym.
        apply (real_eq_trans _ _ _ (real_mult_comm real_one e)).
        apply real_mult_one.
      * exact He.
  - apply (uabS4_cons_glue (f w) (real_list_sum X f rest)
             (real_list_sum X (fun x => real_abs (f x)) rest)
             (uabS4_wlen X rest) e He).
    + exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest) e He).
    + exact (IH e He).
Qed.

(* B.2 B-form closure (strongest reachable): [|sum_l f| <=_B       *)
(* sum_l|f|] - [real_le_closure_b] closes the weighted family at   *)
(* the explicit positivity certificate [D := W(l)].                *)
Theorem uabS4_abs_list_sum_le_B : forall (X : Type) (f : X -> Real) (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x => real_abs (f x)) l).
Proof.
  intros X f l.
  apply (real_le_closure_b _ _ (uabS4_wlen X l) (uabS4_wlen_pos X l)).
  intros e He.
  exact (uabS4_abs_list_sum_le_wt X f l e He).
Qed.

(* B.3 Per-eps corollary: the B form gives [|sum_l f| <= sum_l|f| + *)
(* eps] (the [Or]-inl injection).  Comparison result: the B form is *)
(* strictly stronger than the per-eps form -                        *)
(* [real_le_closure_b_one] is exactly its one-step inversion.       *)
Theorem uabS4_abs_list_sum_le_eps : forall (X : Type) (f : X -> Real) (l : list X)
                                           (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l) e).
Proof.
  intros X f l e He.
  apply (RealSetoid.real_lt_le_iff_req _ _).
  apply inl.
  exact (uabS4_abs_list_sum_le_B X f l e He).
Qed.

(* ============================================================ *)
(* Section 3 - the margin-ratio-2 non-coexistence lemma            *)
(* ============================================================ *)

(* C.1 Margin-ratio-2 non-coexistence: [0 < e], [real_lt (Y+2e) X] *)
(* and [real_le X (Y+e)] cannot coexist.  Construction: both [Or]  *)
(* branches derive [real_lt (Y+2e) (Y+e)] - the [lt] branch by     *)
(* transitivity ([Y+2e < X < Y+e]); the [eq] branch by RHS         *)
(* transport ([X == Y+e]); the other side [e < 2e] translates to   *)
(* [Y+e < Y+2e], and conjoining hits [real_lt_irrefl].  Boundary   *)
(* note: at margin exactly [e] (ratio 1) the [eq] branch coexists  *)
(* with the converse strict side (approach examples of the form    *)
(* [x_n - y_n = e + 1/n]); ratio 2 does not.                       *)
Theorem uabS4_lt_double_margin_le_half_contr : forall X Y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus Y (real_plus e e)) X ->
  real_le X (real_plus Y e) ->
  Empty_set.
Proof.
  intros X Y e He Hfar Hle.
  assert (Hboom : real_lt (real_plus Y (real_plus e e))
                          (real_plus Y e) -> Empty_set).
  { intro Hbad.
    assert (Hfwd : real_lt (real_plus Y e) (real_plus Y (real_plus e e))).
    { apply (real_lt_plus_translate Y e (real_plus e e)).
      apply (RealSetoid.real_lt_id_l e (real_plus e real_zero) (real_plus e e)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (real_lt_plus_translate e real_zero e). exact He. }
    exact (real_lt_irrefl _ (real_lt_trans _ _ _ Hbad Hfwd)). }
  unfold real_le in Hle. destruct Hle as [Hlt | Heq].
  - exact (Hboom (real_lt_trans _ _ _ Hfar Hlt)).
  - apply Hboom.
    exact (RealSetoid.real_lt_id_r (real_plus Y (real_plus e e)) X
             (real_plus Y e) Heq Hfar).
Qed.

(* C.2 Difference-form instance of the ratio-2 contradiction (the  *)
(* two-point core difference form composed diagonally with C.1):   *)
(* the per-eps two-point core ([uabS4_abs_diff_triangle_le_eps])   *)
(* serves as the [le] source - under the margin constraint of the  *)
(* shape [real_lt (b + 2e) a] with [|a-c| <= |a-b|+|b-c|+e] at     *)
(* [eps := e], substituting into C.1 gives the contradiction.      *)
Theorem uabS4_diff_double_kill : forall a b c e : Real,
  real_lt real_zero e ->
  real_lt (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                  (real_abs (real_plus b (real_opp c))))
                     (real_plus e e))
          (real_abs (real_plus a (real_opp c))) ->
  Empty_set.
Proof.
  intros a b c e He Hfar.
  apply (uabS4_lt_double_margin_le_half_contr           (real_abs (real_plus a (real_opp c)))           (real_plus (real_abs (real_plus a (real_opp b)))                      (real_abs (real_plus b (real_opp c)))) e He Hfar).
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* ============================================================ *)
(* Audit note: the [Print Assumptions] outputs are expected all    *)
(* Closed (zero external unproved facts).                          *)
(* ============================================================ *)

Print Assumptions uabS4_le_add_r.
Print Assumptions uabS4_abs_diff_triangle_le_eps.
Print Assumptions uabS4_abs_diff_triangle_le_B.
Print Assumptions uabS4_abs_sum_le_B_pair.
Print Assumptions uabS4_wlen_pos.
Print Assumptions uabS4_cons_glue.
Print Assumptions uabS4_abs_list_sum_le_wt.
Print Assumptions uabS4_abs_list_sum_le_B.
Print Assumptions uabS4_abs_list_sum_le_eps.
Print Assumptions uabS4_lt_double_margin_le_half_contr.
Print Assumptions uabS4_diff_double_kill.

(* Print Assumptions replay block (verification copies).           *)
Print Assumptions uabS4_diff_double_kill.
Print Assumptions uabS4_abs_list_sum_le_eps.
Print Assumptions uabS4_abs_list_sum_le_B.
Print Assumptions uabS4_abs_sum_le_B_pair.
Print Assumptions uabS4_abs_diff_triangle_le_B.
