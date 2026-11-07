(* ConstructiveWorld-Set — differentiable functions over the req interface: the RDF record and the differentiation theorems. *)

(** * UpReqRDF: the RDF record and the differentiation theorem family
      over the [req] interface.

    Mission.  The [ReqDiffPlain] class of plain-form premise slots and the
      [reqRDF] record (derivative with eps-delta correctness budgets); the
      operation theorems [req_rdf_plus]/[req_rdf_mult]/[req_rdf_opp]/
      [req_rdf_minus]/[req_rdf_compose]/[req_rdf_affine]; the applications
      [req_cross_entropy_softmax_diff]/[req_mse_diff]; the [ReqEntropyDiff]
      section; the MV region (the [reqRDFMV] record, the inner-product
      Lipschitz slot, the adjoint-gradient pullbacks
      [req_rdf_mv_compose]/[req_rdf_mv_vec_compose]).

    Dependencies.  The backbone [S01_BaseRing] .. [S15_TailFEPUp],
      [UpReqAlgebra], [UpReqSLM]; Stdlib [List].

    References.  Statements carried over verbatim from the
      differentiable-function sections of the ConstructiveWorld-Main
      baseline ([Differentiable] fields, the scalar/entropy/MV clusters);
      the carrier is pinned to the global [Real] with relation fields
      [real_eq]/[real_lt]/[real_le]; plain slots live in [ReqDiffPlain].

    Constructivity.  All proofs close by [Qed]; zero admission words; no
      classical logic; statement faces carried by [Set] (order/equality
      predicates Set-valued, zero Prop leakage).

    Build.  [coqc -native-compiler no -q -Q . "" UpReqRDF.v] compiles
      cleanly (exit 0); artifact head bytes [436f7121 00015ff4]. *)

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
Require Import UpReqSLM.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Carrier pinning (the [UpReqSLM] pattern): [RealInterfaceEnhancedSetoid] *)
(* is a zero-argument Class in this tree ([S07_RealSetoidExpLog]; the     *)
(* global instance [RealEnhancedReal] resolves the fields); the           *)
(* generation binders were removed and the carrier R is pinned to the     *)
(* global Real by the Notations below.  The relation fields req/lt/le are *)
(* bound by Notation to the concrete S02_CauchyComplete shapes            *)
(* [real_eq]/[real_lt]/[real_le] (exactly the global instance's field     *)
(* values, the same terms the statement face elaborates to): boxed class  *)
(* field projections are erasure faces at extraction and generate         *)
(* [Obj.magic] rewrites when mixed with the concrete carrier, while the   *)
(* bound forms extract as true data (the [ConcMixSelFeed] pattern). *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ===================================================================== *)
(* Part 0: the bridge premise-slot group (honest assumption slots). *)
(* ===================================================================== *)

(* Plain counterpart slots for the eps-form interface fields (three), a   *)
(* slot for the log round-trip field (one), and one plain r_max slot —    *)
(* the min slot pair does not cover the r_max side, so [r_max_ge_plain :  *)
(* le a (r_max a b)] is carried as the plain counterpart of the interface *)
(* [r_max_le_l] field (a zero-proof assumption slot).                     *)
(* Slot inventory: [abs_triangle_plain] mirrors the interface              *)
(* [abs_triangle]; [min_le_l_plain]/[min_le_r_plain] mirror                *)
(* [min_le_l]/[min_le_r]; [log_inv_exp_neg_slot] mirrors                  *)
(* [log_inv_exp_neg] (the req interface only carries the reverse          *)
(* [exp_neg_log_inv]); [r_max_ge_plain] mirrors [r_max_le_l]. *)
Class ReqDiffPlain := {
  abs_triangle_plain : forall a b : R, le (abs (plus a b)) (plus (abs a) (abs b));
  min_le_l_plain : forall a b : R, le (min a b) a;
  min_le_r_plain : forall a b : R, le (min a b) b;
  r_max_ge_plain : forall a b : R, le a (r_max a b);
  log_inv_exp_neg_slot : forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x
}.

(* ===================================================================== *)
(* Part 0.5: the [reqRDF] record bridge (field-by-field counterpart of    *)
(* the baseline [Differentiable] record). *)
(* ===================================================================== *)

Record reqRDF (f : R -> R) : Set := {
  rdf_df : R -> R;
  rdf_correct : forall (x eps : R), lt zero eps ->
    sigT (fun delta : R => And (lt zero delta)
      (forall h : R, lt (abs h) delta ->
        le (abs (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df x) h))))
           (mult eps (abs h))))
}.

(* ===================================================================== *)
(* Part 1: shared machine lemmas (helpers; consumed across the cluster). *)
(* ===================================================================== *)

Section ReqRDFBase.

(* The carrier R is pinned to the global Real; the interface fields      *)
(* resolve through the global instance [RealEnhancedReal] — this section *)
(* has no abstract carrier or instance arguments. *)
(* Honest interface disclosure (a Variable-form slot, the same shape as   *)
(* [UpReqConcMixSel.lt_plus_compat_lt_le]): the plain nonnegativity slot  *)
(* [real_le zero (abs a)] is a real premise — the class [abs_nonneg] is   *)
(* only an eps form and cannot be resolved from it.  The semantics match  *)
(* the same-named plain slot of [UpReqSLM]; the carrier is the concrete   *)
(* [real_le] face so the extraction payload is true data (boxed class     *)
(* field projections are erasure faces, and mixing with the concrete      *)
(* carrier means [Obj.magic] rewrites). *)
Variable abs_nonneg_plain : forall a : R, le zero (abs a).
Context {RDP : ReqDiffPlain}.

(* two-sided compatibility of [req_minus] (no baseline counterpart:       *)
(* [req_minus] is not an interface field, so this is the shared machine). *)
Lemma req_rdf_minus_compat_r : forall a x y : R, req x y -> req (req_minus a x) (req_minus a y).
Proof.
  intros a x y H. unfold req_minus.
  exact (req_plus_compat a a (opp x) (opp y) (req_refl a) (req_opp_compat x y H)).
Qed.

Lemma req_rdf_minus_compat_l : forall a b x : R, req a b -> req (req_minus a x) (req_minus b x).
Proof.
  intros a b x H. unfold req_minus.
  exact (req_plus_compat a b (opp x) (opp x) H (req_refl (opp x))).
Qed.

(* positivity of one half (the canonical witness form of [req_two_pos];    *)
(* witness-relevant: Qed-opaque constants do not convert, so the field is  *)
(* proved directly rather than restating the inlined witness of            *)
(* [UpReqAlgebra.req_half_pos]). *)
Lemma req_rdf_half_pos : forall e : R, lt zero e ->
  lt zero (mult (inv_pos (plus one one) req_two_pos) e).
Proof.
  intros e He.
  apply mult_positive.
  - apply inv_pos_pos.
  - exact He.
Qed.

(* [0 <= eps * |h|] for [eps > 0] (consumes the [abs_nonneg_plain] slot). *)
Lemma req_rdf_zero_le_mult_abs : forall eps h : R, lt zero eps -> le zero (mult eps (abs h)).
Proof.
  intros eps h Heps.
  apply (le_id_l zero (mult zero (abs h)) (mult eps (abs h))).
  - exact (req_sym (mult zero (abs h)) zero
             (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                        (mult_comm zero (abs h)) (mult_zero (abs h)))).
  - exact (le_mult_compat_weak zero eps (abs h) (abs_nonneg_plain h)
             (lt_le_iff zero eps (inl Heps))).
Qed.

(* [E == 0] entails [|E| <= eps * |h|] (the uniform closing lemma for the  *)
(* zero-error cases; consumed seven times: const/id/power_nat base case/  *)
(* ce/mse heads/mv_const/mv_linear). *)
Lemma req_rdf_abs_zero_le : forall E eps h : R,
  lt zero eps -> req E zero -> le (abs E) (mult eps (abs h)).
Proof.
  intros E eps h Heps HE.
  apply (le_trans (abs E) (abs zero) (mult eps (abs h))).
  - exact (le_id_l (abs E) (abs zero) (abs zero) (req_abs_compat E zero HE)
             (le_refl (abs zero))).
  - exact (le_id_l (abs zero) zero (mult eps (abs h)) abs_zero
             (req_rdf_zero_le_mult_abs eps h Heps)).
Qed.

(* [|x| + 1 > 0] (the Lipschitz-constant positivity slot of               *)
(* mult/compose). *)
Lemma req_rdf_abs_plus_one_pos : forall a : R, lt zero (plus (abs a) one).
Proof.
  intro a.
  exact (req_plus_le_lt_pos (abs a) one (abs_nonneg_plain a) one_pos).
Qed.

(* [0 <= |a+b|] (a zero-content alias consuming the [abs_triangle_plain]  *)
(* slot; keeps use-site signatures short). *)
Lemma req_rdf_abs_triangle : forall a b : R, le (abs (plus a b)) (plus (abs a) (abs b)).
Proof.
  intros a b. exact (abs_triangle_plain a b).
Qed.

(* [L * (inv L * t) == t] for [L > 0] (the inv cancellation slot; used    *)
(* three times: compose/mv_compose/mv_vec). *)
Lemma req_rdf_inv_cancel : forall (L t : R) (HL : lt zero L),
  lt zero t -> req (mult L (mult (inv_pos L HL) t)) t.
Proof.
  intros L t HL Ht.
  apply (req_trans (mult L (mult (inv_pos L HL) t))
                   (mult (mult L (inv_pos L HL)) t) t).
  - apply mult_assoc.
  - apply (req_trans (mult (mult L (inv_pos L HL)) t) (mult one t) t).
    + apply (req_mult_compat (mult L (inv_pos L HL)) one t t).
      * exact (inv_pos_correct L HL).
      * apply req_refl.
    + exact (req_trans (mult one t) (mult t one) t (mult_comm one t) (mult_one t)).
Qed.

(* [(inv L * e4) * L <= e4] for [L > 0] (the same-shape slot for compose's *)
(* [eps_f * L <= eps4] and the mv cluster; used twice). *)
Lemma req_rdf_inv_scale_le : forall (L e4 : R) (HL : lt zero L),
  le (mult (mult (inv_pos L HL) e4) L) e4.
Proof.
  intros L e4 HL.
  apply (le_id_l (mult (mult (inv_pos L HL) e4) L) e4 e4).
  - apply (req_trans (mult (mult (inv_pos L HL) e4) L)
                     (mult (inv_pos L HL) (mult e4 L)) e4).
    + exact (req_sym (mult (inv_pos L HL) (mult e4 L))
                     (mult (mult (inv_pos L HL) e4) L) (mult_assoc (inv_pos L HL) e4 L)).
    + apply (req_trans (mult (inv_pos L HL) (mult e4 L))
                       (mult (inv_pos L HL) (mult L e4)) e4).
      * apply (req_mult_compat (inv_pos L HL) (inv_pos L HL) (mult e4 L) (mult L e4)).
        -- apply req_refl.
        -- apply mult_comm.
      * apply (req_trans (mult (inv_pos L HL) (mult L e4))
                         (mult (mult (inv_pos L HL) L) e4) e4).
        -- apply mult_assoc.
        -- apply (req_trans (mult (mult (inv_pos L HL) L) e4)
                            (mult (mult L (inv_pos L HL)) e4) e4).
           ++ apply (req_mult_compat (mult (inv_pos L HL) L) (mult L (inv_pos L HL)) e4 e4).
              ** apply mult_comm.
              ** apply req_refl.
           ++ apply (req_trans (mult (mult L (inv_pos L HL)) e4) (mult one e4) e4).
              ** apply (req_mult_compat (mult L (inv_pos L HL)) one e4 e4).
                 --- exact (inv_pos_correct L HL).
                 --- apply req_refl.
              ** exact (req_trans (mult one e4) (mult e4 one) e4 (mult_comm one e4) (mult_one e4)).
  - apply le_refl.
Qed.

(* [(eps/2) * s + (eps/2) * s == eps * s] (the plus closing arithmetic). *)
Lemma req_rdf_half_pair_req : forall e s : R,
  req (plus (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
            (mult (mult (inv_pos (plus one one) req_two_pos) e) s))
      (mult e s).
Proof.
  intros e s.
  apply (req_sym (mult e s)
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                       (mult (mult (inv_pos (plus one one) req_two_pos) e) s))).
  apply (req_trans (mult e s)
                   (mult (plus (mult (inv_pos (plus one one) req_two_pos) e)
                               (mult (inv_pos (plus one one) req_two_pos) e)) s)).
  - apply (req_mult_compat e (plus (mult (inv_pos (plus one one) req_two_pos) e)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s s).
    + exact (req_sym (plus (mult (inv_pos (plus one one) req_two_pos) e)
                           (mult (inv_pos (plus one one) req_two_pos) e)) e
                     (req_half_twice e req_two_pos)).
    + apply req_refl.
  - exact (req_mult_plus_distr_r (mult (inv_pos (plus one one) req_two_pos) e)
                                 (mult (inv_pos (plus one one) req_two_pos) e) s).
Qed.

Lemma req_rdf_half_pair_le : forall e s : R,
  le (plus (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
           (mult (mult (inv_pos (plus one one) req_two_pos) e) s))
     (mult e s).
Proof.
  intros e s.
  apply (le_id_l _ (mult e s) (mult e s)).
  - exact (req_rdf_half_pair_req e s).
  - apply le_refl.
Qed.

(* [(eps/4) * s + (eps/4) * s == (eps/2) * s] (the first level of the     *)
(* mult/compose closing arithmetic). *)
Lemma req_rdf_quarter_pair_req : forall e s : R,
  req (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) e)) s)
            (mult (mult (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) e)) s))
      (mult (mult (inv_pos (plus one one) req_two_pos) e) s).
Proof.
  intros e s.
  apply (req_sym (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s)
                       (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s))).
  apply (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                   (mult (plus one one)
                         (mult (mult (inv_pos (plus one one) req_two_pos)
                                     (mult (inv_pos (plus one one) req_two_pos) e)) s))).
  - exact (req_sym (mult (plus one one)
                         (mult (mult (inv_pos (plus one one) req_two_pos)
                                     (mult (inv_pos (plus one one) req_two_pos) e)) s))
                   (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
             (req_two_times_quarter e s req_two_pos)).
  - exact (req_two_mult (mult (mult (inv_pos (plus one one) req_two_pos)
                                    (mult (inv_pos (plus one one) req_two_pos) e)) s)).
Qed.

Lemma req_rdf_quarter_pair_le : forall e s : R,
  le (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                       (mult (inv_pos (plus one one) req_two_pos) e)) s)
           (mult (mult (inv_pos (plus one one) req_two_pos)
                       (mult (inv_pos (plus one one) req_two_pos) e)) s))
     (mult (mult (inv_pos (plus one one) req_two_pos) e) s).
Proof.
  intros e s.
  apply (le_id_l _ (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                   (mult (mult (inv_pos (plus one one) req_two_pos) e) s)).
  - exact (req_rdf_quarter_pair_req e s).
  - apply le_refl.
Qed.

(* req counterpart of the baseline [half_le_one] (consumed by             *)
(* [req_rdf_half_le_self]). *)
Lemma req_rdf_half_le_one : le (inv_pos (plus one one) req_two_pos) one.
Proof.
  apply (le_id_l (inv_pos (plus one one) req_two_pos)
                 (mult (inv_pos (plus one one) req_two_pos) one) one).
  - exact (req_sym (mult (inv_pos (plus one one) req_two_pos) one)
                   (inv_pos (plus one one) req_two_pos)
                   (mult_one (inv_pos (plus one one) req_two_pos))).
  - apply (le_id_r (mult (inv_pos (plus one one) req_two_pos) one)
                   (mult (inv_pos (plus one one) req_two_pos) (plus one one)) one).
    + exact (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                       (mult (plus one one) (inv_pos (plus one one) req_two_pos)) one
                       (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                       (inv_pos_correct (plus one one) req_two_pos)).
    + exact (req_le_mult_compat_r (inv_pos (plus one one) req_two_pos) one (plus one one)
              (lt_le_iff zero (inv_pos (plus one one) req_two_pos)
                         (inl (inv_pos_pos (plus one one) req_two_pos)))
              (req_le_plus_nonneg_r one one (lt_le_iff zero one (inl one_pos)))).
Qed.


(* [(eps/2) * s <= eps * s] (req counterpart of the baseline              *)
(* [half_le_self]; consumed at the nonnegative-coefficient sites). *)
Lemma req_rdf_half_le_self : forall a : R,
  le zero a -> le (mult (inv_pos (plus one one) req_two_pos) a) a.
Proof.
  intros a Ha.
  apply (le_trans (mult (inv_pos (plus one one) req_two_pos) a) (mult one a) a).
  - exact (le_mult_compat_weak (inv_pos (plus one one) req_two_pos) one a Ha
             (req_rdf_half_le_one)).
  - exact (le_id_l (mult one a) a a
             (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a))
             (le_refl a)).
Qed.

Lemma req_rdf_quarter_pair_le_final : forall e s : R,
  lt zero e -> le zero s ->
  le (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                       (mult (inv_pos (plus one one) req_two_pos) e)) s)
           (mult (mult (inv_pos (plus one one) req_two_pos)
                     (mult (inv_pos (plus one one) req_two_pos) e)) s))
     (mult e s).
Proof.
  intros e s Heps Hs.
  apply (le_trans (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s)
                        (mult (mult (inv_pos (plus one one) req_two_pos)
                                    (mult (inv_pos (plus one one) req_two_pos) e)) s))
                  (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                  (mult e s)).
  - exact (req_rdf_quarter_pair_le e s).
  - apply (le_trans (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                    (mult (inv_pos (plus one one) req_two_pos) (mult e s))
                    (mult e s)).
    + exact (RealSetoid.real_eq_le (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                           (mult (inv_pos (plus one one) req_two_pos) (mult e s))
                           (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult e s))
                                    (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                                    (mult_assoc (inv_pos (plus one one) req_two_pos) e s))).
    + exact (req_rdf_half_le_self (mult e s)
                                  (le_id_l zero (mult zero s) (mult e s)
                                   (req_sym (mult zero s) zero
                                    (req_trans (mult zero s) (mult s zero) zero
                                     (mult_comm zero s) (mult_zero s)))
                                   (le_mult_compat_weak zero e s Hs
                                    (lt_le_iff zero e (inl Heps))))).
Qed.



(* [|X * Y| <= |X| * |Y|] (the le shell of the [abs_mult] field — the     *)
(* uniform entry for the mult/compose arithmetic). *)
Lemma req_rdf_abs_mult_le : forall a b : R, le (abs (mult a b)) (mult (abs a) (abs b)).
Proof.
  intros a b.
  exact (le_id_l (abs (mult a b)) (mult (abs a) (abs b)) (mult (abs a) (abs b))
                 (abs_mult a b) (le_refl (mult (abs a) (abs b)))).
Qed.

(* increment bound: [|u - (v + d*h)| <= e * |h|] entails                  *)
(* [|u - v| <= (|d| + e) * |h|]                                          *)
(* (used three times: [Hdf_bound]/[Hdg_bound] of mult and compose's       *)
(* [|Dg| <= L * |h|]; a compact reordering of the baseline proof's        *)
(* minus_split + triangle + arithmetic). *)
Lemma req_rdf_delta_bound : forall u v d e hh : R,
  le (abs (req_minus u (plus v (mult d hh)))) (mult e (abs hh)) ->
  le (abs (req_minus u v)) (mult (plus (abs d) e) (abs hh)).
Proof.
  intros u v d e hh Hb.
  apply (le_id_l (abs (req_minus u v))
                 (abs (plus (req_minus u (plus v (mult d hh))) (mult d hh)))
                 (mult (plus (abs d) e) (abs hh))).
  - exact (req_abs_compat (req_minus u v)
             (plus (req_minus u (plus v (mult d hh))) (mult d hh))
             (req_minus_split u v (mult d hh))).
  - apply (le_trans _ (plus (abs (req_minus u (plus v (mult d hh))))
                            (abs (mult d hh)))).
    + exact (req_rdf_abs_triangle (req_minus u (plus v (mult d hh))) (mult d hh)).
    + apply (le_id_r (plus (abs (req_minus u (plus v (mult d hh)))) (abs (mult d hh)))
                     (plus (mult e (abs hh)) (mult (abs d) (abs hh)))
                     (mult (plus (abs d) e) (abs hh))).
      * exact (req_trans (plus (mult e (abs hh)) (mult (abs d) (abs hh)))
                         (plus (mult (abs d) (abs hh)) (mult e (abs hh)))
                         (mult (plus (abs d) e) (abs hh))
                         (plus_comm (mult e (abs hh)) (mult (abs d) (abs hh)))
                         (req_sym (mult (plus (abs d) e) (abs hh))
                                  (plus (mult (abs d) (abs hh)) (mult e (abs hh)))
                                  (req_mult_plus_distr_r (abs d) e (abs hh)))).
      * exact (le_plus_compat (abs (req_minus u (plus v (mult d hh))))
                              (mult e (abs hh))
                              (abs (mult d hh))
                              (mult (abs d) (abs hh))
                              Hb (req_rdf_abs_mult_le d hh)).
Qed.

End ReqRDFBase.

(* ===================================================================== *)
(* Part 2: the scalar cluster (10 statements) plus entropy (1); items     *)
(* 1-11 below. *)
(* ===================================================================== *)

Section ReqRDFScalar.

(* The carrier R is pinned to the global Real; the interface fields      *)
(* resolve through the global instance [RealEnhancedReal] — this section *)
(* has no abstract carrier or instance arguments. *)
(* Honest interface disclosure (a Variable-form slot, the same shape as   *)
(* [UpReqConcMixSel.lt_plus_compat_lt_le]): the plain nonnegativity slot  *)
(* [real_le zero (abs a)] is a real premise — the class [abs_nonneg] is   *)
(* only an eps form and cannot be resolved from it.  The semantics match  *)
(* the same-named plain slot of [UpReqSLM]; the carrier is the concrete   *)
(* [real_le] face so the extraction payload is true data (boxed class     *)
(* field projections are erasure faces, and mixing with the concrete      *)
(* carrier means [Obj.magic] rewrites). *)
Variable abs_nonneg_plain : forall a : R, le zero (abs a).
Context {RDP : ReqDiffPlain}.

(* ---- item 1: differentiable_const -> [req_rdf_const] ------------------- *)

Lemma req_rdf_const : forall c : R, reqRDF (fun _ => c).
Proof.
  intro c.
  exists (fun _ => zero).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Hz : req (mult zero h) zero).
    { exact (req_trans (mult zero h) (mult h zero) zero
               (mult_comm zero h) (mult_zero h)). }
    assert (Herr : req (req_minus c (plus c (mult zero h))) zero).
    { assert (Hs1 : req (plus c (opp (plus c (mult zero h)))) (plus c (opp (plus c zero)))).
      { exact (req_plus_compat c c (opp (plus c (mult zero h))) (opp (plus c zero))
                               (req_refl c)
                               (req_opp_compat (plus c (mult zero h)) (plus c zero)
                                               (req_plus_compat c c (mult zero h) zero
                                                                (req_refl c) Hz))). }
      assert (Hs2 : req (plus c (opp (plus c zero))) (plus c (opp c))).
      { exact (req_plus_compat c c (opp (plus c zero)) (opp c)
                               (req_refl c)
                               (req_opp_compat (plus c zero) c (plus_zero c))). }
      exact (req_trans _ _ _ Hs1 (req_trans _ _ _ Hs2 (plus_opp c))). }
    exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus c (plus c (mult zero h))) eps h Heps Herr).
Qed.

(* ---- item 2: differentiable_id -> [req_rdf_id] ------------------------- *)

Lemma req_rdf_id : reqRDF (fun x => x).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Herr : req (req_minus (plus x h) (plus x (mult one h))) zero).
    { apply (req_minus_self_zero (plus x h) (plus x (mult one h))).
      exact (req_plus_compat x x h (mult one h)
                             (req_refl x)
                             (req_sym (mult one h) h
                                      (req_trans (mult one h) (mult h one) h
                                                 (mult_comm one h) (mult_one h)))). }
    exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus (plus x h) (plus x (mult one h))) eps h Heps Herr).
Qed.

(* ---- item 3: differentiable_plus -> [req_rdf_plus] --------------------- *)

Theorem req_rdf_plus : forall f g : R -> R,
  reqRDF f -> reqRDF g -> reqRDF (fun x => plus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  exists (fun x => plus (rdf_df f Hf x) (rdf_df g Hg x)).
  intros x eps Heps.
  destruct (rdf_correct f Hf x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dfd [Hd1 Hd2]].
  destruct (rdf_correct g Hg x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dgd [Hg1 Hg2]].
  exists (min dfd dgd).
  split.
  - exact (min_pos dfd dgd Hd1 Hg1).
  - intros h Hh.
    assert (Hh1 : lt (abs h) dfd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dfd Hh (min_le_l_plain dfd dgd)). }
    assert (Hh2 : lt (abs h) dgd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dgd Hh (min_le_r_plain dfd dgd)). }
    apply (le_id_l (abs (req_minus (plus (f (plus x h)) (g (plus x h)))
                                   (plus (plus (f x) (g x))
                                         (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h))))
                   (abs (plus (req_minus (f (plus x h))
                                          (plus (f x) (mult (rdf_df f Hf x) h)))
                              (req_minus (g (plus x h))
                                         (plus (g x) (mult (rdf_df g Hg x) h)))))
                   (mult eps (abs h))).
    + exact (req_abs_compat
               (req_minus (plus (f (plus x h)) (g (plus x h)))
                          (plus (plus (f x) (g x))
                                (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h)))
               (plus (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h)))
                     (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h))))
               (req_trans (req_minus (plus (f (plus x h)) (g (plus x h)))
                                     (plus (plus (f x) (g x))
                                           (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h)))
                          (req_minus (plus (f (plus x h)) (g (plus x h)))
                                     (plus (plus (f x) (mult (rdf_df f Hf x) h))
                                           (plus (g x) (mult (rdf_df g Hg x) h))))
                          (plus (req_minus (f (plus x h))
                                           (plus (f x) (mult (rdf_df f Hf x) h)))
                                (req_minus (g (plus x h))
                                           (plus (g x) (mult (rdf_df g Hg x) h))))
                          (req_rdf_minus_compat_r (plus (f (plus x h)) (g (plus x h)))
                             (plus (plus (f x) (g x))
                                   (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h))
                             (plus (plus (f x) (mult (rdf_df f Hf x) h))
                                   (plus (g x) (mult (rdf_df g Hg x) h)))
                             (req_trans (plus (plus (f x) (g x))
                                              (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h))
                                        (plus (plus (f x) (g x))
                                              (plus (mult (rdf_df f Hf x) h)
                                                    (mult (rdf_df g Hg x) h)))
                                        (plus (plus (f x) (mult (rdf_df f Hf x) h))
                                              (plus (g x) (mult (rdf_df g Hg x) h)))
                                        (req_plus_compat (plus (f x) (g x))
                                                         (plus (f x) (g x))
                                                         (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h)
                                                         (plus (mult (rdf_df f Hf x) h)
                                                               (mult (rdf_df g Hg x) h))
                                                         (req_refl (plus (f x) (g x)))
                                                         (req_mult_plus_distr_r (rdf_df f Hf x)
                                                                                (rdf_df g Hg x) h))
                                        (req_plus_swap_mid (f x) (g x)
                                           (mult (rdf_df f Hf x) h)
                                           (mult (rdf_df g Hg x) h))))
                          (req_minus_plus_distr (f (plus x h)) (g (plus x h))
                                                (plus (f x) (mult (rdf_df f Hf x) h))
                                                (plus (g x) (mult (rdf_df g Hg x) h))))).
    + apply (le_trans _
               (plus (abs (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h))))
                     (abs (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h)))))).
      * exact (req_rdf_abs_triangle
                 (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h)))
                 (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h)))).
      * apply (le_trans _
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))).
        -- exact (le_plus_compat
                   (abs (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (abs (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (Hd2 h Hh1) (Hg2 h Hh2)).
        -- exact (req_rdf_half_pair_le eps (abs h)).
Qed.

(* ---- shared machine 2: product share / four-product / inv closing      *)
(* (used by the mult main proof) ---------------- *)

(* [|a| <= m] with [m * e == E4] and [0 <= hh] entails                    *)
(* [|a| * (e * hh) <= E4 * hh]                                           *)
(* (a compact shell of the baseline's two-step Hshare+Hsh2 arithmetic;    *)
(* used twice by mult, with hh always the [|h|] slot). *)
Lemma req_rdf_share : forall a m e E4 hh : R,
  le (abs a) m -> lt zero e -> req (mult m e) E4 -> le zero hh ->
  le (mult (abs a) (mult e hh)) (mult E4 hh).
Proof.
  intros a m e E4 hh Hle_am He Hreq Hnn.
  apply (le_trans (mult (abs a) (mult e hh)) (mult (mult (abs a) e) hh) (mult E4 hh)).
  - exact (le_id_l (mult (abs a) (mult e hh)) (mult (mult (abs a) e) hh)
                   (mult (mult (abs a) e) hh) (mult_assoc (abs a) e hh)
                   (le_refl (mult (mult (abs a) e) hh))).
  - apply (le_trans (mult (mult (abs a) e) hh) (mult (mult m e) hh) (mult E4 hh)).
    + exact (le_mult_compat_weak (mult (abs a) e) (mult m e) hh Hnn
               (le_mult_compat (abs a) m e He Hle_am)).
    + exact (le_id_l (mult (mult m e) hh) (mult E4 hh) (mult E4 hh)
               (req_mult_compat (mult m e) E4 hh hh Hreq (req_refl hh))
               (le_refl (mult E4 hh))).
Qed.

(* [(a1 * s) * (a2 * s) == (a1 * a2) * (s * s)] (a compact shell of the   *)
(* baseline's six-step Hs1-Hs6 chain; used at the mult Hthird site). *)
Lemma req_rdf_four_mult : forall a1 a2 s : R,
  req (mult (mult a1 s) (mult a2 s)) (mult (mult a1 a2) (mult s s)).
Proof.
  intros a1 a2 s.
  apply (req_trans (mult (mult a1 s) (mult a2 s))
                   (mult a1 (mult s (mult a2 s)))
                   (mult (mult a1 a2) (mult s s))).
  - exact (req_sym (mult a1 (mult s (mult a2 s)))
                   (mult (mult a1 s) (mult a2 s)) (mult_assoc a1 s (mult a2 s))).
  - apply (req_trans (mult a1 (mult s (mult a2 s)))
                     (mult a1 (mult (mult s a2) s))
                     (mult (mult a1 a2) (mult s s))).
    + exact (req_mult_compat a1 a1 (mult s (mult a2 s)) (mult (mult s a2) s)
                             (req_refl a1) (mult_assoc s a2 s)).
    + apply (req_trans (mult a1 (mult (mult s a2) s))
                       (mult a1 (mult (mult a2 s) s))
                       (mult (mult a1 a2) (mult s s))).
      * exact (req_mult_compat a1 a1 (mult (mult s a2) s) (mult (mult a2 s) s)
                               (req_refl a1)
                               (req_mult_compat (mult s a2) (mult a2 s) s s
                                                (mult_comm s a2) (req_refl s))).
      * apply (req_trans (mult a1 (mult (mult a2 s) s))
                         (mult (mult a1 (mult a2 s)) s)
                         (mult (mult a1 a2) (mult s s))).
        -- exact (mult_assoc a1 (mult a2 s) s).
        -- apply (req_trans (mult (mult a1 (mult a2 s)) s)
                            (mult (mult (mult a1 a2) s) s)
                            (mult (mult a1 a2) (mult s s))).
           ++ exact (req_mult_compat (mult a1 (mult a2 s)) (mult (mult a1 a2) s) s s
                                     (mult_assoc a1 a2 s) (req_refl s)).
           ++ exact (req_sym (mult (mult a1 a2) (mult s s))
                             (mult (mult (mult a1 a2) s) s)
                             (mult_assoc (mult a1 a2) s s)).
Qed.

(* [D * ((inv D * e2) * hh) == e2 * hh] for [D > 0] (used at the mult Hdq  *)
(* site and in the same-shaped compose budget closing). *)
Lemma req_rdf_inv_pair : forall (D : R) (HD : lt zero D) (e2 hh : R),
  req (mult D (mult (mult (inv_pos D HD) e2) hh)) (mult e2 hh).
Proof.
  intros D HD e2 hh.
  assert (Hinner : req (mult D (mult (inv_pos D HD) e2)) (mult one e2)).
  { apply (req_trans (mult D (mult (inv_pos D HD) e2))
                     (mult (mult D (inv_pos D HD)) e2)
                     (mult one e2)).
    - exact (mult_assoc D (inv_pos D HD) e2).
    - exact (req_mult_compat (mult D (inv_pos D HD)) one e2 e2
                             (inv_pos_correct D HD) (req_refl e2)). }
  apply (req_trans (mult D (mult (mult (inv_pos D HD) e2) hh))
                   (mult (mult D (mult (inv_pos D HD) e2)) hh)
                   (mult e2 hh)).
  - exact (mult_assoc D (mult (inv_pos D HD) e2) hh).
  - exact (req_trans (mult (mult D (mult (inv_pos D HD) e2)) hh)
                     (mult (mult one e2) hh)
                     (mult e2 hh)
                     (req_mult_compat (mult D (mult (inv_pos D HD) e2)) (mult one e2)
                                      hh hh Hinner (req_refl hh))
                     (req_mult_compat (mult one e2) e2 hh hh
                                      (req_trans (mult one e2) (mult e2 one) e2
                                                 (mult_comm one e2) (mult_one e2))
                                      (req_refl hh))).
Qed.

(* ---- item 4: differentiable_mult -> [req_rdf_mult] (the main theorem   *)
(*      of the baseline cluster; the error decomposition uses             *)
(*      [req_mult_diff_decomp] of [UpReqAlgebra]) ------------------ *)

Theorem req_rdf_mult : forall f g : R -> R,
  reqRDF f -> reqRDF g -> reqRDF (fun x => mult (f x) (g x)).
Proof.
  intros f g Hf Hg.
  exists (fun x => plus (mult (rdf_df f Hf x) (g x)) (mult (f x) (rdf_df g Hg x))).
  intros x eps Heps.
  pose (i2 := inv_pos (plus one one) req_two_pos).
  pose (eps4 := mult i2 (mult i2 eps)).
  pose (eps2 := mult i2 eps).
  assert (Heps4 : lt zero eps4).
  { exact (mult_positive i2 (mult i2 eps) (inv_pos_pos (plus one one) req_two_pos)
             (req_rdf_half_pos eps Heps)). }
  pose (Mf := plus (abs (f x)) one).
  assert (Hmf : lt zero Mf) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (f x)).
  pose (Mg := plus (abs (g x)) one).
  assert (Hmg : lt zero Mg) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (g x)).
  pose (eps_f := mult (inv_pos Mg Hmg) eps4).
  assert (Hef : lt zero eps_f).
  { exact (mult_positive (inv_pos Mg Hmg) eps4 (inv_pos_pos Mg Hmg) Heps4). }
  pose (eps_g := mult (inv_pos Mf Hmf) eps4).
  assert (Heg : lt zero eps_g).
  { exact (mult_positive (inv_pos Mf Hmf) eps4 (inv_pos_pos Mf Hmf) Heps4). }
  destruct (rdf_correct f Hf x eps_f Hef) as [dfd [Hd1 Hd2]].
  destruct (rdf_correct g Hg x eps_g Heg) as [dgd [Hg1 Hg2]].
  pose (Den := mult (plus (abs (rdf_df f Hf x)) eps_f) (plus (abs (rdf_df g Hg x)) eps_g)).
  assert (HD1 : lt zero (plus (abs (rdf_df f Hf x)) eps_f)).
  { exact (req_plus_le_lt_pos (abs (rdf_df f Hf x)) eps_f
             (abs_nonneg_plain (rdf_df f Hf x)) Hef). }
  assert (HD2 : lt zero (plus (abs (rdf_df g Hg x)) eps_g)).
  { exact (req_plus_le_lt_pos (abs (rdf_df g Hg x)) eps_g
             (abs_nonneg_plain (rdf_df g Hg x)) Heg). }
  assert (HDpos : lt zero Den).
  { exact (mult_positive (plus (abs (rdf_df f Hf x)) eps_f)
                         (plus (abs (rdf_df g Hg x)) eps_g) HD1 HD2). }
  pose (eps3 := mult (inv_pos Den HDpos) eps2).
  assert (He3 : lt zero eps3).
  { exact (mult_positive (inv_pos Den HDpos) eps2 (inv_pos_pos Den HDpos)
             (req_rdf_half_pos eps Heps)). }
  exists (min (min dfd dgd) eps3).
  split.
  - exact (min_pos (min dfd dgd) eps3 (min_pos dfd dgd Hd1 Hg1) He3).
  - intros h Hh.
    assert (Hh_d : lt (abs h) dfd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dfd
               (lt_le_trans (abs h) (min (min dfd dgd) eps3) (min dfd dgd) Hh
                            (min_le_l_plain (min dfd dgd) eps3))
               (min_le_l_plain dfd dgd)). }
    assert (Hh_dg : lt (abs h) dgd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dgd
               (lt_le_trans (abs h) (min (min dfd dgd) eps3) (min dfd dgd) Hh
                            (min_le_l_plain (min dfd dgd) eps3))
               (min_le_r_plain dfd dgd)). }
    assert (Hh_le3 : le (abs h) eps3).
    { exact (lt_le_iff (abs h) eps3 (inl
               (lt_le_trans (abs h) (min (min dfd dgd) eps3) eps3 Hh
                            (min_le_r_plain (min dfd dgd) eps3)))). }
    assert (Hdf_bound : le (abs (req_minus (f (plus x h)) (f x)))
                           (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))).
    { exact (req_rdf_delta_bound (f (plus x h)) (f x) (rdf_df f Hf x) eps_f h
               (Hd2 h Hh_d)). }
    assert (Hdg_bound : le (abs (req_minus (g (plus x h)) (g x)))
                           (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))).
    { exact (req_rdf_delta_bound (g (plus x h)) (g x) (rdf_df g Hg x) eps_g h
               (Hg2 h Hh_dg)). }
    apply (le_id_l (abs (req_minus (mult (f (plus x h)) (g (plus x h)))
                                   (plus (mult (f x) (g x))
                                         (mult (plus (mult (rdf_df f Hf x) (g x))
                                                     (mult (f x) (rdf_df g Hg x))) h))))
                   (abs (plus (mult (f x) (req_minus (g (plus x h))
                                                      (plus (g x) (mult (rdf_df g Hg x) h))))
                              (plus (mult (g x) (req_minus (f (plus x h))
                                                           (plus (f x) (mult (rdf_df f Hf x) h))))
                                    (mult (req_minus (f (plus x h)) (f x))
                                          (req_minus (g (plus x h)) (g x))))))
                   (mult eps (abs h))).
    + exact (req_abs_compat
               (req_minus (mult (f (plus x h)) (g (plus x h)))
                          (plus (mult (f x) (g x))
                                (mult (plus (mult (rdf_df f Hf x) (g x))
                                            (mult (f x) (rdf_df g Hg x))) h)))
               (plus (mult (f x) (req_minus (g (plus x h))
                                            (plus (g x) (mult (rdf_df g Hg x) h))))
                     (plus (mult (g x) (req_minus (f (plus x h))
                                                  (plus (f x) (mult (rdf_df f Hf x) h))))
                           (mult (req_minus (f (plus x h)) (f x))
                                 (req_minus (g (plus x h)) (g x)))))
               (req_mult_diff_decomp f g (rdf_df f Hf) (rdf_df g Hg) x h)).
    + apply (le_trans _
               (plus (abs (mult (f x) (req_minus (g (plus x h))
                                                 (plus (g x) (mult (rdf_df g Hg x) h)))))
                     (abs (plus (mult (g x) (req_minus (f (plus x h))
                                                       (plus (f x) (mult (rdf_df f Hf x) h))))
                                (mult (req_minus (f (plus x h)) (f x))
                                      (req_minus (g (plus x h)) (g x))))))).
      * exact (req_rdf_abs_triangle
                 (mult (f x) (req_minus (g (plus x h))
                                        (plus (g x) (mult (rdf_df g Hg x) h))))
                 (plus (mult (g x) (req_minus (f (plus x h))
                                              (plus (f x) (mult (rdf_df f Hf x) h))))
                       (mult (req_minus (f (plus x h)) (f x))
                             (req_minus (g (plus x h)) (g x))))).
* apply (le_trans _
               (plus (abs (mult (f x) (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h))))) (plus (abs (mult (g x) (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h))))) (abs (mult (req_minus (f (plus x h)) (f x)) (req_minus (g (plus x h)) (g x))))))).
        -- exact (le_plus_compat
                    (abs (mult (f x) (req_minus (g (plus x h))
                                                (plus (g x) (mult (rdf_df g Hg x) h)))))
                    (abs (mult (f x) (req_minus (g (plus x h))
                                                (plus (g x) (mult (rdf_df g Hg x) h)))))
                    (abs (plus (mult (g x) (req_minus (f (plus x h))
                                                      (plus (f x) (mult (rdf_df f Hf x) h))))
                               (mult (req_minus (f (plus x h)) (f x))
                                     (req_minus (g (plus x h)) (g x)))))
                    (plus (abs (mult (g x) (req_minus (f (plus x h))
                                                      (plus (f x) (mult (rdf_df f Hf x) h)))))
                          (abs (mult (req_minus (f (plus x h)) (f x))
                                     (req_minus (g (plus x h)) (g x)))))
                    (le_refl (abs (mult (f x) (req_minus (g (plus x h))
                                                         (plus (g x) (mult (rdf_df g Hg x) h))))))
                    (req_rdf_abs_triangle
                       (mult (g x) (req_minus (f (plus x h))
                                              (plus (f x) (mult (rdf_df f Hf x) h))))
                       (mult (req_minus (f (plus x h)) (f x))
                             (req_minus (g (plus x h)) (g x))))).
        -- (* merging the three upper bounds [eps4*|h|], [eps4*|h|],       *)
           (* [eps2*|h|] into [<= eps*|h|] *)
           assert (Hb1 : le (abs (mult (f x) (req_minus (g (plus x h))
                                                        (plus (g x) (mult (rdf_df g Hg x) h)))))
                            (mult eps4 (abs h))).
           { assert (Hreqf : req (mult Mf eps_g) eps4).
             { exact (req_trans (mult Mf (mult (inv_pos Mf Hmf) eps4))
                                (mult (mult Mf (inv_pos Mf Hmf)) eps4) eps4
                       (mult_assoc Mf (inv_pos Mf Hmf) eps4)
                       (req_trans (mult (mult Mf (inv_pos Mf Hmf)) eps4)
                                  (mult one eps4) eps4
                                  (req_mult_compat (mult Mf (inv_pos Mf Hmf)) one eps4 eps4
                                                   (inv_pos_correct Mf Hmf) (req_refl eps4))
                                  (req_trans (mult one eps4) (mult eps4 one) eps4
                                             (mult_comm one eps4) (mult_one eps4)))). }
             apply (le_trans (abs (mult (f x) (req_minus (g (plus x h))
                                                         (plus (g x) (mult (rdf_df g Hg x) h)))))
                             (mult (abs (f x)) (mult eps_g (abs h)))
                             (mult eps4 (abs h))).
             - apply (le_trans (abs (mult (f x) (req_minus (g (plus x h))
                                                          (plus (g x) (mult (rdf_df g Hg x) h)))))
                               (mult (abs (f x))
                                     (abs (req_minus (g (plus x h))
                                                     (plus (g x) (mult (rdf_df g Hg x) h)))))
                               (mult (abs (f x)) (mult eps_g (abs h)))).
               + exact (req_rdf_abs_mult_le (f x)
                           (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h)))).
               + exact (req_le_mult_compat_r (abs (f x))
                            (abs (req_minus (g (plus x h))
                                            (plus (g x) (mult (rdf_df g Hg x) h))))
                            (mult eps_g (abs h))
                            (abs_nonneg_plain (f x)) (Hg2 h Hh_dg)).
             - exact (req_rdf_share (f x) Mf eps_g eps4 (abs h)
                        (req_abs_le_abs_plus_one (f x)) Heg Hreqf
                        (abs_nonneg_plain h)). }
           assert (Hb2 : le (abs (mult (g x) (req_minus (f (plus x h))
                                                        (plus (f x) (mult (rdf_df f Hf x) h)))))
                            (mult eps4 (abs h))).
           { assert (Hreqg : req (mult Mg eps_f) eps4).
             { exact (req_trans (mult Mg (mult (inv_pos Mg Hmg) eps4))
                                (mult (mult Mg (inv_pos Mg Hmg)) eps4) eps4
                       (mult_assoc Mg (inv_pos Mg Hmg) eps4)
                       (req_trans (mult (mult Mg (inv_pos Mg Hmg)) eps4)
                                  (mult one eps4) eps4
                                  (req_mult_compat (mult Mg (inv_pos Mg Hmg)) one eps4 eps4
                                                   (inv_pos_correct Mg Hmg) (req_refl eps4))
                                  (req_trans (mult one eps4) (mult eps4 one) eps4
                                             (mult_comm one eps4) (mult_one eps4)))). }
             apply (le_trans (abs (mult (g x) (req_minus (f (plus x h))
                                                         (plus (f x) (mult (rdf_df f Hf x) h)))))
                             (mult (abs (g x)) (mult eps_f (abs h)))
                             (mult eps4 (abs h))).
             - apply (le_trans (abs (mult (g x) (req_minus (f (plus x h))
                                                          (plus (f x) (mult (rdf_df f Hf x) h)))))
                               (mult (abs (g x))
                                     (abs (req_minus (f (plus x h))
                                                     (plus (f x) (mult (rdf_df f Hf x) h)))))
                               (mult (abs (g x)) (mult eps_f (abs h)))).
               + exact (req_rdf_abs_mult_le (g x)
                           (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h)))).
               + exact (req_le_mult_compat_r (abs (g x))
                            (abs (req_minus (f (plus x h))
                                            (plus (f x) (mult (rdf_df f Hf x) h))))
                            (mult eps_f (abs h))
                            (abs_nonneg_plain (g x)) (Hd2 h Hh_d)).
             - exact (req_rdf_share (g x) Mg eps_f eps4 (abs h)
                        (req_abs_le_abs_plus_one (g x)) Hef Hreqg
                        (abs_nonneg_plain h)). }
           assert (Hthird : le (abs (mult (req_minus (f (plus x h)) (f x))
                                          (req_minus (g (plus x h)) (g x))))
                               (mult eps2 (abs h))).
           { assert (HleA : le zero (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))).
             { exact (le_id_l zero (mult zero (abs h))
                        (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                        (req_sym (mult zero (abs h)) zero
                                 (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                                            (mult_comm zero (abs h)) (mult_zero (abs h))))
                        (le_mult_compat_weak zero (plus (abs (rdf_df f Hf x)) eps_f) (abs h)
                         (abs_nonneg_plain h)
                         (lt_le_iff zero (plus (abs (rdf_df f Hf x)) eps_f) (inl HD1)))). }
             assert (HleB : le zero (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))).
             { exact (le_id_l zero (mult zero (abs h))
                        (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                        (req_sym (mult zero (abs h)) zero
                                 (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                                            (mult_comm zero (abs h)) (mult_zero (abs h))))
                        (le_mult_compat_weak zero (plus (abs (rdf_df g Hg x)) eps_g) (abs h)
                         (abs_nonneg_plain h)
                         (lt_le_iff zero (plus (abs (rdf_df g Hg x)) eps_g) (inl HD2)))). }
             apply (le_trans (abs (mult (req_minus (f (plus x h)) (f x))
                                        (req_minus (g (plus x h)) (g x))))
                             (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                   (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                             (mult eps2 (abs h))).
             - apply (le_trans (abs (mult (req_minus (f (plus x h)) (f x))
                                         (req_minus (g (plus x h)) (g x))))
                               (mult (abs (req_minus (f (plus x h)) (f x)))
                                     (abs (req_minus (g (plus x h)) (g x))))
                               (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                     (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))).
               + exact (req_rdf_abs_mult_le (req_minus (f (plus x h)) (f x))
                           (req_minus (g (plus x h)) (g x))).
               + exact (le_trans (mult (abs (req_minus (f (plus x h)) (f x)))
                                       (abs (req_minus (g (plus x h)) (g x))))
                                 (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                       (abs (req_minus (g (plus x h)) (g x))))
                                 (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                       (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                            (le_mult_compat_weak (abs (req_minus (f (plus x h)) (f x)))
                              (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                              (abs (req_minus (g (plus x h)) (g x)))
                              (abs_nonneg_plain (req_minus (g (plus x h)) (g x)))
                              Hdf_bound)
                            (req_le_mult_compat_r
                              (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                              (abs (req_minus (g (plus x h)) (g x)))
                              (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                              HleA Hdg_bound)).
             - exact (le_trans (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                     (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                               (mult Den (mult (abs h) (abs h)))
                               (mult eps2 (abs h))
                       (le_id_l (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                      (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                                (mult Den (mult (abs h) (abs h)))
                                (mult Den (mult (abs h) (abs h)))
                                (req_rdf_four_mult (plus (abs (rdf_df f Hf x)) eps_f)
                                                   (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                                (le_refl (mult Den (mult (abs h) (abs h)))))
                       (le_trans (mult Den (mult (abs h) (abs h)))
                                 (mult Den (mult eps3 (abs h)))
                                 (mult eps2 (abs h))
                         (req_le_mult_compat_r Den (mult (abs h) (abs h)) (mult eps3 (abs h))
                          (lt_le_iff zero Den (inl HDpos))
                          (le_mult_compat_weak (abs h) eps3 (abs h)
                           (abs_nonneg_plain h) Hh_le3))
                         (le_id_l (mult Den (mult eps3 (abs h))) (mult eps2 (abs h))
                          (mult eps2 (abs h))
                          (req_rdf_inv_pair Den HDpos eps2 (abs h))
                          (le_refl (mult eps2 (abs h)))))). }
           apply (le_trans _
                     (plus (mult eps4 (abs h))
                           (plus (mult eps4 (abs h)) (mult eps2 (abs h))))).
           ++ exact (le_plus_compat
                       (abs (mult (f x) (req_minus (g (plus x h))
                                                   (plus (g x) (mult (rdf_df g Hg x) h)))))
                       (mult eps4 (abs h))
                       (plus (abs (mult (g x) (req_minus (f (plus x h))
                                                         (plus (f x) (mult (rdf_df f Hf x) h)))))
                             (abs (mult (req_minus (f (plus x h)) (f x))
                                        (req_minus (g (plus x h)) (g x)))))
                       (plus (mult eps4 (abs h)) (mult eps2 (abs h)))
                       Hb1
                       (le_plus_compat
                          (abs (mult (g x) (req_minus (f (plus x h))
                                                      (plus (f x) (mult (rdf_df f Hf x) h)))))
                          (mult eps4 (abs h))
                          (abs (mult (req_minus (f (plus x h)) (f x))
                                     (req_minus (g (plus x h)) (g x))))
                          (mult eps2 (abs h))
                          Hb2 Hthird)).
           ++ assert (Hj1 : req (plus (mult eps4 (abs h))
                                      (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                                 (mult eps (abs h))).
              { apply (req_trans (plus (mult eps4 (abs h))
                                       (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                                 (plus (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                                       (mult eps2 (abs h)))
                                 (mult eps (abs h))).
                - exact (plus_assoc (mult eps4 (abs h)) (mult eps4 (abs h))
                                    (mult eps2 (abs h))).
                - apply (req_trans (plus (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                                         (mult eps2 (abs h)))
                                   (plus (mult (mult i2 eps) (abs h))
                                         (mult (mult i2 eps) (abs h)))
                                   (mult eps (abs h))).
                  + apply (req_plus_compat (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                                           (mult (mult i2 eps) (abs h))
                                           (mult eps2 (abs h)) (mult (mult i2 eps) (abs h))).
                    -- exact (req_rdf_quarter_pair_req eps (abs h)).
                    -- apply req_refl.
                  + exact (req_rdf_half_pair_req eps (abs h)).
              }
              assert (Hj2 : le zero (mult eps (abs h))).
              { exact (le_id_l zero (mult zero (abs h)) (mult eps (abs h))
                         (req_sym (mult zero (abs h)) zero
                                  (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                                             (mult_comm zero (abs h)) (mult_zero (abs h))))
                         (le_mult_compat_weak zero eps (abs h) (abs_nonneg_plain h)
                          (lt_le_iff zero eps (inl Heps)))). }
              exact (le_id_l (plus (mult eps4 (abs h))
                                   (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                             (mult eps (abs h)) (mult eps (abs h))
                             Hj1 (le_refl (mult eps (abs h)))).
Qed.


(* ---- item 5: differentiable_opp -> [req_rdf_opp] ------------------------ *)

Theorem req_rdf_opp : forall f : R -> R, reqRDF f -> reqRDF (fun x => opp (f x)).
Proof.
  intros f Hf.
  exists (fun x => opp (rdf_df f Hf x)).
  intros x eps Heps.
  destruct (rdf_correct f Hf x eps Heps) as [delta [Hd1 Hd2]].
  exists delta.
  split.
  - exact Hd1.
  - intros h Hh.
    assert (Hz : req (req_minus (opp (f (plus x h)))
                                (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                     (opp (req_minus (f (plus x h))
                                     (plus (f x) (mult (rdf_df f Hf x) h))))).
    { assert (Hinner : req (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                           (plus (f x) (mult (rdf_df f Hf x) h))).
      { apply (req_trans (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                         (plus (opp (opp (f x))) (opp (mult (opp (rdf_df f Hf x)) h)))
                         (plus (f x) (mult (rdf_df f Hf x) h))).
        - exact (req_opp_plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)).
        - apply (req_plus_compat (opp (opp (f x))) (f x)
                                 (opp (mult (opp (rdf_df f Hf x)) h))
                                 (mult (rdf_df f Hf x) h)).
          + exact (req_double_neg (f x)).
          + exact (req_trans (opp (mult (opp (rdf_df f Hf x)) h))
                             (opp (opp (mult (rdf_df f Hf x) h)))
                             (mult (rdf_df f Hf x) h)
                             (req_opp_compat (mult (opp (rdf_df f Hf x)) h)
                                             (opp (mult (rdf_df f Hf x) h))
                                             (req_opp_mult_r (rdf_df f Hf x) h))
                             (req_double_neg (mult (rdf_df f Hf x) h))). }
      unfold req_minus.
      apply (req_trans (plus (opp (f (plus x h)))
                             (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h))))
                       (plus (opp (f (plus x h)))
                             (plus (f x) (mult (rdf_df f Hf x) h)))
                       (opp (plus (f (plus x h))
                                  (opp (plus (f x) (mult (rdf_df f Hf x) h)))))).
        - exact (req_plus_compat (opp (f (plus x h))) (opp (f (plus x h)))
                                 (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                                 (plus (f x) (mult (rdf_df f Hf x) h))
                                 (req_refl (opp (f (plus x h)))) Hinner).
        - exact (req_sym (opp (req_minus (f (plus x h))
                                         (plus (f x) (mult (rdf_df f Hf x) h))))
                         (plus (opp (f (plus x h)))
                               (plus (f x) (mult (rdf_df f Hf x) h)))
                         (req_opp_minus (f (plus x h))
                                        (plus (f x) (mult (rdf_df f Hf x) h)))). }
    apply (le_trans (abs (req_minus (opp (f (plus x h)))
                                    (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h))))
                    (abs (req_minus (f (plus x h))
                                    (plus (f x) (mult (rdf_df f Hf x) h))))
                    (mult eps (abs h))).
      + exact (le_id_l (abs (req_minus (opp (f (plus x h)))
                                       (plus (opp (f x))
                                             (mult (opp (rdf_df f Hf x)) h))))
                       (abs (req_minus (f (plus x h))
                                       (plus (f x) (mult (rdf_df f Hf x) h))))
                       (abs (req_minus (f (plus x h))
                                       (plus (f x) (mult (rdf_df f Hf x) h))))
                       (req_trans (abs (req_minus (opp (f (plus x h)))
                                                  (plus (opp (f x))
                                                        (mult (opp (rdf_df f Hf x)) h))))
                                  (abs (opp (req_minus (f (plus x h))
                                                       (plus (f x)
                                                             (mult (rdf_df f Hf x) h)))))
                                  (abs (req_minus (f (plus x h))
                                                  (plus (f x) (mult (rdf_df f Hf x) h))))
                                  (req_abs_compat
                                     (req_minus (opp (f (plus x h)))
                                                (plus (opp (f x))
                                                      (mult (opp (rdf_df f Hf x)) h)))
                                     (opp (req_minus (f (plus x h))
                                                     (plus (f x)
                                                           (mult (rdf_df f Hf x) h))))
                                     Hz)
                                  (abs_opp (req_minus (f (plus x h))
                                                      (plus (f x)
                                                            (mult (rdf_df f Hf x) h)))))
                       (le_refl (abs (req_minus (f (plus x h))
                                                (plus (f x)
                                                      (mult (rdf_df f Hf x) h)))))).
      + exact (Hd2 h Hh).
Qed.

(* ---- item 6: differentiable_minus -> [req_rdf_minus] ------------------- *)
(*      [req_minus] is transparently [plus . opp]: after unfolding, the   *)
(*      goal converts and closes by direct matching --------- *)

Theorem req_rdf_minus : forall f g : R -> R,
  reqRDF f -> reqRDF g -> reqRDF (fun x => req_minus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  pose proof (req_rdf_opp g Hg) as Hopp.
  pose proof (req_rdf_plus f (fun x => opp (g x)) Hf Hopp) as Hp.
  exists (rdf_df (fun x => plus (f x) (opp (g x))) Hp).
  intros x eps Heps.
  destruct (rdf_correct (fun x => plus (f x) (opp (g x))) Hp x eps Heps)
    as [delta [Hd1 Hd2]].
  exists delta.
  split.
  - exact Hd1.
  - exact (fun h Hh => Hd2 h Hh).
Qed.

(* ---- item 7: differentiable_power_nat -> [req_power_nat] +             *)
(*        [req_rdf_power_nat] (induction with the [req_rdf_mult] carrier  *)
(*        reconstruction) --------------------- *)

Fixpoint req_power_nat (n : nat) (x : R) : R :=
  match n with
  | Datatypes.O => one
  | Datatypes.S n' => mult x (req_power_nat n' x)
  end.

Theorem req_rdf_power_nat : forall n : nat,
  reqRDF (fun x => req_power_nat (Datatypes.S n) x).
Proof.
  intro n.
  induction n as [| n' IH].
  - exists (fun _ => one).
    intros x eps Heps.
    exists one.
    split.
    + exact one_pos.
    + intros h Hh.
      assert (Herr : req (req_minus (mult (plus x h) one)
                                    (plus (mult x one) (mult one h))) zero).
      { apply (req_minus_self_zero (mult (plus x h) one)
                                   (plus (mult x one) (mult one h))).
        exact (req_trans (mult (plus x h) one) (plus x h)
                         (plus (mult x one) (mult one h))
                         (mult_one (plus x h))
                         (req_sym (plus (mult x one) (mult one h)) (plus x h)
                                  (req_plus_compat (mult x one) x (mult one h) h
                                                   (mult_one x)
                                                   (req_trans (mult one h) (mult h one) h
                                                      (mult_comm one h) (mult_one h))))). }
      exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus (mult (plus x h) one)
                                            (plus (mult x one) (mult one h)))
                                 eps h Heps Herr).
  - exact (req_rdf_mult (fun y => y) (fun y => req_power_nat (Datatypes.S n') y)
                        req_rdf_id IH).
Qed.

(* ---- shared machine 3: [A == (A - Y) + Y] (the compose decomposition   *)
(* engine) ------------------------- *)

Lemma req_rdf_minus_pair : forall A Y : R, req A (plus (req_minus A Y) Y).
Proof.
  intros A Y.
  apply (req_sym (plus (req_minus A Y) Y) A).
  unfold req_minus.
  apply (req_trans (plus (plus A (opp Y)) Y) (plus A (plus (opp Y) Y)) A).
  - exact (req_sym (plus A (plus (opp Y) Y)) (plus (plus A (opp Y)) Y)
                   (plus_assoc A (opp Y) Y)).
  - apply (req_trans (plus A (plus (opp Y) Y)) (plus A zero) A).
    + exact (req_plus_compat A A (plus (opp Y) Y) zero (req_refl A) (req_plus_opp_l Y)).
    + exact (plus_zero A).
Qed.


(* [(a + b) - c == a + (b - c)] (req counterpart of the baseline          *)
(* [minus_plus_zero_r]; used by mse/compose). *)
Lemma req_minus_plus_zero_r : forall a b c : R,
  req (req_minus (plus a b) c) (plus a (req_minus b c)).
Proof.
  intros a b c.
  unfold req_minus.
  exact (req_sym (plus a (plus b (opp c))) (plus (plus a b) (opp c))
                 (plus_assoc a b (opp c))).
Qed.



Lemma req_rdf_compose_diff_decomp : forall A B C D G g0 h : R,
  req (req_minus A (plus B (mult (mult C D) h)))
      (plus (req_minus A (plus B (mult C (req_minus G g0))))
            (mult C (req_minus (req_minus G g0) (mult D h)))).
Proof.
  intros A B C D G g0 h.
  apply (req_trans (req_minus A (plus B (mult (mult C D) h)))
                   (req_minus A (plus B (mult C (mult D h))))
                   (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (req_minus (req_minus G g0) (mult D h))))).
  - exact (req_rdf_minus_compat_r A (plus B (mult (mult C D) h))
             (plus B (mult C (mult D h)))
             (req_plus_compat B B (mult (mult C D) h) (mult C (mult D h))
                              (req_refl B)
                              (req_sym (mult C (mult D h)) (mult (mult C D) h)
                                       (mult_assoc C D h)))).
  - apply (req_trans (req_minus A (plus B (mult C (mult D h))))
                     (plus (req_minus A (plus B (mult C (req_minus G g0))))
                           (req_minus (plus B (mult C (req_minus G g0)))
                                      (plus B (mult C (mult D h)))))
                     (plus (req_minus A (plus B (mult C (req_minus G g0))))
                           (mult C (req_minus (req_minus G g0) (mult D h))))).
    + apply (req_trans (req_minus A (plus B (mult C (mult D h))))
                       (req_minus (plus (req_minus A (plus B (mult C (req_minus G g0))))
                                        (plus B (mult C (req_minus G g0))))
                                  (plus B (mult C (mult D h))))
                       (plus (req_minus A (plus B (mult C (req_minus G g0))))
                             (req_minus (plus B (mult C (req_minus G g0)))
                                        (plus B (mult C (mult D h)))))).
      -- exact (req_rdf_minus_compat_l A
                    (plus (req_minus A (plus B (mult C (req_minus G g0))))
                          (plus B (mult C (req_minus G g0))))
                    (plus B (mult C (mult D h)))
                    (req_rdf_minus_pair A (plus B (mult C (req_minus G g0))))).
      -- exact (req_minus_plus_zero_r (req_minus A (plus B (mult C (req_minus G g0))))
                                         (plus B (mult C (req_minus G g0)))
                                         (plus B (mult C (mult D h)))).
    + apply (req_plus_compat (req_minus A (plus B (mult C (req_minus G g0))))
                             (req_minus A (plus B (mult C (req_minus G g0))))
                             (req_minus (plus B (mult C (req_minus G g0)))
                                        (plus B (mult C (mult D h))))
                             (mult C (req_minus (req_minus G g0) (mult D h)))
                             (req_refl (req_minus A (plus B (mult C (req_minus G g0)))))).
      * apply (req_trans (req_minus (plus B (mult C (req_minus G g0)))
                                    (plus B (mult C (mult D h))))
                         (plus (req_minus B B)
                               (req_minus (mult C (req_minus G g0))
                                          (mult C (mult D h))))
                         (mult C (req_minus (req_minus G g0) (mult D h)))).
        -- exact (req_minus_plus_distr B (mult C (req_minus G g0)) B
                                           (mult C (mult D h))).
        -- exact (req_trans (plus (req_minus B B)
                                  (req_minus (mult C (req_minus G g0)) (mult C (mult D h))))
                            (plus zero (mult C (req_minus (req_minus G g0) (mult D h))))
                            (mult C (req_minus (req_minus G g0) (mult D h)))
                            (req_plus_compat (req_minus B B) zero
                                             (req_minus (mult C (req_minus G g0)) (mult C (mult D h)))
                                             (mult C (req_minus (req_minus G g0) (mult D h)))
                                             (req_minus_self_zero B B (req_refl B))
                                             (req_sym (mult C (req_minus (req_minus G g0) (mult D h)))
                                                      (req_minus (mult C (req_minus G g0))
                                                                 (mult C (mult D h)))
                                                      (req_mult_minus_distr_l C (req_minus G g0)
                                                                              (mult D h))))
                            (req_plus_zero_l (mult C (req_minus (req_minus G g0) (mult D h))))).
Qed.

(* ---- item 8: differentiable_compose -> [req_rdf_compose] ----------------- *)

(* the function req-compatibility slot (an honest premise: the baseline   *)
(* transports freely via Leibniz equality, the req side needs the         *)
(* explicit slot). *)
Theorem req_rdf_compose : forall f g : R -> R,
  reqRDF f -> reqRDF g ->
  (forall u v : R, req u v -> req (f u) (f v)) ->
  reqRDF (fun x => f (g x)).
Proof.
  intros f g Hf Hg Hfc.
  exists (fun x => mult (rdf_df f Hf (g x)) (rdf_df g Hg x)).
  intros x eps Heps.
  pose (i2 := inv_pos (plus one one) req_two_pos).
  pose (eps4 := mult i2 (mult i2 eps)).
  assert (Heps4 : lt zero eps4).
  { exact (mult_positive i2 (mult i2 eps) (inv_pos_pos (plus one one) req_two_pos)
             (req_rdf_half_pos eps Heps)). }
  pose (M := plus (abs (rdf_df f Hf (g x))) one).
  assert (HM : lt zero M) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (rdf_df f Hf (g x))).
  pose (L := plus (abs (rdf_df g Hg x)) one).
  assert (HL : lt zero L) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (rdf_df g Hg x)).
  pose (eps_f := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_f : lt zero eps_f).
  { exact (min_pos one (mult (inv_pos L HL) eps4) one_pos
             (mult_positive (inv_pos L HL) eps4 (inv_pos_pos L HL) Heps4)). }
  pose (eps_g := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_g : lt zero eps_g).
  { exact (min_pos one (mult (inv_pos M HM) eps4) one_pos
             (mult_positive (inv_pos M HM) eps4 (inv_pos_pos M HM) Heps4)). }
  destruct (rdf_correct f Hf (g x) eps_f Heps_f) as [dfd [Hd1 Hd2]].
  destruct (rdf_correct g Hg x eps_g Heps_g) as [dgd [Hg1 Hg2]].
  exists (min dgd (min one (mult (inv_pos L HL) dfd))).
  split.
  - exact (min_pos dgd (min one (mult (inv_pos L HL) dfd)) Hg1
             (min_pos one (mult (inv_pos L HL) dfd) one_pos
              (mult_positive (inv_pos L HL) dfd (inv_pos_pos L HL) Hd1))).
  - intros h Hh.
    assert (Hh_dgd : lt (abs h) dgd).
    { exact (lt_le_trans (abs h) (min dgd (min one (mult (inv_pos L HL) dfd))) dgd Hh
                         (min_le_l_plain dgd (min one (mult (inv_pos L HL) dfd)))). }
    assert (Hh_dfd : lt (abs h) (mult (inv_pos L HL) dfd)).
    { exact (lt_le_trans (abs h) (min one (mult (inv_pos L HL) dfd))
                         (mult (inv_pos L HL) dfd)
                         (lt_le_trans (abs h) (min dgd (min one (mult (inv_pos L HL) dfd)))
                                      (min one (mult (inv_pos L HL) dfd)) Hh
                                      (min_le_r_plain dgd (min one (mult (inv_pos L HL) dfd))))
                         (min_le_r_plain one (mult (inv_pos L HL) dfd))). }
    assert (HDg_bound : le (abs (req_minus (g (plus x h)) (g x)))
                           (mult L (abs h))).
    { assert (Hstep : le (abs (req_minus (g (plus x h)) (g x)))
                         (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))).
      { exact (req_rdf_delta_bound (g (plus x h)) (g x) (rdf_df g Hg x) eps_g h
                 (Hg2 h Hh_dgd)). }
      assert (Heg1 : le eps_g one).
      { exact (min_le_l_plain one (mult (inv_pos M HM) eps4)). }
      assert (Hpos : lt zero (plus (abs (rdf_df g Hg x)) eps_g)).
      { exact (req_plus_le_lt_pos (abs (rdf_df g Hg x)) eps_g
                 (abs_nonneg_plain (rdf_df g Hg x)) Heps_g). }
      assert (Hleg1 : le (plus (abs (rdf_df g Hg x)) eps_g)
                          (plus (abs (rdf_df g Hg x)) one)).
      { exact (le_id_r (plus (abs (rdf_df g Hg x)) eps_g)
                       (plus one (abs (rdf_df g Hg x)))
                       (plus (abs (rdf_df g Hg x)) one)
                       (plus_comm one (abs (rdf_df g Hg x)))
                       (le_id_l (plus (abs (rdf_df g Hg x)) eps_g)
                                (plus eps_g (abs (rdf_df g Hg x)))
                                (plus one (abs (rdf_df g Hg x)))
                                (plus_comm (abs (rdf_df g Hg x)) eps_g)
                                (le_plus_compat eps_g one (abs (rdf_df g Hg x))
                                                (abs (rdf_df g Hg x))
                                                Heg1
                                                (le_refl (abs (rdf_df g Hg x)))))). }
      assert (Hleg2 : le (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                          (mult (plus (abs (rdf_df g Hg x)) one) (abs h))).
      { exact (le_mult_compat_weak (plus (abs (rdf_df g Hg x)) eps_g)
                   (plus (abs (rdf_df g Hg x)) one) (abs h) (abs_nonneg_plain h) Hleg1). }
      assert (Hleg3 : req (mult (plus (abs (rdf_df g Hg x)) one) (abs h)) (mult L (abs h))).
      { exact (req_mult_compat (plus (abs (rdf_df g Hg x)) one) L (abs h) (abs h)
                               (req_refl (plus (abs (rdf_df g Hg x)) one)) (req_refl (abs h))). }
      assert (Hleg4 : le (mult (plus (abs (rdf_df g Hg x)) one) (abs h)) (mult L (abs h))).
      { exact (le_id_l (mult (plus (abs (rdf_df g Hg x)) one) (abs h))
                       (mult L (abs h)) (mult L (abs h)) Hleg3 (le_refl (mult L (abs h)))). }
      assert (Hleg5 : le (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)) (mult L (abs h))).
      { exact (le_trans (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                        (mult (plus (abs (rdf_df g Hg x)) one) (abs h)) (mult L (abs h))
                        Hleg2 Hleg4). }
      exact (le_trans (abs (req_minus (g (plus x h)) (g x)))
                      (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                      (mult L (abs h)) Hstep Hleg5). }
    assert (HdfDg : lt (abs (req_minus (g (plus x h)) (g x))) dfd).
    { apply (le_lt_trans (abs (req_minus (g (plus x h)) (g x)))
                         (mult L (abs h)) dfd).
      - exact HDg_bound.
      - assert (Hraw : lt (mult (abs h) L) (mult (mult (inv_pos L HL) dfd) L)).
        { exact (lt_mult_compat (abs h) (mult (inv_pos L HL) dfd) L HL Hh_dfd). }
        exact (lt_id_l (mult L (abs h)) (mult (abs h) L) dfd
                       (mult_comm L (abs h))
                       (lt_id_r (mult (abs h) L)
                                (mult (mult (inv_pos L HL) dfd) L) dfd
                                (req_trans (mult (mult (inv_pos L HL) dfd) L)
                                           (mult L (mult (inv_pos L HL) dfd)) dfd
                                           (mult_comm (mult (inv_pos L HL) dfd) L)
                                           (req_rdf_inv_cancel L dfd HL Hd1))
                                Hraw)). }
    assert (HT1 : le (abs (req_minus (f (g (plus x h)))
                                     (plus (f (g x)) (mult (rdf_df f Hf (g x))
                                                           (req_minus (g (plus x h)) (g x))))))
                        (mult eps4 (abs h))).
    { apply (le_trans (abs (req_minus (f (g (plus x h)))
                                      (plus (f (g x))
                                            (mult (rdf_df f Hf (g x))
                                                  (req_minus (g (plus x h)) (g x))))))
                      (mult eps_f (abs (req_minus (g (plus x h)) (g x))))
                      (mult eps4 (abs h))).
      - exact (le_id_l (abs (req_minus (f (g (plus x h)))
                                       (plus (f (g x))
                                             (mult (rdf_df f Hf (g x))
                                                   (req_minus (g (plus x h)) (g x))))))
                       (abs (req_minus (f (plus (g x) (req_minus (g (plus x h)) (g x))))
                                       (plus (f (g x))
                                             (mult (rdf_df f Hf (g x))
                                                   (req_minus (g (plus x h)) (g x))))))
                       (mult eps_f (abs (req_minus (g (plus x h)) (g x))))
                       (req_abs_compat
                          (req_minus (f (g (plus x h)))
                                     (plus (f (g x))
                                           (mult (rdf_df f Hf (g x))
                                                 (req_minus (g (plus x h)) (g x)))))
                          (req_minus (f (plus (g x) (req_minus (g (plus x h)) (g x))))
                                     (plus (f (g x))
                                           (mult (rdf_df f Hf (g x))
                                                 (req_minus (g (plus x h)) (g x)))))
                          (req_rdf_minus_compat_l (f (g (plus x h)))
                             (f (plus (g x) (req_minus (g (plus x h)) (g x))))
                             (plus (f (g x))
                                   (mult (rdf_df f Hf (g x))
                                         (req_minus (g (plus x h)) (g x))))
                             (Hfc (g (plus x h))
                                  (plus (g x) (req_minus (g (plus x h)) (g x)))
                                  (req_sym (plus (g x) (req_minus (g (plus x h)) (g x)))
                                           (g (plus x h))
                                           (req_minus_plus_cancel (g x) (g (plus x h)))))))
                       (Hd2 (req_minus (g (plus x h)) (g x)) HdfDg)).
      - assert (Hsc : le (mult eps_f L) eps4).
        { exact (le_trans (mult eps_f L)
                          (mult (mult (inv_pos L HL) eps4) L) eps4
                          (le_mult_compat_weak eps_f (mult (inv_pos L HL) eps4) L
                           (lt_le_iff zero L (inl HL))
                           (min_le_r_plain one (mult (inv_pos L HL) eps4)))
                          (req_rdf_inv_scale_le L eps4 HL)). }
        assert (Hsc2 : le (mult eps_f (mult L (abs h))) (mult eps4 (abs h))).
        { exact (le_trans (mult eps_f (mult L (abs h)))
                          (mult (mult eps_f L) (abs h)) (mult eps4 (abs h))
                          (le_id_l (mult eps_f (mult L (abs h)))
                                   (mult (mult eps_f L) (abs h))
                                   (mult (mult eps_f L) (abs h))
                                   (mult_assoc eps_f L (abs h))
                                   (le_refl (mult (mult eps_f L) (abs h))))
                          (le_mult_compat_weak (mult eps_f L) eps4 (abs h)
                           (abs_nonneg_plain h) Hsc)). }
        exact (le_trans (mult eps_f (abs (req_minus (g (plus x h)) (g x))))
                        (mult eps_f (mult L (abs h))) (mult eps4 (abs h))
                        (req_le_mult_compat_r eps_f (abs (req_minus (g (plus x h)) (g x)))
                                              (mult L (abs h))
                                              (lt_le_iff zero eps_f (inl Heps_f)) HDg_bound)
                        Hsc2). }
    assert (HT2 : le (abs (mult (rdf_df f Hf (g x))
                                (req_minus (req_minus (g (plus x h)) (g x))
                                           (mult (rdf_df g Hg x) h))))
                       (mult eps4 (abs h))).
    { apply (le_trans (abs (mult (rdf_df f Hf (g x))
                                 (req_minus (req_minus (g (plus x h)) (g x))
                                            (mult (rdf_df g Hg x) h))))
                      (mult (abs (rdf_df f Hf (g x)))
                            (mult eps_g (abs h)))
                      (mult eps4 (abs h))).
      - apply (le_trans (abs (mult (rdf_df f Hf (g x))
                                   (req_minus (req_minus (g (plus x h)) (g x))
                                              (mult (rdf_df g Hg x) h))))
                        (mult (abs (rdf_df f Hf (g x)))
                              (abs (req_minus (req_minus (g (plus x h)) (g x))
                                              (mult (rdf_df g Hg x) h))))
                        (mult (abs (rdf_df f Hf (g x))) (mult eps_g (abs h)))).
        + exact (req_rdf_abs_mult_le (rdf_df f Hf (g x))
                    (req_minus (req_minus (g (plus x h)) (g x))
                               (mult (rdf_df g Hg x) h))).
        + exact (req_le_mult_compat_r (abs (rdf_df f Hf (g x)))
                    (abs (req_minus (req_minus (g (plus x h)) (g x))
                                    (mult (rdf_df g Hg x) h)))
                    (mult eps_g (abs h))
                    (abs_nonneg_plain (rdf_df f Hf (g x)))
                    (le_id_l (abs (req_minus (req_minus (g (plus x h)) (g x))
                                             (mult (rdf_df g Hg x) h)))
                             (abs (req_minus (g (plus x h))
                                             (plus (g x) (mult (rdf_df g Hg x) h))))
                             (mult eps_g (abs h))
                             (req_abs_compat (req_minus (req_minus (g (plus x h)) (g x))
                                                        (mult (rdf_df g Hg x) h))
                                             (req_minus (g (plus x h))
                                                        (plus (g x)
                                                              (mult (rdf_df g Hg x) h)))
                                             (req_sym (req_minus (g (plus x h))
                                                                 (plus (g x)
                                                                       (mult (rdf_df g Hg x) h)))
                                                      (req_minus (req_minus (g (plus x h)) (g x))
                                                                 (mult (rdf_df g Hg x) h))
                                                      (req_minus_plus_r (g (plus x h)) (g x)
                                                                        (mult (rdf_df g Hg x) h))))
                             (Hg2 h Hh_dgd))).
      - apply (le_trans (mult (abs (rdf_df f Hf (g x))) (mult eps_g (abs h)))
                        (mult M (mult eps_g (abs h)))
                        (mult eps4 (abs h))).
        + exact (le_mult_compat_weak (abs (rdf_df f Hf (g x))) M (mult eps_g (abs h))
                   (req_rdf_zero_le_mult_abs abs_nonneg_plain eps_g h Heps_g)
                    (req_abs_le_abs_plus_one (rdf_df f Hf (g x)))).
        + assert (HreqM : le (mult M eps_g) eps4).
          { exact (le_trans (mult M eps_g)
                            (mult M (mult (inv_pos M HM) eps4)) eps4
                            (req_le_mult_compat_r M eps_g (mult (inv_pos M HM) eps4)
                             (lt_le_iff zero M (inl HM))
                             (min_le_r_plain one (mult (inv_pos M HM) eps4)))
                            (le_id_l (mult M (mult (inv_pos M HM) eps4)) eps4 eps4
                             (req_trans (mult M (mult (inv_pos M HM) eps4))
                                        (mult (mult M (inv_pos M HM)) eps4) eps4
                                        (mult_assoc M (inv_pos M HM) eps4)
                                        (req_trans (mult (mult M (inv_pos M HM)) eps4)
                                                   (mult one eps4) eps4
                                                   (req_mult_compat (mult M (inv_pos M HM)) one
                                                                    eps4 eps4
                                                                    (inv_pos_correct M HM)
                                                                    (req_refl eps4))
                                                   (req_trans (mult one eps4) (mult eps4 one) eps4
                                                              (mult_comm one eps4)
                                                              (mult_one eps4))))
                             (le_refl eps4))). }
          exact (le_trans (mult M (mult eps_g (abs h)))
                          (mult (mult M eps_g) (abs h)) (mult eps4 (abs h))
                          (le_id_l (mult M (mult eps_g (abs h)))
                                   (mult (mult M eps_g) (abs h))
                                   (mult (mult M eps_g) (abs h))
                                   (mult_assoc M eps_g (abs h))
                                   (le_refl (mult (mult M eps_g) (abs h))))
                          (le_mult_compat_weak (mult M eps_g) eps4 (abs h)
                           (abs_nonneg_plain h) HreqM)).
          }
    apply (le_id_l (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (rdf_df f Hf (g x)) (rdf_df g Hg x)) h)))) (abs (plus (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (mult eps (abs h))).
    + exact (req_abs_compat (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (rdf_df f Hf (g x)) (rdf_df g Hg x)) h))) (plus (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h)))) (req_rdf_compose_diff_decomp (f (g (plus x h))) (f (g x)) (rdf_df f Hf (g x)) (rdf_df g Hg x) (g (plus x h)) (g x) h)).
+ exact (le_trans (abs (plus (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (plus (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x)))))) (abs (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (mult eps (abs h)) (req_rdf_abs_triangle (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h)))) (le_trans (plus (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x)))))) (abs (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps (abs h)) (le_plus_compat (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x)))))) (mult eps4 (abs h)) (abs (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h)))) (mult eps4 (abs h)) HT1 HT2) (le_trans (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps (abs h)) (mult eps (abs h)) (req_rdf_quarter_pair_le_final eps (abs h) Heps (abs_nonneg_plain h)) (le_refl (mult eps (abs h)))))).
Qed.

(* ---- helper: [(a + b) - c == a + (b - c)] (the mse/compose             *)
(* decomposition engine) ------------------------ *)

Lemma req_rdf_minus_plus_zero_r : forall a b c : R,
  req (req_minus (plus a b) c) (plus (req_minus a c) b).
Proof.
  intros a b c.
  unfold req_minus.
  apply (req_trans (plus (plus a b) (opp c)) (plus a (plus b (opp c)))
                   (plus (plus a (opp c)) b)).
  - exact (req_sym (plus a (plus b (opp c))) (plus (plus a b) (opp c))
                   (plus_assoc a b (opp c))).
  - apply (req_trans (plus a (plus b (opp c))) (plus a (plus (opp c) b))
                     (plus (plus a (opp c)) b)).
    + exact (req_plus_compat a a (plus b (opp c)) (plus (opp c) b)
                             (req_refl a) (plus_comm b (opp c))).
    + exact (plus_assoc a (opp c) b).
Qed.

(* ---- helper: [(x+h-t)^2 - ((x-t)^2 + 2*(x-t)*h) == h^2] (the baseline   *)
(* [square_diff_expand] *)


Lemma req_rdf_square_diff_expand : forall x target h : R,
  req (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
            (plus (mult (req_minus x target) (req_minus x target))
                  (mult (mult (plus one one) (req_minus x target)) h)))
       (mult h h).
Proof.
  intros x target h.
  assert (Hv : req (req_minus (plus x h) target) (plus (req_minus x target) h)).
  { exact (req_rdf_minus_plus_zero_r x h target). }
  assert (Hpair : req (plus (mult (req_minus x target) h) (mult h (req_minus x target)))
                      (mult (mult (plus one one) (req_minus x target)) h)).
  { apply (req_trans (plus (mult (req_minus x target) h) (mult h (req_minus x target)))
                     (mult (plus (req_minus x target) (req_minus x target)) h)
                     (mult (mult (plus one one) (req_minus x target)) h)).
    - exact (req_trans (plus (mult (req_minus x target) h) (mult h (req_minus x target)))
                       (plus (mult (req_minus x target) h) (mult (req_minus x target) h))
                       (mult (plus (req_minus x target) (req_minus x target)) h)
                       (req_plus_compat (mult (req_minus x target) h)
                                        (mult (req_minus x target) h)
                                        (mult h (req_minus x target))
                                        (mult (req_minus x target) h)
                                        (req_refl (mult (req_minus x target) h))
                                        (mult_comm h (req_minus x target)))
                       (req_sym (mult (plus (req_minus x target) (req_minus x target)) h)
                                (plus (mult (req_minus x target) h) (mult (req_minus x target) h))
                                (req_mult_plus_distr_r (req_minus x target) (req_minus x target) h))).
    - exact (req_mult_compat (plus (req_minus x target) (req_minus x target))
                             (mult (plus one one) (req_minus x target)) h h
                             (req_sym (mult (plus one one) (req_minus x target))
                                      (plus (req_minus x target) (req_minus x target))
                                      (req_two_mult (req_minus x target)))
                             (req_refl h)).
  }

  assert (HR : req (plus (plus (mult (req_minus x target) (req_minus x target))
                              (mult (req_minus x target) h))
                         (plus (mult h (req_minus x target)) (mult h h)))
                   (plus (plus (mult (req_minus x target) (req_minus x target))
                               (mult (mult (plus one one) (req_minus x target)) h))
                         (mult h h))).
{ exact (req_trans (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (req_sym (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus_assoc (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (req_trans (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h))) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h)) (req_refl (mult (req_minus x target) (req_minus x target))) (plus_assoc (mult (req_minus x target) h) (mult h (req_minus x target)) (mult h h))) (req_trans (plus (mult (req_minus x target) (req_minus x target)) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h)) (req_refl (mult (req_minus x target) (req_minus x target))) (req_plus_compat (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult (mult (plus one one) (req_minus x target)) h) (mult h h) (mult h h) Hpair (req_refl (mult h h)))) (plus_assoc (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h))))). }
  apply (req_trans (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                              (plus (mult (req_minus x target) (req_minus x target))
                                    (mult (mult (plus one one) (req_minus x target)) h)))
                   (req_minus (plus (plus (mult (req_minus x target) (req_minus x target))
                                          (mult (req_minus x target) h))
                                    (plus (mult h (req_minus x target)) (mult h h)))
                              (plus (mult (req_minus x target) (req_minus x target))
                                    (mult (mult (plus one one) (req_minus x target)) h)))
                   (mult h h)).
  - exact (req_rdf_minus_compat_l (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (req_trans (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (mult (plus (req_minus x target) h) (plus (req_minus x target) h)) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (req_mult_compat (req_minus (plus x h) target) (plus (req_minus x target) h) (req_minus (plus x h) target) (plus (req_minus x target) h) Hv Hv) (req_trans (mult (plus (req_minus x target) h) (plus (req_minus x target) h)) (plus (mult (req_minus x target) (plus (req_minus x target) h)) (mult h (plus (req_minus x target) h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (req_mult_plus_distr_r (req_minus x target) h (plus (req_minus x target) h)) (req_plus_compat (mult (req_minus x target) (plus (req_minus x target) h)) (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (mult h (plus (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h)) (req_trans (mult (req_minus x target) (plus (req_minus x target) h)) (mult (plus (req_minus x target) h) (req_minus x target)) (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (req_mult_comm_rewrite (req_minus x target) (plus (req_minus x target) h)) (req_trans (mult (plus (req_minus x target) h) (req_minus x target)) (plus (mult (req_minus x target) (req_minus x target)) (mult h (req_minus x target))) (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (req_mult_plus_distr_r (req_minus x target) h (req_minus x target)) (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (mult h (req_minus x target)) (mult (req_minus x target) h) (req_mult_comm_rewrite (req_minus x target) (req_minus x target)) (req_mult_comm_rewrite h (req_minus x target))))) (req_trans (mult h (plus (req_minus x target) h)) (mult (plus (req_minus x target) h) h) (plus (mult h (req_minus x target)) (mult h h)) (req_mult_comm_rewrite h (plus (req_minus x target) h)) (req_trans (mult (plus (req_minus x target) h) h) (plus (mult (req_minus x target) h) (mult h h)) (plus (mult h (req_minus x target)) (mult h h)) (req_mult_plus_distr_r (req_minus x target) h h) (req_plus_compat (mult (req_minus x target) h) (mult h (req_minus x target)) (mult h h) (mult h h) (req_mult_comm_rewrite (req_minus x target) h) (req_mult_comm_rewrite h h)))))))).
  - exact (req_trans (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (mult h h) (req_sym (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (req_rdf_minus_compat_l (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (req_sym (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) HR))) (req_minus_plus_cancel_r (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h))).
Qed.

(* ---- item 9: cross_entropy_softmax_diff ->                             *)
(* [req_cross_entropy_softmax_diff]                                        *)
(*   (consumes the [log_inv_exp_neg_slot]; the error folds to the identity *)
(*   map and vanishes — the baseline Hfold shape)  *)

Theorem req_cross_entropy_softmax_diff :
  reqRDF (fun logit => log_inv (exp_neg logit) (exp_neg_pos logit)).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Hz1 : req (mult one h) h).
    { exact (req_trans (mult one h) (mult h one) h (mult_comm one h) (mult_one h)). }
    assert (Herr : req (req_minus (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                                  (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h)))
                       zero).
    { apply (req_minus_self_zero (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                                 (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h))).
      apply (req_trans (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                       (plus x h)
                       (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h))).
      - exact (log_inv_exp_neg_slot (plus x h)).
      - exact (req_plus_compat x (log_inv (exp_neg x) (exp_neg_pos x)) h (mult one h)
                               (req_sym (log_inv (exp_neg x) (exp_neg_pos x)) x
                                        (log_inv_exp_neg_slot x))
                               (req_sym (mult one h) h Hz1)). }
    exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                                          (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h)))
                               eps h Heps Herr).
Qed.

(* ---- item 10: mse_diff -> [req_mse_diff] -------------------------------- *)
(*   (carried by the helper [req_rdf_square_diff_expand]; delta =          *)
(*   [min one eps] with the [min_le_*_plain] slot pair;                    *)
(*   [|h^2| = |h|^2 <= eps*|h|] via [le_mult_compat_weak])  *)

Theorem req_mse_diff : forall target : R,
  reqRDF (fun pred => mult (req_minus pred target) (req_minus pred target)).
Proof.
  intro target.
  exists (fun pred => mult (plus one one) (req_minus pred target)).
  intros x eps Heps.
  exists (min one eps).
  split.
  - exact (min_pos one eps one_pos Heps).
  - intros h Hh.
    assert (Hexp : req (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                  (plus (mult (req_minus x target) (req_minus x target))
                                        (mult (mult (plus one one) (req_minus x target)) h)))
                       (mult h h))
      by exact (req_rdf_square_diff_expand x target h).
    apply (le_trans (abs (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                    (plus (mult (req_minus x target) (req_minus x target))
                                          (mult (mult (plus one one) (req_minus x target)) h))))
                    (mult (abs h) (abs h))
                    (mult eps (abs h))).
    + apply (le_id_l (abs (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                     (plus (mult (req_minus x target) (req_minus x target))
                                           (mult (mult (plus one one) (req_minus x target)) h))))
                     (abs (mult h h))
                     (mult (abs h) (abs h))).
      * exact (req_abs_compat (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                         (plus (mult (req_minus x target) (req_minus x target))
                                               (mult (mult (plus one one) (req_minus x target)) h)))
                              (mult h h) Hexp).
      * exact (req_rdf_abs_mult_le h h).
    + apply (le_mult_compat_weak (abs h) eps (abs h)).
      * exact (abs_nonneg_plain h).
      * exact (lt_le_iff (abs h) eps
                   (inl (lt_le_trans (abs h) (min one eps) eps Hh (min_le_r_plain one eps)))).
Qed.

(* ---- item: differentiable_affine -> [req_rdf_affine].  [f(x) = a*x+b],  *)
(*   [df = a], the error is identically zero: reshape by                  *)
(*   [req_mult_plus_distr_r] (right distributivity moved left through      *)
(*   [mult_comm] in three hops), reassociate the plus in three steps and   *)
(*   close by [req_minus_self_zero]; the budget goes through the uniform   *)
(*   zero-error channel [req_rdf_abs_zero_le] on the [abs_nonneg_plain]    *)
(*   slot (the [req_rdf_const] shape). *)

Theorem req_rdf_affine : forall a b : R, reqRDF (fun x => plus (mult a x) b).
Proof.
  intros a b.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    apply (req_rdf_abs_zero_le abs_nonneg_plain
             (req_minus (plus (mult a (plus x h)) b)
                        (plus (plus (mult a x) b) (mult a h))) eps h Heps).
    apply (req_minus_self_zero (plus (mult a (plus x h)) b)
                               (plus (plus (mult a x) b) (mult a h))).
    apply (req_trans (plus (mult a (plus x h)) b)
                     (plus (plus (mult a x) (mult a h)) b)
                     (plus (plus (mult a x) b) (mult a h))).
    + exact (req_plus_compat (mult a (plus x h))
                             (plus (mult a x) (mult a h))
                             b b
                             (req_trans (mult a (plus x h))
                                        (plus (mult x a) (mult h a))
                                        (plus (mult a x) (mult a h))
                                        (req_trans (mult a (plus x h))
                                                   (mult (plus x h) a)
                                                   (plus (mult x a) (mult h a))
                                                   (mult_comm a (plus x h))
                                                   (req_mult_plus_distr_r x h a))
                                        (req_plus_compat (mult x a) (mult a x)
                                                         (mult h a) (mult a h)
                                                         (mult_comm x a)
                                                         (mult_comm h a)))
                             (req_refl b)).
    + exact (req_trans (plus (plus (mult a x) (mult a h)) b)
                       (plus (mult a x) (plus (mult a h) b))
                       (plus (plus (mult a x) b) (mult a h))
                       (req_sym (plus (mult a x) (plus (mult a h) b))
                                (plus (plus (mult a x) (mult a h)) b)
                                (plus_assoc (mult a x) (mult a h) b))
                       (req_trans (plus (mult a x) (plus (mult a h) b))
                                  (plus (mult a x) (plus b (mult a h)))
                                  (plus (plus (mult a x) b) (mult a h))
                                  (req_plus_compat (mult a x) (mult a x)
                                                   (plus (mult a h) b)
                                                   (plus b (mult a h))
                                                   (req_refl (mult a x))
                                                   (plus_comm (mult a h) b))
                                  (plus_assoc (mult a x) b (mult a h)))).
Qed.

(* ---- item 11: entropy_differentiable -> [req_entropy_differentiable] ----- *)
(*   (the domain premise slot [rdf_log_diff] = "the log chain closes for   *)
(*   differentiable functions with positive total", the req-domained       *)
(*   counterpart of the baseline's universal [log_differentiable] slot;    *)
(*   the [Omega_B_wd] honesty slot is the req compose function             *)
(*   compatibility premise — the baseline gets it from funext for free,    *)
(*   the req interface has no such transport, so it stays an explicit      *)
(*   slot)  *)

Section ReqEntropyDiff.

(* R/RIS/RNN/RDP are inherited from the outer [ReqRDFScalar] section (no  *)
(* redeclaration in the nested section). *)

Variable Omega_A : R -> R.
Variable Omega_B : R -> R.
Variable dOmega_A : reqRDF Omega_A.
Variable dOmega_B : reqRDF Omega_B.
Variable Omega_A_pos : forall E_A : R, lt zero (Omega_A E_A).
Variable Omega_B_pos : forall E_B : R, lt zero (Omega_B E_B).
Variable Omega_B_wd : forall u v : R, req u v -> req (Omega_B u) (Omega_B v).
Variable E_total : R.
Variable k_B : R.

Definition req_rdf_E_B_ent (E_A : R) : R := req_minus E_total E_A.
Definition req_rdf_Omega_total_ent (E_A : R) : R := mult (Omega_A E_A) (Omega_B (req_rdf_E_B_ent E_A)).
Definition Omega_total_pos_ent (E_A : R) : lt zero (req_rdf_Omega_total_ent E_A).
Proof.
  exact (mult_positive (Omega_A E_A) (Omega_B (req_rdf_E_B_ent E_A))
                       (Omega_A_pos E_A) (Omega_B_pos (req_rdf_E_B_ent E_A))).
Defined.
Definition req_rdf_entropy_ent (E_A : R) : R :=
  mult k_B (log (req_rdf_Omega_total_ent E_A) (Omega_total_pos_ent E_A)).

Variable rdf_log_diff : forall (g : R -> R) (Hg : forall y : R, lt zero (g y)),
  reqRDF (fun z => log (g z) (Hg z)).

Theorem req_entropy_differentiable : reqRDF req_rdf_entropy_ent.
Proof.
  assert (HEB_d : reqRDF req_rdf_E_B_ent).
  { exact (req_rdf_minus (fun _ => E_total) (fun x => x)
             (req_rdf_const E_total) req_rdf_id). }
  assert (HcompB : reqRDF (fun E_A => Omega_B (req_rdf_E_B_ent E_A))).
  { exact (req_rdf_compose Omega_B req_rdf_E_B_ent dOmega_B HEB_d Omega_B_wd). }
  assert (HOmega_d : reqRDF req_rdf_Omega_total_ent).
  { exact (req_rdf_mult Omega_A (fun E_A => Omega_B (req_rdf_E_B_ent E_A)) dOmega_A HcompB). }
  assert (Hlog_d : reqRDF (fun z => log (req_rdf_Omega_total_ent z) (Omega_total_pos_ent z))).
  { exact (rdf_log_diff req_rdf_Omega_total_ent Omega_total_pos_ent). }
  exact (req_rdf_mult (fun _ => k_B)
                      (fun z => log (req_rdf_Omega_total_ent z) (Omega_total_pos_ent z))
                      (req_rdf_const k_B) Hlog_d).
Qed.

End ReqEntropyDiff.

(* ===================================================================== *)
(* Part 3: the MV bridge — definitional transcriptions of the state and   *)
(* Hilbert space records plus the [reqRDFMV]/[reqRDFMVVec] record bridges. *)
(* Honest-difference notes for the MV region:                             *)
(* 5. Law-field layering: the R-valued laws ([metric_sym]/[sminus],       *)
(*    [inner_sym]/[splus_l]/[smult_l], [snorm_smult]/[triangle],           *)
(*    [proj_orthogonal]) take the req form; the carrier laws (the         *)
(*    [splus]/[smult] families, and the conclusions of [metric_zero],      *)
(*    [clim_unique], [inner_definite]) keep the baseline Leibniz form —   *)
(*    the req carrier form would need carrier-setoid fields, and all      *)
(*    sixteen use sites sit at the R-value layer, so zero uses means zero *)
(*    assumptions.  The req form is weaker; this is the safe direction.   *)
(* 6. The [rdf_inner_zero] slot ([<szero, h> == zero]): the req interface *)
(*    has no [id_cong], so substituting [szero] into an [inner] argument  *)
(*    position has no transport (a standing same-family restriction); the *)
(*    baseline [inner_szero_l] is a provable theorem, but its req         *)
(*    counterpart is not replicable at the interface level, so it stays   *)
(*    an explicit assumption. *)
(* ===================================================================== *)

Record reqStateSpace := {
  rs_carrier : Set;
  rs_zero : rs_carrier;
  rs_plus : rs_carrier -> rs_carrier -> rs_carrier;
  rs_mult : R -> rs_carrier -> rs_carrier;
  rs_opp : rs_carrier -> rs_carrier;
  rs_plus_assoc : forall a b c : rs_carrier,
    Id (rs_plus a (rs_plus b c)) (rs_plus (rs_plus a b) c);
  rs_plus_comm : forall a b : rs_carrier, Id (rs_plus a b) (rs_plus b a);
  rs_plus_zero : forall a : rs_carrier, Id (rs_plus a rs_zero) a;
  rs_plus_opp : forall a : rs_carrier, Id (rs_plus a (rs_opp a)) rs_zero;
  rs_mult_one : forall a : rs_carrier, Id (rs_mult one a) a;
  rs_mult_assoc : forall (a b : R) (x : rs_carrier),
    Id (rs_mult a (rs_mult b x)) (rs_mult (mult a b) x);
  rs_mult_distrib_r : forall (a : R) (x y : rs_carrier),
    Id (rs_mult a (rs_plus x y)) (rs_plus (rs_mult a x) (rs_mult a y));
  rs_mult_distrib_l : forall (a b : R) (x : rs_carrier),
    Id (rs_mult (plus a b) x) (rs_plus (rs_mult a x) (rs_mult b x));
  rs_metric : rs_carrier -> rs_carrier -> R;
  rs_metric_sym : forall a b : rs_carrier, req (rs_metric a b) (rs_metric b a);
  rs_metric_pos : forall a b : rs_carrier, le zero (rs_metric a b);
  rs_metric_zero : forall a b : rs_carrier,
    req (rs_metric a b) zero -> Id a b;
  rs_metric_triangle : forall a b c : rs_carrier,
    le (rs_metric a c) (plus (rs_metric a b) (rs_metric b c));
  rs_clim : (nat -> rs_carrier) -> rs_carrier -> Set;
  rs_clim_unique : forall (u : nat -> rs_carrier) (l1 l2 : rs_carrier),
    rs_clim u l1 -> rs_clim u l2 -> Id l1 l2;
  rs_cauchy_complete : forall (u : nat -> rs_carrier),
    (forall eps : R, lt zero eps ->
      sigT (fun N : nat => forall m n : nat,
        NatLe N m -> NatLe N n -> lt (rs_metric (u m) (u n)) eps)) ->
    sigT (fun l : rs_carrier => rs_clim u l)
}.

Record reqHilbertSpace
                       (SS : reqStateSpace) := {
  rh_inner : rs_carrier SS -> rs_carrier SS -> R;
  rh_inner_sym : forall x y : rs_carrier SS, req (rh_inner x y) (rh_inner y x);
  rh_inner_pos : forall x : rs_carrier SS, le zero (rh_inner x x);
  rh_inner_definite : forall x : rs_carrier SS,
    Id (rh_inner x x) zero -> Id x (rs_zero SS);
  rh_inner_splus_l : forall x y z : rs_carrier SS,
    req (rh_inner (rs_plus SS x y) z) (plus (rh_inner x z) (rh_inner y z));
  rh_inner_smult_l : forall (a : R) (x y : rs_carrier SS),
    req (rh_inner (rs_mult SS a x) y) (mult a (rh_inner x y));
  rh_proj : rs_carrier SS -> rs_carrier SS -> rs_carrier SS;
  rh_proj_linear : forall u v w : rs_carrier SS,
    Id (rh_proj u (rs_plus SS v w))
       (rs_plus SS (rh_proj u v) (rh_proj u w));
  rh_proj_orthogonal : forall u v : rs_carrier SS,
    req (rh_inner (rs_plus SS v (rs_opp SS (rh_proj u v))) u) zero
}.

Definition req_sminus
                       (SS : reqStateSpace)
                       (u v : rs_carrier SS) : rs_carrier SS :=
  rs_plus SS u (rs_opp SS v).

Record reqStateSpaceExtended
                             (SS : reqStateSpace) := {
  re_base :> reqStateSpace;
  re_mult_zero : forall x : rs_carrier SS,
    Id (rs_mult SS zero x) (rs_zero SS);
  re_mult_opp : forall (a : R) (x : rs_carrier SS),
    Id (rs_mult SS (opp a) x) (rs_opp SS (rs_mult SS a x));
  re_snorm : rs_carrier SS -> R;
  re_snorm_pos : forall x : rs_carrier SS, le zero (re_snorm x);
  re_snorm_zero : forall x : rs_carrier SS,
    req (re_snorm x) zero -> Id x (rs_zero SS);
  re_snorm_smult : forall (a : R) (x : rs_carrier SS),
    req (re_snorm (rs_mult SS a x)) (mult (abs a) (re_snorm x));
  re_snorm_triangle : forall x y : rs_carrier SS,
    le (re_snorm (rs_plus SS x y)) (plus (re_snorm x) (re_snorm y));
  re_metric_sminus : forall u v : rs_carrier SS,
    req (rs_metric SS u v) (re_snorm (req_sminus SS u v))
}.

Record reqRDFMV
                (SS : reqStateSpace) (HS : reqHilbertSpace SS)
                (f : rs_carrier SS -> R) : Set := {
  rdfmv : rs_carrier SS -> rs_carrier SS;
  rdfmv_correct : forall (x : rs_carrier SS) (eps : R), lt zero eps ->
    sigT (fun delta : R => And (lt zero delta)
      (forall h : rs_carrier SS,
        lt (rs_metric SS h (rs_zero SS)) delta ->
        le (abs (req_minus (f (rs_plus SS x h))
                           (plus (f x) (rh_inner SS HS (rdfmv x) h))))
           (mult eps (rs_metric SS h (rs_zero SS)))))
}.

Record reqRDFMVVec
                   (SS : reqStateSpace)
                   (f : rs_carrier SS -> rs_carrier SS) : Set := {
  rdfvec : rs_carrier SS -> rs_carrier SS -> rs_carrier SS;
  rdfvec_correct : forall (x : rs_carrier SS) (eps : R), lt zero eps ->
    sigT (fun delta : R => And (lt zero delta)
      (forall h : rs_carrier SS,
        lt (rs_metric SS h (rs_zero SS)) delta ->
        le (rs_metric SS (req_sminus SS (f (rs_plus SS x h)) (f x))
                               (rdfvec x h))
           (mult eps (rs_metric SS h (rs_zero SS)))))
}.

(* ===================================================================== *)
(* Part 4: the MV-region statements (items 12-16). *)
(* ===================================================================== *)

Section ReqRDFMV.

(* R/RIS/RNN/RDP are inherited from the outer [Section ReqRDFScalar]; not *)
(* redeclared here. *)
Context (SS : reqStateSpace).
Context (HSE : reqStateSpaceExtended SS).
Context (HS : reqHilbertSpace SS).

Let Sc : Set := rs_carrier SS.
Let S0 : Sc := rs_zero SS.
Let spl : Sc -> Sc -> Sc := rs_plus SS.
Let mtr : Sc -> Sc -> R := rs_metric SS.
Let inn : Sc -> Sc -> R := rh_inner SS HS.

(* helper: req counterpart of [inner_splus_r] — direct from the interface *)
(* field. *)
Lemma req_inner_splus_r : forall x y z : Sc,
  req (inn x (spl y z)) (plus (inn x y) (inn x z)).
Proof.
  intros x y z.
  apply (req_trans (inn x (spl y z)) (inn (spl y z) x) (plus (inn x y) (inn x z))).
  - exact (rh_inner_sym SS HS x (spl y z)).
  - apply (req_trans (inn (spl y z) x) (plus (inn y x) (inn z x))
                     (plus (inn x y) (inn x z))).
    + exact (rh_inner_splus_l SS HS y z x).
    + exact (req_plus_compat (inn y x) (inn x y) (inn z x) (inn x z)
                             (rh_inner_sym SS HS y x)
                             (rh_inner_sym SS HS z x)).
Qed.

(* ---- item 12: differentiable_mv_const -> [req_rdf_mv_const] ------------- *)
(*   (consumes the [rdf_inner_zero] slot)  *)

Variable rdf_inner_zero : forall h : Sc, req (inn S0 h) zero.

Theorem req_rdf_mv_const : forall c : R, reqRDFMV SS HS (fun _ => c).
Proof.
  intro c.
  exists (fun _ => S0).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Herr : req (req_minus c (plus c (inn S0 h))) zero).
    { apply (req_minus_self_zero c (plus c (inn S0 h))).
      apply (req_trans c (plus c zero) (plus c (inn S0 h))).
      - exact (req_sym (plus c zero) c (plus_zero c)).
      - exact (req_plus_compat c c zero (inn S0 h) (req_refl c)
                 (req_sym (inn S0 h) zero (rdf_inner_zero h))). }
    assert (Hzm : le zero (mult eps (mtr h S0))).
    { apply (le_id_l zero (mult zero (mtr h S0)) (mult eps (mtr h S0))).
      - exact (req_sym (mult zero (mtr h S0)) zero
                 (req_trans (mult zero (mtr h S0)) (mult (mtr h S0) zero) zero
                            (mult_comm zero (mtr h S0)) (mult_zero (mtr h S0)))).
      - exact (le_mult_compat_weak zero eps (mtr h S0)
                   (rs_metric_pos SS h S0)
                   (lt_le_iff zero eps (inl Heps))). }
    exact (le_trans (abs (req_minus c (plus c (inn S0 h)))) (abs zero)
                    (mult eps (mtr h S0))
                    (le_id_l (abs (req_minus c (plus c (inn S0 h)))) (abs zero)
                             (abs zero)
                             (req_abs_compat (req_minus c (plus c (inn S0 h)))
                                             zero Herr)
                             (le_refl (abs zero)))
                    (le_id_l (abs zero) zero (mult eps (mtr h S0)) abs_zero Hzm)).
Qed.

(* ---- item 13: differentiable_mv_linear -> [req_rdf_mv_linear] ----------- *)
(*   (the attention logits are differentiable: attention_score(s) =        *)
(*   <s, key> with df = key; consumes the [req_inner_splus_r] helper)  *)

Theorem req_rdf_mv_linear : forall a : Sc, reqRDFMV SS HS (fun x => inn a x).
Proof.
  intro a.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Herr : req (req_minus (inn a (spl x h)) (plus (inn a x) (inn a h))) zero).
    { apply (req_minus_self_zero (inn a (spl x h)) (plus (inn a x) (inn a h))).
      exact (req_inner_splus_r a x h). }
    assert (Hzm : le zero (mult eps (mtr h S0))).
    { apply (le_id_l zero (mult zero (mtr h S0)) (mult eps (mtr h S0))).
      - exact (req_sym (mult zero (mtr h S0)) zero
                 (req_trans (mult zero (mtr h S0)) (mult (mtr h S0) zero) zero
                            (mult_comm zero (mtr h S0)) (mult_zero (mtr h S0)))).
      - exact (le_mult_compat_weak zero eps (mtr h S0)
                   (rs_metric_pos SS h S0)
                   (lt_le_iff zero eps (inl Heps))). }
    exact (le_trans (abs (req_minus (inn a (spl x h)) (plus (inn a x) (inn a h))))
                    (abs zero) (mult eps (mtr h S0))
                    (le_id_l (abs (req_minus (inn a (spl x h))
                                             (plus (inn a x) (inn a h))))
                             (abs zero) (abs zero)
                             (req_abs_compat (req_minus (inn a (spl x h))
                                                        (plus (inn a x) (inn a h)))
                                             zero Herr)
                             (le_refl (abs zero)))
                    (le_id_l (abs zero) zero (mult eps (mtr h S0)) abs_zero Hzm)).
Qed.

(* ---- item 14: differentiable_mv_plus -> [req_rdf_mv_plus] --------------- *)
(*   (consumes [req_inner_splus_r] plus the [req_rdf_plus]-shaped eps/2    *)
(*   arithmetic; the min plain-le slot pair of [ReqDiffPlain] mirrors the  *)
(*   baseline [min_le_l]/[min_le_r]; the error decomposes in three hops:   *)
(*   inner linearity, the plus middle swap, then [req_minus_plus_distr]    *)
(*   splits the two branches)  *)

Theorem req_rdf_mv_plus : forall f g : Sc -> R,
  reqRDFMV SS HS f -> reqRDFMV SS HS g ->
  reqRDFMV SS HS (fun x => plus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  destruct Hf as [df Hdf]. destruct Hg as [dg Hdg].
  exists (fun x => spl (df x) (dg x)).
  intros x eps Heps.
  destruct (Hdf x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dfd [Hd1 Hd2]].
  destruct (Hdg x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dgd [Hg1 Hg2]].
  exists (min dfd dgd).
  split.
  - exact (min_pos dfd dgd Hd1 Hg1).
  - intros h Hh.
    assert (Hh1 : lt (mtr h S0) dfd).
    { exact (lt_le_trans (mtr h S0) (min dfd dgd) dfd Hh
                         (min_le_l_plain dfd dgd)). }
    assert (Hh2 : lt (mtr h S0) dgd).
    { exact (lt_le_trans (mtr h S0) (min dfd dgd) dgd Hh
                         (min_le_r_plain dfd dgd)). }
    apply (le_id_l (abs (req_minus (plus (f (spl x h)) (g (spl x h)))
                                   (plus (plus (f x) (g x))
                                         (inn (spl (df x) (dg x)) h))))
                   (abs (plus (req_minus (f (spl x h))
                                          (plus (f x) (inn (df x) h)))
                              (req_minus (g (spl x h))
                                         (plus (g x) (inn (dg x) h)))))
                   (mult eps (mtr h S0))).
    + exact (req_abs_compat
               (req_minus (plus (f (spl x h)) (g (spl x h)))
                          (plus (plus (f x) (g x))
                                (inn (spl (df x) (dg x)) h)))
               (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                     (req_minus (g (spl x h)) (plus (g x) (inn (dg x) h))))
               (req_trans
                  (req_minus (plus (f (spl x h)) (g (spl x h)))
                             (plus (plus (f x) (g x))
                                   (inn (spl (df x) (dg x)) h)))
                  (req_minus (plus (f (spl x h)) (g (spl x h)))
                             (plus (plus (f x) (inn (df x) h))
                                   (plus (g x) (inn (dg x) h))))
                  (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                        (req_minus (g (spl x h))
                                   (plus (g x) (inn (dg x) h))))
                  (req_rdf_minus_compat_r (plus (f (spl x h)) (g (spl x h)))
                     (plus (plus (f x) (g x)) (inn (spl (df x) (dg x)) h))
                     (plus (plus (f x) (inn (df x) h))
                           (plus (g x) (inn (dg x) h)))
                     (req_trans (plus (plus (f x) (g x))
                                      (inn (spl (df x) (dg x)) h))
                                (plus (plus (f x) (g x))
                                      (plus (inn (df x) h) (inn (dg x) h)))
                                (plus (plus (f x) (inn (df x) h))
                                      (plus (g x) (inn (dg x) h)))
                                (req_plus_compat (plus (f x) (g x))
                                                 (plus (f x) (g x))
                                                 (inn (spl (df x) (dg x)) h)
                                                 (plus (inn (df x) h)
                                                       (inn (dg x) h))
                                                 (req_refl (plus (f x) (g x)))
                                                 (rh_inner_splus_l SS HS
                                                                   (df x) (dg x)
                                                                   h))
                                (req_plus_swap_mid (f x) (g x)
                                                   (inn (df x) h)
                                                   (inn (dg x) h))))
                  (req_minus_plus_distr (f (spl x h)) (g (spl x h))
                                        (plus (f x) (inn (df x) h))
                                        (plus (g x) (inn (dg x) h))))).
    + apply (le_trans _
               (plus (abs (req_minus (f (spl x h))
                                     (plus (f x) (inn (df x) h))))
                     (abs (req_minus (g (spl x h))
                                     (plus (g x) (inn (dg x) h)))))).
      * exact (req_rdf_abs_triangle
                 (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                 (req_minus (g (spl x h)) (plus (g x) (inn (dg x) h)))).
      * apply (le_trans _
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                             (mtr h S0))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                             (mtr h S0)))).
        -- exact (le_plus_compat
                   (abs (req_minus (f (spl x h))
                                   (plus (f x) (inn (df x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                         (mtr h S0))
                   (abs (req_minus (g (spl x h))
                                   (plus (g x) (inn (dg x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                         (mtr h S0))
                   (Hd2 h Hh1) (Hg2 h Hh2)).
        -- exact (req_rdf_half_pair_le eps (mtr h S0)).
Qed.

(* ---- item 15 helper A (pure R-layer algebra): req counterpart of        *)
(* [minus_minus_distr] -------------- *)

Lemma req_rdf_minus_minus_distr : forall A B C : R,
  req (req_minus (req_minus A B) C) (req_minus A (plus B C)).
Proof.
  intros A B C. unfold req_minus.
  exact (req_trans (plus (plus A (opp B)) (opp C))
                   (plus A (plus (opp B) (opp C)))
                   (plus A (opp (plus B C)))
                   (req_sym (plus A (plus (opp B) (opp C)))
                            (plus (plus A (opp B)) (opp C))
                            (plus_assoc A (opp B) (opp C)))
                   (req_plus_compat A A (plus (opp B) (opp C)) (opp (plus B C))
                      (req_refl A)
                      (req_sym (opp (plus B C)) (plus (opp B) (opp C))
                               (req_opp_plus B C)))).
Qed.

(* ---- item 15/16 helper B (pure R-layer algebra): the general error      *)
(* decomposition [A - (B + X) == (A - (B + Y)) + (Y - X)].                 *)
(*   Zero premise slots (after unfolding [req_minus] a pure                *)
(*   [plus]/[opp]/[req_opp_plus] chain).  ------------------ *)

Lemma req_rdf_mv_vec_decomp : forall A B X Y : R,
  req (req_minus A (plus B X)) (plus (req_minus A (plus B Y)) (req_minus Y X)).
Proof.
  intros A B X Y. unfold req_minus.
  assert (Hcancel : req (plus (opp (plus B Y)) Y) (opp B)).
  { exact (req_trans (plus (opp (plus B Y)) Y)
                     (plus (plus (opp B) (opp Y)) Y) (opp B)
                     (req_plus_compat (opp (plus B Y)) (plus (opp B) (opp Y))
                                      Y Y (req_opp_plus B Y) (req_refl Y))
                     (req_trans (plus (plus (opp B) (opp Y)) Y)
                                (plus (opp B) (plus (opp Y) Y)) (opp B)
                                (req_sym (plus (opp B) (plus (opp Y) Y))
                                         (plus (plus (opp B) (opp Y)) Y)
                                         (plus_assoc (opp B) (opp Y) Y))
                                (req_trans (plus (opp B) (plus (opp Y) Y))
                                           (plus (opp B) zero) (opp B)
                                           (req_plus_compat (opp B) (opp B)
                                              (plus (opp Y) Y) zero
                                              (req_refl (opp B))
                                              (req_plus_opp_l Y))
                                           (req_plus_zero_r (opp B))))). }
  assert (Hre : req (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                    (plus A (opp (plus B X)))).
  { apply (req_trans (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                     (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                     (plus A (opp (plus B X)))).
    - exact (req_trans (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                       (plus A (plus (opp (plus B Y)) (plus Y (opp X))))
                       (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                       (req_sym (plus A (plus (opp (plus B Y)) (plus Y (opp X))))
                                (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                                (plus_assoc A (opp (plus B Y)) (plus Y (opp X))))
                       (req_plus_compat A A
                          (plus (opp (plus B Y)) (plus Y (opp X)))
                          (plus (plus (opp (plus B Y)) Y) (opp X))
                          (req_refl A)
                          (plus_assoc (opp (plus B Y)) Y (opp X)))).
    - apply (req_trans (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                       (plus A (plus (opp B) (opp X)))
                       (plus A (opp (plus B X)))).
      + exact (req_plus_compat A A (plus (plus (opp (plus B Y)) Y) (opp X))
                                 (plus (opp B) (opp X)) (req_refl A)
                                 (req_plus_compat (plus (opp (plus B Y)) Y) (opp B)
                                    (opp X) (opp X) Hcancel (req_refl (opp X)))).
      + exact (req_plus_compat A A (plus (opp B) (opp X)) (opp (plus B X))
                                 (req_refl A)
                                 (req_sym (opp (plus B X)) (plus (opp B) (opp X))
                                          (req_opp_plus B X))). }
  exact (req_sym (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                 (plus A (opp (plus B X))) Hre).
Qed.

(* ---- item 15 helper C: the product-form error decomposition (req        *)
(* counterpart of the baseline mv_compose_diff_decomp) ---- *)

Lemma req_rdf_mv_compose_decomp : forall A B C U W : R,
  req (req_minus A (plus B (mult C W)))
      (plus (req_minus A (plus B (mult C U))) (mult C (req_minus U W))).
Proof.
  intros A B C U W.
  apply (req_trans (req_minus A (plus B (mult C W)))
                   (plus (req_minus A (plus B (mult C U)))
                         (req_minus (mult C U) (mult C W)))
                   (plus (req_minus A (plus B (mult C U)))
                         (mult C (req_minus U W)))).
  - exact (req_rdf_mv_vec_decomp A B (mult C W) (mult C U)).
  - exact (req_plus_compat (req_minus A (plus B (mult C U)))
                           (req_minus A (plus B (mult C U)))
                           (req_minus (mult C U) (mult C W))
                           (mult C (req_minus U W))
                           (req_refl (req_minus A (plus B (mult C U))))
                           (req_sym (mult C (req_minus U W))
                                    (req_minus (mult C U) (mult C W))
                                    (req_mult_minus_distr_l C U W))).
Qed.

(* ---- the inner-product Lipschitz slot (honest premise; the sigT shape   *)
(* of the baseline [inner_lipschitz]) ---- *)

Variable req_inner_lipschitz : forall a : Sc,
  sigT (fun N : R => And (le zero N) (forall h : Sc,
    le (abs (inn a h)) (mult N (mtr h S0)))).

(* ---- item 15: differentiable_mv_compose -> [req_rdf_mv_compose] ---------- *)
(*   (consumes the [req_inner_lipschitz] slot; the outer-g function        *)
(*   compatibility premise follows the [req_rdf_compose] precedent of      *)
(*   item 8; the budget eps4 = eps/4: T1 <= eps_g * |Dg| <= eps4 * s       *)
(*   ([req_rdf_inv_scale_le]); T2 <= |dg (f x)| * eps_f * s <= eps4 * s    *)
(*   ([inv_pos_correct] arithmetic); closed by                             *)
(*   [req_rdf_quarter_pair_le_final])  *)

Theorem req_rdf_mv_compose : forall (f : Sc -> R) (g : R -> R),
  reqRDFMV SS HS f -> reqRDF g ->
  (forall u v : R, req u v -> req (g u) (g v)) ->
  reqRDFMV SS HS (fun x => g (f x)).
Proof.
  intros f g Hf Hg Hgwd.
  destruct Hf as [df Hdf]. destruct Hg as [dg Hdg].
  exists (fun x => rs_mult SS (dg (f x)) (df x)).
  intros x eps Heps.
  destruct (req_inner_lipschitz (df x)) as [N [HN0 HN2]].
  pose (eps4 := mult (inv_pos (plus one one) req_two_pos)
                     (mult (inv_pos (plus one one) req_two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive.
    - apply inv_pos_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps]. }
  pose (L := plus N one).
  assert (HL : lt zero L) by (unfold L; exact (req_plus_le_lt_pos N one HN0 one_pos)).
  pose (M := plus (abs (dg (f x))) one).
  assert (HM : lt zero M) by (unfold M; exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (dg (f x)))).
  pose (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f).
  { unfold eps_f. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  pose (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g).
  { unfold eps_g. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  destruct (Hdf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hdg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    exact (min_pos dfd (min one (mult (inv_pos L HL) dgd)) Hdf1
             (min_pos one (mult (inv_pos L HL) dgd) one_pos Hltm)).
  - intros h Hh.
    pose (s := mtr h S0).
    pose (Dg := req_minus (f (spl x h)) (f x)).
    assert (Hh_dfd : lt s dfd).
    { exact (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd))) dfd Hh
             (min_le_l_plain dfd (min one (mult (inv_pos L HL) dgd)))). }
    assert (Hh_one : lt s one).
    { exact (lt_le_trans s (min one (mult (inv_pos L HL) dgd)) one
               (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd)))
                            (min one (mult (inv_pos L HL) dgd)) Hh
                            (min_le_r_plain dfd
                               (min one (mult (inv_pos L HL) dgd))))
               (min_le_l_plain one (mult (inv_pos L HL) dgd))). }
    assert (Hh_dgds : lt s (mult (inv_pos L HL) dgd)).
    { exact (lt_le_trans s (min one (mult (inv_pos L HL) dgd))
                         (mult (inv_pos L HL) dgd)
               (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd)))
                            (min one (mult (inv_pos L HL) dgd)) Hh
                            (min_le_r_plain dfd
                               (min one (mult (inv_pos L HL) dgd))))
               (min_le_r_plain one (mult (inv_pos L HL) dgd))). }
    assert (Hef : le eps_f one).
    { exact (min_le_l_plain one (mult (inv_pos M HM) eps4)). }
    assert (Hspos : le zero s) by exact (rs_metric_pos SS h S0).
    (* (a) [|Dg| <= L * s]: split + triangle + the eps_f/N branches + the   *)
    (* coefficient [(eps_f + N) <= L] *)
    assert (HDg : le (abs Dg) (mult L s)).
    { apply (le_id_l (abs Dg)
               (abs (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                          (inn (df x) h)))
               (mult L s)
               (req_abs_compat Dg
                  (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                        (inn (df x) h))
                  (req_minus_split (f (spl x h)) (f x) (inn (df x) h)))).
      apply (le_trans (abs (plus (req_minus (f (spl x h))
                                            (plus (f x) (inn (df x) h)))
                                 (inn (df x) h)))
                      (plus (abs (req_minus (f (spl x h))
                                            (plus (f x) (inn (df x) h))))
                            (abs (inn (df x) h)))
                      (mult L s)).
      - exact (req_rdf_abs_triangle (req_minus (f (spl x h))
                                               (plus (f x) (inn (df x) h)))
                                    (inn (df x) h)).
      - apply (le_trans (plus (abs (req_minus (f (spl x h))
                                              (plus (f x) (inn (df x) h))))
                              (abs (inn (df x) h)))
                        (plus (mult eps_f s) (mult N s)) (mult L s)).
        + exact (le_plus_compat (abs (req_minus (f (spl x h))
                                                (plus (f x) (inn (df x) h))))
                                (mult eps_f s)
                                (abs (inn (df x) h)) (mult N s)
                                (Hdf2 h Hh_dfd) (HN2 h)).
        + apply (le_trans (plus (mult eps_f s) (mult N s))
                          (mult (plus eps_f N) s) (mult L s)).
          * exact (le_id_l (plus (mult eps_f s) (mult N s))
                           (mult (plus eps_f N) s) (mult (plus eps_f N) s)
                           (req_sym (mult (plus eps_f N) s)
                                    (plus (mult eps_f s) (mult N s))
                                    (req_mult_plus_distr_r eps_f N s))
                           (le_refl (mult (plus eps_f N) s))).
          * exact (le_mult_compat_weak (plus eps_f N) L s Hspos
                       (le_trans (plus eps_f N) (plus one N) L
                                 (le_plus_compat eps_f one N N Hef
                                                 (le_refl N))
                                 (le_id_l (plus one N) L L (plus_comm one N)
                                          (le_refl L)))). }
    (* |Dg| < dgd（L·s < L·(inv L·dgd) ≡ dgd） *)
    assert (HDg_lt : lt (abs Dg) dgd).
    { apply (le_lt_trans (abs Dg) (mult L s) dgd).
      - exact HDg.
      - exact (lt_id_l (mult L s) (mult s L) dgd (mult_comm L s)
                 (lt_id_r (mult s L) (mult (mult (inv_pos L HL) dgd) L) dgd
                    (req_trans (mult (mult (inv_pos L HL) dgd) L)
                               (mult L (mult (inv_pos L HL) dgd)) dgd
                               (mult_comm (mult (inv_pos L HL) dgd) L)
                               (req_rdf_inv_cancel L dgd HL Hdg1))
                    (lt_mult_compat s (mult (inv_pos L HL) dgd) L HL Hh_dgds))). }
    (* T1: the outer error [<= eps_g * |Dg| <= eps4 * s] *)
    assert (HT1 : le (abs (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (mult (dg (f x)) Dg))))
                      (mult eps4 s)).
    { apply (le_trans (abs (req_minus (g (f (spl x h)))
                                      (plus (g (f x)) (mult (dg (f x)) Dg))))
                      (mult eps_g (abs Dg)) (mult eps4 s)).
      - apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                       (plus (g (f x)) (mult (dg (f x)) Dg))))
                       (abs (req_minus (g (plus (f x) Dg))
                                       (plus (g (f x)) (mult (dg (f x)) Dg))))
                       (mult eps_g (abs Dg))
                       (req_abs_compat
                          (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (mult (dg (f x)) Dg)))
                          (req_minus (g (plus (f x) Dg))
                                     (plus (g (f x)) (mult (dg (f x)) Dg)))
                          (req_rdf_minus_compat_l (g (f (spl x h)))
                             (g (plus (f x) Dg))
                             (plus (g (f x)) (mult (dg (f x)) Dg))
                             (Hgwd (f (spl x h)) (plus (f x) Dg)
                                (req_trans (f (spl x h)) (plus Dg (f x))
                                           (plus (f x) Dg)
                                           (req_rdf_minus_pair (f (spl x h)) (f x))
                                           (plus_comm Dg (f x))))))).
        exact (Hdg2 Dg HDg_lt).
      - apply (le_trans (mult eps_g (abs Dg)) (mult eps_g (mult L s))
                        (mult eps4 s)).
        + exact (req_le_mult_compat_r eps_g (abs Dg) (mult L s)
                     (lt_le_iff zero eps_g (inl Heps_g)) HDg).
        + apply (le_trans (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                          (mult eps4 s)).
          * exact (le_id_l (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                           (mult (mult eps_g L) s) (mult_assoc eps_g L s)
                           (le_refl (mult (mult eps_g L) s))).
          * apply (le_trans (mult (mult eps_g L) s)
                            (mult (mult (mult (inv_pos L HL) eps4) L) s)
                            (mult eps4 s)).
            -- exact (le_mult_compat_weak (mult eps_g L)
                          (mult (mult (inv_pos L HL) eps4) L) s Hspos
                          (le_trans (mult eps_g L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (le_mult_compat_weak eps_g
                                       (mult (inv_pos L HL) eps4) L
                                       (lt_le_iff zero L (inl HL))
                                       (min_le_r_plain one
                                          (mult (inv_pos L HL) eps4)))
                                    (le_refl (mult (mult (inv_pos L HL) eps4) L)))).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos L HL) eps4) L)
                          eps4 s Hspos (req_rdf_inv_scale_le L eps4 HL)). }
    (* T2：|dg(f x)|·|Dg−⟨df x,h⟩| ≤ eps4·s *)
    assert (HT2 : le (abs (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                      (mult eps4 s)).
    { apply (le_id_l (abs (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                     (mult (abs (dg (f x)))
                           (abs (req_minus Dg (inn (df x) h))))
                     (mult eps4 s)
                     (abs_mult (dg (f x)) (req_minus Dg (inn (df x) h)))).
      apply (le_trans (mult (abs (dg (f x)))
                            (abs (req_minus Dg (inn (df x) h))))
                      (mult (abs (dg (f x))) (mult eps_f s)) (mult eps4 s)).
      - exact (req_le_mult_compat_r (abs (dg (f x)))
                   (abs (req_minus Dg (inn (df x) h)))
                   (mult eps_f s)
                   (abs_nonneg_plain (dg (f x)))
                   (le_id_l (abs (req_minus Dg (inn (df x) h)))
                            (abs (req_minus (f (spl x h))
                                            (plus (f x) (inn (df x) h))))
                            (mult eps_f s)
                            (req_abs_compat (req_minus Dg (inn (df x) h))
                               (req_minus (f (spl x h))
                                          (plus (f x) (inn (df x) h)))
                               (req_rdf_minus_minus_distr (f (spl x h)) (f x)
                                                          (inn (df x) h)))
                            (Hdf2 h Hh_dfd))).
      - apply (le_trans (mult (abs (dg (f x))) (mult eps_f s))
                        (mult (mult (abs (dg (f x))) eps_f) s) (mult eps4 s)).
        + exact (le_id_l (mult (abs (dg (f x))) (mult eps_f s))
                         (mult (mult (abs (dg (f x))) eps_f) s)
                         (mult (mult (abs (dg (f x))) eps_f) s)
                         (mult_assoc (abs (dg (f x))) eps_f s)
                         (le_refl (mult (mult (abs (dg (f x))) eps_f) s))).
        + apply (le_trans (mult (mult (abs (dg (f x))) eps_f) s)
                          (mult (mult (mult (inv_pos M HM) eps4) (abs (dg (f x)))) s)
                          (mult eps4 s)).
          * exact (le_trans (mult (mult (abs (dg (f x))) eps_f) s)
                            (mult (mult (abs (dg (f x)))
                                        (mult (inv_pos M HM) eps4)) s)
                            (mult (mult (mult (inv_pos M HM) eps4) (abs (dg (f x)))) s)
                            (le_mult_compat_weak (mult (abs (dg (f x))) eps_f)
                               (mult (abs (dg (f x))) (mult (inv_pos M HM) eps4)) s
                               Hspos
                               (req_le_mult_compat_r (abs (dg (f x))) eps_f
                                  (mult (inv_pos M HM) eps4)
                                  (abs_nonneg_plain (dg (f x)))
                                  (min_le_r_plain one
                                     (mult (inv_pos M HM) eps4))))
                            (le_id_l (mult (mult (abs (dg (f x)))
                                                 (mult (inv_pos M HM) eps4)) s)
                                     (mult (mult (mult (inv_pos M HM) eps4)
                                                 (abs (dg (f x)))) s)
                                     (mult (mult (mult (inv_pos M HM) eps4)
                                                 (abs (dg (f x)))) s)
                                     (req_mult_compat
                                        (mult (abs (dg (f x)))
                                              (mult (inv_pos M HM) eps4))
                                        (mult (mult (inv_pos M HM) eps4)
                                              (abs (dg (f x)))) s s
                                        (mult_comm (abs (dg (f x)))
                                                   (mult (inv_pos M HM) eps4))
                                        (req_refl s))
                                     (le_refl (mult (mult (mult (inv_pos M HM) eps4)
                                                        (abs (dg (f x)))) s)))).
          * apply (le_trans (mult (mult (mult (inv_pos M HM) eps4) (abs (dg (f x)))) s)
                            (mult (mult (mult (inv_pos M HM) eps4) M) s)
                            (mult eps4 s)).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos M HM) eps4)
                                                (abs (dg (f x))))
                          (mult (mult (inv_pos M HM) eps4) M) s Hspos
                          (req_le_mult_compat_r (mult (inv_pos M HM) eps4)
                             (abs (dg (f x))) M
                             (le_id_l zero (mult zero eps4)
                                (mult (inv_pos M HM) eps4)
                                (req_sym (mult zero eps4) zero
                                   (req_trans (mult zero eps4) (mult eps4 zero)
                                              zero
                                              (mult_comm zero eps4)
                                              (mult_zero eps4)))
                                (le_mult_compat_weak zero (inv_pos M HM) eps4
                                   (lt_le_iff zero eps4 (inl Heps4))
                                   (lt_le_iff zero (inv_pos M HM)
                                              (inl (inv_pos_pos M HM)))))
                             (req_le_plus_nonneg_r (abs (dg (f x))) one
                                (lt_le_iff zero one (inl one_pos))))).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos M HM) eps4) M)
                          eps4 s Hspos (req_rdf_inv_scale_le M eps4 HM)). }
    (* closing: [E == T1 + T2] with [|T1 + T2| <= eps4 * s + eps4 * s       *)
    (* <= eps * s] *)
    apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                   (plus (g (f x))
                                         (inn (rs_mult SS (dg (f x)) (df x))
                                              h))))
                   (abs (plus (req_minus (g (f (spl x h)))
                                          (plus (g (f x)) (mult (dg (f x)) Dg)))
                              (mult (dg (f x)) (req_minus Dg (inn (df x) h)))))
                   (mult eps s)).
    + exact (req_abs_compat
               (req_minus (g (f (spl x h)))
                          (plus (g (f x))
                                (inn (rs_mult SS (dg (f x)) (df x)) h)))
               (plus (req_minus (g (f (spl x h)))
                                (plus (g (f x)) (mult (dg (f x)) Dg)))
                     (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
               (req_trans
                  (req_minus (g (f (spl x h)))
                             (plus (g (f x))
                                   (inn (rs_mult SS (dg (f x)) (df x)) h)))
                  (req_minus (g (f (spl x h)))
                             (plus (g (f x)) (mult (dg (f x)) (inn (df x) h))))
                  (plus (req_minus (g (f (spl x h)))
                                   (plus (g (f x)) (mult (dg (f x)) Dg)))
                        (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                  (req_rdf_minus_compat_r (g (f (spl x h)))
                     (plus (g (f x))
                           (inn (rs_mult SS (dg (f x)) (df x)) h))
                     (plus (g (f x)) (mult (dg (f x)) (inn (df x) h)))
                     (req_plus_compat (g (f x)) (g (f x))
                        (inn (rs_mult SS (dg (f x)) (df x)) h)
                        (mult (dg (f x)) (inn (df x) h))
                        (req_refl (g (f x)))
                        (rh_inner_smult_l SS HS (dg (f x)) (df x) h)))
                  (req_rdf_mv_compose_decomp (g (f (spl x h))) (g (f x)) (dg (f x))
                     (req_minus (f (spl x h)) (f x)) (inn (df x) h)))).
    + apply (le_trans (abs (plus (req_minus (g (f (spl x h)))
                                                (plus (g (f x))
                                                      (mult (dg (f x)) Dg)))
                                         (mult (dg (f x))
                                               (req_minus Dg (inn (df x) h)))))
                      (plus (abs (req_minus (g (f (spl x h)))
                                            (plus (g (f x)) (mult (dg (f x)) Dg))))
                            (abs (mult (dg (f x))
                                       (req_minus Dg (inn (df x) h)))))
                      (mult eps s)).
      * exact (req_rdf_abs_triangle (req_minus (g (f (spl x h)))
                                               (plus (g (f x))
                                                     (mult (dg (f x)) Dg)))
                                    (mult (dg (f x))
                                          (req_minus Dg (inn (df x) h)))).
      * apply (le_trans (plus (abs (req_minus (g (f (spl x h)))
                                              (plus (g (f x)) (mult (dg (f x)) Dg))))
                              (abs (mult (dg (f x))
                                         (req_minus Dg (inn (df x) h)))))
                        (plus (mult eps4 s) (mult eps4 s)) (mult eps s)).
        -- exact (le_plus_compat
                    (abs (req_minus (g (f (spl x h)))
                                    (plus (g (f x)) (mult (dg (f x)) Dg))))
                    (mult eps4 s)
                    (abs (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                    (mult eps4 s) HT1 HT2).
        -- exact (req_rdf_quarter_pair_le_final eps s Heps Hspos).
Qed.

(* ---- item 16 premise-slot group (honest slots; isomorphic to the three  *)
(*   Variables of the baseline vec region, plus three honesty slots: the   *)
(*   field compatibility, second-argument linearity and metric            *)
(*   translation — the baseline carrier has no inner-product transport,    *)
(*   so they continue at the interface level)  *)

Variable req_mv_adjoint : forall Ld : Sc -> Sc,
  sigT (fun Lad : Sc -> Sc => forall h w : Sc,
    req (inn (Ld h) w) (inn h (Lad w))).

Variable req_op_lipschitz : forall Ld : Sc -> Sc,
  sigT (fun N : R => And (le zero N) (forall h : Sc,
    le (mtr (Ld h) S0) (mult N (mtr h S0)))).

Variable req_sfield_wd : forall (w : Sc -> R) (u v : Sc),
  Id u v -> req (w u) (w v).

Variable req_inner_sminus_r : forall (a u v : Sc),
  req (inn a (req_sminus SS u v)) (req_minus (inn a u) (inn a v)).

Variable req_smetric_sminus_zero : forall u v : Sc,
  req (mtr (req_sminus SS u v) S0) (mtr u v).

(* ---- item 16: differentiable_mv_vec_compose ->                          *)
(* [req_rdf_mv_vec_compose] --                                             *)
(*   (six slots consumed: [req_mv_adjoint]/[req_op_lipschitz]/             *)
(*   [req_inner_lipschitz]/[req_sfield_wd]/[req_inner_sminus_r]/           *)
(*   [req_smetric_sminus_zero]; adjoint pullback gradient; the general     *)
(*   error decomposition [req_rdf_mv_vec_decomp] matches directly; the     *)
(*   budget is as in item 15, T1 the [eps_g * |Dg|] family and T2 the      *)
(*   [N_a * |<a, Dg> - <a, df h>|] family; closed by                       *)
(*   [quarter_pair_le_final])  *)

Theorem req_rdf_mv_vec_compose : forall (f : Sc -> Sc) (g : Sc -> R),
  reqRDFMVVec SS f -> reqRDFMV SS HS g ->
  reqRDFMV SS HS (fun x => g (f x)).
Proof.
  intros f g Hf Hg.
  destruct Hf as [df Hdf]. destruct Hg as [dg Hdg].
  exists (fun x => projT1 (req_mv_adjoint (df x)) (dg (f x))).
  intros x eps Heps.
  destruct (req_inner_lipschitz (dg (f x))) as [Na [HNa0 HNa2]].
  destruct (req_op_lipschitz (df x)) as [Nop [HNop0 HNop2]].
  pose (eps4 := mult (inv_pos (plus one one) req_two_pos)
                     (mult (inv_pos (plus one one) req_two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive.
    - apply inv_pos_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps]. }
  pose (M := plus Na one).
  assert (HM : lt zero M) by (unfold M; exact (req_plus_le_lt_pos Na one HNa0 one_pos)).
  pose (L := plus Nop one).
  assert (HL : lt zero L) by (unfold L; exact (req_plus_le_lt_pos Nop one HNop0 one_pos)).
  pose (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f).
  { unfold eps_f. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  pose (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g).
  { unfold eps_g. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  destruct (Hdf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hdg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    exact (min_pos dfd (min one (mult (inv_pos L HL) dgd)) Hdf1
             (min_pos one (mult (inv_pos L HL) dgd) one_pos Hltm)).
  - intros h Hh.
    pose (s := mtr h S0).
    pose (Dg := req_sminus SS (f (spl x h)) (f x)).
    pose (adj := projT1 (req_mv_adjoint (df x)) (dg (f x))).
    assert (Hadj : forall w : Sc, req (inn (df x w) (dg (f x))) (inn w adj)).
    { intro w. exact (projT2 (req_mv_adjoint (df x)) w (dg (f x))). }
    assert (Hh_dfd : lt s dfd).
    { exact (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd))) dfd Hh
             (min_le_l_plain dfd (min one (mult (inv_pos L HL) dgd)))). }
    assert (Hh_dgds : lt s (mult (inv_pos L HL) dgd)).
    { exact (lt_le_trans s (min one (mult (inv_pos L HL) dgd))
                         (mult (inv_pos L HL) dgd)
               (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd)))
                            (min one (mult (inv_pos L HL) dgd)) Hh
                            (min_le_r_plain dfd
                               (min one (mult (inv_pos L HL) dgd))))
               (min_le_r_plain one (mult (inv_pos L HL) dgd))). }
    assert (Hef : le eps_f one).
    { exact (min_le_l_plain one (mult (inv_pos M HM) eps4)). }
    assert (Hspos : le zero s) by exact (rs_metric_pos SS h S0).
    (* carrier-difference cancellation (the same family as the baseline     *)
    (* [splus_sminus_cancel]; direct from the record's law fields) *)
    assert (Hcancel : Id (spl (f x) Dg) (f (spl x h))).
    { unfold req_sminus.
      assert (H1 : Id (spl (f x) (spl (f (spl x h)) (rs_opp SS (f x))))
                      (spl (f x) (spl (rs_opp SS (f x)) (f (spl x h)))))
        by exact (id_cong (fun z => spl (f x) z)
                          (rs_plus_comm SS (f (spl x h))
                                        (rs_opp SS (f x)))).
      assert (H2 : Id (spl (f x) (spl (rs_opp SS (f x)) (f (spl x h))))
                      (spl (spl (f x) (rs_opp SS (f x))) (f (spl x h))))
        by exact (rs_plus_assoc SS (f x) (rs_opp SS (f x))
                                (f (spl x h))).
      assert (H3 : Id (spl (spl (f x) (rs_opp SS (f x))) (f (spl x h)))
                      (spl S0 (f (spl x h))))
        by exact (id_cong (fun z => spl z (f (spl x h)))
                          (rs_plus_opp SS (f x))).
      assert (H4 : Id (spl S0 (f (spl x h))) (f (spl x h)))
        by exact (id_trans (rs_plus_comm SS S0 (f (spl x h)))
                           (rs_plus_zero SS (f (spl x h)))).
      exact (id_trans H1 (id_trans H2 (id_trans H3 H4))). }
    assert (Hgu : req (g (spl (f x) Dg)) (g (f (spl x h)))).
    { exact (req_sfield_wd g (spl (f x) Dg) (f (spl x h)) Hcancel). }
    (* (a) |Dg| ≤ L·s *)
    assert (HDg : le (mtr Dg S0) (mult L s)).
    { apply (le_trans (mtr Dg S0)
                      (plus (mtr Dg (df x h)) (mtr (df x h) S0)) (mult L s)).
      - exact (rs_metric_triangle SS Dg (df x h) S0).
      - apply (le_trans (plus (mtr Dg (df x h)) (mtr (df x h) S0))
                        (plus (mult eps_f s) (mult Nop s)) (mult L s)).
        + exact (le_plus_compat (mtr Dg (df x h)) (mult eps_f s)
                                (mtr (df x h) S0) (mult Nop s)
                                (Hdf2 h Hh_dfd) (HNop2 h)).
        + apply (le_trans (plus (mult eps_f s) (mult Nop s))
                          (mult (plus eps_f Nop) s) (mult L s)).
          * exact (le_id_l (plus (mult eps_f s) (mult Nop s))
                           (mult (plus eps_f Nop) s) (mult (plus eps_f Nop) s)
                           (req_sym (mult (plus eps_f Nop) s)
                                    (plus (mult eps_f s) (mult Nop s))
                                    (req_mult_plus_distr_r eps_f Nop s))
                           (le_refl (mult (plus eps_f Nop) s))).
          * exact (le_mult_compat_weak (plus eps_f Nop) L s Hspos
                       (le_trans (plus eps_f Nop) (plus one Nop) L
                                 (le_plus_compat eps_f one Nop Nop Hef
                                                 (le_refl Nop))
                                 (le_id_l (plus one Nop) L L (plus_comm one Nop)
                                          (le_refl L)))). }
    (* |Dg| < dgd *)
    assert (HDg_lt : lt (mtr Dg S0) dgd).
    { apply (le_lt_trans (mtr Dg S0) (mult L s) dgd).
      - exact HDg.
      - exact (lt_id_l (mult L s) (mult s L) dgd (mult_comm L s)
                 (lt_id_r (mult s L) (mult (mult (inv_pos L HL) dgd) L) dgd
                    (req_trans (mult (mult (inv_pos L HL) dgd) L)
                               (mult L (mult (inv_pos L HL) dgd)) dgd
                               (mult_comm (mult (inv_pos L HL) dgd) L)
                               (req_rdf_inv_cancel L dgd HL Hdg1))
                    (lt_mult_compat s (mult (inv_pos L HL) dgd) L HL Hh_dgds))). }
    (* T1 *)
    assert (HT1 : le (abs (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (inn (dg (f x)) Dg))))
                      (mult eps4 s)).
    { apply (le_trans (abs (req_minus (g (f (spl x h)))
                                      (plus (g (f x)) (inn (dg (f x)) Dg))))
                      (mult eps_g (mtr Dg S0)) (mult eps4 s)).
      - apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                       (plus (g (f x)) (inn (dg (f x)) Dg))))
                       (abs (req_minus (g (spl (f x) Dg))
                                       (plus (g (f x)) (inn (dg (f x)) Dg))))
                       (mult eps_g (mtr Dg S0))
                       (req_abs_compat
                          (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (inn (dg (f x)) Dg)))
                          (req_minus (g (spl (f x) Dg))
                                     (plus (g (f x)) (inn (dg (f x)) Dg)))
                          (req_rdf_minus_compat_l (g (f (spl x h)))
                             (g (spl (f x) Dg))
                             (plus (g (f x)) (inn (dg (f x)) Dg))
                             (req_sym (g (spl (f x) Dg)) (g (f (spl x h)))
                                      Hgu)))).
        exact (Hdg2 Dg HDg_lt).
      - apply (le_trans (mult eps_g (mtr Dg S0)) (mult eps_g (mult L s))
                        (mult eps4 s)).
        + exact (req_le_mult_compat_r eps_g (mtr Dg S0) (mult L s)
                     (lt_le_iff zero eps_g (inl Heps_g)) HDg).
        + apply (le_trans (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                          (mult eps4 s)).
          * exact (le_id_l (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                           (mult (mult eps_g L) s) (mult_assoc eps_g L s)
                           (le_refl (mult (mult eps_g L) s))).
          * apply (le_trans (mult (mult eps_g L) s)
                            (mult (mult (mult (inv_pos L HL) eps4) L) s)
                            (mult eps4 s)).
            -- exact (le_mult_compat_weak (mult eps_g L)
                          (mult (mult (inv_pos L HL) eps4) L) s Hspos
                          (le_trans (mult eps_g L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (le_mult_compat_weak eps_g
                                       (mult (inv_pos L HL) eps4) L
                                       (lt_le_iff zero L (inl HL))
                                       (min_le_r_plain one
                                          (mult (inv_pos L HL) eps4)))
                                    (le_refl (mult (mult (inv_pos L HL) eps4) L)))).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos L HL) eps4) L)
                          eps4 s Hspos (req_rdf_inv_scale_le L eps4 HL)). }
    (* T2: the adjoint-gradient inner-product difference bounded by the     *)
    (* [N_a] family *)
    assert (HT2 : le (abs (req_minus (inn (dg (f x)) Dg)
                                     (inn (dg (f x)) (df x h))))
                      (mult eps4 s)).
    { apply (le_trans (abs (req_minus (inn (dg (f x)) Dg)
                                      (inn (dg (f x)) (df x h))))
                      (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                      (mult eps4 s)).
      - exact (le_id_l (abs (req_minus (inn (dg (f x)) Dg)
                                       (inn (dg (f x)) (df x h))))
                       (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                       (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                       (req_abs_compat (req_minus (inn (dg (f x)) Dg)
                                                  (inn (dg (f x)) (df x h)))
                          (inn (dg (f x)) (req_sminus SS Dg (df x h)))
                          (req_sym (inn (dg (f x)) (req_sminus SS Dg (df x h)))
                                   (req_minus (inn (dg (f x)) Dg)
                                              (inn (dg (f x)) (df x h)))
                                   (req_inner_sminus_r (dg (f x)) Dg (df x h))))
                       (le_refl (abs (inn (dg (f x))
                                          (req_sminus SS Dg (df x h)))))).
      - apply (le_trans (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                        (mult Na (mtr (req_sminus SS Dg (df x h)) S0))
                        (mult eps4 s)).
        + exact (HNa2 (req_sminus SS Dg (df x h))).
        + apply (le_trans (mult Na (mtr (req_sminus SS Dg (df x h)) S0))
                          (mult Na (mult eps_f s)) (mult eps4 s)).
          * exact (le_id_l (mult Na (mtr (req_sminus SS Dg (df x h)) S0))
                           (mult Na (mtr Dg (df x h)))
                           (mult Na (mult eps_f s))
                           (req_mult_compat Na Na
                              (mtr (req_sminus SS Dg (df x h)) S0)
                              (mtr Dg (df x h))
                              (req_refl Na)
                              (req_smetric_sminus_zero Dg (df x h)))
                           (req_le_mult_compat_r Na (mtr Dg (df x h))
                              (mult eps_f s) HNa0 (Hdf2 h Hh_dfd))).
          * apply (le_trans (mult Na (mult eps_f s))
                            (mult (mult Na eps_f) s) (mult eps4 s)).
            -- exact (le_id_l (mult Na (mult eps_f s))
                              (mult (mult Na eps_f) s)
                              (mult (mult Na eps_f) s) (mult_assoc Na eps_f s)
                              (le_refl (mult (mult Na eps_f) s))).
            -- apply (le_trans (mult (mult Na eps_f) s)
                              (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                              (mult eps4 s)).
              ++ exact (le_trans (mult (mult Na eps_f) s)
                                 (mult (mult Na (mult (inv_pos M HM) eps4)) s)
                                 (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                 (le_mult_compat_weak (mult Na eps_f)
                                    (mult Na (mult (inv_pos M HM) eps4)) s
                                    Hspos
                                    (req_le_mult_compat_r Na eps_f
                                       (mult (inv_pos M HM) eps4) HNa0
                                       (min_le_r_plain one
                                          (mult (inv_pos M HM) eps4))))
                                 (le_id_l
                                    (mult (mult Na (mult (inv_pos M HM) eps4)) s)
                                    (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                    (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                    (req_mult_compat
                                       (mult Na (mult (inv_pos M HM) eps4))
                                       (mult (mult (inv_pos M HM) eps4) Na) s s
                                       (mult_comm Na (mult (inv_pos M HM) eps4))
                                       (req_refl s))
                                    (le_refl (mult (mult (mult (inv_pos M HM) eps4)
                                                       Na) s)))).
              ++ assert (Hcoef : le (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                            (mult eps4 s)).
                 { apply (le_trans (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                   (mult (mult (mult (inv_pos M HM) eps4) M) s)
                                   (mult eps4 s)).
                   - exact (le_mult_compat_weak
                               (mult (mult (inv_pos M HM) eps4) Na)
                               (mult (mult (inv_pos M HM) eps4) M) s Hspos
                               (req_le_mult_compat_r
                                  (mult (inv_pos M HM) eps4) Na M
                                  (le_id_l zero (mult zero eps4)
                                     (mult (inv_pos M HM) eps4)
                                     (req_sym (mult zero eps4) zero
                                        (req_trans (mult zero eps4)
                                                   (mult eps4 zero) zero
                                                   (mult_comm zero eps4)
                                                   (mult_zero eps4)))
                                     (le_mult_compat_weak zero
                                        (inv_pos M HM) eps4
                                        (lt_le_iff zero eps4 (inl Heps4))
                                        (lt_le_iff zero (inv_pos M HM)
                                                   (inl (inv_pos_pos M HM)))))
                                  (req_le_plus_nonneg_r Na one
                                     (lt_le_iff zero one (inl one_pos))))).
                   - exact (le_mult_compat_weak
                               (mult (mult (inv_pos M HM) eps4) M)
                               eps4 s Hspos (req_rdf_inv_scale_le M eps4 HM)). }
                 exact Hcoef. }
    (* closing: the adjoint-identity reshape + the general decomposition +  *)
    (* triangle + the eps/4 arithmetic *)
    apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                   (plus (g (f x)) (inn adj h))))
                   (abs (plus (req_minus (g (f (spl x h)))
                                          (plus (g (f x)) (inn (dg (f x)) Dg)))
                              (req_minus (inn (dg (f x)) Dg)
                                        (inn (dg (f x)) (df x h)))))
                   (mult eps s)).
    + exact (req_abs_compat
               (req_minus (g (f (spl x h))) (plus (g (f x)) (inn adj h)))
               (plus (req_minus (g (f (spl x h)))
                                (plus (g (f x)) (inn (dg (f x)) Dg)))
                     (req_minus (inn (dg (f x)) Dg)
                                (inn (dg (f x)) (df x h))))
               (req_trans
                  (req_minus (g (f (spl x h))) (plus (g (f x)) (inn adj h)))
                  (req_minus (g (f (spl x h)))
                             (plus (g (f x)) (inn (dg (f x)) (df x h))))
                  (plus (req_minus (g (f (spl x h)))
                                   (plus (g (f x)) (inn (dg (f x)) Dg)))
                        (req_minus (inn (dg (f x)) Dg)
                                   (inn (dg (f x)) (df x h))))
                  (req_rdf_minus_compat_r (g (f (spl x h)))
                     (plus (g (f x)) (inn adj h))
                     (plus (g (f x)) (inn (dg (f x)) (df x h)))
                     (req_plus_compat (g (f x)) (g (f x))
                        (inn adj h) (inn (dg (f x)) (df x h))
                        (req_refl (g (f x)))
                        (req_trans (inn adj h) (inn h adj)
                                   (inn (dg (f x)) (df x h))
                                   (rh_inner_sym SS HS adj h)
                                   (req_trans (inn h adj)
                                              (inn (df x h) (dg (f x)))
                                              (inn (dg (f x)) (df x h))
                                              (req_sym (inn (df x h) (dg (f x)))
                                                       (inn h adj)
                                                       (Hadj h))
                                              (rh_inner_sym SS HS
                                                 (df x h) (dg (f x)))))))
                  (req_rdf_mv_vec_decomp (g (f (spl x h))) (g (f x))
                     (inn (dg (f x)) (df x h)) (inn (dg (f x)) Dg)))).
    + apply (le_trans (abs (plus (req_minus (g (f (spl x h)))
                                                (plus (g (f x))
                                                      (inn (dg (f x)) Dg)))
                                         (req_minus (inn (dg (f x)) Dg)
                                                    (inn (dg (f x)) (df x h)))))
                      (plus (abs (req_minus (g (f (spl x h)))
                                            (plus (g (f x)) (inn (dg (f x)) Dg))))
                            (abs (req_minus (inn (dg (f x)) Dg)
                                            (inn (dg (f x)) (df x h)))))
                      (mult eps s)).
      * exact (req_rdf_abs_triangle (req_minus (g (f (spl x h)))
                                               (plus (g (f x))
                                                     (inn (dg (f x)) Dg)))
                                    (req_minus (inn (dg (f x)) Dg)
                                               (inn (dg (f x)) (df x h)))).
      * apply (le_trans (plus (abs (req_minus (g (f (spl x h)))
                                              (plus (g (f x))
                                                    (inn (dg (f x)) Dg))))
                              (abs (req_minus (inn (dg (f x)) Dg)
                                              (inn (dg (f x)) (df x h)))))
                        (plus (mult eps4 s) (mult eps4 s)) (mult eps s)).
        -- exact (le_plus_compat
                    (abs (req_minus (g (f (spl x h)))
                                    (plus (g (f x)) (inn (dg (f x)) Dg))))
                    (mult eps4 s)
                    (abs (req_minus (inn (dg (f x)) Dg)
                                    (inn (dg (f x)) (df x h))))
                    (mult eps4 s) HT1 HT2).
        -- exact (req_rdf_quarter_pair_le_final eps s Heps Hspos).
Qed.

End ReqRDFMV.

(* ===================================================================== *)
(* ===================================================================== *)
End ReqRDFScalar.


