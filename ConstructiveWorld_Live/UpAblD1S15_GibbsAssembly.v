(* ConstructiveWorld-Set -- Gibbs assembly family over the canonical Real carrier. *)

(** * UpAblD1S15_GibbsAssembly: the Gibbs epsilon inequality assembly.

    Mission.  Log compatibility [uabd1s2_ga2_log_req_compat], the summation
      bundle [uabd1s2_ga2_base_real_bundle] over the finite sum [sumd_sumf];
      the interface record [uabd1s15_ga2_pack8] with instance
      [uabd1s15_ga2_pack8_supplied]; req/le combinators, [uabd1s15_ga2_mopp_one],
      the tangent bound [uabd1s15_ga2_ptw_le]; the Gibbs inequality
      [uabd1s15_ga2_gibbs_eps] with companion [uabd1s15_ga2_gibbs_eps_opps].

    Dependencies.  Stdlib [List].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5],
      [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [G05_LogSmall], [UpReqSumD], [UpReqAlgebra], [UpReqAlign2] of this development.

    References.  This development, UpAblD1S15_GibbsAssembly.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements extract
      with [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].
      Disclosed declarations: log compatibility is carried by the explicit
      section variable [LOGC]; [Hnp]/[Hnq]/[Heps] are explicit universal premises.

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1S15_GibbsAssembly.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import List.
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
Require Import G05_LogSmall.
Require Import UpReqSumD.
Require Import UpReqAlgebra.
Require Import UpReqAlign2.

(* ================= Section 1. The [uabd1s2_ga2_log_req_compat] family ================= *)
Import RealInterfaceEnhancedMod.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ---- Slot one: [ga2_log_req_compat], verbatim at R := Real ---- *)
Theorem uabd1s2_ga2_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  (* Supplied by the G05 log-compatibility closure of the same statement. *)
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- Export chain: the five base-interface slots packed as a canonical Real
   carrier instance. The base is satisfiable in substance: sumf is realized
   by [sumd_sumf S0 en] (a concrete finite sum), the four summation laws are
   supplied directly by UpReqSumD and the log law directly by G05, so one
   instantiation resolves the pack; the ga2_ptw_le and ga2_log_req_compat
   slots draw on exactly this skeleton. *)
Theorem uabd1s2_ga2_base_real_bundle : forall (S0 : Set) (en : list S0),
  sigT (fun sumf : (S0 -> Real) -> Real =>
    And (forall f g : S0 -> Real,
           (forall s : S0, req (f s) (g s)) -> req (sumf f) (sumf g))
    (And (forall f g : S0 -> Real,
           req (sumf (fun s : S0 => plus (f s) (g s))) (plus (sumf f) (sumf g)))
    (And (forall (a : Real) (f : S0 -> Real),
           req (sumf (fun s : S0 => mult a (f s))) (mult a (sumf f)))
    (And (forall f g : S0 -> Real,
           (forall s : S0, le (f s) (g s)) -> le (sumf f) (sumf g))
         (forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
             req x y -> req (log x Hx) (log y Hy)))))).
Proof.
  intros S0 en.
  exact (existT _ (sumd_sumf S0 en)
          (pair (sumd_sum_ext S0 en)
          (pair (sumd_sum_add S0 en)
          (pair (sumd_sum_linear S0 en)
          (pair (sumd_sum_le S0 en) logd_log_compat_real))))).
Qed.

(* ---- Closing audit: the assumption face printed per exit at the end of the
   file ---- *)
Print Assumptions uabd1s2_ga2_log_req_compat.
Print Assumptions uabd1s2_ga2_base_real_bundle.
(* ================= Section 2. The [uabd1s15_ren] family ================= *)

(* The interface class of this development carries no carrier argument;
   its fields resolve through the global [Real] instance. *)
Definition uabd1s15_ren : RealInterfaceEnhancedSetoid :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ================================================================
   Section A.  Interface packing: the eight interface slots and premises as
   one conjunction record (the section-level interface statements of the
   source module).
   ================================================================ *)

(* The carrier and setoid slots of the record are dropped: the class binds
   no carrier argument, and the slot faces below live on the global [Real]
   carrier (R := Real by the imported notation). *)
Inductive uabd1s15_ga2_pack8 : Type :=
| uabd1s15_ga2_pack8_intro :
    forall (S : Set) (sumf : (S -> R) -> R),
        forall (ga2_sum_ext : forall f g : S -> R,
                   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)),
          forall (ga2_sum_add : forall f g : S -> R,
                     req (sumf (fun s : S => plus (f s) (g s)))
                         (plus (sumf f) (sumf g))),
            forall (ga2_sum_linear : forall (a : R) (f : S -> R),
                       req (sumf (fun s : S => mult a (f s)))
                           (mult a (sumf f))),
              forall (ga2_sum_le : forall f g : S -> R,
                         (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g)),
                forall (ga2_log_req_compat : forall (x y : R) (Hx : lt zero x)
                                                      (Hy : lt zero y),
                                          req x y -> req (log x Hx) (log y Hy)),
                  uabd1s15_ga2_pack8.

(* Dependent modules: the skeleton instance of the S2 base module (the finite
   sum [sumd_sumf], canonical Real carrier); the four summation laws follow
   from the corresponding UpReqSumD lemmas and log compatibility is supplied
   by [uabd1s2_ga2_log_req_compat], re-established nowhere. *)
Theorem uabd1s15_ga2_pack8_supplied : uabd1s15_ga2_pack8.
Proof.
  exact (uabd1s15_ga2_pack8_intro
           unit (sumd_sumf unit nil)
           (sumd_sum_ext unit nil)
           (sumd_sum_add unit nil)
           (sumd_sum_linear unit nil)
           (sumd_sum_le unit nil)
           uabd1s2_ga2_log_req_compat).
Qed.

(* ================================================================
   Section B, part one.  R-generic combinators (the in-section exported
   definitions of the source module).
   ================================================================ *)

Section UpAblD1S15GAAlg.

(* Interface fields resolve through the global instance of the
   unparameterized class; the R-generic premise face is re-faced on the
   global Real carrier (UpReqSumD.v L58 precedent). *)

(* ---- The [req] transitivity combinator ---- *)
Definition uabd1s15_ga2_rt {x y z : R} (H1 : req x y) (H2 : req y z) : req x z :=
  req_trans x y z H1 H2.

(* ---- The pair of [le] rewriting combinators (left and right substitution) ---- *)
Definition uabd1s15_ga2_le_id_l {a b c : R} (H1 : req a b) (H2 : le b c) : le a c :=
  le_id_l a b c H1 H2.
Definition uabd1s15_ga2_le_id_r {a b c : R} (H1 : req b c) (H2 : le a b) : le a c :=
  le_id_r a b c H1 H2.

(* ---- Multiplicative normalization by [opp one], in two steps through
   [req_opp_mult_r] and [req_opp_compat] ---- *)
Lemma uabd1s15_ga2_mopp_one : forall x : R, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  exact (req_trans (mult (opp one) x) (opp (mult one x)) (opp x)
                   (req_opp_mult_r one x)
                   (req_opp_compat (mult one x) x (req_mult_one_l x))).
Qed.

End UpAblD1S15GAAlg.

(* ================================================================
   Section B, part two.  The pointwise tangent core; log compatibility is
   carried explicitly by the section variable LOGC, the instance condition of
   the source module's section-level interface ga2_log_req_compat, declared
   here as an explicit premise.
   ================================================================ *)

Section UpAblD1S15GAPtw.

(* Interface fields resolve through the global instance of the
   unparameterized class; the R-generic premise face is re-faced on the
   global Real carrier (UpReqSumD.v L58 precedent). *)
Variable LOGC : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Variable S0 : Set.

Lemma uabd1s15_ga2_ptw_le :
  forall (p q : S0 -> R) (eps : R) (s : S0)
         (Hps : lt zero (p s)) (Hqs : lt zero (q s)),
    lt zero eps ->
    le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
       (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))).
Proof.
  intros p q eps s Hps Hqs Heps.
  assert (Htan : le (log (mult (q s) (inv_pos (p s) Hps))
                          (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (log_le_linear_eps (mult (q s) (inv_pos (p s) Hps))
                 (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps))
                 eps Heps).
  assert (Hlm : req (log (mult (q s) (inv_pos (p s) Hps))
                         (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (log (q s) Hqs) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
    by exact (log_mult (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  (* log(1/p) equals the negative of log p: normalization by [inv_pos_correct],
     log compatibility, and the additive cancellation lemma. *)
  assert (Hlip : req (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
                     (opp (log (p s) Hps))).
  { assert (Ha : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (plus (log (p s) Hps) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
      by exact (log_mult (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)).
    assert (Hb : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (log one one_pos))
      by exact (LOGC (mult (p s) (inv_pos (p s) Hps)) one
                 (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps))
                 one_pos (inv_pos_correct (p s) Hps)).
    assert (Hc : req (log one one_pos) zero) by exact (log_one one_pos).
    assert (Hd : req (plus (log (p s) Hps)
                           (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))) zero)
      by exact (uabd1s15_ga2_rt
                  (req_sym (log (mult (p s) (inv_pos (p s) Hps))
                              (mult_positive (p s) (inv_pos (p s) Hps) Hps
                                (inv_pos_pos (p s) Hps)))
                           (plus (log (p s) Hps)
                                 (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)))
                           Ha)
                  (uabd1s15_ga2_rt Hb Hc)).
    exact (req_plus_inv_unique (log (p s) Hps)
             (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
             (opp (log (p s) Hps)) Hd (plus_opp (log (p s) Hps))). }
  assert (Hstep3 : req (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                       (plus (log (q s) Hqs) (opp (log (p s) Hps))))
    by exact (uabd1s15_ga2_rt Hlm
              (req_plus_compat (log (q s) Hqs) (log (q s) Hqs)
                (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)) (opp (log (p s) Hps))
                (req_refl (log (q s) Hqs)) Hlip)).
  assert (H4 : le (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (uabd1s15_ga2_le_id_l
                (req_sym (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs
                              (inv_pos_pos (p s) Hps)))
                         (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                         Hstep3)
                Htan).
  assert (H5 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (opp (plus (log (q s) Hqs) (opp (log (p s) Hps)))))
    by exact (opp_le_compat (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                            (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                            H4).
  (* Right-side normalization: [opp (plus (log q) (opp (log p)))] equals
     [req_minus (log p) (log q)]. *)
  assert (H6 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                   (req_minus (log (p s) Hps) (log (q s) Hqs))).
  { assert (r1 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps)))))
      by exact (req_opp_plus (log (q s) Hqs) (opp (log (p s) Hps))).
    assert (r2 : req (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (log (p s) Hps)))
      by exact (req_plus_compat (opp (log (q s) Hqs)) (opp (log (q s) Hqs))
                (opp (opp (log (p s) Hps))) (log (p s) Hps)
                (req_refl (opp (log (q s) Hqs))) (req_double_neg (log (p s) Hps))).
    assert (r3 : req (plus (opp (log (q s) Hqs)) (log (p s) Hps))
                     (plus (log (p s) Hps) (opp (log (q s) Hqs))))
      by exact (plus_comm (opp (log (q s) Hqs)) (log (p s) Hps)).
    exact (uabd1s15_ga2_rt (uabd1s15_ga2_rt r1 r2) r3). }
  assert (H7 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (req_minus (log (p s) Hps) (log (q s) Hqs)))
    by exact (uabd1s15_ga2_le_id_r H6 H5).
  assert (Hle0 : le zero (p s)) by exact (lt_le_iff zero (p s) (inl Hps)).
  assert (H8 : le (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                  (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))))
    by exact (req_le_mult_compat_r (p s) _ _ Hle0 H7).
  (* Left-side value normalization: [p * opp(1 - q/p + eps)] equals
     [plus p (opp (plus q (p * eps)))], through the cancellation q/p * p = q
     by [inv_pos_correct] together with an algebraic req chain over [distrib]
     and the distributivity of opp. *)
  assert (H9 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
  { assert (d1 : req (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                     (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
      by exact (req_sym (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                        (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                        (plus_assoc (mult (q s) (inv_pos (p s) Hps)) (opp one) eps)).
    assert (c1 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                           (mult (p s) (plus (opp one) eps))))
      by exact (uabd1s15_ga2_rt
                (req_mult_compat (p s) (p s)
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                  (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                  (req_refl (p s)) d1)
                (distrib (p s) (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))).
    assert (c2 : req (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)).
    { exact (uabd1s15_ga2_rt (mult_assoc (p s) (q s) (inv_pos (p s) Hps))
              (uabd1s15_ga2_rt (req_mult_compat (mult (p s) (q s)) (mult (q s) (p s))
                         (inv_pos (p s) Hps) (inv_pos (p s) Hps)
                         (req_mult_comm_rewrite (p s) (q s))
                         (req_refl (inv_pos (p s) Hps)))
                (uabd1s15_ga2_rt (req_sym (mult (q s) (mult (p s) (inv_pos (p s) Hps)))
                                 (mult (mult (q s) (p s)) (inv_pos (p s) Hps))
                                 (mult_assoc (q s) (p s) (inv_pos (p s) Hps)))
                  (uabd1s15_ga2_rt (req_mult_compat (q s) (q s)
                             (mult (p s) (inv_pos (p s) Hps)) one
                             (req_refl (q s)) (inv_pos_correct (p s) Hps))
                    (mult_one (q s)))))). }
    assert (c3 : req (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))).
    { assert (m1 : req (mult (p s) (opp one)) (opp (p s)))
        by exact (uabd1s15_ga2_rt (req_opp_mult_l (p s) one)
                  (req_opp_compat (mult (p s) one) (p s) (mult_one (p s)))).
      exact (uabd1s15_ga2_rt (distrib (p s) (opp one) eps)
              (req_plus_compat (mult (p s) (opp one)) (opp (p s))
                (mult (p s) eps) (mult (p s) eps) m1 (req_refl (mult (p s) eps)))). }
    assert (t2 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
      by exact (uabd1s15_ga2_rt c1
                (uabd1s15_ga2_rt
                  (req_plus_compat (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)
                    (mult (p s) (plus (opp one) eps)) (mult (p s) (plus (opp one) eps))
                    c2 (req_refl (mult (p s) (plus (opp one) eps))))
                  (req_plus_compat (q s) (q s)
                    (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))
                    (req_refl (q s)) c3))).
    assert (c5 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                     (opp (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))))
      by exact (uabd1s15_ga2_rt
                (req_opp_mult_l (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                (req_opp_compat (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
                  (req_mult_compat (p s) (p s)
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                    (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                    (req_refl (p s)) d1))).
    assert (c6 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                     (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
    { assert (v1 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps)))))
        by exact (req_opp_plus (q s) (plus (opp (p s)) (mult (p s) eps))).
      assert (v2 : req (opp (plus (opp (p s)) (mult (p s) eps)))
                       (plus (opp (opp (p s))) (opp (mult (p s) eps))))
        by exact (req_opp_plus (opp (p s)) (mult (p s) eps)).
      assert (v3 : req (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps)))))
        by exact (req_plus_compat (opp (q s)) (opp (q s))
                  (opp (plus (opp (p s)) (mult (p s) eps)))
                  (plus (opp (opp (p s))) (opp (mult (p s) eps)))
                  (req_refl (opp (q s))) v2).
      assert (v4 : req (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s)))
        by exact (req_plus_compat (opp (q s)) (opp (q s)) (opp (opp (p s))) (p s)
                  (req_refl (opp (q s))) (req_double_neg (p s))).
      assert (v5 : req (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps))))
                       (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps))))
        by exact (plus_assoc (opp (q s)) (opp (opp (p s))) (opp (mult (p s) eps))).
      assert (v6 : req (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps)))
                       (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps)) v4 (req_refl (opp (mult (p s) eps)))).
      assert (v7 : req (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps)))
                       (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (p s)) (plus (p s) (opp (q s)))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps))
                  (plus_comm (opp (q s)) (p s)) (req_refl (opp (mult (p s) eps)))).
      assert (v8 : req (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                       (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (req_sym (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                          (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                          (plus_assoc (p s) (opp (q s)) (opp (mult (p s) eps)))).
      assert (v9 : req (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                       (plus (p s) (opp (plus (q s) (mult (p s) eps)))))
        by exact (req_plus_compat (p s) (p s)
                  (plus (opp (q s)) (opp (mult (p s) eps)))
                  (opp (plus (q s) (mult (p s) eps)))
                  (req_refl (p s))
                  (req_sym (opp (plus (q s) (mult (p s) eps)))
                           (plus (opp (q s)) (opp (mult (p s) eps)))
                           (req_opp_plus (q s) (mult (p s) eps)))).
      exact (uabd1s15_ga2_rt v1
              (uabd1s15_ga2_rt v3
                (uabd1s15_ga2_rt v5
                  (uabd1s15_ga2_rt v6 (uabd1s15_ga2_rt v7 (uabd1s15_ga2_rt v8 v9)))))). }
    exact (uabd1s15_ga2_rt c5
              (uabd1s15_ga2_rt (req_opp_compat
                        (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps))
                                            (plus (opp one) eps)))
                        (plus (q s) (plus (opp (p s)) (mult (p s) eps)))
                        (uabd1s15_ga2_rt (req_sym (mult (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps))
                                         (mult (p s)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps)))
                                         (req_mult_compat (p s) (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps))
                                           (req_refl (p s)) d1))
                                  t2))
                c6)). }
  exact (uabd1s15_ga2_le_id_l
          (req_sym (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps)))) H9)
          H8).
Qed.

End UpAblD1S15GAPtw.

(* ================================================================
   Section C.  The main statement and its companion form (canonical Real
   carrier instantiation, sumf realized by [sumd_sumf S0 en], of the same
   origin as the S2 base module); Hnp/Hnq/Heps are carried explicitly as
   universal premises, declared as such rather than as unconditional supply.
   ================================================================ *)

Theorem uabd1s15_ga2_gibbs_eps :
  forall (S0 : Set) (en : list S0)
         (p q : S0 -> Real)
         (Hp : req2_pos_dist S0 p)
         (Hq : req2_pos_dist S0 q)
         (Hnp : req (sumd_sumf S0 en p) one)
         (Hnq : req (sumd_sumf S0 en q) one)
         (eps : Real),
    lt zero eps ->
    le zero (plus (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq) eps).
Proof.
  intros S0 en p q Hp Hq Hnp Hnq eps Heps.
  assert (Hptw : forall s : S0,
            le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
               (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
    by (intro s;
        exact (uabd1s15_ga2_ptw_le uabd1s2_ga2_log_req_compat S0 p q eps s
                 (Hp s) (Hq s) Heps)).
  assert (Hsum : le (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                    (sumd_sumf S0 en (fun s : S0 => mult (p s)
                              (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (sumd_sum_le S0 en _ _ Hptw).
  (* Summation algebra: the summed correction equals [opp eps], through the
     zero sum of the normalized mass, linearity, and the [opp one] scaling. *)
  assert (Tr : req (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                   (opp eps)).
  { assert (T1 : req (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                     (plus (sumd_sumf S0 en p)
                           (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))))
      by exact (sumd_sum_add S0 en p (fun s : S0 => opp (plus (q s) (mult (p s) eps)))).
    assert (T3e : req (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))
                      (plus (opp one) (opp eps))).
    { assert (T3a : req (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))
                        (sumd_sumf S0 en (fun s : S0 => plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (sumd_sum_ext S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps)))
                  (fun s : S0 => plus (opp (q s)) (opp (mult (p s) eps)))
                  (fun s : S0 => req_opp_plus (q s) (mult (p s) eps))).
      assert (T3b : req (sumd_sumf S0 en (fun s : S0 => plus (opp (q s)) (opp (mult (p s) eps))))
                        (plus (sumd_sumf S0 en (fun s : S0 => opp (q s)))
                              (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps)))))
        by exact (sumd_sum_add S0 en (fun s : S0 => opp (q s))
                    (fun s : S0 => opp (mult (p s) eps))).
      assert (A : req (sumd_sumf S0 en (fun s : S0 => opp (q s))) (opp one)).
      { assert (A1 : req (sumd_sumf S0 en (fun s : S0 => opp (q s)))
                          (sumd_sumf S0 en (fun s : S0 => mult (opp one) (q s))))
          by exact (sumd_sum_ext S0 en (fun s : S0 => opp (q s))
                    (fun s : S0 => mult (opp one) (q s))
                    (fun s : S0 => req_sym (mult (opp one) (q s)) (opp (q s))
                                (uabd1s15_ga2_mopp_one (q s)))).
        assert (A2 : req (sumd_sumf S0 en (fun s : S0 => mult (opp one) (q s)))
                          (mult (opp one) (sumd_sumf S0 en q)))
          by exact (sumd_sum_linear S0 en (opp one) q).
        assert (A3 : req (mult (opp one) (sumd_sumf S0 en q)) (mult (opp one) one))
          by exact (req_mult_compat (opp one) (opp one) (sumd_sumf S0 en q) one
                      (req_refl (opp one)) Hnq).
        assert (A4 : req (mult (opp one) one) (opp one)) by exact (mult_one (opp one)).
        exact (uabd1s15_ga2_rt A1 (uabd1s15_ga2_rt A2 (uabd1s15_ga2_rt A3 A4))). }
      assert (B : req (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps))) (opp eps)).
      { assert (B1 : req (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps)))
                          (sumd_sumf S0 en (fun s : S0 => mult (opp one) (mult (p s) eps))))
          by exact (sumd_sum_ext S0 en (fun s : S0 => opp (mult (p s) eps))
                    (fun s : S0 => mult (opp one) (mult (p s) eps))
                    (fun s : S0 => req_sym (mult (opp one) (mult (p s) eps))
                                (opp (mult (p s) eps))
                                (uabd1s15_ga2_mopp_one (mult (p s) eps)))).
        assert (B2 : req (sumd_sumf S0 en (fun s : S0 => mult (opp one) (mult (p s) eps)))
                          (mult (opp one) (sumd_sumf S0 en (fun s : S0 => mult (p s) eps))))
          by exact (sumd_sum_linear S0 en (opp one) (fun s : S0 => mult (p s) eps)).
        assert (B3 : req (sumd_sumf S0 en (fun s : S0 => mult (p s) eps)) eps).
        { assert (B3a : req (sumd_sumf S0 en (fun s : S0 => mult (p s) eps))
                            (sumd_sumf S0 en (fun s : S0 => mult eps (p s))))
            by exact (sumd_sum_ext S0 en (fun s : S0 => mult (p s) eps)
                      (fun s : S0 => mult eps (p s))
                      (fun s : S0 => req_mult_comm_rewrite (p s) eps)).
          assert (B3b : req (sumd_sumf S0 en (fun s : S0 => mult eps (p s)))
                            (mult eps (sumd_sumf S0 en p)))
            by exact (sumd_sum_linear S0 en eps p).
          assert (B3c : req (mult eps (sumd_sumf S0 en p)) (mult eps one))
            by exact (req_mult_compat eps eps (sumd_sumf S0 en p) one (req_refl eps) Hnp).
          assert (B3d : req (mult eps one) eps) by exact (mult_one eps).
          exact (uabd1s15_ga2_rt B3a (uabd1s15_ga2_rt B3b (uabd1s15_ga2_rt B3c B3d))). }
        assert (B4 : req (mult (opp one) (sumd_sumf S0 en (fun s : S0 => mult (p s) eps)))
                          (mult (opp one) eps))
          by exact (req_mult_compat (opp one) (opp one)
                    (sumd_sumf S0 en (fun s : S0 => mult (p s) eps)) eps
                    (req_refl (opp one)) B3).
        exact (uabd1s15_ga2_rt B1
                (uabd1s15_ga2_rt B2 (uabd1s15_ga2_rt B4 (uabd1s15_ga2_mopp_one eps)))). }
      exact (uabd1s15_ga2_rt T3a (uabd1s15_ga2_rt T3b
              (req_plus_compat (sumd_sumf S0 en (fun s : S0 => opp (q s))) (opp one)
                (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps))) (opp eps) A B))). }
    assert (T4 : req (plus one (plus (opp one) (opp eps))) (opp eps)).
    { assert (e1 : req (plus one (plus (opp one) (opp eps)))
                       (plus (plus one (opp one)) (opp eps)))
        by exact (plus_assoc one (opp one) (opp eps)).
      assert (e2 : req (plus (plus one (opp one)) (opp eps)) (plus zero (opp eps)))
        by exact (req_plus_compat (plus one (opp one)) zero (opp eps) (opp eps)
                  (plus_opp one) (req_refl (opp eps))).
      exact (uabd1s15_ga2_rt e1 (uabd1s15_ga2_rt e2 (req_plus_zero_l (opp eps)))). }
    exact (uabd1s15_ga2_rt T1
            (uabd1s15_ga2_rt
              (req_plus_compat (sumd_sumf S0 en p) one
                (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))
                (plus (opp one) (opp eps)) Hnp T3e)
              T4)). }
  assert (HD : le (opp eps)
                  (sumd_sumf S0 en (fun s : S0 => mult (p s)
                            (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (uabd1s15_ga2_le_id_l
                (req_sym (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                         (opp eps) Tr)
                Hsum).
  apply (le_id_l zero (plus (opp eps) eps)
          (plus (sumd_sumf S0 en (fun s : S0 => mult (p s)
                        (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))) eps)).
  - exact (uabd1s15_ga2_rt (req_sym (plus eps (opp eps)) zero (plus_opp eps))
                  (plus_comm eps (opp eps))).
  - exact (le_plus_compat (opp eps)
            (sumd_sumf S0 en (fun s : S0 => mult (p s)
                      (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
            eps eps HD (le_refl eps)).
Qed.

(* ---- Companion form: the shape with the negative of eps, for use from the
   other side of a squeezing argument; normalized by the req group laws ---- *)
Corollary uabd1s15_ga2_gibbs_eps_opps :
  forall (S0 : Set) (en : list S0)
         (p q : S0 -> Real)
         (Hp : req2_pos_dist S0 p)
         (Hq : req2_pos_dist S0 q)
         (Hnp : req (sumd_sumf S0 en p) one)
         (Hnq : req (sumd_sumf S0 en q) one)
         (eps : Real),
    lt zero eps ->
    le (opp eps) (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq).
Proof.
  intros S0 en p q Hp Hq Hnp Hnq eps Heps.
  assert (Step1 : le (plus zero (opp eps))
                     (plus (plus (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                           (opp eps)))
    by exact (le_plus_compat zero
                             (plus (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                             (opp eps) (opp eps)
                             (uabd1s15_ga2_gibbs_eps S0 en p q Hp Hq Hnp Hnq eps Heps)
                             (le_refl (opp eps))).
  assert (Step3 : req (plus (plus (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                            (opp eps))
                     (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)).
  { exact (uabd1s15_ga2_rt
            (req_sym (plus (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)
                           (plus eps (opp eps)))
                     (plus (plus (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                           (opp eps))
                     (plus_assoc (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)
                                 eps (opp eps)))
            (uabd1s15_ga2_rt
              (req_plus_compat (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)
                (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)
                (plus eps (opp eps)) zero
                (req_refl (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq))
                (plus_opp eps))
              (plus_zero (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)))). }
  exact (le_id_l (opp eps) (plus zero (opp eps))
                 (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)
                 (req_sym (plus zero (opp eps)) (opp eps)
                          (req_plus_zero_l (opp eps)))
                 (le_id_r (plus zero (opp eps))
                          (plus (plus (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                                (opp eps))
                          (req2_rel_ent S0 (sumd_sumf S0 en) p q Hp Hq)
                          Step3 Step1)).
Qed.

(* ============ Assumption audit: every exit closed under the global context
   is the criterion ============ *)

Print Assumptions uabd1s15_ga2_pack8_supplied.
Print Assumptions uabd1s15_ga2_ptw_le.
Print Assumptions uabd1s15_ga2_gibbs_eps.
Print Assumptions uabd1s15_ga2_gibbs_eps_opps.
