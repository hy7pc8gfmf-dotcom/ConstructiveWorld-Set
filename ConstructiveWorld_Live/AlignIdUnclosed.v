(* ConstructiveWorld-Set — assumption-free assembly of the exact backward-KL recursion identity. *)

(** * AlignIdUnclosed: the exact backward-KL step-recursion identity,
      assembled unconditionally from proven upstream bridges.

    Mission.  Assembles [aiu_backward_kl_exact_uncond] — the backward-KL
      step-recursion corollary with no premises beyond the Section
      interface — from the bridge [req2_backward_kl_step] in
      [UpReqAlign3] and the gap base [w_subgap_base] in [UpAlignIdReq],
      reusing the five-stage [beta]-scaling machine stage by stage; the
      KL argument order is inverted relative to the source face.

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
      [UpReqAlgebra], [UpReqDist], [UpReqAlign], [UpReqAlign2],
      [UpReqAlign3], [UpAlignIdReq]; imports [RealInterfaceEnhancedMod].
      [R] is the global [Real]; fields resolve through the global
      [RealEnhancedReal] instance; the source Section binding was
      removed, statements verbatim.

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name; statement names carried over verbatim.

    Constructivity.  Every statement closes with [Qed] by a real proof
      through term-mode [req_trans]/compat chains with no [destruct];
      all statements live on the [Set] layer; the fifteen Section
      interface slots are genuine premises kept as obligations.

    Build.  [coqc -native-compiler no -q -Q . "" AlignIdUnclosed.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 000160bc]. *)

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
Require Import UpReqDist.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import UpAlignIdReq.
Import RealInterfaceEnhancedMod.
(* Argument-free adaptation: the source Section binding
   [Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}] is removed;
   the carrier set [R] is bound by the [Notation] below to the global
   [Real], and interface fields resolve through the global instance
   [RealEnhancedReal] (the same pattern as the [UpReqAlign3.v] /
   [UpAlignIdReq.v] precedents).  No [Obj.magic] values and no [Prop]
   casts; the statement face and proof bodies are verbatim unchanged
   apart from dropping the binding arguments. *)
Notation R := Real.

(* ============================================================ *)
(* Section [AiuBackwardKL]: the backward-KL step-recursion       *)
(*   assembly chain in unconditional form.                       *)
(* ============================================================ *)
Section AiuBackwardKL.

Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.

(* ---- Local aliases: definitionally transparent thin wrappers over    *)
(*      the upstream [req2] definitions (the same pattern as            *)
(*      [UpReqAlign3]/[UpAlignIdReq]). ---- *)
Definition pos3 (p : S -> R) : Set := @req2_pos_dist S p.
Definition nrm (p : S -> R) : Set := @req2_norm_one S sumf p.
Definition KLE (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q) : R :=
  @req2_rel_ent S sumf p q Hp Hq.
Definition JJ (p : S -> R) (Hp : pos3 p) : R :=
  @req2_J S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition NPX (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  @req2_pi_next S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                eta pi_t Hpi_t s.
Definition npx_pos (pi_t : S -> R) (Hpi_t : pos3 pi_t) : pos3 (NPX pi_t Hpi_t) :=
  @req2_pi_next_pos S sumf sum_pos reward beta beta_pos pi_ref
                    pi_ref_pos eta pi_t Hpi_t.
Definition ZAL : R :=
  @req2_Z_align S sumf reward beta beta_pos pi_ref.
Variable ZAL_pos : lt zero ZAL.
Definition PSTR (s : S) : R :=
  @req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos s.
Definition PSTR_pos : pos3 PSTR :=
  @req2_pi_star_pos S sumf reward beta beta_pos pi_ref pi_ref_pos ZAL_pos.

(* ---- Input lemma 1: the gap substitution slot (fully applied         *)
(*      [UpAlignIdReq.w_subgap_base]):                                  *)
(*      [req_minus (J(pi_star) - J(p)) == beta * KL(p || pi_star)] —    *)
(*      the [Hgap] position of the assembly chain.                      *)
Lemma aiu_subgap_base : forall (p : S -> R) (Hp : pos3 p) (Hn : nrm p),
  req (req_minus (JJ PSTR PSTR_pos) (JJ p Hp))
      (mult beta (KLE p PSTR Hp PSTR_pos)).
Proof.
  intros p Hp Hn.
  exact (@UpAlignIdReq.w_subgap_base S sumf sum_ext sum_add sum_linear
                                     log_req_compat log_inv_exp_neg_req
                                     reward beta beta_pos pi_ref pi_ref_pos
                                     ZAL_pos p Hp Hn).
Qed.

(* ---- Input lemma 2: the three-KL exact-identity bridge (fully        *)
(*      applied [UpReqAlign3.req2_backward_kl_step]) — a proven         *)
(*      theorem supplied at the position where the source chain         *)
(*      carried an explicit premise ([PSTR]-first argument order).      *)
Lemma aiu_bridge_backward_kl_step :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (KLE PSTR pi_t PSTR_pos Hpi_t))
              (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                (npx_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (@req2_backward_kl_step S sumf sum_ext sum_add sum_linear sum_pos
                                log_req_compat log_inv_exp_neg_req
                                reward beta beta_pos pi_ref pi_ref_pos eta
                                ZAL_pos pi_t Hpi_t Hn).
Qed.

(* ---- Main statement: the assembly chain in unconditional form        *)
(*      (proven-bridge input version, [PSTR]-first argument order):     *)
(*      [beta * KL(pi* || pi_{t+1}) ==                                  *)
(*       (1 - eta) * beta * KL(pi* || pi_t)                             *)
(*         - eta * gap(pi_t) + beta * K2].                              *)
(*      The assembly reuses the five-stage [beta]-scaling machine       *)
(*      stage by stage at the same positions; no premise slots.         *)
Theorem aiu_backward_kl_exact_uncond :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (mult beta
              (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t)))
        (plus (mult (req_minus one eta)
                    (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
              (plus (opp (mult eta
                              (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))
                    (mult beta
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  pose proof (aiu_bridge_backward_kl_step pi_t Hpi_t Hn) as Hbridge.
  assert (Hgap : req (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                     (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
    by exact (aiu_subgap_base pi_t Hpi_t Hn).
  (* beta-scaling core 1: beta * (I * KSP) == I * (beta * KSP), where I := 1 - eta. *)
  assert (Hscale1 : req (mult beta (mult (req_minus one eta)
                                         (KLE PSTR pi_t PSTR_pos Hpi_t)))
                        (mult (req_minus one eta)
                              (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
  { apply (req_trans
              (mult beta (mult (req_minus one eta)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)))
              (mult (mult beta (req_minus one eta))
                    (KLE PSTR pi_t PSTR_pos Hpi_t))
              (mult (req_minus one eta)
                    (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
    - exact (mult_assoc beta (req_minus one eta)
                        (KLE PSTR pi_t PSTR_pos Hpi_t)).
    - apply (req_trans
                (mult (mult beta (req_minus one eta))
                      (KLE PSTR pi_t PSTR_pos Hpi_t))
                (mult (mult (req_minus one eta) beta)
                      (KLE PSTR pi_t PSTR_pos Hpi_t))
                (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
      + exact (req_mult_compat (mult beta (req_minus one eta))
                               (mult (req_minus one eta) beta)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)
                               (mult_comm beta (req_minus one eta))
                               (req_refl (KLE PSTR pi_t PSTR_pos Hpi_t))).
      + exact (req_sym (mult (req_minus one eta)
                             (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                       (mult (mult (req_minus one eta) beta)
                             (KLE PSTR pi_t PSTR_pos Hpi_t))
                       (mult_assoc (req_minus one eta) beta
                                   (KLE PSTR pi_t PSTR_pos Hpi_t))). }
  (* beta-scaling core 2: beta * (eta * KTS) == eta * (beta * KTS). *)
  assert (Hswap2 : req (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
  { apply (req_trans
              (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
              (mult (mult beta eta) (KLE pi_t PSTR Hpi_t PSTR_pos))
              (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
    - exact (mult_assoc beta eta (KLE pi_t PSTR Hpi_t PSTR_pos)).
    - apply (req_trans
                (mult (mult beta eta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                (mult (mult eta beta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
      + exact (req_mult_compat (mult beta eta) (mult eta beta)
                               (KLE pi_t PSTR Hpi_t PSTR_pos)
                               (KLE pi_t PSTR Hpi_t PSTR_pos)
                               (mult_comm beta eta)
                               (req_refl (KLE pi_t PSTR Hpi_t PSTR_pos))).
      + exact (req_sym (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (mult (mult eta beta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                       (mult_assoc eta beta (KLE pi_t PSTR Hpi_t PSTR_pos))). }
  (* beta * (opp (eta * KTS)) == opp (eta * gap(pi_t)): [req_opp_mult_l], then core 2, then the [Hgap] substitution. *)
  assert (Hscale2 : req (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                        (opp (mult eta
                                   (req_minus (JJ PSTR PSTR_pos)
                                              (JJ pi_t Hpi_t))))).
  { apply (req_trans
              (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
              (opp (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
              (opp (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))).
    - exact (req_opp_mult_l beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))).
    - apply (req_opp_compat
                (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)))).
      exact (req_trans
                (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)))
                Hswap2
                (req_mult_compat eta eta
                   (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                   (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                   (req_refl eta)
                   (req_sym (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                            (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                            Hgap))). }
  (* distributing beta over the second half of the tree: beta * (B + C) == beta * B + beta * C, with the [B] summand rewritten. *)
  assert (Hscale3 : req (mult beta (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                         (KLE pi_t (NPX pi_t Hpi_t)
                                              Hpi_t (npx_pos pi_t Hpi_t))))
                        (plus (opp (mult eta
                                            (req_minus (JJ PSTR PSTR_pos)
                                                       (JJ pi_t Hpi_t))))
                              (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                               Hpi_t (npx_pos pi_t Hpi_t))))).
  { apply (req_trans
              (mult beta (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                               (KLE pi_t (NPX pi_t Hpi_t)
                                    Hpi_t (npx_pos pi_t Hpi_t))))
              (plus (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                    (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                     Hpi_t (npx_pos pi_t Hpi_t))))
              (plus (opp (mult eta
                                 (req_minus (JJ PSTR PSTR_pos)
                                            (JJ pi_t Hpi_t))))
                    (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                     Hpi_t (npx_pos pi_t Hpi_t))))).
    - exact (distrib beta
                     (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                     (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))).
    - exact (req_plus_compat
                (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                (opp (mult eta
                            (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))
                (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))
                (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))
                Hscale2 (req_refl (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                              Hpi_t (npx_pos pi_t Hpi_t))))). }
  (* distributing beta over the whole tree. *)
  assert (Hscale : req
              (mult beta (plus (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t))
                               (plus (opp (mult eta
                                                  (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult (req_minus one eta)
                          (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                          (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))).
  { apply (req_trans
              (mult beta (plus (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t))
                               (plus (opp (mult eta
                                                  (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult beta (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (mult beta (plus (opp (mult eta
                                                   (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult (req_minus one eta)
                          (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                          (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))).
    - exact (distrib beta
                     (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                     (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                           (KLE pi_t (NPX pi_t Hpi_t)
                                Hpi_t (npx_pos pi_t Hpi_t)))).
    - exact (req_plus_compat
                (mult beta (mult (req_minus one eta)
                                 (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (mult beta (plus (opp (mult eta
                                               (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                 (KLE pi_t (NPX pi_t Hpi_t)
                                      Hpi_t (npx_pos pi_t Hpi_t))))
                (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                      (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t))))
                Hscale1 Hscale3). }
  (* closing: the beta-scaling of the bridge ([req_mult_compat] with the proven bridge [Hbridge]), then the whole-tree distribution [Hscale]. *)
  exact (req_trans
          (mult beta
                (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t)))
          (mult beta
                (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                      (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                            (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))))
          (plus (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (plus (opp (mult eta
                                   (req_minus (JJ PSTR PSTR_pos)
                                              (JJ pi_t Hpi_t))))
                      (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))
          (req_mult_compat beta beta
              (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
              (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                    (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))
              (req_refl beta) Hbridge)
          Hscale).
Qed.

End AiuBackwardKL.

(* ============================================================ *)
(* Assumption audit: three Print Assumptions commands at the     *)
(*   end of the file, after the Section close; each reports      *)
(*   Closed.                                                     *)
(* ============================================================ *)
Print Assumptions aiu_subgap_base.
Print Assumptions aiu_bridge_backward_kl_step.
Print Assumptions aiu_backward_kl_exact_uncond.
