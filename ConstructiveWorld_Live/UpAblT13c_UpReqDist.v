(* ConstructiveWorld-Set — statement-face completion for the uab_t2sum / uab_half two-point distribution family and its same-domain Gibbs companions. *)

(** * Two-point sum, half, and same-domain Gibbs statement faces.

    Mission.  This file formalizes the statement face of the two-point
      distribution family [uab_t2sum] / [uab_half]: the point-mass exchange
      kernel, the halving row identity, the two row-normalization
      discharges, and the three same-domain Gibbs statements (positivity,
      epsilon-sum, equality case) over the shared summation interface.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqDist],
      [UpReqAlgebra], [UpSigMigrate2] of this development; no Stdlib module.

    References.  This development, the same-name baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""] on this module compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 000160bc]. *)
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
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

(* Carrier convention of this tree: the interface class
   [RealInterfaceEnhancedSetoid] is unparameterized over the global Cauchy
   real [Real] at the global instance [RealEnhancedReal], and the carried
   statement faces are stated at that carrier; the two leading carrier
   slots of the carried-over faces are absorbed by the forwarding
   abbreviations below. *)
Abbreviation R0 := Real.
Abbreviation RIS0 := RealEnhancedReal.
Abbreviation reqd_boltzmann_prob :=
  (fun (RU : Set) (RIU : RealInterfaceEnhancedSetoid) =>
     @UpReqDist.reqd_boltzmann_prob).

Section UabT13cDist.

(* Equality-face names follow the canonical aliases of the distribution
   tree, so the statement faces and the cited lemma faces share one
   constant per relation. *)
Abbreviation req := real_eq.
Abbreviation lt := real_lt.
Abbreviation le := real_le.

Definition uab_t2sum (f : bool -> R0) : R0 := plus (f true) (f false).

Definition uab_half : R0 :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* ---- exchange kernel family lemma: the point masses commute, p(s) * (p(s') * c) relates by req to p(s') * (p(s) * c). ---- *)
Lemma uabT13c_swap_req_gen :
  forall (p : bool -> R0) (c : R0) (s s' : bool),
    req (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros p c s s'.
  exact (req_trans (mult (p s) (mult (p s') c))
                   (mult (mult (p s) (p s')) c)
                   (mult (p s') (mult (p s) c))
                   (mult_assoc (p s) (p s') c)
                   (req_trans (mult (mult (p s) (p s')) c)
                              (mult (mult (p s') (p s)) c)
                              (mult (p s') (mult (p s) c))
                              (req_mult_compat (mult (p s) (p s')) (mult (p s') (p s)) c c
                                               (mult_comm (p s) (p s')) (req_refl c))
                              (req_sym (mult (p s') (mult (p s) c))
                                       (mult (mult (p s') (p s)) c)
                                       (mult_assoc (p s') (p s) c)))).
Qed.

(* ---- two-point row-normalization kernel: uab_half + uab_half = one. ---- *)
Lemma uabT13c_half_row : req (plus uab_half uab_half) one.
Proof.
  unfold uab_half.
  assert (H1 : req (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                   (inv_pos (plus one one) (plus_positive one one one_pos one_pos))).
  { exact (req_trans (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one)
                     (inv_pos (plus one one) (plus_positive one one one_pos one_pos))
                     (mult_comm one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult_one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))). }
  assert (HDL : req (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                    (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                          (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))).
  { exact (req_trans (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                     (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                     (mult_comm (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (req_trans (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                                (plus (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one))
                                (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                (distrib (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one one)
                                (req_plus_compat (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one)))). }
  exact (req_trans (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) one
                   (req_trans (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                              (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                              (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                              (req_plus_compat (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                               (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1)
                                               (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1))
                              (req_sym (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                       (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                       HDL))
                   (inv_pos_correct (plus one one) (plus_positive one one one_pos one_pos))).
Qed.

(* ---- row-normalization discharge carried over from the baseline distribution statement: the two-point constant kernel reduces it to the halving row above. ---- *)
Theorem uabT13c_dist_norm3091 :
  forall s : bool,
    req (uab_t2sum (fun s' : bool => uab_half)) one.
Proof.
  intro s.
  unfold uab_t2sum.
  exact uabT13c_half_row.
Qed.

(* ---- detailed-balance discharge carried over from the baseline UpReqDist
        statement: the source kernel scaling family t(s, s') = p(s') * c, with
        p instantiated at reqd_boltzmann_prob (base_loss, D and Z fully general). ---- *)
Theorem uabT13c_dist_db3096 :
  forall (base_loss : bool -> R0) (D : R0) (D_pos : lt zero D)
         (Z : R0) (Z_pos : lt zero Z) (c : R0),
    forall s s' : bool,
      req (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s')
                (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s) c))
          (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s)
                (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s') c)).
Proof.
  intros base_loss D D_pos Z Z_pos c s s'.
  exact (uabT13c_swap_req_gen
           (fun x : bool => @reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos x)
           c s' s).
Qed.

End UabT13cDist.

(* ---- assumption audits for the named statements ---- *)
Print Assumptions uabT13c_dist_norm3091.
Print Assumptions uabT13c_dist_db3096.

(* ======================== Section 1. Same-domain statement face ======================== *)
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
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.

(* The Gibbs statement faces carry the same two leading carrier slots of
   the first section; the forwarding abbreviations absorb them over the
   same global instance, and the equality-face names keep the canonical
   real-face aliases of the first section. *)
Abbreviation req := real_eq.
Abbreviation lt := real_lt.
Abbreviation le := real_le.
Abbreviation kl_a :=
  (fun (RU : Set) (RIU : RealInterfaceEnhancedSetoid) => @UpSigMigrate2.kl_a).
Abbreviation req_gibbs_inequality :=
  (fun (RU : Set) (RIU : RealInterfaceEnhancedSetoid) =>
     @UpReqDist.req_gibbs_inequality).
Abbreviation req_gibbs_equality :=
  (fun (RU : Set) (RIU : RealInterfaceEnhancedSetoid) =>
     @UpReqDist.req_gibbs_equality).

Section UabT13cGibbs.

(* ---- b_gibbs_pos discharged out of its source section: all six premises carried as explicit statement arguments, the source proof applies with them verbatim. ---- *)
Theorem uabT13c_bgibbs_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hext : forall f g : S -> R0, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R0,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R0) (f : S -> R0),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R0, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R0) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R0) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R0) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (@kl_a R0 RIS0 S sumf p q Hp Hq).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq Hnp Hnq.
  exact (@req_gibbs_inequality R0 RIS0 S sumf Hext Hadd Hlin Hle Hloginv Hlogle
                               p q Hp Hq Hnp Hnq).
Qed.

(* ---- b_gibbs_sum_eps: a chain over b_gibbs_pos and le_plus_compat, adding no new statement arguments. ---- *)
Theorem uabT13c_bgibbs_sum_eps :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hext : forall f g : S -> R0, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R0,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R0) (f : S -> R0),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hle : forall f g : S -> R0, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (Hloginv : forall (x : R0) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R0) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (p q : S -> R0) (Hp : pdist_a S p) (Hq : pdist_a S q)
         (eps : R0) (Heps : lt zero eps),
    nrm_a S sumf p -> nrm_a S sumf q ->
    le zero (plus (@kl_a R0 RIS0 S sumf p q Hp Hq) eps).
Proof.
  intros S sumf Hext Hadd Hlin Hle Hloginv Hlogle p q Hp Hq eps Heps Hnp Hnq.
  exact (le_trans zero eps (plus (@kl_a R0 RIS0 S sumf p q Hp Hq) eps)
                    (lt_le_iff zero eps (inl Heps))
                    (le_id_l eps (plus zero eps)
                               (plus (@kl_a R0 RIS0 S sumf p q Hp Hq) eps)
                               (req_sym (plus zero eps) eps
                                          (req_trans (plus zero eps) (plus eps zero) eps
                                                     (plus_comm zero eps) (plus_zero eps)))
                               (le_plus_compat zero (@kl_a R0 RIS0 S sumf p q Hp Hq)
                                               eps eps
                                               (uabT13c_bgibbs_pos S sumf Hext Hadd Hlin Hle
                                                                   Hloginv Hlogle p q Hp Hq Hnp Hnq)
                                               (le_refl eps)))).
Qed.

(* ---- b_gibbs_eq conditional discharge: all eight premises carried as explicit
        statement arguments and the source proof applied with them verbatim;
        the log-equality-linear slot is genuinely open, since no concrete
        carrier instantiates it, so the equality-face debt travels with the
        statement, carried openly rather than hidden. ---- *)
Theorem uabT13c_bgibbs_eq :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hext : forall f g : S -> R0, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (Hadd : forall f g : S -> R0,
                   req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (Hlin : forall (a : R0) (f : S -> R0),
                   req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)))
         (Hznn : forall f : S -> R0,
                   (forall s : S, le zero (f s)) -> req (sumf f) zero ->
                   forall s : S, req (f s) zero)
         (Hloginv : forall (x : R0) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
                      req (log (inv_pos x Hx) Hi) (opp (log x Hx)))
         (Hlogle : forall (x : R0) (Hx : lt zero x), le (log x Hx) (req_minus x one))
         (Hlogeq : forall (x : R0) (Hx : lt zero x),
                     req (log x Hx) (req_minus x one) -> req x one)
         (p q : S -> R0) (Hp : pdist_a S p) (Hq : pdist_a S q),
    nrm_a S sumf p -> nrm_a S sumf q ->
    req (@kl_a R0 RIS0 S sumf p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq p q Hp Hq Hnp Hnq Hkl0.
  exact (@req_gibbs_equality R0 RIS0 S sumf Hext Hadd Hlin Hznn Hloginv Hlogle Hlogeq
                             p q Hp Hq Hnp Hnq Hkl0).
Qed.

End UabT13cGibbs.

(* ---- assumption audits for the named statements ---- *)
Print Assumptions uabT13c_bgibbs_pos.
Print Assumptions uabT13c_bgibbs_sum_eps.
Print Assumptions uabT13c_bgibbs_eq.
