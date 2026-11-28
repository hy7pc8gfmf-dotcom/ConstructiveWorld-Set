(* ========================================================================= *)
(* Module   : SqrtfCauchyDischarge                                           *)
(* Mission. (1) frd_*: five theorems over an abstract finite-sum carrier     *)
(*    tying the firewall witness face (entropy fw_h, energy fw_et, KL-mix    *)
(*    fw_kl of the Boltzmann family) to the proved resolution face of the    *)
(*    temperature entropy layer; the recovery-gain identity and its dual     *)
(*    close all three witness slots. (2) ibw_*: |norm(-a)| == |norm(a)| in   *)
(*    Id and QeqT form over the expression algebra bxib_E. (3) sfcx_*:       *)
(*    |t| <= t + eps under 0 <= t, 0 < eps (real + slot face), the metric    *)
(*    identity d(a,b) == |a-b|, the ReqMetricAbs mixin with its Real         *)
(*    instance, and 1 < 1+1. (4) qd_*: plain right-slot bound b <=           *)
(*    r_max a b via the swap bridge, and sin(arctan 1) == cos(arctan 1),     *)
(*    the general form discharged trivially.                                 *)
(* Dependencies. S01_BaseRing through S15_TailFEPUp, UpReqAlgebra,           *)
(*    UpReqDist, UpReqTempEntropy, UpFirewallReq, UpReqBanachInstB,          *)
(*    UpReqBanachInstReal, UpReqRDF, RMaxSwap; Stdlib QArith, Extraction.    *)
(* References. Statement faces carried over verbatim from the same-named     *)
(*    host module of the source tree, modulo carrier completion: setoid      *)
(*    interface = zero-argument class RealInterfaceEnhancedSetoid + global   *)
(*    instance RealEnhancedReal (S07); Real, real_eq/real_lt/real_le and     *)
(*    the Q carriers QeqT/QltT are the existing S02 shapes.                  *)
(* Constructivity. Statements are Set-carried (real_lt/real_le = sigT/Or     *)
(*    per-eps carriers, QeqT/QltT = decidable Q carriers; embedded Q-order   *)
(*    faces mirror the S02 sigT shapes). Zero axioms, zero admits; proofs    *)
(*    are exact-chains into Qed'd library constants (Qed on proof constants  *)
(*    only, no opaque data definition); section hypotheses are honest        *)
(*    interface slots leaving as explicit Set-typed arguments.               *)
(* Build. rocq c -native-compiler no -q -Q <tree root> ""                    *)
(*    SqrtfCauchyDischarge.v (this directory as workdir).                    *)
(* ========================================================================= *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs.

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
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInstReal.
Require Import UpReqRDF.
Require Import RMaxSwap.

Import RealInterfaceEnhancedMod.
Local Open Scope Q_scope.

(* ============================================================ *)
(* Section 1. The temperature-entropy discharge family.          *)
(*   The carrier is the global Cauchy Real and the interface is  *)
(*   the global instance; the section quantifies over the sum    *)
(*   carrier S, the sum functional sumf and the interface slots  *)
(*   shared by the witness face and the resolution face.         *)
(* ============================================================ *)
Section FrdTempDischarge.
Notation R := Real.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- the summation face (linearity, extensionality, positivity) ---- *)
Hypothesis frd_sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis frd_sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis frd_sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis frd_sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis frd_sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis frd_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero ->
    forall s : S, real_eq (f s) zero.

Variable base_loss : S -> R.

(* ---- the log bridge slots (positivity-carried logarithm) ---- *)
Hypothesis frd_dist_log_inv_one_inv :
  forall (x : R) (Hx : real_lt zero x) (Hi : real_lt zero (inv_pos x Hx)),
    real_eq (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis frd_dist_log_exp_neg :
  forall u : R, real_eq (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis frd_dist_log_le_linear :
  forall (x : R) (Hx : real_lt zero x), real_le (log x Hx) (req_minus x one).
Hypothesis frd_dist_log_eq_linear :
  forall (x : R) (Hx : real_lt zero x),
    real_eq (log x Hx) (req_minus x one) -> real_eq x one.

(* ---- the partition-function interface (the Z_temp slot) ---- *)
Variable Z_temp : R -> R.
Hypothesis frd_Z_temp_spec : forall (t : R) (Ht : real_lt zero t),
  real_eq (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ---- piece A: explicit temperature entropy; the witness slot and the
   resolution slot are fed with the same hypotheses above. ---- *)
Theorem frd_req_entropy_temp_explicit :
  forall (t : R) (Ht : real_lt zero t),
  real_eq (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss Z_temp
                           frd_Z_temp_spec t Ht)
      (plus (mult (inv_pos t Ht)
                  (UpFirewallReq.fw_et S sumf frd_sum_pos base_loss
                                        Z_temp frd_Z_temp_spec t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t Ht))).
Proof.
  intros t Ht.
  exact (UpReqTempEntropy.req_entropy_temp_explicit
           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos
           base_loss
           frd_dist_log_inv_one_inv frd_dist_log_exp_neg
           Z_temp frd_Z_temp_spec t Ht).
Qed.

(* ---- piece B: the KL temperature decomposition; the normalization
   witness enters as fw_norm, fed with the same slots. ---- *)
Theorem frd_req_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : real_lt zero t2) (t1 : R) (Ht1 : real_lt zero t1),
  real_eq (UpFirewallReq.fw_kl S sumf frd_sum_pos base_loss Z_temp
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
  exact (UpReqTempEntropy.req_relative_entropy_temp_decomp
           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos
           base_loss
           frd_dist_log_inv_one_inv frd_dist_log_exp_neg
           Z_temp frd_Z_temp_spec t2 Ht2
           (UpFirewallReq.fw_bt S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t1 Ht1)
           (UpFirewallReq.fw_bt_pos S sumf frd_sum_pos base_loss
                                    Z_temp frd_Z_temp_spec t1 Ht1)
           (UpFirewallReq.fw_norm S sumf frd_sum_linear frd_sum_pos
                                   base_loss Z_temp frd_Z_temp_spec t1 Ht1)).
Qed.

(* ---- piece C: the strict identity coupling the symmetrized KL mix
   with the inverse-temperature spread. ---- *)
Theorem frd_req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_eq (plus (req_relative_entropy S sumf
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
  exact (UpReqTempEntropy.req_temp_strict_ident2
           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos
           base_loss
           frd_dist_log_inv_one_inv frd_dist_log_exp_neg
           Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2).
Qed.

(* ---- piece D: the recovery-gain identity; the A/B slots are fed by
   the two restatement pieces above. ---- *)
Theorem frd_recovery_entropy_gain :
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_eq (req_minus (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss
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
  exact (UpFirewallReq.req_recovery_entropy_gain
           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec
           frd_req_entropy_temp_explicit
           frd_req_relative_entropy_temp_decomp
           t1 t2 Ht1 Ht2).
Qed.

(* ---- piece E: the dual form; piece C feeds the third slot, so all
   three replacement slots are closed here. ---- *)
Theorem frd_recovery_entropy_gain_alt :
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_eq (req_minus (UpFirewallReq.fw_h S sumf frd_sum_pos base_loss
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
  exact (UpFirewallReq.req_recovery_entropy_gain_alt
           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec
           frd_req_entropy_temp_explicit
           frd_req_relative_entropy_temp_decomp
           frd_req_temp_strict_ident2
           t1 t2 Ht1 Ht2).
Qed.

End FrdTempDischarge.

(* ============================================================ *)
(* Section 2. The norm-of-negation pair over the expression      *)
(*   algebra bxib_E: |(-a)| == |a| as an Id fact and, via the    *)
(*   Id-to-QeqT bridge, in QeqT form for the Q-comparison use    *)
(*   sites. The evaluation of a negation node is negation of the *)
(*   evaluation (iota), so the statement reduces to the Q-layer  *)
(*   abs-opp normal-form lemma.                                  *)
(* ============================================================ *)
Theorem ibw_bnorm_opp : forall a : bxib_E,
  Id (bxib_bnorm (bxib_eopp a)) (bxib_bnorm a).
Proof.
  intro a. unfold bxib_bnorm.
  change (bxib_ev (bxib_eopp a)) with (Qopp (bxib_ev a)).
  exact (bxra_qabs_opp_norm (bxib_ev a)).
Qed.

Lemma ibw_bnorm_opp_qeqt : forall a : bxib_E,
  QeqT (bxib_bnorm (bxib_eopp a)) (bxib_bnorm a).
Proof.
  intro a. apply bxib_qeqT_of_id. apply ibw_bnorm_opp.
Qed.

(* ============================================================ *)
(* Section 3. The absolute-value / metric interface fills on the *)
(*   Cauchy real.                                                *)
(*   |t| <= t + eps under 0 <= t and 0 < eps: the premise        *)
(*   0 <= t is the Or-carrier le, so it destructs constructively *)
(*   into case data (lt branch: |t| == t by abs-pos and the      *)
(*   additive shift t < t + eps; eq branch: |t| == 0 by           *)
(*   abs-compat with t == 0 and t + eps == eps); both branches   *)
(*   enter the disjunction left via lt-le.                       *)
(* ============================================================ *)
Theorem sfcx_abs_le_plus_eps_real :
  forall t : Real, real_le real_zero t ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_abs t) (real_plus t eps).
Proof.
  intros t Hle eps Heps.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heq].
  - (* the lt branch: 0 < t gives |t| == t; 0 < eps shifted by t gives t < t+eps *)
    assert (Habs : real_eq (real_abs t) t)
      by exact (real_abs_pos_req t Hlt).
    assert (Htz : real_lt (real_plus t real_zero) (real_plus t eps))
      by exact (real_lt_plus_translate t real_zero eps Heps).
    assert (Hte : real_lt t (real_plus t eps))
      by exact (RealSetoid.real_lt_id_l t (real_plus t real_zero)
                  (real_plus t eps)
                  (real_eq_sym (real_plus t real_zero) t (real_plus_zero t))
                  Htz).
    assert (Habslt : real_lt (real_abs t) (real_plus t eps))
      by exact (RealSetoid.real_lt_id_l (real_abs t) t
                  (real_plus t eps) Habs Hte).
    apply (RealSetoid.real_lt_le_iff_req (real_abs t) (real_plus t eps)).
    left. exact Habslt.
  - (* the eq branch: t == 0 gives |t| == 0 and t + eps == eps, so 0 < t + eps *)
    assert (Hsym : real_eq t real_zero)
      by exact (real_eq_sym real_zero t Heq).
    assert (Habs0 : real_eq (real_abs t) real_zero)
      by exact (real_eq_trans (real_abs t) (real_abs real_zero) real_zero
                  (RealSetoid.real_eq_abs_compat t real_zero Hsym)
                  real_abs_zero_req).
    assert (Hpt : real_eq (real_plus t eps) (real_plus real_zero eps))
      by exact (RealSetoid.real_eq_plus_compat t eps real_zero eps Hsym
                  (real_eq_refl eps)).
    assert (Hpt2 : real_eq (real_plus t eps) eps)
      by exact (real_eq_trans (real_plus t eps)
                  (real_plus real_zero eps) eps Hpt
                  (real_eq_trans (real_plus real_zero eps)
                     (real_plus eps real_zero) eps
                     (real_plus_comm real_zero eps) (real_plus_zero eps))).
    assert (Hlt1 : real_lt real_zero (real_plus t eps))
      by exact (RealSetoid.real_lt_id_r real_zero eps (real_plus t eps)
                  (real_eq_sym (real_plus t eps) eps Hpt2) Heps).
    assert (Habslt : real_lt (real_abs t) (real_plus t eps))
      by exact (RealSetoid.real_lt_id_l (real_abs t) real_zero
                  (real_plus t eps) Habs0 Hlt1).
    apply (RealSetoid.real_lt_le_iff_req (real_abs t) (real_plus t eps)).
    left. exact Habslt.
Qed.

(* ---- interface slot face of the same bound: the statement through
   the instance projections, definitionally the real face above. ---- *)
Theorem sfcx_abs_le_plus_eps_slot :
  forall t : Real, le zero t ->
  forall eps : Real, lt zero eps ->
  le (abs t) (plus t eps).
Proof. exact sfcx_abs_le_plus_eps_real. Qed.

(* ---- the metric identity: metric a b is definitionally
   |a + (-b)|, so reflexivity of the real equality closes it. ---- *)
Theorem sfcx_metric_abs_real : forall a b : Real,
  real_eq (real_metric a b) (real_abs (real_plus a (real_opp b))).
Proof.
  intros a b.
  exact (real_eq_refl (real_metric a b)).
Qed.

(* ---- interface slot face of the metric identity. ---- *)
Theorem sfcx_metric_abs_slot :
  forall a b : Real,
  req (metric a b) (abs (req_minus a b)).
Proof. exact sfcx_metric_abs_real. Qed.

(* ---- the interface mixin: consumers over the setoid interface can
   hang req_metric_abs on the class; the Real instance installs the
   slot face above (the UpReqSLM plain-slot boilerplate). ---- *)
Class ReqMetricAbs := {
  req_metric_abs : forall a b : Real, req (metric a b) (abs (req_minus a b))
}.

Instance ReqMetricAbsReal : ReqMetricAbs := {
  req_metric_abs := sfcx_metric_abs_slot
}.

(* ---- the strict pin 1 < 1 + 1: shift 0 < 1 by one on the left,
   then transport 1 + 0 to 1 along the equality (an exact-chain, so
   the instance projections reduce by full conversion). ---- *)
Theorem sfcx_lt_one_two_slot :
  lt one (plus one one).
Proof.
  exact (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero)
           (real_plus real_one real_one)
           (real_eq_sym (real_plus real_one real_zero) real_one
                        (real_plus_zero real_one))
           (real_lt_plus_translate real_one real_zero real_one
                                   real_lt_zero_one)).
Qed.

(* ---- extraction check of the two real faces: the extracted terms
   must be pure data (the real_* function chain carries everything). ---- *)
Extraction "sfcx_G3.ml" sfcx_abs_le_plus_eps_real sfcx_metric_abs_real.

(* ============================================================ *)
(* Section 4. The plain-form discharges.                         *)
(* ============================================================ *)

(* ---- the plain right-slot bound b <= r_max a b: given a symmetric
   r_max as an explicit witness, the left-slot plain bound transports
   across the swap by compatibility of the non-strict order with the
   equality; the plain left-slot bound comes from the ReqDiffPlain
   class slot. ---- *)
Theorem qd_r_max_le_r_plain :
  forall (RDP : ReqDiffPlain),
    (forall a b : Real, real_eq (r_max a b) (r_max b a)) ->
    forall a b : Real, real_le b (r_max a b).
Proof.
  intros RDP rcomm a b.
  exact (@rms_le_r_of_ge rcomm (@r_max_ge_plain RDP) a b).
Qed.

(* ---- the endpoint identity sin(arctan 1) == cos(arctan 1): the
   proved instance of the endpoint bridge, fed with the proved
   witness of E(1) == 0 on the unit family. ---- *)
Theorem qd_hsc_a3 :
  real_eq (cauchy_real_sin arctan_one_real)
          (cauchy_real_cos arctan_one_real).
Proof.
  exact (b5b_hsc_theorem b5dS_E_zero_on_unit).
Qed.

(* ---- the general form: the conclusion does not depend on the
   witness x or its hypotheses, so any witness of E(1) == 0 on the
   unit family discharges every premise at once. ---- *)
Theorem qd_b5b_hsc_general :
  forall (x : Real) (Hx : cw_unit x),
    real_lt real_zero x -> real_lt x (real_const 1) ->
    real_eq (real_E x Hx) real_zero ->
    real_eq (cauchy_real_sin arctan_one_real)
            (cauchy_real_cos arctan_one_real).
Proof.
  intros x Hx Hlt0 Hlt1 HEz.
  exact (b5b_hsc_theorem b5dS_E_zero_on_unit).
Qed.

(* ============================================================ *)
(* Assumption audit: one line per theorem of this piece.         *)
(* ============================================================ *)
Print Assumptions frd_req_entropy_temp_explicit.
Print Assumptions frd_req_relative_entropy_temp_decomp.
Print Assumptions frd_req_temp_strict_ident2.
Print Assumptions frd_recovery_entropy_gain.
Print Assumptions frd_recovery_entropy_gain_alt.
Print Assumptions ibw_bnorm_opp.
Print Assumptions ibw_bnorm_opp_qeqt.
Print Assumptions sfcx_abs_le_plus_eps_real.
Print Assumptions sfcx_abs_le_plus_eps_slot.
Print Assumptions sfcx_metric_abs_real.
Print Assumptions sfcx_metric_abs_slot.
Print Assumptions sfcx_lt_one_two_slot.
Print Assumptions qd_r_max_le_r_plain.
Print Assumptions qd_hsc_a3.
Print Assumptions qd_b5b_hsc_general.
