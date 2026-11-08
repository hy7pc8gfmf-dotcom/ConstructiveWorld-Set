(* ConstructiveWorld-Set — finite merge group: log/exp primitive proof lemmas. *)

(** * G05_LogSmall: merged statement family for log/exp primitive proof
      lemmas (series G5, [logd_] prefix).

    Mission.  A finite merge group (members merged verbatim) carrying the
      log/exp primitive proof lemmas of series G5 (the [logd_] family):
      the unconditional request-layer reduction lattice, positivity
      transport, compatibility slots, and the Real-layer unconditional
      closures ([logd_log_compat_real], [logd_log_exp_neg_real],
      [logd_log_inv_one_inv_real], [logd_log_inv_exp_neg_real],
      [logd_log_witness_real], [logd_exp_neg_ext_real]).

    Dependencies.  The library files listed in the Require face below.

    References.  Elementary log/exp identities over constructive reals
      (monotonicity, inverse cancellation, exponential laws).

    Constructivity.  All proofs close by [Qed]; zero admission words; no
      classical axioms; the statement face is carried by the [Set] layer
      (all conclusions are [req]/[lt]/[le] interface values, zero Prop
      leakage).

    Build.  [coqc -native-compiler no -q -Q . "" G05_LogSmall.v] compiles
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
Require Import UpRealLeB.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the
   global Real, and the field names below are bound to the global constants. *)
Notation R := Real.
Notation req := real_eq.
Notation req_refl := real_eq_refl.
Notation req_sym := real_eq_sym.
Notation req_trans := real_eq_trans.
Notation zero := real_zero.
Notation one := real_one.
Notation plus := real_plus.
Notation mult := real_mult.
Notation opp := real_opp.
Notation lt := real_lt.
Notation le := real_le.
Notation req_plus_compat := RealSetoid.real_eq_plus_compat_adapt.
Notation req_opp_compat := RealSetoid.real_eq_opp_compat.
Notation req_lt_compat := RealSetoid.real_lt_compat.
Notation plus_assoc := real_plus_assoc.
Notation plus_comm := real_plus_comm.
Notation plus_zero := real_plus_zero.
Notation plus_opp := real_plus_opp.
Notation mult_comm := real_mult_comm.
Notation le_antisym := real_le_antisym.
Notation lt_le_iff := RealSetoid.real_lt_le_iff_req.
Notation le_id_r := RealSetoid.real_le_id_r.
Notation inv_pos := real_inv_pos.
Notation inv_pos_correct := real_inv_pos_correct.
Notation one_pos := real_lt_zero_one.
Notation mult_positive := real_mult_positive.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.
Notation exp_neg_plus := real_exp_neg_plus.
Notation exp_neg_le_decr := real_exp_neg_le_decr.
Notation log := real_log.
Notation log_mult := real_log_mult.
Notation log_one := real_log_one.
Notation log_inv := real_log_inv.
Notation log_inv_log := real_log_inv_log.
Notation exp_neg_log_inv := real_exp_neg_log_inv.

(* ============================================================ *)
(* Part 0: req-algebra small pieces (pure derivations from the interface fields,
   zero destruct) *)
(* ============================================================ *)

(* P0-a: req implies le (the right branch of lt_le_iff); a one-way lifting
   primitive at the req layer — like real_le -> real_le_b it is one-way only,
   since the reverse Or-form closure is not provable constructively *)
Lemma logd_req_to_le : forall 
    (x y : R), req x y -> le x y.
Proof.
  intros x y H.
  exact (lt_le_iff x y (inr H)).
Qed.

(* P0-b: the additive left zero (zero + a ≡ a; the right-zero form of plus_zero
   reached by a commutativity swap) *)
Lemma logd_req_plus_zero_l : forall 
    (a : R), req (plus zero a) a.
Proof.
  intros a.
  apply (req_trans (plus zero a) (plus a zero) a).
  - exact (plus_comm zero a).
  - exact (plus_zero a).
Qed.

(* P0-c: opp is an involution (opp (opp a) ≡ a; two instances of plus_opp
   chained through assoc/comm/zero) *)
Lemma logd_req_opp_opp : forall 
    (a : R), req (opp (opp a)) a.
Proof.
  intros a.
  assert (H1 : req (plus (opp a) (opp (opp a))) zero) by exact (plus_opp (opp a)).
  assert (H2 : req (plus a (opp a)) zero) by exact (plus_opp a).
  apply (req_trans (opp (opp a)) (plus zero (opp (opp a))) a).
  - apply req_sym. exact (logd_req_plus_zero_l  (opp (opp a))).
  - apply (req_trans (plus zero (opp (opp a)))
                     (plus (plus a (opp a)) (opp (opp a))) a).
    + apply (req_plus_compat zero (plus a (opp a)) (opp (opp a)) (opp (opp a))).
      * apply req_sym. exact H2.
      * apply req_refl.
    + apply (req_trans (plus (plus a (opp a)) (opp (opp a)))
                       (plus a (plus (opp a) (opp (opp a)))) a).
      * apply req_sym. exact (plus_assoc a (opp a) (opp (opp a))).
      * apply (req_trans (plus a (plus (opp a) (opp (opp a))))
                         (plus a zero) a).
        -- apply (req_plus_compat a a (plus (opp a) (opp (opp a))) zero
                    (req_refl a) H1).
        -- exact (plus_zero a).
Qed.

(* P0-d: right-zero elimination for addition (a + b ≡ zero implies b ≡ opp a) *)
Lemma logd_req_plus_zero_r : forall 
    (a b : R), req (plus a b) zero -> req b (opp a).
Proof.
  intros a b H.
  apply (req_trans b (plus zero b) (opp a)).
  - apply req_sym. exact (logd_req_plus_zero_l  b).
  - apply (req_trans (plus zero b) (plus (plus (opp a) a) b) (opp a)).
    + apply (req_plus_compat zero (plus (opp a) a) b b).
      * apply req_sym.
        apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
        -- exact (plus_comm (opp a) a).
        -- exact (plus_opp a).
      * apply req_refl.
    + apply (req_trans (plus (plus (opp a) a) b)
                       (plus (opp a) (plus a b)) (opp a)).
      * apply req_sym. exact (plus_assoc (opp a) a b).
      * apply (req_trans (plus (opp a) (plus a b))
                         (plus (opp a) zero) (opp a)).
        -- apply (req_plus_compat (opp a) (opp a) (plus a b) zero
                    (req_refl (opp a)) H).
        -- exact (plus_zero (opp a)).
Qed.

(* ============================================================ *)
(* Part 1: interface-layer primitives (generic RIS; the supply slots of the
   conditional forms made explicit) *)
(* ============================================================ *)

(* P1-a: exp_neg is compatible with req — an unconditional interface-layer
   theorem (covering the whole req_exp_neg_ext family, UpSigMigrate:521).
   Route: req lifts to le in both directions through the right branch of
   lt_le_iff, exp_neg_le_decr yields one inequality per direction, and
   le_antisym closes. Interface fields only, no extra supply. *)
Lemma logd_exp_neg_ext : forall 
    (x y : R), req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply (le_antisym (exp_neg x) (exp_neg y)).
  - apply exp_neg_le_decr.
    apply (logd_req_to_le  y x).
    exact (req_sym x y Hxy).
  - apply exp_neg_le_decr.
    apply (logd_req_to_le  x y).
    exact Hxy.
Qed.

(* P1-b: transporting strict positivity along req (the zero-point specialization
   of req_lt_compat) *)
Lemma logd_lt_req_transport : forall 
    (a b : R), req a b -> lt zero a -> lt zero b.
Proof.
  intros a b H Hlt.
  exact (req_lt_compat zero zero a b (req_refl zero) H Hlt).
Qed.

(* P1-c: pointwise positivity transport (the Real-instance form of
   expf_pos@UpReqFEPAttn:264 — a conditional proof whose premises are
   expf_agree (req (expf x) (exp_pos_fn_setoid x)) plus the positivity of
   exp_pos_fn_setoid (pushed directly from the exp_neg family fields).
   expf_agree itself is the specification of the abstract expf operator — a
   slot, not provable.) *)
Lemma logd_pos_of_agree : forall 
    (ef tgt : R -> R),
  (forall x : R, req (ef x) (tgt x)) ->
  (forall x : R, lt zero (tgt x)) ->
  forall x : R, lt zero (ef x).
Proof.
  intros ef tgt Hagree Hpos x.
  apply (logd_lt_req_transport  (tgt x) (ef x)).
  - apply req_sym. exact (Hagree x).
  - exact (Hpos x).
Qed.

(* P2-a: log compatibility from a single monotone le slot (the same position as
   log_req_compat in UpReqU2, rebuilt independently under the logd_ prefix; req
   lifts to le in both directions and le_antisym closes) *)
Lemma logd_log_compat_of_mono :
  
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    le x y -> le (log x Hx) (log y Hy)) ->
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros Hmono x y Hx Hy Hxy.
  apply (le_antisym (log x Hx) (log y Hy)).
  - apply (Hmono x y Hx Hy).
    exact (lt_le_iff x y (inr Hxy)).
  - apply (Hmono y x Hy Hx).
    exact (lt_le_iff y x (inr (req_sym x y Hxy))).
Qed.

(* P2-b: log(1/x) ≡ −log x from a log-compatibility slot (decomposition by
   log_mult, compatibility transport to log one, and additive zero elimination;
   the reduction piece of the same-named slots in UpReqFEPAttn/UpReqDist) *)
Lemma logd_log_inv_one_inv_of_compat :
  
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)) ->
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros Hcompat x Hx Hi.
  assert (Hponelt : lt zero one) by exact one_pos.
  assert (Hprod : req (mult (inv_pos x Hx) x) one).
  { apply (req_trans (mult (inv_pos x Hx) x) (mult x (inv_pos x Hx)) one).
    - exact (mult_comm (inv_pos x Hx) x).
    - exact (inv_pos_correct x Hx). }
  assert (Hlog1 : req (log (mult (inv_pos x Hx) x)
                         (mult_positive (inv_pos x Hx) x Hi Hx)) zero).
  { apply (req_trans (log (mult (inv_pos x Hx) x)
                       (mult_positive (inv_pos x Hx) x Hi Hx))
                     (log one one_pos) zero).
    - exact (Hcompat (mult (inv_pos x Hx) x) one
               (mult_positive (inv_pos x Hx) x Hi Hx) one_pos Hprod).
    - exact (log_one one_pos). }
  assert (Hdec : req (plus (log (inv_pos x Hx) Hi) (log x Hx)) zero).
  { exact (req_trans (plus (log (inv_pos x Hx) Hi) (log x Hx))
                     (log (mult (inv_pos x Hx) x)
                        (mult_positive (inv_pos x Hx) x Hi Hx)) zero
                     (req_sym (log (mult (inv_pos x Hx) x)
                            (mult_positive (inv_pos x Hx) x Hi Hx))
                        (plus (log (inv_pos x Hx) Hi) (log x Hx))
                        (log_mult (inv_pos x Hx) x Hi Hx))
                     Hlog1). }
  apply (req_sym (opp (log x Hx)) (log (inv_pos x Hx) Hi)).
  apply (req_trans (opp (log x Hx)) (opp (opp (log (inv_pos x Hx) Hi)))
                   (log (inv_pos x Hx) Hi)).
  - apply req_sym.
    apply req_opp_compat.
    apply req_sym.
    exact (logd_req_plus_zero_r  (log (inv_pos x Hx) Hi) (log x Hx) Hdec).
  - exact (logd_req_opp_opp  (log (inv_pos x Hx) Hi)).
Qed.

(* P2-c: log_inv∘exp_neg ≡ id from the log∘exp_neg ≡ −id slot (a log_inv_log
   conversion plus the opp involution; the forward direction of the mutual
   reduction between the two slots) *)
Lemma logd_log_inv_exp_neg_of_log_exp_neg :
  
  (forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u)) ->
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intros Hlen x.
  apply (req_trans (log_inv (exp_neg x) (exp_neg_pos x))
                   (opp (log (exp_neg x) (exp_neg_pos x))) x).
  - exact (log_inv_log (exp_neg x) (exp_neg_pos x)).
  - apply (req_trans (opp (log (exp_neg x) (exp_neg_pos x)))
                     (opp (opp x)) x).
    + apply req_opp_compat. exact (Hlen x).
    + exact (logd_req_opp_opp  x).
Qed.

(* P2-d: log∘exp_neg ≡ −id from the log_inv∘exp_neg ≡ id slot (symmetric to
   P2-c; the two slots imply each other, and either one serves as the external
   root supply — the Real-layer root is real_log_exp_neg@42231) *)
Lemma logd_log_exp_neg_of_log_inv_exp_neg :
  
  (forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) ->
  forall x : R, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intros Hinv x.
  apply (req_sym (opp x) (log (exp_neg x) (exp_neg_pos x))).
  apply (req_trans (opp x) (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                   (log (exp_neg x) (exp_neg_pos x))).
  - apply req_opp_compat.
    apply (req_trans x (log_inv (exp_neg x) (exp_neg_pos x))
                      (opp (log (exp_neg x) (exp_neg_pos x)))).
    + apply req_sym. exact (Hinv x).
    + exact (log_inv_log (exp_neg x) (exp_neg_pos x)).
  - exact (logd_req_opp_opp  (log (exp_neg x) (exp_neg_pos x))).
Qed.

(* ============================================================ *)
(* Part 2: unconditional Real-layer closures (the template-2 slot shapes; the
   root primitives provided directly by CW_ConstructiveWorld_219) *)
(* ============================================================ *)

(* B1-a: req compatibility in the log argument (the monotone-chain shape:
   real_log_le_mono@CW_ConstructiveWorld_219:112106 feeds P2-a directly; the
   family covers 15 slots such as log_req_compat) *)
Lemma logd_log_compat_real : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (logd_log_compat_of_mono
           (fun (a b : Real) (Ha : lt zero a) (Hb : lt zero b)
              (Hab : le a b) => real_log_le_mono a b Ha Hb Hab)).
  exact Hxy.
Qed.

(* B1-b: the same statement via the second route (provided directly by
   real_log_wd@CW_ConstructiveWorld_219:42277; both routes reach the same
   conclusion and the dual forms coexist) *)
Lemma logd_log_compat_real_wd : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (real_log_wd x y Hx Hy Hxy).
Qed.

(* B2: log(e^{-x}) ≡ −x (provided verbatim by
   real_log_exp_neg@CW_ConstructiveWorld_219:42231; the family
   log_exp_neg/dist_log_exp_neg/b_log_exp_neg/req_log_exp_neg totals 6 slots;
   this is the Real-layer root supply, the external root for P2-c/d) *)
Lemma logd_log_exp_neg_real : forall (x : Real),
  req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (real_log_exp_neg x).
Qed.

(* B3: log(1/x) ≡ −log x (P2-b assembled over B1; the family
   log_inv_one_inv (2) / dist_log_inv_one_inv (3) totals 5 slots; the same
   shape appears as kl_log_inv@574 in cw_log form, and this piece is assembled
   independently in the req slot form) *)
Lemma logd_log_inv_one_inv_real : forall (x : Real) (Hx : lt zero x)
    (Hi : lt zero (inv_pos x Hx)),
  req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_of_compat
           logd_log_compat_real x Hx Hi).
Qed.

(* B4: log_inv(e^{-x}) ≡ x (P2-c assembled over B2; the family
   log_inv_exp_neg_req (5) / ralt_log_inv_exp_neg_req /
   rdl_log_inv_exp_neg_req totals 7 slots) *)
Lemma logd_log_inv_exp_neg_real : forall (x : Real),
  req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  apply (logd_log_inv_exp_neg_of_log_exp_neg).
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* B5: log is witness-independent (converting between two positivity witnesses
   of the same point into the req form; the same-position dual form is
   log_req_witness_compat in UpReqU2; the Real-layer root is
   real_log_proof_irrel@42291) *)
Lemma logd_log_witness_real : forall (x : Real) (Hx Hx' : lt zero x),
  req (log x Hx) (log x Hx').
Proof.
  intros x Hx Hx'.
  exact (logd_log_compat_real x x Hx Hx' (req_refl x)).
Qed.

(* B6: the Real instantiation of exp_neg extensionality (a template-2
   specialization of P1-a, matching the UpSigMigrate:521 slot shape pointwise) *)
Lemma logd_exp_neg_ext_real : forall (x y : Real), req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y H.
  exact (logd_exp_neg_ext x y H).
Qed.

(* ============================================================ *)
(* closure audit: [Print Assumptions] on every main proof piece *)
(* ============================================================ *)
Print Assumptions logd_exp_neg_ext.
Print Assumptions logd_pos_of_agree.
Print Assumptions logd_log_compat_of_mono.
Print Assumptions logd_log_inv_one_inv_of_compat.
Print Assumptions logd_log_inv_exp_neg_of_log_exp_neg.
Print Assumptions logd_log_exp_neg_of_log_inv_exp_neg.
Print Assumptions logd_log_compat_real.
Print Assumptions logd_log_compat_real_wd.
Print Assumptions logd_log_exp_neg_real.
Print Assumptions logd_log_inv_one_inv_real.
Print Assumptions logd_log_inv_exp_neg_real.
Print Assumptions logd_log_witness_real.
Print Assumptions logd_exp_neg_ext_real.

(* ======== G05_LogSmall member piece: UpReqLogLinD (merged verbatim, with its own Requires) ======== *)
(* ============================================================ *)
(* UpReqLogLinD.v — discharging the four same-shaped declaration sites of the *)
(*   log_le_linear interface slot (the gap pieces of G08_Gibbs.v Part A/C *)
(*   reused across modules) *)
(* ------------------------------------------------------------------ *)
(*   site 1  UpReqU2.v          L313  Hypothesis log_le_linear        *)
(*   site 2  UpReqFEPAttn.v     L90   Hypothesis log_le_linear        *)
(*   site 3  UpReqTempEntropy.v L60   Hypothesis dist_log_le_linear   *)
(*   site 4  UpFirewallReq.v    L101  Variable  dist_log_le_linear    *)
(*   the four slot statements are verbatim identical: *)
(*   forall x Hx, le (log x Hx) (req_minus x one). *)
(* ------------------------------------------------------------------ *)
(*   the slots conclude with the interface le (the le field of the *)
(*   RealEnhancedReal instance := real_le, the Or encoding at *)
(*   CW_ConstructiveWorld_219:41130); the B-form engine real_log_le_linear_B *)
(*   (UpRealLeB:535) concludes with real_le_b (the Bishop form). The reverse *)
(*   bridge real_le_b -> real_le is the exact closure of the Or form and is not *)
(*   provable constructively (the closing note of UpRealLeB records the same *)
(*   verdict). Accordingly, the four site proof pieces are uniformly lifted to *)
(*   "Real-instantiated theorems": the order is given as real_le_b with the *)
(*   premise positions supplied directly by the engine; should a later interface *)
(*   extension add le_b-form premise positions, the four given forms of this *)
(*   file connect directly (zero changes). *)
(* ------------------------------------------------------------------ *)
(*   site 1: w2_gibbs_eq @UpReqU2:477 -> req_gibbs_equality *)
(*           @UpReqDist:2148 (slot + log_eq_linear dual premise positions). *)
(*   site 2: req_attention_minimizes_free_energy_unique @UpReqFEPAttn: *)
(*           211 -> req_min_free_energy_is_boltzmann (the <= branch, premise *)
(*           position) + req_free_energy_min_unique (the uniqueness branch, *)
(*           slot + eq_linear dual positions). *)
(*   site 3: pieces 2/4 (L554/L592) use req_gibbs_inequality (premise *)
(*           position); piece 5 (L593) uses req_gibbs_equality (slot + *)
(*           eq_linear dual positions). *)
(*   site 4: pieces 5/6 (L312/L378) use @req_gibbs_inequality (premise *)
(*           position, the temperature pair (fw_bt t1, fw_bt t2)). *)
(* remaining gaps (reported per site, with the fallbacks actually taken): *)
(*   a. the downstream end pieces of all four sites (gibbs_equality / *)
(*      min_energy_unique) share two missing pieces that block their full Real *)
(*      replay; this file does not overstep: *)
(*      (i)  the downstream KL term has the p·(log p−log q) shape *)
(*           (req2_rel_ent @UpReqAlign2:111 / req_relative_entropy, same *)
(*           shape); its identity with the canonical real_kl_term form needs the *)
(*           log inverse cancellation (log(inv p)==−log p), which *)
(*           CW_ConstructiveWorld_219 does not provide; *)
(*      (ii) the Bishop counterpart of req-layer fsum_zero_nonneg (Σd==0 plus *)
(*           pointwise 0 ≤_B d implies d s==0) needs the In-machinery partial-sum *)
(*           machinery, which Part A/C do not provide. *)
(*   b. for the abstract-sumf downstream theorems, the @-instantiation route *)
(*      hits the same verdict as the ZPosD tier: real_list_sum_pos carries a *)
(*      nonempty-datum premise (CW_ConstructiveWorld_219:41666) and cannot feed *)
(*      the abstract fsum_pos premise position (the δ premise shape does not *)
(*      match) — the site 3/4 temperature pairs are therefore replayed concretely *)
(*      in the BTReal section of this file. *)
(*   c. the nonempty-datum premise follows the existing signature shape *)
(*      (zposd_Z_pos @G12_ZPosFam:82, "Not (enum = nil)" as the base-Set version *)
(*      of Not; the same position as CW_ConstructiveWorld_219 real_list_sum_pos); *)
(*      no stronger claim is made. *)
(* ------------------------------------------------------------------ *)
(* provided: *)
(*   [shared foundation] lld_lt_zero_sub_r / lld_le_b_zero_sub — the subtractive *)
(*     positivity of lt plus the Bishop-order subtractive lifting (2 extension *)
(*     pieces beyond Part A). *)
(*   [four-site given pieces] lld_{u2,fep,tempent,fw}_log_le_linear_B — the *)
(*     Real-instantiated Bishop forms of the four site slots (supplied directly *)
(*     by the engine; four isomorphic instances). *)
(*   [site 1] lld_u2_gibbs_eq_step1_B — the first-step branch of *)
(*     req_gibbs_equality (Hd_nonneg: 0 ≤ d(s) pointwise) in Bishop form, given *)
(*     in one step by gibbsd_gibbs_pointwise_B. *)
(*   [site 2] the FEPReal section: the Real-concrete forms of the *)
(*     softmax/boltzmann carrier pair (the five Definitions base/invT/Zf/ *)
(*     softmax/boltz, pointwise isomorphic to the site premise positions, in *)
(*     datum form) + 3 pointwise positivity pieces + *)
(*     lld_fep_softmax_boltz_pointwise_B (the paradigm instantiation of piece 4's *)
(*     main-theorem carrier pair). *)
(*   [site 3] the BTReal section temperature Boltzmann family (the concrete *)
(*     forms lld_btz/lld_bt + positivity/normalization) + *)
(*     lld_tempent_kl_nonneg_B (the Bishop form of the L554 branch) + *)
(*     lld_tempent_entropy_neg_sum_B (the eq companion piece at the *)
(*     real_list_sum layer for the req_entropy_neg_sum use site). *)
(*   [site 4] lld_fw_kl_boltz_pair_nonneg_B — the Bishop form of the pieces 5/6 *)
(*     Hkl/Hkl21 branches (the req_gibbs_inequality temperature pair). *)
(*   / le_b_id_l / minus_flip / le_b_mult_pos_r) + the six Part C sum-layer *)
(*   machinery pieces are all reusable downstream per this line of work; the Part *)
(*   D template D0 provided-forms replay verbatim at the four site given pieces. *)
(* constraints: zero Prop at the Set layer (real_le_b / real_eq / real_lt are *)
(*   all Set-valued; the datum premise is listed separately in the zposd *)
(*   convention); everything closes by Qed; zero axioms; no existing file *)
(*   modified; the lld_ prefix guards against name clashes library-wide (grep *)
(*   checked: zero hits before creation). *)
(* ============================================================ *)

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
Require Import G08_Gibbs.
Require Import UpReqU2.
Require Import UpReqFEPAttn.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part H: the shared foundation layer (2 extension pieces beyond Part A) *)
(* ============================================================ *)

(* H1: subtractive positivity of lt: a < c implies 0 < c − a (the subtractive
   entry point for the Bishop order) *)
Lemma lld_lt_zero_sub_r : forall a c : Real,
  real_lt a c -> real_lt real_zero (real_plus c (real_opp a)).
Proof.
  intros a c Hac.
  apply (RealSetoid.real_lt_compat
           (real_plus (real_opp a) a) real_zero
           (real_plus (real_opp a) c) (real_plus c (real_opp a))).
  - apply (real_eq_trans (real_plus (real_opp a) a)
                         (real_plus a (real_opp a)) real_zero).
    + exact (real_plus_comm (real_opp a) a).
    + exact (real_plus_opp a).
  - exact (real_plus_comm (real_opp a) c).
  - exact (real_lt_plus_translate (real_opp a) a c Hac).
Qed.

(* H2: the Bishop-order subtractive lifting: a ≤_B b implies 0 ≤_B b − a *)
(*   (the engine position for the site 1 step1 branch; closed by a swap_mid +
   plus_zero conversion) *)
Lemma lld_le_b_zero_sub : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H. unfold real_le_b. intros eps Heps.
  apply (RealSetoid.real_lt_compat
           real_zero real_zero
           (real_plus (real_plus b eps) (real_opp a))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply real_eq_refl.
  - exact (real_eq_trans
             (real_plus (real_plus b eps) (real_opp a))
             (real_plus (real_plus b eps) (real_plus (real_opp a) real_zero))
             (real_plus (real_plus b (real_opp a)) eps)
             (RealSetoid.real_eq_plus_compat
                (real_plus b eps) (real_opp a)
                (real_plus b eps) (real_plus (real_opp a) real_zero)
                (real_eq_refl (real_plus b eps))
                (real_eq_sym (real_plus (real_opp a) real_zero)
                             (real_opp a)
                             (real_plus_zero (real_opp a))))
             (real_eq_trans
                (real_plus (real_plus b eps)
                           (real_plus (real_opp a) real_zero))
                (real_plus (real_plus b (real_opp a))
                           (real_plus eps real_zero))
                (real_plus (real_plus b (real_opp a)) eps)
                (real_plus_swap_mid b eps (real_opp a) real_zero)
                (RealSetoid.real_eq_plus_compat
                   (real_plus b (real_opp a)) (real_plus eps real_zero)
                   (real_plus b (real_opp a)) eps
                   (real_eq_refl (real_plus b (real_opp a)))
                   (real_plus_zero eps)))).
  - exact (lld_lt_zero_sub_r a (real_plus b eps) (H eps Heps)).
Qed.

(* ============================================================ *)
(* Part S: the four-site given pieces (the Real-instantiated Bishop forms of the
   slots; four isomorphic instances) *)
(*   the four slot statements are verbatim identical (the coordinates read from
   the sources), and the given forms are isomorphic — *)
(* ============================================================ *)

(* site 1 (UpReqU2.v L313, log_le_linear): the given form *)
Lemma lld_u2_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* site 2 (UpReqFEPAttn.v L90, log_le_linear): the given form *)
Lemma lld_fep_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* site 3 (UpReqTempEntropy.v L60, dist_log_le_linear): the given form *)
Lemma lld_tempent_log_le_linear_B :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* site 4 (UpFirewallReq.v L101, dist_log_le_linear): the given form *)
Lemma lld_fw_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* ============================================================ *)
(* Part U2: the downstream first-step branch of site 1 (UpReqU2.v L313) *)
(*   the slot use site w2_gibbs_eq (UpReqU2:477) -> the first step of *)
(*   req_gibbs_equality (UpReqDist:2148), Hd_nonneg: 0 ≤ d(s) pointwise (the *)
(*   req le form) — the Bishop form lifts via gibbsd_gibbs_pointwise_B (the *)
(*   Part D template D0) plus H2. *)
(*   the blocking verdicts for the final replay are in the header note a(i)(ii). *)
(* ============================================================ *)

Lemma lld_u2_gibbs_eq_step1_B : forall (X : Type) (p q : X -> Real) (s : X)
  (Hps : real_lt real_zero (p s)) (Hqs : real_lt real_zero (q s)),
  real_le_b real_zero
    (real_plus (real_kl_term (p s) (q s) Hps Hqs)
               (real_opp (real_plus (p s) (real_opp (q s))))).
Proof.
  intros X p q s Hps Hqs.
  apply lld_le_b_zero_sub.
  exact (gibbsd_gibbs_pointwise_B X p q s Hps Hqs).
Qed.

(* ============================================================ *)
(* Part FEP: site 2 (UpReqFEPAttn.v L90), the concrete form of the carrier pair *)
(*   the site section premises (base/invT/Zf/softmax_z/boltz_z, *)
(*   UpReqFEPAttn:107-121) are isomorphic pointwise over Real; sumf := *)
(*   real_list_sum (datum form, the zposd convention); exp_pos_fn_setoid y == *)
(*   exp_neg (opp y) (CW_ConstructiveWorld_219:66191) — the exp term of the site *)
(*   softmax lands pointwise via base := opp z (transparent in delta). *)
(* ============================================================ *)

Section FEPReal.

Variable X : Set.
Variable lX : list X.
Variable lX_ne : lX <> nil.
Variable zz : X -> Real.
Variable TT : Real.
Variable TT_pos : real_lt real_zero TT.

Definition lld_fep_base (s : X) : Real := real_opp (zz s).
Definition lld_fep_invT : Real := real_inv_pos TT TT_pos.
Definition lld_fep_Zf : Real :=
  real_list_sum X (fun s : X => real_exp_neg (real_mult lld_fep_invT (zz s))) lX.

(* helper 1: the termwise positivity of the Boltzmann factors (the sum_pos branch
   of the site Zf_pos) *)
Lemma lld_fep_boltz_factor_pos : forall s : X,
  real_lt real_zero (real_exp_neg (real_mult lld_fep_invT (zz s))).
Proof.
  intro s. exact (real_exp_neg_pos (real_mult lld_fep_invT (zz s))).
Qed.

(* the positivity of the partition function (the datum form of the site Zf_pos) *)
Lemma lld_fep_Zf_pos : real_lt real_zero lld_fep_Zf.
Proof.
  exact (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult lld_fep_invT (zz s))) lX
           lld_fep_boltz_factor_pos lX_ne).
Qed.

(* softmax_z / boltz_z, pointwise isomorphic (the site UpReqFEPAttn:118/120) *)
Definition lld_fep_softmax (s : X) : Real :=
  real_mult (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
            (real_inv_pos lld_fep_Zf lld_fep_Zf_pos).
Definition lld_fep_boltz (s : X) : Real :=
  real_mult (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
            (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s))).

Lemma lld_fep_softmax_pos : forall s : X, real_lt real_zero (lld_fep_softmax s).
Proof.
  intro s.
  exact (real_mult_positive
           (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg_pos (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos_pos lld_fep_Zf lld_fep_Zf_pos)).
Qed.

Lemma lld_fep_boltz_pos : forall s : X, real_lt real_zero (lld_fep_boltz s).
Proof.
  intro s.
  exact (real_mult_positive
           (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg_pos (real_mult lld_fep_invT (lld_fep_base s)))).
Qed.

(* the paradigm instantiation of the main-theorem carrier pair: the pointwise *)
(* Gibbs tangent Bishop form of piece 4 (the softmax/boltz pair of *)
(* req_attention_minimizes_free_energy_unique) — the Part D template D0 *)
(* assembled with @ fully explicit over the site 2 carrier. For the blocking of *)
(* the full <=-branch / uniqueness-branch replay see header note a. *)
Lemma lld_fep_softmax_boltz_pointwise_B : forall s : X,
  real_le_b (real_plus (lld_fep_softmax s) (real_opp (lld_fep_boltz s)))
            (real_kl_term (lld_fep_softmax s) (lld_fep_boltz s)
                          (lld_fep_softmax_pos s) (lld_fep_boltz_pos s)).
Proof.
  intro s.
  exact (gibbsd_gibbs_pointwise_B X lld_fep_softmax lld_fep_boltz s
           (lld_fep_softmax_pos s) (lld_fep_boltz_pos s)).
Qed.

End FEPReal.

(* ============================================================ *)
(* Part BT: the temperature Boltzmann family shared by sites 3/4 (Real concrete *)
(*   forms) *)
(*   the real_list_sum concrete forms of site 3 tB (UpReqTempEntropy:71) and *)
(*   site 4 fw_bt (UpFirewallReq:105) (the Real replay of *)
(*   reqd_boltzmann_dist_temp; the abstract fsum_pos premise position does not *)
(*   match in delta, so the replay is concrete along the ZPosD precedent). *)
(* ============================================================ *)

Section BTReal.

Variable X : Set.
Variable lX : list X.
Variable lX_ne : lX <> nil.
Variable be : X -> Real.

(* the temperature partition function Z_t (the concrete form of the site
   Z_temp_spec) *)
Definition lld_btz (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_list_sum X (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s))) lX.

Lemma lld_btz_pos : forall (t : Real) (Ht : real_lt real_zero t),
  real_lt real_zero (lld_btz t Ht).
Proof.
  intros t Ht.
  exact (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s))) lX
           (fun s : X => real_exp_neg_pos (real_mult (real_inv_pos t Ht) (be s)))
           lX_ne).
Qed.

(* the temperature Boltzmann distribution (the concrete form of the sites
   tB / fw_bt) *)
Definition lld_bt (t : Real) (Ht : real_lt real_zero t) (s : X) : Real :=
  real_mult (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
            (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht)).

Lemma lld_bt_pos : forall (t : Real) (Ht : real_lt real_zero t) (s : X),
  real_lt real_zero (lld_bt t Ht s).
Proof.
  intros t Ht s.
  exact (real_mult_positive
           (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
           (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
           (real_exp_neg_pos (real_mult (real_inv_pos t Ht) (be s)))
           (real_inv_pos_pos (lld_btz t Ht) (lld_btz_pos t Ht))).
Qed.

(* normalization (the concrete form of the sites tBnorm / fw_norm; the linear
   factor pulled out, closed by the inverse) *)
Lemma lld_bt_norm : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq (real_list_sum X (lld_bt t Ht) lX) real_one.
Proof.
  intros t Ht.
  apply (real_eq_trans
           (real_list_sum X (lld_bt t Ht) lX)
           (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                      (lld_btz t Ht))
           real_one).
  - apply (real_eq_trans
             (real_list_sum X (lld_bt t Ht) lX)
             (real_list_sum X
                (fun s : X => real_mult (real_inv_pos (lld_btz t Ht)
                                                          (lld_btz_pos t Ht))
                                        (real_exp_neg
                                           (real_mult (real_inv_pos t Ht)
                                                      (be s)))) lX)
             (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                        (lld_btz t Ht))).
    + apply real_list_sum_ext. intro s.
      exact (real_mult_comm (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
                            (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))).
    + exact (real_list_sum_linear X
               (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
               (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
               lX).
  - apply (real_eq_trans
             (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                        (lld_btz t Ht))
             (real_mult (lld_btz t Ht)
                        (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht)))
             real_one).
    + exact (real_mult_comm (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                            (lld_btz t Ht)).
    + exact (real_inv_pos_correct (lld_btz t Ht) (lld_btz_pos t Ht)).
Qed.

(* ============================================================ *)
(* the site 3 piece: the Real-instantiated Bishop form of the L554 branch *)
(*   (req_gibbs_inequality p (tB t), the slot use site of pieces 2/4 of *)
(*   UpReqTempEntropy) — the Part D template D1 assembled with @ fully explicit *)
(*   over the site 3 use pair (p, lld_bt t). *)
(* ============================================================ *)

Lemma lld_tempent_kl_nonneg_B : forall (t : Real) (Ht : real_lt real_zero t)
  (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
  (Hnormp : real_eq (real_list_sum X p lX) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (lld_bt t Ht s)
                     (Hp s) (lld_bt_pos t Ht s)) lX).
Proof.
  intros t Ht p Hp Hnormp.
  exact (gibbsd_gibbs_inequality X lX p (lld_bt t Ht)
           Hp (lld_bt_pos t Ht) Hnormp (lld_bt_norm t Ht)).
Qed.

(* the site 3 eq companion: the real_list_sum-layer counterpart of *)
(*   req_entropy_neg_sum (UpReqDist:1947, the use site of the site entropy chain) *)
(*   — Σ p·log p == −Σ p·(−log p). *)
Lemma lld_tempent_entropy_neg_sum_B : forall (p : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X (fun s : X => real_mult (p s) (real_log (p s) (Hp s))) lX)
          (real_opp (real_list_sum X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) lX)).
Proof.
  intros p Hp.
  apply (real_eq_trans
           (real_list_sum X (fun s : X => real_mult (p s) (real_log (p s) (Hp s))) lX)
           (real_list_sum X
              (fun s : X => real_opp (real_mult (p s)
                                                (real_opp (real_log (p s) (Hp s))))) lX)
           (real_opp (real_list_sum X
              (fun s : X => real_mult (p s)
                                      (real_opp (real_log (p s) (Hp s)))) lX))).
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans (real_mult (p s) (real_log (p s) (Hp s)))
                         (real_opp (real_opp (real_mult (p s) (real_log (p s) (Hp s)))))
                         (real_opp (real_mult (p s) (real_opp (real_log (p s) (Hp s)))))).
    + exact (real_eq_sym (real_opp (real_opp (real_mult (p s) (real_log (p s) (Hp s)))))
                         (real_mult (p s) (real_log (p s) (Hp s)))
                         (real_opp_opp (real_mult (p s) (real_log (p s) (Hp s))))).
    + exact (RealSetoid.real_eq_opp_compat
               (real_opp (real_mult (p s) (real_log (p s) (Hp s))))
               (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
               (real_opp_mult (p s) (real_log (p s) (Hp s)))).
  - exact (real_list_sum_opp X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) lX).
Qed.

(* ============================================================ *)
(* the site 4 piece: the Real-instantiated Bishop form of the L312/L378 branches *)
(*   (@req_gibbs_inequality (fw_bt t1) (fw_bt t2), the slot use sites of piece 5 *)
(*   Hkl / piece 6 Hkl21) — the Part D template D1 assembled with @ fully *)
(*   explicit over the site 4 temperature pair. *)
(* ============================================================ *)

Lemma lld_fw_kl_boltz_pair_nonneg_B : forall (t1 t2 : Real)
  (Ht1 : real_lt real_zero t1) (Ht2 : real_lt real_zero t2),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (lld_bt t1 Ht1 s) (lld_bt t2 Ht2 s)
                     (lld_bt_pos t1 Ht1 s) (lld_bt_pos t2 Ht2 s)) lX).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (gibbsd_gibbs_inequality X lX (lld_bt t1 Ht1) (lld_bt t2 Ht2)
           (lld_bt_pos t1 Ht1) (lld_bt_pos t2 Ht2)
           (lld_bt_norm t1 Ht1) (lld_bt_norm t2 Ht2)).
Qed.

End BTReal.

(* ============================================================ *)
(* inventory (18 Qed in total): *)
(*   shared foundation, 2 pieces: lld_lt_zero_sub_r / lld_le_b_zero_sub (the *)
(*   extensions beyond Part A: subtractive positivity of lt + the Bishop-order *)
(*   subtractive lifting). *)
(*   four-site given pieces, 4: lld_{u2,fep,tempent,fw}_log_le_linear_B. *)
(*   site 1: lld_u2_gibbs_eq_step1_B (the Bishop form of the gibbs_equality *)
(*   first-step branch). *)
(*   site 2: the FEPReal section, 5 Qed (boltz_factor_pos / Zf_pos / softmax_pos / *)
(*   boltz_pos / softmax_boltz_pointwise_B) + 5 carrier-isomorphic Definitions. *)
(*   site 3: within the BTReal section, lld_tempent_kl_nonneg_B + *)
(*   lld_tempent_entropy_neg_sum_B; the 3 BT family pieces (btz_pos/bt_pos/ *)
(*   bt_norm) are shared by sites 3/4. *)
(*   site 4: lld_fw_kl_boltz_pair_nonneg_B. *)
(*   the four-site isomorphic proof of the log_le_linear slot confirms the Part *)
(*   A/C reuse (the predicted gap pieces are all discharged); the shared *)
(*   downstream blockers remain two: the log inverse cancellation (the *)
(*   p·(log p−log q) shape is the same at all four sites) and the Bishop *)
(*   fsum_zero_nonneg (the In-machinery partial-sum machinery); the abstract *)
(*   fsum_pos @-instantiation delta verdict follows the ZPosD convention (the *)
(*   nonempty-datum premise listed separately). *)
(*   the Bishop subtractive lifter lld_le_b_zero_sub (a ≤_B b implies *)
(*   0 ≤_B b−a) is a generic entry piece for slot proof families, closed by *)
(*   real_lt_zero_sub_r + swap_mid; a candidate for the Part A reuse list. *)
(* ============================================================ *)

(* ======== G05_LogSmall member piece: UpReqLogD (merged verbatim, with its own Requires) ======== *)
(* ============================================================ *)
(* UpReqLogD.v — proofs of the log inequality family (the S family, 17 slots): *)
(*   the execution module of the generalized main-theorem chain *)
(* ------------------------------------------------------------------ *)
(* engine coordinates (read from the sources): *)
(*   (1) the Real-layer B-form engine (UpRealLeB): real_log_le_linear_B@535 / *)
(*      real_gibbs_inequality_B@592 / real_le_to_le_b@78 / *)
(*      real_log_one_plus_le_B@543 / real_exp_ge_linear_B@526. *)
(*   (2) root pieces (read from the CW_ConstructiveWorld_219 sources): *)
(*      real_log_le_linear_eps@41058 (the Or form per eps; the interface field *)
(*      log_le_linear_eps@41134 is on record) / real_log_mult@40403 / real_log_one / *)
(*      real_two_pos@41807 / real_gibbs_inequality_eps@41704 / *)
(*      real_kl_term@41696 / real_boltzmann_dist_r@43686 (the Section *)
(*      RealRLHFMain exports). *)
(*   (3) the G5 supply (UpReqLogPrimD): logd_log_inv_one_inv_real (log(1/x) *)
(*      ≡ −log x) — the named gap piece of the G08_Gibbs register, delivered in *)
(*      this file. *)
(*   (4) the bridge audit: real_le_to_le_b@78 / latb_real_lt_to_le_b@87 / *)
(*      real_lt_le_bridge@G01_CoreMicro:16 are all one-way (real_le/lt -> *)
(*      real_le_b); the reverse real_le_b -> real_le is the exact closure of the *)
(*      Or form and is not provable constructively. The req-layer unconditional *)
(*      Or-form slot (the verbatim log_le_linear form) is therefore not proved; *)
(*      it is given instead in per-eps / le_b language (the fallback: *)
(*      Real-instantiated theorems). *)
(* ------------------------------------------------------------------ *)
(* provided (slot proof pieces = concrete instances of the slots filled by the *)
(*   engine, the template-2 shape): *)
(*   [slot family 1: the log_le_linear / dist_log_le_linear dual forms, 5 *)
(*    premise positions] *)
(*    logd_log_le_linear_eps — the per-eps Or form (the closest reachable form *)
(*      of the req slot statement; provided directly by real_log_le_linear_eps); *)
(*    logd_log_le_linear_B — the le_b form (provided directly by *)
(*      real_log_le_linear_B). *)
(*   [slot family 2: the three strict-monotonicity-of-log slots] *)
(*    logd_log_lt_mono_real (the verbatim forms of log_lt_mono_cc@UpReqCauchy:819 *)
(*      and ralt_log_lt_mono@UpReqAlignRestA:80; provided directly by *)
(*      real_log_lt_mono); logd_log_two_pos_real (the verbatim form at *)
(*      UpPredRelaxReq:221; assembled from the 1<2 translation + real_log_lt_mono *)
(*      + real_log_one). *)
(*   [slot family 3: the KL verbatim-form bridge — the main theorem] *)
(*    logd_kl_term_minus_form: real_kl_term p q ≡ p·(log p − log q) *)
(*      (decomposition by real_log_mult + the G5 log inverse cancellation); the *)
(*      Real-instantiated supply components of b_gibbs_pos / b_gibbs_sum_eps *)
(*      (the UpSigMigrate2 kl_a = Σ p·(log p − log q) verbatim form) and *)
(*      req2_gibbs_inequality: logd_list_sum_kl_minus_form / *)
(*      logd_gibbs_inequality_minus_B (0 ≤_B the verbatim sum) / *)
(*      logd_gibbs_inequality_minus_eps (0 ≤ the verbatim sum + eps). *)
(*      The verbatim-form bridge is closed in this file through the G5 pieces: *)
(*      all verbatim forms go through. *)
(*   [slot family 4: the real_gibbs_sum_eps@UpRealLeB:206 slot] *)
(*      logd_gibbs_sum_eps_boltzmann_list — the filling piece instantiated with *)
(*      real_sum_over_S := real_list_sum (q := real_boltzmann_dist_r; the supply *)
(*      slot Hnormb=Σp_b==1 made explicit — an honest conditional proof of the *)
(*      same shape as the G5 logd_pos_of_agree; the real_rlhf_optimal_B supply *)
(*      chain closes here). *)
(*   proofs (Real-instantiated): log_le_linear / dist_log_le_linear / *)
(*    log_lt_mono_cc / ralt_log_lt_mono / log_two_pos / real_gibbs_sum_ *)
(*    eps (conditional) = 6; verbatim-form supply (the gibbs family *)
(*    reinforcement): b_gibbs_pos / b_gibbs_sum_eps / req2_gibbs_inequality = 3. *)
(*   X-blocked (the equality cases; not overstepped): log_eq_linear / *)
(*    dist_log_eq_linear / b_gibbs_eq / bridge_free_energy_min_unique = 4 — *)
(*    they need the strict concavity of log to close (the CW_ConstructiveWorld_219 *)
(*    L41199 note: requires strong trichotomy / LPO; not provable *)
(*    constructively). *)
(*   S-blocked (composite; the supply chains are known): entropy_tangent (the *)
(*    entropy_gradient abstraction carries no spec) / req_energy_exp_temp_mono / *)
(*    req_energy_exp_temp_strict_mono (the fw_et temperature composition; the *)
(*    supply, the req_entropy_temp_explicit slot, is itself S-blocked per the G5 *)
(*    verdicts) / bridge_min_free_energy (the Real instantiation is already on *)
(*    disk = real_rlhf_optimal_B@UpRealLeB:237; the req Or form is blocked by the *)
(*    one-way order bridge) = 4. *)
(* name-clash guard: the logd_ prefix shares the family with the G5 *)
(*    UpReqLogPrimD; the 10 new names of this file plus the file name have zero *)
(*    grep hits library-wide (checked name by name before creation). *)
(* constraints: zero Prop at the Set layer (real_le/real_lt/real_eq/real_le_b *)
(*    are all Set-valued; zero Prop leakage in statements and proofs); all close *)
(*    by Qed; zero axioms; no existing file modified; dual forms coexist *)
(*    (the le_b / per-eps dual + the kl_term / verbatim-form dual). *)
(* ============================================================ *)

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
Require Import G08_Gibbs.

From Stdlib Require Import List.

(* ============================================================ *)
(* Part A: Bishop-order algebra complements (the right-end dual of
   gibbsd_le_b_id_l) *)
(* ============================================================ *)

(* A1: converting the right end of a Bishop order along real_eq (the le_b
   counterpart of the req-layer le_id_r) *)
Lemma logd_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hab. unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat a a
           (real_plus b eps) (real_plus c eps)).
  - apply real_eq_refl.
  - exact (RealSetoid.real_eq_plus_compat b eps c eps Hab
             (real_eq_refl eps)).
  - exact (H eps Heps).
Qed.

(* ============================================================ *)
(* Part B: slot family 1 — the dual-form proofs of log_le_linear /
   dist_log_le_linear *)
(*   (UpReqU2:313 / UpReqFEPAttn:90 / UpReqDist:1029 / *)
(*     UpReqTempEntropy:60 / UpFirewallReq:101; the req-layer verbatim Or form *)
(*     is not overstepped — the reverse bridge is one-way — so this part lands *)
(*     on the fallback form) *)
(* ============================================================ *)

(* B1: the per-eps Or form (the closest reachable form of the req slot
   statement; supplied directly by real_log_le_linear_eps) *)
Lemma logd_log_le_linear_eps : forall (x eps : Real)
    (Hx : real_lt real_zero x),
  real_lt real_zero eps ->
  real_le (real_log x Hx) (real_plus (real_plus x (real_opp real_one)) eps).
Proof.
  intros x eps Hx Heps.
  exact (RealInterfaceEnhancedMod.real_log_le_linear_eps x eps Hx Heps).
Qed.

(* B2: the le_b form (the Bishop-order version of the slot statement; provided *)
(*     directly by real_log_le_linear_B@UpRealLeB:535 — coexisting with B1 as *)
(*     the dual form) *)
Lemma logd_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx.
  exact (real_log_le_linear_B x Hx).
Qed.

(* ============================================================ *)
(* Part C: slot family 2 — the three strict-monotonicity-of-log slots *)
(*   (log_lt_mono_cc / *)
(*   ralt_log_lt_mono / log_two_pos; supplied by *)
(*   real_log_lt_mono@CW_ConstructiveWorld_219:39059) *)
(* ============================================================ *)

(* C1: the verbatim form of the strict monotonicity of log (the slot shapes of *)
(*     UpReqCauchy:819 / UpReqAlignRestA:80; provided directly by *)
(*     real_log_lt_mono; the cw_log ≡ real_log conversion along delta happens *)
(*     inside exact) *)
Lemma logd_log_lt_mono_real : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hlt.
  exact (real_log_lt_mono a b Ha Hb Hlt).
Qed.

(* C2: log 2 > 0 (the slot shape at UpPredRelaxReq:221 provided verbatim; the *)
(*     2>0 witness position real_plus_positive one one one_pos one_pos matches *)
(*     the slot pointwise) *)
Lemma logd_log_two_pos_real :
  real_lt real_zero
    (real_log (real_plus real_one real_one)
       (real_plus_positive real_one real_one
          real_lt_zero_one real_lt_zero_one)).
Proof.
  apply (RealSetoid.real_lt_compat
           (real_log real_one real_lt_zero_one) real_zero
           (real_log (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))
           (real_log (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))).
  - exact (real_log_one real_lt_zero_one).
  - apply real_eq_refl.
  - apply (real_log_lt_mono real_one (real_plus real_one real_one)
             real_lt_zero_one
             (real_plus_positive real_one real_one
                real_lt_zero_one real_lt_zero_one)).
    (* 1 < 2: the additive translation of 0<1 plus the one+zero==one conversion *)
    apply (RealSetoid.real_lt_compat
             (real_plus real_one real_zero) real_one
             (real_plus real_one real_one) (real_plus real_one real_one)).
    + exact (real_plus_zero real_one).
    + apply real_eq_refl.
    + exact (real_lt_plus_translate real_one real_zero real_one
               real_lt_zero_one).
Qed.

(* ============================================================ *)
(* Part D: slot family 3 (the main theorem) — the KL verbatim-form bridge *)
(*   real_kl_term p q (the CW_ConstructiveWorld_219 canonical form *)
(*   p·(−log(q/p))) ≡ p·(log p − log q) *)
(*   (the b_gibbs_* / req2_gibbs_inequality / fe_a verbatim forms). Chain: *)
(*   log(q/p) == log q + log(1/p) (real_log_mult) + log(1/p) == −log p *)
(*   (the G5 logd_log_inv_one_inv_real, the named gap piece now delivered) -> *)
(* ============================================================ *)

(* D1 (the slot proof position): the pointwise identity of real_kl_term with the *)
(*    verbatim form (the Real instantiation of the req_kl_term_equiv-type slot — *)
(*    the inverse of the filling direction of the Section RealRLHFMain honest *)
(*    interface real_kl_term_equiv; the dual forms coexist) *)
Lemma logd_kl_term_minus_form : forall (p q : Real)
    (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult p (real_plus (real_log p Hp)
                                  (real_opp (real_log q Hq)))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  set (Hi := real_inv_pos_pos p Hp).
  set (Hr := real_mult_positive q (real_inv_pos p Hp) Hq Hi).
  (* log(q/p) == log q + (−log p) (the log_mult decomposition + the G5 log
     inverse cancellation) *)
  assert (Hlog : real_eq
                   (real_log (real_mult q (real_inv_pos p Hp)) Hr)
                   (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
  { apply (real_eq_trans
             (real_log (real_mult q (real_inv_pos p Hp)) Hr)
             (real_plus (real_log q Hq) (real_log (real_inv_pos p Hp) Hi))
             (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
    - exact (real_log_mult q (real_inv_pos p Hp) Hq Hi).
    - apply (RealSetoid.real_eq_plus_compat (real_log q Hq)
               (real_log (real_inv_pos p Hp) Hi) (real_log q Hq)
               (real_opp (real_log p Hp))).
      + apply real_eq_refl.
      + exact (logd_log_inv_one_inv_real p Hp Hi). }
  (* p·(−log(q/p)) == p·(log p − log q): negation + reordering + the opp
     involution *)
  apply (RealSetoid.real_eq_mult_compat p
           (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hr)) p
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hr))
             (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
    + apply (RealSetoid.real_eq_opp_compat
               (real_log (real_mult q (real_inv_pos p Hp)) Hr)
               (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
      exact Hlog.
    + apply (real_eq_trans
               (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
               (real_plus (real_opp (real_log q Hq))
                          (real_opp (real_opp (real_log p Hp))))
               (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
      * exact (real_opp_plus (real_log q Hq) (real_opp (real_log p Hp))).
      * apply (real_eq_trans
                 (real_plus (real_opp (real_log q Hq))
                            (real_opp (real_opp (real_log p Hp))))
                 (real_plus (real_opp (real_opp (real_log p Hp)))
                            (real_opp (real_log q Hq)))
                 (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
        -- apply real_plus_comm.
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_opp (real_opp (real_log p Hp)))
                     (real_opp (real_log q Hq))
                     (real_log p Hp) (real_opp (real_log q Hq))).
           ++ exact (real_opp_opp (real_log p Hp)).
           ++ apply real_eq_refl.
Qed.

(* D2: the sum-layer verbatim-form identity (lifted pointwise by
   real_list_sum_ext) *)
Lemma logd_list_sum_kl_minus_form :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
    (real_list_sum X
       (fun s : X => real_mult (p s)
                      (real_plus (real_log (p s) (Hp s))
                                 (real_opp (real_log (q s) (Hq s))))) l).
Proof.
  intros X l p q Hp Hq.
  apply real_list_sum_ext.
  intro s.
  exact (logd_kl_term_minus_form (p s) (q s) (Hp s) (Hq s)).
Qed.

(* D3 (the fallback main piece): 0 ≤_B Σ p·(log p − log q) — the Real *)
(*    instantiation of the b_gibbs_pos verbatim form (the canonical *)
(*    gibbsd_gibbs_inequality form + the D2 conversion; coexisting with the *)
(*    canonical real_gibbs_inequality_B form as the dual) *)
Lemma logd_gibbs_inequality_minus_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_mult (p s)
                      (real_plus (real_log (p s) (Hp s))
                                 (real_opp (real_log (q s) (Hq s))))) l).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  apply (logd_le_b_id_r real_zero
           (real_list_sum X
              (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_list_sum X
              (fun s : X => real_mult (p s)
                             (real_plus (real_log (p s) (Hp s))
                                        (real_opp (real_log (q s) (Hq s))))) l)).
  - exact (gibbsd_gibbs_inequality X l p q Hp Hq Hnormp Hnormq).
  - exact (logd_list_sum_kl_minus_form X l p q Hp Hq).
Qed.

(* D4: 0 ≤ Σ p·(log p − log q) + eps — the Real instantiation of the *)
(*    b_gibbs_sum_eps verbatim form (the canonical real_gibbs_inequality_eps *)
(*    form + the D2 conversion; coexisting with D3 as the dual: the Or per-eps *)
(*    form / the Bishop form) *)
Lemma logd_gibbs_inequality_minus_eps :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one)
    (eps : Real), real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_list_sum X
          (fun s : X => real_mult (p s)
                         (real_plus (real_log (p s) (Hp s))
                                    (real_opp (real_log (q s) (Hq s))))) l)
       eps).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq eps Heps.
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus
              (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
              eps)
           (real_plus
              (real_list_sum X
                 (fun s : X => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s))))) l)
              eps)).
  - exact (RealSetoid.real_eq_plus_compat
             (real_list_sum X
                (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
             eps
             (real_list_sum X
                (fun s : X => real_mult (p s)
                               (real_plus (real_log (p s) (Hp s))
                                          (real_opp (real_log (q s) (Hq s))))) l)
             eps
             (logd_list_sum_kl_minus_form X l p q Hp Hq)
             (real_eq_refl eps)).
  - exact (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq eps Heps).
Qed.

(* ============================================================ *)
(* Part E: slot family 4 — the filling piece of the *)
(*   real_gibbs_sum_eps@UpRealLeB:206 slot *)
(*   (the supply slot of Section RealRLHFLeB; instantiated with *)
(*     real_sum_over_S := real_list_sum; q := real_boltzmann_dist_r; the supply *)
(*     slot Hnormb = Σ p_b == 1 made explicit — an honest conditional proof by *)
(*     the same technique as the G5 logd_pos_of_agree; the real_rlhf_optimal_B *)
(*     supply chain closes here onto a single analytic piece) *)
(* ============================================================ *)

Lemma logd_gibbs_sum_eps_boltzmann_list :
  forall (X : Type) (base : X -> Real) (D : Real)
    (D_pos : real_lt real_zero D) (Z : Real) (Z_pos : real_lt real_zero Z)
    (l : list X) (p : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s) l)
                real_one)
    (eps : Real), real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_list_sum X
          (fun s : X => real_kl_term (p s)
                          (real_boltzmann_dist_r X base D D_pos Z Z_pos s)
                          (Hp s)
                          (real_boltzmann_dist_r_pos X base D D_pos Z Z_pos s)) l)
       eps).
Proof.
  intros X base D D_pos Z Z_pos l p Hp Hnormp Hnormb eps Heps.
  exact (real_gibbs_inequality_eps X l p
           (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s)
           Hp
           (fun s : X => real_boltzmann_dist_r_pos X base D D_pos Z Z_pos s)
           Hnormp Hnormb eps Heps).
Qed.

(* ============================================================ *)
(* closure audit: [Print Assumptions] on every proof piece plus the extraction
   constant face *)
(* ============================================================ *)
Print Assumptions logd_le_b_id_r.
Print Assumptions logd_log_le_linear_eps.
Print Assumptions logd_log_le_linear_B.
Print Assumptions logd_log_lt_mono_real.
Print Assumptions logd_log_two_pos_real.
Print Assumptions logd_kl_term_minus_form.
Print Assumptions logd_list_sum_kl_minus_form.
Print Assumptions logd_gibbs_inequality_minus_B.
Print Assumptions logd_gibbs_inequality_minus_eps.
Print Assumptions logd_gibbs_sum_eps_boltzmann_list.

From Stdlib Require Import Extraction.
(* the full extraction face (10 pieces; the magic census is 73, all of them in *)
(*    the coq_RealEnhancedReal class-instance wrapper constants and the G5 *)
(*    UpReqLogPrimD class projection chain — the proof bodies of this file's own *)
(*    10 pieces carry zero magic, the single touch point being one forced *)
(*    conversion in D1 when it uses the G5 logd_log_inv_one_inv_real) *)
Extraction "_logd_g3_extract.ml" logd_le_b_id_r logd_log_le_linear_eps
  logd_log_le_linear_B logd_log_lt_mono_real logd_log_two_pos_real
  logd_kl_term_minus_form logd_list_sum_kl_minus_form
  logd_gibbs_inequality_minus_B logd_gibbs_inequality_minus_eps
  logd_gibbs_sum_eps_boltzmann_list.
(* the pure extraction face (5 pieces with no class-instance dependencies;
   magic = 0) *)
Extraction "_logd_g3_pure.ml" logd_le_b_id_r logd_log_le_linear_eps
  logd_log_le_linear_B logd_log_lt_mono_real logd_log_two_pos_real.

(* ============================================================ *)
(*   slot family 1 (the log_le_linear dual forms, 5 premise positions): *)
(*    - log_le_linear@UpReqU2:313 / @UpReqFEPAttn:90 — Real-instantiated proofs *)
(*      (the B1/B2 dual forms); the req-layer verbatim Or form is not overstepped *)
(*      (the reverse bridge is one-way). *)
(*    - dist_log_le_linear@UpReqDist:1029 / @UpReqTempEntropy:60 / *)
(*      @UpFirewallReq:101 — likewise (independent declarations of the same *)
(*      statement, one landing per file). *)
(*   slot family 2 (strict monotonicity of log, 3 slots): *)
(*    - log_lt_mono_cc@UpReqCauchy:819 / ralt_log_lt_mono@ *)
(*      UpReqAlignRestA:80 — verbatim-form proofs (provided directly by C1). *)
(*    - log_two_pos@UpPredRelaxReq:221 — a verbatim-form proof (assembled by *)
(*      C2). *)
(*   slot family 3 (the gibbs verbatim-form bridge, 4 slots): *)
(*    - b_gibbs_pos@UpSigMigrate2:913 / b_gibbs_sum_eps@916 — verbatim-form *)
(*      Real-instantiated proofs (D3/D4; the kl_a verbatim form aligned *)
(*      pointwise). *)
(*    - req2_gibbs_inequality@UpReqAlign3:1451 / @UpReqU2:356 — supplied the *)
(*      same way (the KLE verbatim form is isomorphic to kl_a; the verdict that *)
(*      the req-layer Or form is blocked matches the UpReqAlign3 register entry *)
(*      "the plain-le form is not derivable from the interface per-eps fields"). *)
(*   4 X-blocked slots (the equality cases; not provable constructively — the *)
(*    CW_ConstructiveWorld_219 L41199 note requires strong trichotomy / LPO): *)
(*    - log_eq_linear@UpReqU2:315 / @UpReqFEPAttn:92; *)
(*      dist_log_eq_linear@UpReqDist:1031 / @UpReqTempEntropy:62; *)
(*      b_gibbs_eq@UpSigMigrate2:921; *)
(*      bridge_free_energy_min_unique@UpReqAlign:288 (the FEP unique minimum = *)
(*      the KL equality case). *)
(*   4 S-blocked slots (composite/abstract; the supply chains are known): *)
(*    - entropy_tangent@UpEntropyGainReq:77 / @UpReqCauchy:1383 — *)
(*      the entropy_gradient abstraction carries no spec (the premise "abstract *)
(*      entropy concavity"). *)
(*    - req_energy_exp_temp_mono@UpFirewallReq:135 / *)
(*      req_energy_exp_temp_strict_mono@138 — the fw_et temperature composition; *)
(*      the supply, the req_entropy_temp_explicit slot, is itself S-blocked (per *)
(*      the G5 verdicts); the strict version additionally needs an Or-lt form of *)
(*      KL>0 (the equality tier, X-blocked). *)
(*    - bridge_min_free_energy@UpReqAlign:285 — the Real instantiation is already *)
(*      on disk (real_rlhf_optimal_B@UpRealLeB:237, the le_b form; the supply *)
(*      chain closes through Part E of this file onto the single analytic piece *)
(*      Σp_b==1); the req-layer Or form is blocked by the one-way order bridge. *)
(*   slot family 4: real_gibbs_sum_eps@UpRealLeB:206 — a conditional proof *)
(*      (Part E; the analytic instantiation of the supply slot Σ p_b == 1 is *)
(*      recorded). *)
(*   log_mult / exp_neg_plus are on record, so the req per-eps forms are directly *)
(*   available; the real_kl_term ↔ p·(log p − log q) verbatim-form bridge is *)
(*   fully open (Part D), and the Section RealRLHFMain honest-interface slot *)
(*   real_kl_term_equiv can now be filled. *)
(*   the Bishop-order right-end conversion piece logd_le_b_id_r is the dual of *)
(*   gibbsd_le_b_id_l (Part A is reusable across modules); the proofs of the *)
(*   b_gibbs_* verbatim-form family need only the gibbsd sum machinery plus the *)
(*   single point D1, with no sum-layer rebuild. *)
(* ============================================================ *)
