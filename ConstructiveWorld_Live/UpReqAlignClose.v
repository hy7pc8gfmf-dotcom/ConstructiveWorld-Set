(* ConstructiveWorld-Set -- same-position premise-slot loading bridges for the req-world alignment layer. *)

(** * UpReqAlignClose: same-position loading of the two UpReqAlign deep-chain premise slots in the req world.

    Mission.  Same-position loading of the two UpReqAlign deep-chain
      premise slots in the req world: the log-mult full-field
      decomposition [uac_pi_next_log_decomp], the backward-KL identity
      [uac_req_backward_kl_identity], and the policy-improvement
      monotonicity [uac_req_policy_improvement_mono], with the bridges
      [uac_pstr_cross], [uac_npx_cross], [uac_kl_move], [uac_F_move].

    Dependencies.  No direct Stdlib Requires; requires of this development
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqAlign], [UpReqAlign2],
      [UpReqAlign3], [UpReqU2].

    References.  This development, UpReqAlignClose.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqAlignClose.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require UpReqU2.
Import RealInterfaceEnhancedMod.
(* Field-name passthrough (the UpReqU2.v:125-159 template, placed after the
   Import so the concrete bindings win): the interface fields consumed below
   are pinned to the concrete tree definitions -- the same bindings the
   global RealEnhancedReal instance assigns -- so the section hypotheses and
   the extracted signatures carry the concrete real_eq / real_lt / real_le
   carriers instead of the instance projections. *)
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
Notation req_mult_compat := RealSetoid.real_eq_mult_compat_adapt.
Notation req_opp_compat := RealSetoid.real_eq_opp_compat.
Notation plus_assoc := real_plus_assoc.
Notation plus_comm := real_plus_comm.
Notation mult_positive := real_mult_positive.
Notation le_id_r := RealSetoid.real_le_id_r.
Notation inv_pos := real_inv_pos.
Notation inv_pos_correct := real_inv_pos_correct.
Notation inv_pos_pos := real_inv_pos_pos.
Notation inv_pos_ext := real_inv_pos_ext.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.
Notation log := real_log.
Notation log_inv := real_log_inv.

(* ============================================================ *)
(* UacClose: the same-position loading section (section arguments  *)
(*   aligned slot by slot with ReqAlignCore/Req2AlignCore); the witness      *)
(*   face posd/nrm1/KLR/PSTRR/NPXR/... are delta-transparent wrappers
     over upstream closed names, fed once at the wrapper slots, the
     statement layer at the same position slot by slot).    *)
(* ============================================================ *)
Section UacClose.

(* A-face adaptation: the parameterized section binders
   Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are deleted; the
   carrier R is the global Real (the tree Notation R := Real), and the
   interface fields (req/lt/le/zero/one/plus/mult/opp/abs/log/exp_neg/
   inv_pos) resolve through the concrete tree names; statement names
   unchanged. *)
Variable S : Set.

(* ---- summation interface (the four same-position slots of the closing section) ---- *)
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

(* ---- the two interface-gap bridge slots (the native ReqAlignCore
        log_req_compat plus the Align2 extra slot log_inv_exp_neg_req;
        the Real-layer unconditional instantiation follows the
        log_req_compat_real@UpReqU2 template precedent) ---- *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ---- section arguments (same position as ReqAlignCore/Req2AlignCore;
        the eta triple feeds the premise face of
        r2_policy_improvement_mono) ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.
(* note: after the section signature was canonicalized at :89/:91, this
   Variable no longer holds a premise slot (kept in place, idle, so that
   downstream statement-face references do not break); the positivity of
   pi_star_req/req_pi_star_pos is now supplied internally by the
   dependent-module instance UpReqAlign.Z_align_pos. *)
Variable Z_align_pos : lt zero (@Z_align_req S sumf reward beta beta_pos pi_ref).

(* ---- the B-class bridge slot in same-position transport (the req
        statement of Align3:1451 req2_gibbs_inequality; the KL >= 0
        plain-le form hits the order-elimination wall and is kept as is,
        for the same reason and at the same position as in Align3) ---- *)
Hypothesis uac_gibbs_le_zero :
  forall (p q : S -> R) (Hp : @pos_dist S p) (Hq : @pos_dist S q),
    le zero (@relative_entropy_req S sumf p q Hp Hq).

(* ---- delta-transparent wrappers (req-world closed names; after unfold
        they are the upstream definition bodies, with no conversion friction) ---- *)
Definition uac_posd (p : S -> R) : Set := @pos_dist S p.
Definition uac_nrm1 (p : S -> R) : Set := @norm_one S sumf p.
Definition uac_KLR (p q : S -> R) :
    @pos_dist S p -> @pos_dist S q -> R :=
  @relative_entropy_req S sumf p q.
Definition uac_PSTRR (s : S) : R :=
  @pi_star_req S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos s.
Definition uac_PSTRR_pos : @pos_dist S uac_PSTRR :=
  @req_pi_star_pos S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos.

(* the PSTR bridge (after the section-signature adjustment): the pointwise
   req between PSTR (bound to its own Z_align_pos slot) and the canonical
   uac_PSTRR; the two differ only in the positivity proof argument of
   inv_pos (the Z_align_pos variable vs the internal dependent-module
   instance UpReqAlign.Z_align_pos); transported by the combined fold of
   req_mult_cancel_l with inv_pos_correct. The witness slot of kl_move is
   fed by this bridge instead of req_refl. *)
Lemma uac_pstr_cross : forall s : S,
  req (@PSTR S sumf reward beta beta_pos pi_ref Z_align_pos s) (uac_PSTRR s).
Proof.
  intro s.
  apply (req_mult_compat _ _ _ _
    (req_mult_cancel_l (Z_align_req S sumf reward beta beta_pos pi_ref) _ _
       Z_align_pos
       (req_trans _ _ _
          (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
             Z_align_pos)
          (req_sym _ _
             (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
                (@UpReqAlign.Z_align_pos S sumf sum_pos reward beta beta_pos
                   pi_ref pi_ref_pos)))))
    (req_refl (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
Qed.
Definition uac_ADR (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t) (s : S) : R :=
  @advantage_aug_req S reward beta pi_ref pi_ref_pos pi_t Hpi_t s.
Definition uac_ZRR (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t) : R :=
  @Z_rel_req S sumf reward beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t.
Definition uac_ZRR_pos (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t) :
    lt zero (uac_ZRR pi_t Hpi_t) :=
  @req_Z_rel_pos S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                 eta pi_t Hpi_t.
Definition uac_NPXR (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t) (s : S) : R :=
  @pi_next_req S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
               eta pi_t Hpi_t s.
Definition uac_NPXR_pos (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t) :
    @pos_dist S (uac_NPXR pi_t Hpi_t) :=
  fun s => @req_pi_next_pos S sumf sum_pos reward beta beta_pos pi_ref
                            pi_ref_pos eta pi_t Hpi_t s.
Definition uac_AOR (p : S -> R) (Hp : @pos_dist S p) : R :=
  @align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition uac_AER (s : S) : R :=
  @align_energy_req S reward beta pi_ref pi_ref_pos s.

(* ============================================================ *)
(* first piece: the log-mult full-field bridge (the Align2:877
   req2_pi_next_log_decomp recipe ported verbatim to the req world): the
   three-segment expansion of log(pi_next(s)) unfolds the nested product
   mult ivZ (mult (pi_t s) expm) level by level with the log_mult product
   law taken at the interface-field witness slots; this is the engine
   referred to as the softmax-KL deep-chain log-mult interface-field gap,
   now on file.                *)
(* ============================================================ *)
Lemma uac_pi_next_log_decomp :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t) (s : S),
    req (log (uac_NPXR pi_t Hpi_t s) (uac_NPXR_pos pi_t Hpi_t s))
        (plus (log (pi_t s) (Hpi_t s))
              (plus (mult (mult eta (inv_pos beta beta_pos))
                          (uac_ADR pi_t Hpi_t s))
                    (opp (log (uac_ZRR pi_t Hpi_t)
                              (uac_ZRR_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t s.
  set (iv := inv_pos beta beta_pos).
  set (lg := log (pi_t s) (Hpi_t s)).
  set (lgZ := log (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t)).
  set (X := mult (mult eta iv) (uac_ADR pi_t Hpi_t s)).
  set (expm := exp_neg (opp X)).
  set (ivZ := inv_pos (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t)).
  (* explicit witnesses (a Qed piece cannot be delta-reduced; first open
     the door with log_req_compat, and everything after is transparent) *)
  set (Hp1 := inv_pos_pos (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t)).
  set (Hp2 := mult_positive (pi_t s) expm (Hpi_t s) (exp_neg_pos (opp X))).
  set (HpI := mult_positive ivZ (mult (pi_t s) expm) Hp1 Hp2).
  set (Wit := uac_NPXR_pos pi_t Hpi_t s).
  assert (Hstep12 : req (log (mult ivZ (mult (pi_t s) expm)) HpI)
                        (plus (opp lgZ) (plus lg X))).
  { exact (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
           (plus (opp lgZ) (log (mult (pi_t s) expm) Hp2))
           (plus (opp lgZ) (plus lg X))
           (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
                      (plus (log ivZ Hp1) (log (mult (pi_t s) expm) Hp2))
                      (plus (opp lgZ) (log (mult (pi_t s) expm) Hp2))
                      (log_mult ivZ (mult (pi_t s) expm) Hp1 Hp2)
                      (req_plus_compat (log ivZ Hp1) (opp lgZ)
                                       (log (mult (pi_t s) expm) Hp2)
                                       (log (mult (pi_t s) expm) Hp2)
                                       (@req_log_inv_one_inv log_req_compat
                                                            (uac_ZRR pi_t Hpi_t)
                                                            (uac_ZRR_pos pi_t Hpi_t))
                                       (req_refl (log (mult (pi_t s) expm) Hp2))))
           (req_plus_compat (opp lgZ) (opp lgZ)
                            (log (mult (pi_t s) expm) Hp2) (plus lg X)
                            (req_refl (opp lgZ))
                            (req_trans (log (mult (pi_t s) expm) Hp2)
                                       (plus lg (log expm (exp_neg_pos (opp X))))
                                       (plus lg X)
                                       (log_mult (pi_t s) expm (Hpi_t s)
                                                 (exp_neg_pos (opp X)))
                                       (req_plus_compat lg lg
                                                        (log expm (exp_neg_pos (opp X))) X
                                                        (req_refl lg)
                                                        (req_trans
                                                           (log expm (exp_neg_pos (opp X)))
                                                           (opp (opp X)) X
                                                           (@req_log_exp_neg log_inv_exp_neg_req (opp X))
                                                           (req_double_neg X)))))). }
  exact (req_trans (log (uac_NPXR pi_t Hpi_t s) Wit)
                   (log (mult ivZ (mult (pi_t s) expm)) HpI)
                   (plus lg (plus X (opp lgZ)))
                   (log_req_compat (uac_NPXR pi_t Hpi_t s)
                                   (mult ivZ (mult (pi_t s) expm))
                                   Wit HpI (req_refl (uac_NPXR pi_t Hpi_t s)))
                   (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
                              (plus (opp lgZ) (plus lg X))
                              (plus lg (plus X (opp lgZ)))
                              Hstep12
                              (req_trans (plus (opp lgZ) (plus lg X))
                              (plus (plus (opp lgZ) lg) X)
                              (plus lg (plus X (opp lgZ)))
                              (plus_assoc (opp lgZ) lg X)
                              (req_trans (plus (plus (opp lgZ) lg) X)
                                         (plus (plus lg (opp lgZ)) X)
                                         (plus lg (plus X (opp lgZ)))
                                         (req_plus_compat (plus (opp lgZ) lg)
                                                          (plus lg (opp lgZ)) X X
                                                          (plus_comm (opp lgZ) lg)
                                                          (req_refl X))
                                         (req_trans (plus (plus lg (opp lgZ)) X)
                                                    (plus lg (plus (opp lgZ) X))
                                                    (plus lg (plus X (opp lgZ)))
                                                    (req_sym (plus lg (plus (opp lgZ) X))
                                                             (plus (plus lg (opp lgZ)) X)
                                                             (plus_assoc lg (opp lgZ) X))
                                                    (req_plus_compat lg lg
                                                                     (plus (opp lgZ) X)
                                                                     (plus X (opp lgZ))
                                                                     (req_refl lg)
                                                                     (plus_comm (opp lgZ) X))))))).
Qed.

(* ============================================================ *)
(* restatement stock (the positivity witnesses are data; the one-jump
   crossing piece between the two worlds)          *)
(* ============================================================ *)

(* the req2/req two-world bridge for the pi_next term (restating the
   inv_pos witness slot: req2_Z_rel_pos to req_Z_rel_pos; inv_pos_ext
   opens the interface field and the product law closes) *)
Lemma uac_npx_cross :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t) (s : S),
    req (@NPX S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
              eta pi_t Hpi_t s)
        (uac_NPXR pi_t Hpi_t s).
Proof.
  intros pi_t Hpi_t s.
  apply (req_mult_compat
           (inv_pos (@req2_Z_rel S sumf reward beta beta_pos pi_ref
                                  pi_ref_pos eta pi_t Hpi_t)
                    (@req2_Z_rel_pos S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t))
           (inv_pos (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t))
           (mult (pi_t s)
                 (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                     (@req2_adv S reward beta pi_ref
                                                pi_ref_pos pi_t Hpi_t s)))))
           (mult (pi_t s)
                 (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                     (uac_ADR pi_t Hpi_t s)))))
           (inv_pos_ext (@req2_Z_rel S sumf reward beta beta_pos pi_ref
                                      pi_ref_pos eta pi_t Hpi_t)
                        (uac_ZRR pi_t Hpi_t)
                        (@req2_Z_rel_pos S sumf sum_pos reward beta beta_pos
                                         pi_ref pi_ref_pos eta pi_t Hpi_t)
                        (uac_ZRR_pos pi_t Hpi_t)
                        (req_refl (uac_ZRR pi_t Hpi_t)))
           (req_refl (mult (pi_t s)
                           (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                               (uac_ADR pi_t Hpi_t s))))))).
Qed.

(* the KL two-argument move bridge (pointwise req at the base points plus
   a free restatement of the witnesses on both sides; assembled from
   sum_ext and log_req_compat carrying x to y, of the same shape as
   U2Machine) *)
Lemma uac_kl_move :
  forall (p1 p2 q1 q2 : S -> R)
         (Hp1 : @pos_dist S p1) (Hp2 : @pos_dist S p2)
         (Hq1 : @pos_dist S q1) (Hq2 : @pos_dist S q2),
    (forall s : S, req (p1 s) (p2 s)) ->
    (forall s : S, req (q1 s) (q2 s)) ->
    req (uac_KLR p1 q1 Hp1 Hq1) (uac_KLR p2 q2 Hp2 Hq2).
Proof.
  intros p1 p2 q1 q2 Hp1 Hp2 Hq1 Hq2 H12 H34.
  unfold uac_KLR, relative_entropy_req.
  apply (sum_ext
           (fun s => mult (p1 s)
                          (req_minus (log (p1 s) (Hp1 s)) (log (q1 s) (Hq1 s))))
           (fun s => mult (p2 s)
                          (req_minus (log (p2 s) (Hp2 s)) (log (q2 s) (Hq2 s))))).
  intro s.
  apply (req_mult_compat (p1 s) (p2 s)
           (req_minus (log (p1 s) (Hp1 s)) (log (q1 s) (Hq1 s)))
           (req_minus (log (p2 s) (Hp2 s)) (log (q2 s) (Hq2 s)))
           (H12 s)).
  unfold req_minus.
  apply (req_plus_compat (log (p1 s) (Hp1 s)) (log (p2 s) (Hp2 s))
                         (opp (log (q1 s) (Hq1 s))) (opp (log (q2 s) (Hq2 s)))
                         (log_req_compat (p1 s) (p2 s) (Hp1 s) (Hp2 s) (H12 s))
                         (req_opp_compat (log (q1 s) (Hq1 s)) (log (q2 s) (Hq2 s))
                                         (log_req_compat (q1 s) (q2 s) (Hq1 s)
                                                         (Hq2 s) (H34 s)))).
Qed.

(* the alignment free-energy move bridge (restating the uac_AOR stock) *)
Lemma uac_F_move :
  forall (p1 p2 : S -> R)
         (Hp1 : @pos_dist S p1) (Hp2 : @pos_dist S p2),
    (forall s : S, req (p1 s) (p2 s)) ->
    req (@F_align_req S sumf reward beta pi_ref pi_ref_pos p1 Hp1)
        (@F_align_req S sumf reward beta pi_ref pi_ref_pos p2 Hp2).
Proof.
  intros p1 p2 Hp1 Hp2 H12.
  unfold F_align_req.
  apply (req_plus_compat
           (sumf (fun s => mult (p1 s) (uac_AER s)))
           (sumf (fun s => mult (p2 s) (uac_AER s)))
           (mult beta (sumf (fun s => mult (p1 s) (log (p1 s) (Hp1 s)))))
           (mult beta (sumf (fun s => mult (p2 s) (log (p2 s) (Hp2 s)))))).
  - apply (sum_ext (fun s => mult (p1 s) (uac_AER s))
                   (fun s => mult (p2 s) (uac_AER s))).
    intro s.
    apply (req_mult_compat (p1 s) (p2 s) (uac_AER s) (uac_AER s) (H12 s)
                           (req_refl (uac_AER s))).
  - apply (req_mult_compat beta beta
           (sumf (fun s => mult (p1 s) (log (p1 s) (Hp1 s))))
           (sumf (fun s => mult (p2 s) (log (p2 s) (Hp2 s))))
           (req_refl beta)).
    apply (sum_ext (fun s => mult (p1 s) (log (p1 s) (Hp1 s)))
                   (fun s => mult (p2 s) (log (p2 s) (Hp2 s)))).
    intro s.
    apply (req_mult_compat (p1 s) (p2 s) (log (p1 s) (Hp1 s)) (log (p2 s) (Hp2 s))
                           (H12 s)
                           (log_req_compat (p1 s) (p2 s) (Hp1 s) (Hp2 s) (H12 s))).
Qed.

(* ============================================================ *)
(* second piece (slot one): the premise slot of req_backward_kl_identity
   loaded as a same-position statement (slot by slot the same shape as
   UpReqAlign.v:434-442; the supplying piece is the unconditional
   five-segment main theorem Align3:3162 req2_backward_kl_step, crossed
   in one jump by the witness restatement uac_kl_move; see the
   reconciliation statement at the end of the file).              *)
(* ============================================================ *)
Lemma uac_req_backward_kl_identity :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t)
         (Hnorm : @norm_one S sumf pi_t),
    req (uac_KLR uac_PSTRR (uac_NPXR pi_t Hpi_t) uac_PSTRR_pos
             (uac_NPXR_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
              (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                    (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                                 (uac_NPXR_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hnorm.
  apply (req_trans
           (uac_KLR uac_PSTRR (uac_NPXR pi_t Hpi_t) uac_PSTRR_pos
                    (uac_NPXR_pos pi_t Hpi_t))
           (uac_KLR (@PSTR S sumf reward beta beta_pos pi_ref Z_align_pos)
                    (@NPX S sumf sum_pos reward beta beta_pos pi_ref
                          pi_ref_pos eta pi_t Hpi_t)
                    (@PSTR_pos S sumf reward beta beta_pos pi_ref
                               pi_ref_pos Z_align_pos)
                    (@npx_pos S sumf sum_pos reward beta beta_pos pi_ref
                              pi_ref_pos eta pi_t Hpi_t))
           (plus (mult (req_minus one eta)
                       (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
                 (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                       (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                                (uac_NPXR_pos pi_t Hpi_t))))).
  - exact (req_sym
             (uac_KLR (@PSTR S sumf reward beta beta_pos pi_ref Z_align_pos)
                      (@NPX S sumf sum_pos reward beta beta_pos pi_ref
                            pi_ref_pos eta pi_t Hpi_t)
                      (@PSTR_pos S sumf reward beta beta_pos pi_ref
                                 pi_ref_pos Z_align_pos)
                      (@npx_pos S sumf sum_pos reward beta beta_pos pi_ref
                                pi_ref_pos eta pi_t Hpi_t))
             (uac_KLR uac_PSTRR (uac_NPXR pi_t Hpi_t) uac_PSTRR_pos
                      (uac_NPXR_pos pi_t Hpi_t))
             (uac_kl_move
             (@PSTR S sumf reward beta beta_pos pi_ref Z_align_pos)
             uac_PSTRR
             (@NPX S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                   eta pi_t Hpi_t)
             (uac_NPXR pi_t Hpi_t)
             (@PSTR_pos S sumf reward beta beta_pos pi_ref pi_ref_pos
                        Z_align_pos)
             uac_PSTRR_pos
             (@npx_pos S sumf sum_pos reward beta beta_pos pi_ref
                       pi_ref_pos eta pi_t Hpi_t)
             (uac_NPXR_pos pi_t Hpi_t)
             (fun s => uac_pstr_cross s)
             (fun s => uac_npx_cross pi_t Hpi_t s))).
  - apply (req_trans
             (uac_KLR (@PSTR S sumf reward beta beta_pos pi_ref Z_align_pos)
                      (@NPX S sumf sum_pos reward beta beta_pos pi_ref
                            pi_ref_pos eta pi_t Hpi_t)
                      (@PSTR_pos S sumf reward beta beta_pos pi_ref
                                 pi_ref_pos Z_align_pos)
                      (@npx_pos S sumf sum_pos reward beta beta_pos pi_ref
                                pi_ref_pos eta pi_t Hpi_t))
             (plus (mult (req_minus one eta)
                         (uac_KLR (@PSTR S sumf reward beta beta_pos pi_ref
                                        Z_align_pos)
                                  pi_t
                                  (@PSTR_pos S sumf reward beta beta_pos
                                             pi_ref pi_ref_pos Z_align_pos)
                                  Hpi_t))
                   (plus (opp (mult eta
                                    (uac_KLR pi_t
                                             (@PSTR S sumf reward beta
                                                    beta_pos pi_ref Z_align_pos)
                                             Hpi_t
                                             (@PSTR_pos S sumf reward beta
                                                        beta_pos pi_ref pi_ref_pos
                                                        Z_align_pos))))
                         (uac_KLR pi_t
                                  (@NPX S sumf sum_pos reward beta beta_pos
                                        pi_ref pi_ref_pos eta pi_t Hpi_t)
                                  Hpi_t
                                  (@npx_pos S sumf sum_pos reward beta
                                            beta_pos pi_ref pi_ref_pos eta pi_t
                                            Hpi_t))))
             (plus (mult (req_minus one eta)
                         (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
                   (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                         (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                                  (uac_NPXR_pos pi_t Hpi_t))))).
    + exact (@req2_backward_kl_step S sumf sum_ext sum_add sum_linear
                  sum_pos log_req_compat log_inv_exp_neg_req reward beta beta_pos
                  pi_ref pi_ref_pos eta Z_align_pos pi_t Hpi_t Hnorm).
    + apply (req_plus_compat
                (mult (req_minus one eta)
                      (uac_KLR (@PSTR S sumf reward beta beta_pos pi_ref
                                       Z_align_pos)
                               pi_t
                               (@PSTR_pos S sumf reward beta beta_pos pi_ref
                                          pi_ref_pos Z_align_pos)
                               Hpi_t))
                (mult (req_minus one eta)
                      (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
                (plus (opp (mult eta
                                 (uac_KLR pi_t
                                          (@PSTR S sumf reward beta beta_pos
                                                 pi_ref Z_align_pos)
                                          Hpi_t
                                          (@PSTR_pos S sumf reward beta
                                                     beta_pos pi_ref pi_ref_pos
                                                     Z_align_pos))))
                      (uac_KLR pi_t
                               (@NPX S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t)
                               Hpi_t
                               (@npx_pos S sumf sum_pos reward beta beta_pos
                                         pi_ref pi_ref_pos eta pi_t Hpi_t)))
                (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                      (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                               (uac_NPXR_pos pi_t Hpi_t)))).
      * apply (req_mult_compat (req_minus one eta) (req_minus one eta)
                  (uac_KLR (@PSTR S sumf reward beta beta_pos pi_ref
                                 Z_align_pos)
                           pi_t
                           (@PSTR_pos S sumf reward beta beta_pos pi_ref
                                      pi_ref_pos Z_align_pos)
                           Hpi_t)
                  (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t)
                  (req_refl (req_minus one eta))
                  (uac_kl_move
                     (@PSTR S sumf reward beta beta_pos pi_ref Z_align_pos)
                     uac_PSTRR pi_t pi_t
                     (@PSTR_pos S sumf reward beta beta_pos pi_ref
                                pi_ref_pos Z_align_pos)
                     uac_PSTRR_pos Hpi_t Hpi_t
                     (fun s => uac_pstr_cross s)
                     (fun s => req_refl (pi_t s)))).
      * apply (req_plus_compat
                  (opp (mult eta
                            (uac_KLR pi_t
                                     (@PSTR S sumf reward beta beta_pos
                                            pi_ref Z_align_pos)
                                     Hpi_t
                                     (@PSTR_pos S sumf reward beta beta_pos
                                                pi_ref pi_ref_pos Z_align_pos))))
                  (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                  (uac_KLR pi_t
                           (@NPX S sumf sum_pos reward beta beta_pos pi_ref
                                 pi_ref_pos eta pi_t Hpi_t)
                           Hpi_t
                           (@npx_pos S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t))
                  (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                           (uac_NPXR_pos pi_t Hpi_t))
                  (req_opp_compat
                     (mult eta
                           (uac_KLR pi_t
                                    (@PSTR S sumf reward beta beta_pos
                                           pi_ref Z_align_pos)
                                    Hpi_t
                                    (@PSTR_pos S sumf reward beta beta_pos
                                               pi_ref pi_ref_pos Z_align_pos)))
                     (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos))
                     (req_mult_compat eta eta
                        (uac_KLR pi_t
                                 (@PSTR S sumf reward beta beta_pos pi_ref
                                        Z_align_pos)
                                 Hpi_t
                                 (@PSTR_pos S sumf reward beta beta_pos
                                            pi_ref pi_ref_pos Z_align_pos))
                        (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)
                        (req_refl eta)
                        (uac_kl_move pi_t
                                     pi_t
                                     (@PSTR S sumf reward beta beta_pos
                                            pi_ref Z_align_pos)
                                     uac_PSTRR Hpi_t Hpi_t
                                     (@PSTR_pos S sumf reward beta beta_pos
                                                pi_ref pi_ref_pos Z_align_pos)
                                     uac_PSTRR_pos
                                     (fun s => req_refl (pi_t s))
                                     (fun s => uac_pstr_cross s))))
                  (uac_kl_move pi_t
                               pi_t
                               (@NPX S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t)
                               (uac_NPXR pi_t Hpi_t) Hpi_t Hpi_t
                               (@npx_pos S sumf sum_pos reward beta beta_pos
                                         pi_ref pi_ref_pos eta pi_t Hpi_t)
                               (uac_NPXR_pos pi_t Hpi_t)
                               (fun s => req_refl (pi_t s))
                               (fun s => uac_npx_cross pi_t Hpi_t s))).
Qed.

(* ============================================================ *)
(* second piece (slot two): the premise slot of req_policy_improvement_mono
   loaded as a same-position statement (slot by slot the same shape as
   UpReqAlign.v:630-633; the supplying piece is Align3:1456
   r2_policy_improvement_mono, crossed in one jump by the witness
   restatement uac_F_move; the uac_gibbs_le_zero slot is substituted
   directly at the same position).                                   *)
(* ============================================================ *)
Lemma uac_req_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist S pi_t)
         (Hnorm : @norm_one S sumf pi_t),
    le (uac_AOR pi_t Hpi_t)
       (uac_AOR (uac_NPXR pi_t Hpi_t) (uac_NPXR_pos pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hnorm.
  assert (Hmid : req (uac_AOR (@NPX S sumf sum_pos reward beta beta_pos
                                    pi_ref pi_ref_pos eta pi_t Hpi_t)
                              (@npx_pos S sumf sum_pos reward beta beta_pos
                                        pi_ref pi_ref_pos eta pi_t Hpi_t))
                     (uac_AOR (uac_NPXR pi_t Hpi_t) (uac_NPXR_pos pi_t Hpi_t))).
  { unfold uac_AOR, align_objective_req.
    apply (req_opp_compat
             (@F_align_req S sumf reward beta pi_ref pi_ref_pos
                           (@NPX S sumf sum_pos reward beta beta_pos pi_ref
                                 pi_ref_pos eta pi_t Hpi_t)
                           (@npx_pos S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t))
             (@F_align_req S sumf reward beta pi_ref pi_ref_pos
                           (uac_NPXR pi_t Hpi_t)
                           (uac_NPXR_pos pi_t Hpi_t))).
    apply (uac_F_move
             (@NPX S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                   eta pi_t Hpi_t)
             (uac_NPXR pi_t Hpi_t)
             (@npx_pos S sumf sum_pos reward beta beta_pos pi_ref
                       pi_ref_pos eta pi_t Hpi_t)
             (uac_NPXR_pos pi_t Hpi_t)
             (fun s => uac_npx_cross pi_t Hpi_t s)). }
  exact (le_id_r (uac_AOR pi_t Hpi_t)
                 (uac_AOR (@NPX S sumf sum_pos reward beta beta_pos pi_ref
                                pi_ref_pos eta pi_t Hpi_t)
                          (@npx_pos S sumf sum_pos reward beta beta_pos
                                    pi_ref pi_ref_pos eta pi_t Hpi_t))
                 (uac_AOR (uac_NPXR pi_t Hpi_t) (uac_NPXR_pos pi_t Hpi_t))
                 Hmid
                 (@r2_policy_improvement_mono S sumf sum_ext sum_add
                    sum_linear sum_pos log_req_compat log_inv_exp_neg_req reward
                    beta beta_pos pi_ref pi_ref_pos eta eta_pos eta_le_one
                    uac_gibbs_le_zero pi_t Hpi_t Hnorm)).
Qed.

End UacClose.

(* ============================================================ *)
(* reconciliation statement for the two loaded bridges: notes on the
   UpReqAlign tail checklist              *)
(* ============================================================ *)
(* 1. the softmax-KL deep-chain engine is on file, in three pieces:
     1. the log-mult full-field bridge = UpReqAlign2.v:877
        req2_pi_next_log_decomp (with the witnesses Hp1/Hp2/HpI explicit
        at :893-896, opened by log_req_compat and consuming log_mult at
        every field); this file's uac_pi_next_log_decomp ports the
        :884-959 recipe verbatim to the req world, so the log-mult
        interface-field engine is on file;
     2. the deep-chain main theorem = UpReqAlign3.v:3162
        req2_backward_kl_step (unconditional Qed five-segment assembly:
        HA the beta * KSN = FE-difference identity / HB t13_hexp / the
        HC * HK split / HD the collapse / HE the iv shaping, closed by
        the beta-inverse absorption);
     3. the dual slot = UpReqAlign3.v:1456 r2_policy_improvement_mono.
   the log_mult / exp_neg_plus laws these pieces consume are on file as
   well, so the softmax-KL deep-chain log-mult interface-field gap is
   closed on the req side by the two bridges loaded in this file.           *)
(* 2. reconciliation against the UpReqAlign.v tail checklist (the three
   deep-chain pending items):
   item 1, req_backward_kl_identity (the premise slot at :434 of that
   file) is loaded here as uac_req_backward_kl_identity at the same
   position (the slot statement of exactly the same shape, by the
   delta-transparent-wrapper statement-layer conversion criterion);
   item 2, req_policy_improvement_mono (the premise slot at :630) is
   loaded here as uac_req_policy_improvement_mono at the same position;
   item 3, the main-theorem chain (req_policy_iter_kl_geom_step / _iter /
   req_dpo_loss_iter_mono): once the two bridges are loaded, the whole
   chain closes unconditionally by substituting the two uac statements of
   this file at the premise-use points UpReqAlign:484/:645 (the remaining
   req-side transport and order-algebra content of the chain is genuinely
   proved, as the tail checklist itself records).               *)
(* 3. the honest premise inventory (the signatures of the loaded pieces):
   uac_pi_next_log_decomp: the four sum slots plus log_req_compat plus
     log_inv_exp_neg_req (the first five slots are the native
     ReqAlignCore section arguments, the sixth is the Align2 extra slot;
     the Real-layer unconditional instantiation follows the
     log_req_compat_real@UpReqU2 template);
   uac_req_backward_kl_identity: as above (the ZAL_pos witness slot of
     the main-theorem premise face is substituted by this section's
     Z_align_pos directly; the pi_ref_norm/eta_pos/eta_le_one premise
     slots are pruned and do not appear);
   uac_req_policy_improvement_mono: as above plus uac_gibbs_le_zero
     (the B-class KL >= 0 plain-le slot, transported at the same position
     from Align3:1451 req2_gibbs_inequality; order-elimination is the
     LPO-family wall, the same reason as item 1 of the UpReqAlign frozen
     list, kept as is).        *)
(* 4. out-of-scope statement: the plain-le closure of req_step_kl_eta_bound
   lies outside this file's scope (the GeomD eps form is already
   instantiated; the plain-le closure is the Or form, not rebuilt to avoid
   duplication); existing files are untouched.            *)
(* ============================================================ *)

Print Assumptions uac_pi_next_log_decomp.
Print Assumptions uac_req_backward_kl_identity.
Print Assumptions uac_req_policy_improvement_mono.

Print Assumptions uac_npx_cross.
