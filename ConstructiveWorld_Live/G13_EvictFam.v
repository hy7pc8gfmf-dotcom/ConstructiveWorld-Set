(* ==========================================================================
   G13_EvictFam.v -- KV cache eviction identity family: Id layer + req layer.
   Mission. Section UpEvictId (the Id layer): detailed_balance, the
   detailed-balance breaking term identically zero
   (eviction_db_breaking_zero), the exact shape of the steady-state equation,
   and the partition increment family. Section EvictIdReq (an item-by-item
   req-layer copy): the 14 same-named req-shaped items such as
   req_boltzmann_factor_detailed_balance, with a per-item coverage checklist
   against the Id-layer originals.
   Dependencies. CW_ConstructiveWorld_219 (the S01_BaseRing .. S15_TailFEPUp
   chain), UpReqAlgebra, UpReqDist; Stdlib Extraction.
   References. Detailed balance and stationary identities of Markov-chain
   eviction transitions (a formalization of KV cache eviction policies).
   Constructivity. All items close with Qed; zero admission literals; no
   classical logic; the statement face is carried by the Set layer (order
   predicates and equalities are Set-valued; zero Prop leakage).
   Build. Rocq 9.1 direct invocation, coqc -Q . "" -native-compiler no
   (same-world rebuild in a vo shadow tree), cpu_guard wrapped load caps.
   ========================================================================== *)

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

Section UpEvictId.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* ---- Same world as the root AttentionGibbsBridge (variable names and premise shapes aligned) ---- *)

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition evict_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition evict_Z_thermo : R := sum_over_S evict_boltzmann_factor.

Variable Z_thermo_pos : lt zero evict_Z_thermo.

Definition evict_boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos evict_Z_thermo Z_thermo_pos) (evict_boltzmann_factor s).

Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.

Variable detailed_balance :
  forall s s',
    Id (mult (evict_boltzmann_dist_attn s) (transition s s'))
       (mult (evict_boltzmann_dist_attn s') (transition s' s)).

Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Definition evict_evicted_transition (s s' : S) : R :=
  if keep_dec s then
    if keep_dec s' then transition s s' else zero
  else zero.

Definition evict_evicted_partition : R :=
  sum_over_S (fun s => if keep_dec s then evict_boltzmann_factor s else zero).

Variable evicted_partition_pos : lt zero evict_evicted_partition.

Definition evict_evicted_boltzmann (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evict_evicted_partition evicted_partition_pos) (evict_boltzmann_factor s)
  else zero.

Definition evict_db_breaking (s s' : S) : R :=
  abs (minus (mult (evict_evicted_boltzmann s) (evict_evicted_transition s s'))
             (mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s))).

(* Keep-set-parameterized conditional partition function (needed for the monotonicity / increment comparisons; same as root L29446) *)
Definition evict_evicted_partition_of (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sum_over_S (fun s => if kd s then evict_boltzmann_factor s else zero).

(* ---- Local algebra helpers (no ready-made Set-layer minus_zero_r / opp_zero in the root) ---- *)

Lemma opp_zero_u : Id (opp zero) zero.
Proof.
  apply (plus_inv_unique zero (opp zero) zero (plus_opp zero)).
  exact (plus_zero zero).
Qed.

Lemma minus_zero_r_u : forall a : R, Id (minus a zero) a.
Proof.
  intro a.
  unfold minus.
  apply (id_trans (id_cong (fun x => plus a x) opp_zero_u) (plus_zero a)).
Qed.

(* ---- Factor-level detailed balance: detailed_balance with the
   evict_Z_thermo inverse cancelled ---- (the algebraic core of item 1a:
   bd(s)*t(s,s') == bd(s')*t(s',s); multiply both sides by evict_Z_thermo
   and absorb the inverse via inv_pos_correct + mult_one.) *)
Lemma boltzmann_factor_detailed_balance :
  forall s s' : S,
    Id (mult (evict_boltzmann_factor s) (transition s s'))
       (mult (evict_boltzmann_factor s') (transition s' s)).
Proof.
  intros s s'.
  pose proof (detailed_balance s s') as Hdb.
  unfold evict_boltzmann_dist_attn in Hdb.
  pose proof (inv_pos_correct evict_Z_thermo Z_thermo_pos) as HZinv.
  pose proof
    (id_trans
       (mult_assoc evict_Z_thermo
                   (mult (inv_pos evict_Z_thermo Z_thermo_pos) (evict_boltzmann_factor s))
                   (transition s s'))
       (id_cong (fun x => mult x (transition s s'))
                (id_trans (mult_assoc evict_Z_thermo (inv_pos evict_Z_thermo Z_thermo_pos)
                                        (evict_boltzmann_factor s))
                          (id_trans (id_cong (fun x => mult x (evict_boltzmann_factor s)) HZinv)
                                    (id_trans (mult_comm one (evict_boltzmann_factor s))
                                              (mult_one (evict_boltzmann_factor s))))))) as HZl.
  pose proof
    (id_trans
       (mult_assoc evict_Z_thermo
                   (mult (inv_pos evict_Z_thermo Z_thermo_pos) (evict_boltzmann_factor s'))
                   (transition s' s))
       (id_cong (fun x => mult x (transition s' s))
                (id_trans (mult_assoc evict_Z_thermo (inv_pos evict_Z_thermo Z_thermo_pos)
                                        (evict_boltzmann_factor s'))
                          (id_trans (id_cong (fun x => mult x (evict_boltzmann_factor s')) HZinv)
                                    (id_trans (mult_comm one (evict_boltzmann_factor s'))
                                              (mult_one (evict_boltzmann_factor s'))))))) as HZr.
  exact (id_trans (id_sym HZl) (id_trans (id_cong (fun x => mult evict_Z_thermo x) Hdb) HZr)).
Qed.

(* ---- Masked-kernel pointwise detailed balance (shared core of items
   1a/1b): if either end is evicted both products are zero; when both ends
   are kept, rescale by the factor-level detailed balance and the
   evict_evicted_partition inverse. All 4 branches constructive (same branch
   discipline as the all-kept special case at root L29573). *)
Lemma evicted_db_products :
  forall s s' : S,
    Id (mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s))
       (mult (evict_evicted_boltzmann s) (evict_evicted_transition s s')).
Proof.
  intros s s'.
  unfold evict_evicted_boltzmann, evict_evicted_transition.
  destruct (keep_dec s) as [Hs | Hs]; destruct (keep_dec s') as [Hs' | Hs'].
  - (* both kept: inv_ev*f(s')*t(s',s) == inv_ev*f(s)*t(s,s') *)
    pose proof (id_sym (boltzmann_factor_detailed_balance s s')) as Hf.
    apply (id_trans (id_sym (mult_assoc
                               (inv_pos evict_evicted_partition evicted_partition_pos)
                               (evict_boltzmann_factor s') (transition s' s)))).
    apply (id_trans (id_cong (fun x => mult (inv_pos evict_evicted_partition evicted_partition_pos) x)
                             Hf)).
    apply (mult_assoc (inv_pos evict_evicted_partition evicted_partition_pos)
                      (evict_boltzmann_factor s) (transition s s')).
  - (* s kept, s' evicted: both products are zero *)
    exact (id_trans (mult_zero zero)
                    (id_sym (mult_zero (mult (inv_pos evict_evicted_partition evicted_partition_pos)
                                             (evict_boltzmann_factor s))))).
  - (* s evicted, s' kept: both products are zero *)
    exact (id_trans (mult_zero (mult (inv_pos evict_evicted_partition evicted_partition_pos)
                                     (evict_boltzmann_factor s')))
                    (id_sym (mult_zero zero))).
  - (* both evicted *)
    reflexivity.
Qed.

(* ================= Item 1a: the breaking term is identically zero (the fluctuation-dissipation premise is wholly redundant) ============ *)

Theorem eviction_db_breaking_zero :
  forall s s' : S, Id (evict_db_breaking s s') zero.
Proof.
  intros s s'.
  unfold evict_db_breaking.
  (* Named-witness decomposition: swap witness -> subtract-from-self-zero witness -> abs reshaping witness -> zero closure; assembled in four named steps *)
  pose proof (id_sym (evicted_db_products s s')) as Hswap.
  pose proof (minus_self_zero
                (mult (evict_evicted_boltzmann s) (evict_evicted_transition s s'))
                (mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s))
                Hswap) as Hminuszero.
  pose proof (id_cong abs Hminuszero) as Habszero.
  exact (id_trans Habszero abs_zero).
Qed.

(* ================= Item 1b: the truncated-kernel steady-state equation
   (exact identity) ====================
   Shape matches the scan-report A1 draft verbatim:
   sum_{s'} ev_b(s')*ev_t(s',s) == ev_b(s)*sum_{s'} ev_t(s,s')
   (the keep factor appears explicitly on the right -- the masked-kernel row
   sum of ev_t(s,.) is in general < 1; it equals 1 only in the all-kept case,
   see the special case below). *)

Theorem evicted_boltzmann_steady_exact :
  forall s : S,
    Id (sum_over_S (fun s' => mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s)))
       (mult (evict_evicted_boltzmann s) (sum_over_S (fun s' => evict_evicted_transition s s'))).
Proof.
  intro s.
  apply (id_trans (sum_over_S_ext
                    (fun s' => mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s))
                    (fun s' => mult (evict_evicted_boltzmann s) (evict_evicted_transition s s'))
                    (fun s' => id_sym (evicted_db_products s' s)))).
  apply (sum_over_S_linear (evict_evicted_boltzmann s) (fun s' => evict_evicted_transition s s')).
Qed.

(* All-kept bridge: ev_t returns pointwise to t (cf. root L29506 eviction_transition_full) *)
Lemma eviction_transition_pointwise_full :
  (forall s, keep s) ->
  forall s s' : S, Id (evict_evicted_transition s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evict_evicted_transition.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + reflexivity.
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* All-kept row normalization of the masked kernel: sum ev_t(s,.) == 1 (absorbed by transition_normalization) *)
Lemma evicted_transition_row_sum_one :
  (forall s, keep s) ->
  forall s : S, Id (sum_over_S (fun s' => evict_evicted_transition s s')) one.
Proof.
  intros Hkall s.
  apply (id_trans (sum_over_S_ext (fun s' => evict_evicted_transition s s')
                                  (fun s' => transition s s')
                                  (fun s' => eviction_transition_pointwise_full Hkall s s'))).
  apply (transition_normalization s).
Qed.

(* Special case (bare ev_b(s) shape on the right): with all states kept, the truncated-kernel steady-state equation is the full steady-state equation *)
Corollary evicted_boltzmann_steady_full_keep :
  (forall s, keep s) ->
  forall s : S,
    Id (sum_over_S (fun s' => mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s)))
       (evict_evicted_boltzmann s).
Proof.
  intros Hkall s.
  (* Named-witness decomposition: steady-state witness -> row-normalization
     witness -> scaling-replacement witness -> multiply-by-one witness; each
     of the three hops named, the tail closed by explicit composition *)
  pose proof (evicted_boltzmann_steady_exact s) as Hsteady.
  pose proof (evicted_transition_row_sum_one Hkall s) as Hrowone.
  pose proof (id_cong (fun x => mult (evict_evicted_boltzmann s) x) Hrowone)
    as Hscale.
  pose proof (mult_one (evict_evicted_boltzmann s)) as Hmultone.
  exact (id_trans Hsteady (id_trans Hscale Hmultone)).
Qed.

(* ================= Item 1c: the Theorem 6.1 deviation is identically
   zero (a one-step corollary of 1b) =============
   In the root L29626 bound, |stationary gap| <= sum of evict_db_breaking;
   its right side vanishes term by term, so the stationary gap is identically
   zero -- the exact form of "the cost of eviction lies in support
   shrinkage, not in breaking stationarity". *)

Theorem eviction_steady_deviation_zero :
  forall s : S,
    Id (abs (minus (sum_over_S (fun s' => mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s)))
                   (mult (evict_evicted_boltzmann s) (sum_over_S (fun s' => evict_evicted_transition s s')))))
       zero.
Proof.
  intro s.
  (* Named-witness decomposition: steady-state witness -> subtract-from-self-zero witness -> abs reshaping witness -> zero closure *)
  pose proof (evicted_boltzmann_steady_exact s) as Hsteady.
  pose proof (minus_self_zero
                (sum_over_S (fun s' => mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s)))
                (mult (evict_evicted_boltzmann s) (sum_over_S (fun s' => evict_evicted_transition s s')))
                Hsteady) as Hminuszero.
  pose proof (id_cong abs Hminuszero) as Habszero.
  exact (id_trans Habszero abs_zero).
Qed.

Corollary eviction_steady_deviation_le_zero :
  forall s : S,
    le (abs (minus (sum_over_S (fun s' => mult (evict_evicted_boltzmann s') (evict_evicted_transition s' s)))
                   (mult (evict_evicted_boltzmann s) (sum_over_S (fun s' => evict_evicted_transition s s')))))
       zero.
Proof.
  intro s.
  apply (le_id_l _ zero zero).
  - apply (eviction_steady_deviation_zero s).
  - apply le_refl.
Qed.

(* ================= Item 2: the exact increment identity for keep-set
   growth ======================
   The equality upgrade of the monotone <= bound at L29485: when k1 is a
   subset of k2, the exact value of the newly kept mass equals the sum of the
   Boltzmann masses of the newly included states (kd2 true, kd1 false). *)

Lemma partition_increment_pointwise :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    Id (minus (if kd2 s then evict_boltzmann_factor s else zero)
              (if kd1 s then evict_boltzmann_factor s else zero))
       (if kd2 s then (if kd1 s then zero else evict_boltzmann_factor s) else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | H1]; destruct (kd2 s) as [H2 | H2].
  - (* kd1 s and kd2 s: f - f = 0 *)
    apply (minus_self_zero (evict_boltzmann_factor s) (evict_boltzmann_factor s)).
    apply id_refl.
  - (* kd1 s and not kd2 s: contradicts Hsub *)
    exact (match H2 (Hsub s H1) with end).
  - (* not kd1 s and kd2 s: f - 0 = f (a newly included state contributes its full mass) *)
    apply (minus_zero_r_u (evict_boltzmann_factor s)).
  - (* not kd1 s and not kd2 s: 0 - 0 = 0 *)
    apply (minus_self_zero zero zero).
    apply id_refl.
Qed.

Theorem eviction_partition_increment :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    Id (minus (evict_evicted_partition_of k2 kd2) (evict_evicted_partition_of k1 kd1))
       (sum_over_S (fun s => if kd2 s then (if kd1 s then zero else evict_boltzmann_factor s)
                            else zero)).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evict_evicted_partition_of.
  apply (id_trans (id_sym (sum_over_S_minus
                            (fun s => if kd2 s then evict_boltzmann_factor s else zero)
                            (fun s => if kd1 s then evict_boltzmann_factor s else zero)))).
  apply (sum_over_S_ext
           (fun s => minus (if kd2 s then evict_boltzmann_factor s else zero)
                           (if kd1 s then evict_boltzmann_factor s else zero))
           (fun s => if kd2 s then (if kd1 s then zero else evict_boltzmann_factor s) else zero)).
  intro s.
  apply (partition_increment_pointwise k1 k2 Hsub kd1 kd2 s).
Qed.

(* Parallel: the full-partition difference identity (equality upgrade of
   the <= bound at L29526) -- the evicted mass loss
   evict_Z_thermo - evict_evicted_partition(k) equals the sum of the masses
   of the evicted states. *)
Corollary eviction_partition_le_full_exact :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
    Id (minus evict_Z_thermo (evict_evicted_partition_of k kd))
       (sum_over_S (fun s => if kd s then zero else evict_boltzmann_factor s)).
Proof.
  intros k kd.
  unfold evict_Z_thermo, evict_evicted_partition_of.
  apply (id_trans (id_sym (sum_over_S_minus evict_boltzmann_factor
                            (fun s => if kd s then evict_boltzmann_factor s else zero)))).
  apply (sum_over_S_ext
           (fun s => minus (evict_boltzmann_factor s) (if kd s then evict_boltzmann_factor s else zero))
           (fun s => if kd s then zero else evict_boltzmann_factor s)).
  intro s.
  destruct (kd s) as [Hk | Hk].
  - apply (minus_self_zero (evict_boltzmann_factor s) (evict_boltzmann_factor s)).
    apply id_refl.
  - apply (minus_zero_r_u (evict_boltzmann_factor s)).
Qed.

End UpEvictId.

(* ---- Extraction check (extractability verification; G3 gate object) ---- *)
From Stdlib Require Import Extraction.
Extraction "up_evict_ww_probe.ml" evicted_db_products
  eviction_db_breaking_zero evicted_boltzmann_steady_exact
  evicted_boltzmann_steady_full_keep eviction_steady_deviation_zero
  eviction_partition_increment eviction_partition_le_full_exact.

(* ======== G13_EvictFam member: UpEvictIdReq (merged as-is, bringing its own Requires) ======== *)
(* ========================================================================= *)
(* UpEvictIdReq.v -- signature-migration batch 4, second module: the req companion of UpEvictId (14 items) *)
(*   Source: attn\UpEvictId.v (Section 6, the KV eviction identity batch) *)
(*   Plan: the signature-migration plan, batch 4, "module companions" *)
(*   Companion shape: an independent companion Section of req_* items, same tree as the source (the attn directory) *)
(* ------------------------------------------------------------------------- *)
(* Coverage check (req item name -> source Id original @ line; counting rule: *)
(* statements containing Id, or declarations with an Id-transplanted proof
   core, count; Variable assumption slots included; grep measured 16
   declarations, 2 frozen deductions):                                       *)
(*   item 1  req assumption slot transition_normalization    <- source L65 (Id summation normalization) *)
(*   item 2  req assumption slot detailed_balance            <- source L68 (Id detailed balance) *)
(*   item 3  req_boltzmann_factor_detailed_balance  <- source L117               *)
(*   item 4  req_evicted_db_products                <- source L154               *)
(*   item 5  req_eviction_db_breaking_zero          <- source L185 (main theorem one)     *)
(*   item 6  req_evicted_boltzmann_steady_exact     <- source L202 (main theorem two)     *)
(*   item 7  req_eviction_transition_pointwise_full <- source L216               *)
(*   item 8  req_evicted_transition_row_sum_one     <- source L230               *)
(*   item 9  req_evicted_boltzmann_steady_full_keep <- source L242               *)
(*   item 10 req_eviction_steady_deviation_zero     <- source L259               *)
(*   item 11 req_eviction_steady_deviation_le_zero  <- source L274               *)
(*   item 12 req_partition_increment_pointwise      <- source L290               *)
(*   item 13 req_eviction_partition_increment       <- source L313               *)
(*   item 14 req_eviction_partition_le_full_exact   <- source L336               *)
(*   Frozen deductions (2 items, with reasons on the batch 4 (d) list):      *)
(*   - source opp_zero_u @L101: the req counterpart exists from batch 2      *)
(*     (UpReqDist ReqDistCommon reqd_opp_zero); used here, not rebuilt.      *)
(*   - source minus_zero_r_u @L107: the req counterpart exists from batch 2  *)
(*     (UpReqDist ReqDistCommon reqd_minus_zero_r); items 12/14 use it.      *)
(* ------------------------------------------------------------------------- *)
(* Every Id->req difference is a genuine proof, not a transcription: the     *)
(* source id_trans/id_cong/id_sym chains are replaced everywhere by          *)
(* req_trans/req_mult_compat/req_sym; the source local minus_self_zero by    *)
(* batch-1 req_minus_self_zero; sum reshaping by the req_sum assumption      *)
(* slots + batch-2 reqd_sum_minus. Slot discipline: items 1/2 keep the       *)
(* req-shaped form of the source Id premises slot by slot (req               *)
(* normalization / req detailed balance), claims not enlarged;               *)
(* transition_nonneg kept at the source slot (unused by the 14 items; kept
   so the two worlds align verbatim). Grading: items 3/4/6/13/14 = A         *)
(* (genuine req chains, branch-by-branch constructive); 5/9/10 = A-
   (engine-item one-step assembly); 7/12 = B (branches + contradiction);     *)
(* 8/11 = B (direct field reference); 1/2 = assumption-slot migration.
   Discipline: pure term mode (zero rewrite / zero Morphisms); all           *)
(* statements Set-layer (req/le/lt/Or/sigT Set-valued; zero Prop leakage);
   every proof closes with Qed; zero banned literals.                        *)
(* ========================================================================= *)

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
Import RealInterfaceEnhancedMod.
(* Interface-face note (this tree's interface class is unparameterized; the
   same adaptation is registered in UpReqAlgebra and in the ablation
   companion of this module): the carrier is the global Cauchy
   real [Real], the class fields resolve through the global instance
   [RealEnhancedReal], and the equality face [req] is definitionally
   [real_eq] at that instance. The mathematical content of every statement
   is unchanged from the source-world statement face. *)
Notation R := Real.
(* Explicit concrete-carrier take (extraction-face fix, fa56b plan B
   discipline): the boxed-class fields [req]/[lt]/[le] at the global instance
   [RealEnhancedReal] are definitionally the global Set-carrier relations
   [real_eq]/[real_lt]/[real_le] (S02_CauchyComplete); binding the names to the
   concrete carriers here makes every statement take its carrier explicitly.
   Zero logical change (convertible at the instance) and zero Prop leakage
   (all three carriers are Set-valued). This is what keeps the extracted
   Obj.magic count at zero: the extractor sees one concrete carrier on both
   sides of every use site instead of an opaque boxed-class field. *)
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

Section EvictIdReq.

(* ---- req summation assumption slots (the source SumOver class,
   CW_ConstructiveWorld_219 L1400; the fields used here are carried to req
   one by one: the three items linear / add / ext; the le / nonneg /
   zero_nonneg / abs triangle fields are unused by the 14 items here, so no
   slots are created) ---- *)
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).

(* ---- The same eviction world as the source, adapted to this tree's unparameterized interface class (carrier = the global Real; fields resolve through the global instance RealEnhancedReal) ---- *)

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition evq_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition evq_Z_thermo : R := sumf evq_boltzmann_factor.

Variable Z_thermo_pos : lt zero evq_Z_thermo.

Definition evq_boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s).

Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').

(* item 1: req-shaped form of the source L65 Id summation normalization (assumption slot preserved bit for bit) *)
Variable transition_normalization :
  forall s, req (sumf (fun s' => transition s s')) one.

(* item 2: req-shaped form of the source L68 Id detailed balance (assumption slot preserved bit for bit) *)
Variable detailed_balance :
  forall s s',
    req (mult (evq_boltzmann_dist_attn s) (transition s s'))
        (mult (evq_boltzmann_dist_attn s') (transition s' s)).

Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Definition evq_evicted_transition (s s' : S) : R :=
  if keep_dec s then
    if keep_dec s' then transition s s' else zero
  else zero.

Definition evq_evicted_partition : R :=
  sumf (fun s => if keep_dec s then evq_boltzmann_factor s else zero).

Variable evicted_partition_pos : lt zero evq_evicted_partition.

Definition evq_evicted_boltzmann (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evq_evicted_partition evicted_partition_pos) (evq_boltzmann_factor s)
  else zero.

Definition evq_db_breaking (s s' : S) : R :=
  abs (req_minus (mult (evq_evicted_boltzmann s) (evq_evicted_transition s s'))
                 (mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s))).

(* Keep-set-parameterized conditional partition function (same shape as source L96) *)
Definition evq_evicted_partition_of (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sumf (fun s => if kd s then evq_boltzmann_factor s else zero).

(* ---- item 3: factor-level detailed balance (genuine req-chain proof:
   the source id_trans/id_cong chain replaced throughout by
   req_trans/req_mult_compat; the inv_pos_correct field absorbs the
   evq_Z_thermo inverse) ---- *)

(* Z*(invZ*f) == f (inverse-scaling core, shared by the s / s' branches) *)
Lemma req_evict_zinv_scale :
  forall s0 : S,
    req (mult evq_Z_thermo (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s0)))
        (evq_boltzmann_factor s0).
Proof.
  intro s0.
  assert (Hinv : req (mult evq_Z_thermo (inv_pos evq_Z_thermo Z_thermo_pos)) one).
  { exact (inv_pos_correct evq_Z_thermo Z_thermo_pos). }
  apply (req_trans (mult evq_Z_thermo (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s0)))
                   (mult (mult evq_Z_thermo (inv_pos evq_Z_thermo Z_thermo_pos)) (evq_boltzmann_factor s0))
                   (evq_boltzmann_factor s0)).
  - apply mult_assoc.
  - apply (req_trans (mult (mult evq_Z_thermo (inv_pos evq_Z_thermo Z_thermo_pos)) (evq_boltzmann_factor s0))
                     (mult one (evq_boltzmann_factor s0))
                     (evq_boltzmann_factor s0)).
    + exact (req_mult_compat (mult evq_Z_thermo (inv_pos evq_Z_thermo Z_thermo_pos)) one
                             (evq_boltzmann_factor s0) (evq_boltzmann_factor s0)
                             Hinv (req_refl (evq_boltzmann_factor s0))).
    + exact (req_trans (mult one (evq_boltzmann_factor s0))
                       (mult (evq_boltzmann_factor s0) one)
                       (evq_boltzmann_factor s0)
                       (mult_comm one (evq_boltzmann_factor s0))
                       (mult_one (evq_boltzmann_factor s0))).
Qed.

Lemma req_boltzmann_factor_detailed_balance :
  forall s s' : S,
    req (mult (evq_boltzmann_factor s) (transition s s'))
        (mult (evq_boltzmann_factor s') (transition s' s)).
Proof.
  intros s s'.
  pose proof (detailed_balance s s') as Hdb.
  unfold evq_boltzmann_dist_attn in Hdb.
  (* HZl : Z*((invZ*f s)*t s s') == f s*t s s' *)
  assert (HZl : req (mult evq_Z_thermo
                          (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s))
                                (transition s s')))
                    (mult (evq_boltzmann_factor s) (transition s s'))).
  { apply (req_trans
             (mult evq_Z_thermo
                   (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s))
                         (transition s s')))
             (mult (mult evq_Z_thermo (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s)))
                   (transition s s'))
             (mult (evq_boltzmann_factor s) (transition s s'))).
    - apply mult_assoc.
    - exact (req_mult_compat
                (mult evq_Z_thermo (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s)))
                (evq_boltzmann_factor s)
                (transition s s') (transition s s')
                (req_evict_zinv_scale s)
                (req_refl (transition s s'))). }
  (* HZr : Z*((invZ*f s')*t s' s) == f s'*t s' s *)
  assert (HZr : req (mult evq_Z_thermo
                          (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s'))
                                (transition s' s)))
                    (mult (evq_boltzmann_factor s') (transition s' s))).
  { apply (req_trans
             (mult evq_Z_thermo
                   (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s'))
                         (transition s' s)))
             (mult (mult evq_Z_thermo (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s')))
                   (transition s' s))
             (mult (evq_boltzmann_factor s') (transition s' s))).
    - apply mult_assoc.
    - exact (req_mult_compat
                (mult evq_Z_thermo (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s')))
                (evq_boltzmann_factor s')
                (transition s' s) (transition s' s)
                (req_evict_zinv_scale s')
                (req_refl (transition s' s))). }
  exact (req_trans
           (mult (evq_boltzmann_factor s) (transition s s'))
           (mult evq_Z_thermo
                 (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s))
                       (transition s s')))
           (mult (evq_boltzmann_factor s') (transition s' s))
           (req_sym (mult evq_Z_thermo
                          (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s))
                                (transition s s')))
                    (mult (evq_boltzmann_factor s) (transition s s'))
                    HZl)
           (req_trans
              (mult evq_Z_thermo
                    (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s))
                          (transition s s')))
              (mult evq_Z_thermo
                    (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s'))
                          (transition s' s)))
              (mult (evq_boltzmann_factor s') (transition s' s))
              (req_mult_compat evq_Z_thermo evq_Z_thermo
                 (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s))
                       (transition s s'))
                 (mult (mult (inv_pos evq_Z_thermo Z_thermo_pos) (evq_boltzmann_factor s'))
                       (transition s' s))
                 (req_refl evq_Z_thermo) Hdb)
              HZr)).
Qed.

(* ---- item 4: masked-kernel pointwise detailed balance (genuine req
   proof: all 4 branches constructive; the both-kept branch rescales the
   evq_evicted_partition inverse via item 3 + the mult assoc/compat req
   fields) ---- *)
Lemma req_evicted_db_products :
  forall s s' : S,
    req (mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s))
        (mult (evq_evicted_boltzmann s) (evq_evicted_transition s s')).
Proof.
  intros s s'.
  unfold evq_evicted_boltzmann, evq_evicted_transition.
  destruct (keep_dec s) as [Hs | Hs]; destruct (keep_dec s') as [Hs' | Hs'].
  - (* both kept: inv_ev*f(s')*t(s',s) == inv_ev*f(s)*t(s,s') (three-hop req chain) *)
    apply (req_trans
             (mult (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                         (evq_boltzmann_factor s'))
                   (transition s' s))
             (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                   (mult (evq_boltzmann_factor s') (transition s' s)))
             (mult (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                         (evq_boltzmann_factor s))
                   (transition s s'))).
    + exact (req_sym (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                           (mult (evq_boltzmann_factor s') (transition s' s)))
                     (mult (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                                 (evq_boltzmann_factor s'))
                           (transition s' s))
                     (mult_assoc (inv_pos evq_evicted_partition evicted_partition_pos)
                                 (evq_boltzmann_factor s') (transition s' s))).
    + apply (req_trans
                (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                      (mult (evq_boltzmann_factor s') (transition s' s)))
                (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                      (mult (evq_boltzmann_factor s) (transition s s')))
                (mult (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                            (evq_boltzmann_factor s))
                      (transition s s'))).
      * exact (req_mult_compat
                  (inv_pos evq_evicted_partition evicted_partition_pos)
                  (inv_pos evq_evicted_partition evicted_partition_pos)
                  (mult (evq_boltzmann_factor s') (transition s' s))
                  (mult (evq_boltzmann_factor s) (transition s s'))
                  (req_refl (inv_pos evq_evicted_partition evicted_partition_pos))
                  (req_sym (mult (evq_boltzmann_factor s) (transition s s'))
                           (mult (evq_boltzmann_factor s') (transition s' s))
                           (req_boltzmann_factor_detailed_balance s s'))).
      * apply mult_assoc.
  - (* s kept, s' evicted: both products are zero *)
    exact (req_trans (mult zero zero) zero
                     (mult (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                                 (evq_boltzmann_factor s))
                           zero)
                     (mult_zero zero)
                     (req_sym (mult (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                                          (evq_boltzmann_factor s))
                                    zero)
                              zero
                              (mult_zero (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                                               (evq_boltzmann_factor s))))).
  - (* s evicted, s' kept: both products are zero *)
    exact (req_trans (mult (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                                 (evq_boltzmann_factor s'))
                           zero)
                     zero
                     (mult zero zero)
                     (mult_zero (mult (inv_pos evq_evicted_partition evicted_partition_pos)
                                      (evq_boltzmann_factor s')))
                     (req_sym (mult zero zero) zero (mult_zero zero))).
  - (* both evicted *)
    exact (req_refl (mult zero zero)).
Qed.

(* ================= item 5 (main theorem one): the breaking term is identically zero ============================= *)
(* source L185: |db| identically zero. Genuine req-flavored proof: the
   source local minus_self_zero is replaced by the batch-1
   req_minus_self_zero (engine L728); the abs reshaping goes through
   req_abs_compat + abs_zero. *)
Theorem req_eviction_db_breaking_zero :
  forall s s' : S, req (evq_db_breaking s s') zero.
Proof.
  intros s s'.
  unfold evq_db_breaking.
  (* Named-witness decomposition: req swap witness -> req
   subtract-from-self-zero witness -> req abs reshaping witness -> closure
   via req_trans with all four arguments explicit *)
  pose proof (req_sym
                (mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s))
                (mult (evq_evicted_boltzmann s) (evq_evicted_transition s s'))
                (req_evicted_db_products s s')) as Hswap.
  pose proof (req_minus_self_zero
                (mult (evq_evicted_boltzmann s) (evq_evicted_transition s s'))
                (mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s))
                Hswap) as Hminuszero.
  pose proof (req_abs_compat
                (req_minus (mult (evq_evicted_boltzmann s) (evq_evicted_transition s s'))
                           (mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
                zero
                Hminuszero) as Habszero.
  exact (req_trans
           (abs (req_minus (mult (evq_evicted_boltzmann s) (evq_evicted_transition s s'))
                           (mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s))))
           (abs zero)
           zero
           Habszero
           abs_zero).
Qed.

(* ================= item 6 (main theorem two): truncated-kernel steady-state equation (exact identity) ============ *)
(* source L202: sum ev_b*ev_t == ev_b(s)*sum ev_t. Genuine req-flavored
   proof: sum_over_S_ext replaced by the req sum_ext assumption slot
   (pointwise req_sym from item 4); sum_over_S_linear replaced by the req
   sum_linear assumption slot. *)
Theorem req_evicted_boltzmann_steady_exact :
  forall s : S,
    req (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
        (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s'))).
Proof.
  intro s.
  apply (req_trans
           (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
           (sumf (fun s' => mult (evq_evicted_boltzmann s) (evq_evicted_transition s s')))
           (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))).
  - exact (sum_ext
             (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s))
             (fun s' => mult (evq_evicted_boltzmann s) (evq_evicted_transition s s'))
             (fun s' => req_sym (mult (evq_evicted_boltzmann s) (evq_evicted_transition s s'))
                                (mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s))
                                (req_evicted_db_products s' s))).
  - exact (sum_linear (evq_evicted_boltzmann s) (fun s' => evq_evicted_transition s s')).
Qed.

(* ---- item 7: all-kept bridge (source L216; the only req difference is
   the req_refl reshaping -- the definition of evq_evicted_transition has
   zero Id content; branch enumeration + contradiction elimination as in the
   source) ---- *)
Lemma req_eviction_transition_pointwise_full :
  (forall s, keep s) ->
  forall s s' : S, req (evq_evicted_transition s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evq_evicted_transition.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + exact (req_refl (transition s s')).
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* ---- item 8: all-kept row normalization of the masked kernel (source L230; direct reference to the req summation assumption slots) ---- *)
Lemma req_evicted_transition_row_sum_one :
  (forall s, keep s) ->
  forall s : S, req (sumf (fun s' => evq_evicted_transition s s')) one.
Proof.
  intros Hkall s.
  apply (req_trans (sumf (fun s' => evq_evicted_transition s s'))
                   (sumf (fun s' => transition s s')) one).
  - exact (sum_ext (fun s' => evq_evicted_transition s s')
                   (fun s' => transition s s')
                   (fun s' => req_eviction_transition_pointwise_full Hkall s s')).
  - exact (transition_normalization s).
Qed.

(* ---- item 9: all-kept special case (source L242; closed by req_mult_one_r) ---- *)
Corollary req_evicted_boltzmann_steady_full_keep :
  (forall s, keep s) ->
  forall s : S,
    req (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
        (evq_evicted_boltzmann s).
Proof.
  intros Hkall s.
  apply (req_trans
           (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
           (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))
           (evq_evicted_boltzmann s)).
  - exact (req_evicted_boltzmann_steady_exact s).
  - exact (req_trans
             (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))
             (mult (evq_evicted_boltzmann s) one)
             (evq_evicted_boltzmann s)
             (req_mult_compat (evq_evicted_boltzmann s) (evq_evicted_boltzmann s)
                              (sumf (fun s' => evq_evicted_transition s s')) one
                              (req_refl (evq_evicted_boltzmann s))
                              (req_evicted_transition_row_sum_one Hkall s))
             (req_mult_one_r (evq_evicted_boltzmann s))).
Qed.

(* ---- item 10: the Theorem 6.1 deviation is identically zero (source L259; the req_minus_self_zero engine item) ---- *)
Theorem req_eviction_steady_deviation_zero :
  forall s : S,
    req (abs (req_minus
                 (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
                 (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))))
         zero.
Proof.
  intro s.
  (* Named-witness decomposition: steady-state witness -> req
   subtract-from-self-zero witness -> req abs reshaping witness -> closure
   via req_trans with all four arguments explicit (the sumf branch is
   isomorphic to main theorem one) *)
  pose proof (req_evicted_boltzmann_steady_exact s) as Hsteady.
  pose proof (req_minus_self_zero
                (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
                (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))
                Hsteady) as Hminuszero.
  pose proof (req_abs_compat
                (req_minus
                   (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
                   (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s'))))
                zero
                Hminuszero) as Habszero.
  exact (req_trans
           (abs (req_minus
                   (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
                   (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))))
           (abs zero)
           zero
           Habszero
           abs_zero).
Qed.

(* ---- item 11: parallel le shape (source L274; direct reference to the req-interface le_id_l field) ---- *)
Corollary req_eviction_steady_deviation_le_zero :
  forall s : S,
    le (abs (req_minus
                (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
                (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))))
       zero.
Proof.
  intro s.
  (* Named-witness decomposition: req zero witness + le reflexivity witness both named; closure via le_id_l with all three value arguments explicit *)
  pose proof (req_eviction_steady_deviation_zero s) as Hreqzero.
  pose proof (le_refl zero) as Hlezero.
  exact (le_id_l
           (abs (req_minus
                   (sumf (fun s' => mult (evq_evicted_boltzmann s') (evq_evicted_transition s' s)))
                   (mult (evq_evicted_boltzmann s) (sumf (fun s' => evq_evicted_transition s s')))))
           zero zero
           Hreqzero
           Hlezero).
Qed.

(* ---- item 12: the pointwise increment (source L290; genuine
   req-flavored proof: req_minus_self_zero + batch-2 reqd_minus_zero_r
   (the use site of the frozen-deduction item)) ---- *)
Lemma req_partition_increment_pointwise :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    req (req_minus (if kd2 s then evq_boltzmann_factor s else zero)
                   (if kd1 s then evq_boltzmann_factor s else zero))
        (if kd2 s then (if kd1 s then zero else evq_boltzmann_factor s) else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | H1]; destruct (kd2 s) as [H2 | H2].
  - (* kd1 s and kd2 s: f - f == 0 *)
    exact (req_minus_self_zero (evq_boltzmann_factor s) (evq_boltzmann_factor s)
                               (req_refl (evq_boltzmann_factor s))).
  - (* kd1 s and not kd2 s: contradicts Hsub *)
    exact (match H2 (Hsub s H1) with end).
  - (* not kd1 s and kd2 s: f - 0 == f (batch-2 reqd_minus_zero_r use site) *)
    exact (reqd_minus_zero_r (evq_boltzmann_factor s)).
  - (* not kd1 s and not kd2 s: 0 - 0 == 0 *)
    exact (req_minus_self_zero zero zero (req_refl zero)).
Qed.

(* ---- item 13: the exact increment identity for keep-set growth
   (source L313; genuine req-flavored proof: sum_over_S_minus replaced by
   batch-2 reqd_sum_minus (assumption slots aligned bit for bit), then
   pointwise closure rearranged via req sum_ext) ---- *)
Theorem req_eviction_partition_increment :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    req (req_minus (evq_evicted_partition_of k2 kd2) (evq_evicted_partition_of k1 kd1))
        (sumf (fun s => if kd2 s then (if kd1 s then zero else evq_boltzmann_factor s)
                            else zero)).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evq_evicted_partition_of.
  apply (req_trans
           (req_minus (sumf (fun s => if kd2 s then evq_boltzmann_factor s else zero))
                      (sumf (fun s => if kd1 s then evq_boltzmann_factor s else zero)))
           (sumf (fun s => req_minus (if kd2 s then evq_boltzmann_factor s else zero)
                                     (if kd1 s then evq_boltzmann_factor s else zero)))
           (sumf (fun s => if kd2 s then (if kd1 s then zero else evq_boltzmann_factor s)
                                 else zero))).
  - exact (req_sym
             (sumf (fun s => req_minus (if kd2 s then evq_boltzmann_factor s else zero)
                                       (if kd1 s then evq_boltzmann_factor s else zero)))
             (req_minus (sumf (fun s => if kd2 s then evq_boltzmann_factor s else zero))
                        (sumf (fun s => if kd1 s then evq_boltzmann_factor s else zero)))
             (reqd_sum_minus S sumf sum_ext sum_add sum_linear
                (fun s => if kd2 s then evq_boltzmann_factor s else zero)
                (fun s => if kd1 s then evq_boltzmann_factor s else zero))).
  - apply sum_ext.
    intro s.
    exact (req_partition_increment_pointwise k1 k2 Hsub kd1 kd2 s).
Qed.

(* ---- item 14: the full-partition difference identity (source L336; genuine req-flavored proof, same discipline as item 13) ---- *)
Corollary req_eviction_partition_le_full_exact :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
    req (req_minus evq_Z_thermo (evq_evicted_partition_of k kd))
        (sumf (fun s => if kd s then zero else evq_boltzmann_factor s)).
Proof.
  intros k kd.
  unfold evq_Z_thermo, evq_evicted_partition_of.
  apply (req_trans
           (req_minus (sumf evq_boltzmann_factor)
                      (sumf (fun s => if kd s then evq_boltzmann_factor s else zero)))
           (sumf (fun s => req_minus (evq_boltzmann_factor s)
                                     (if kd s then evq_boltzmann_factor s else zero)))
           (sumf (fun s => if kd s then zero else evq_boltzmann_factor s))).
  - exact (req_sym
             (sumf (fun s => req_minus (evq_boltzmann_factor s)
                                       (if kd s then evq_boltzmann_factor s else zero)))
             (req_minus (sumf evq_boltzmann_factor)
                        (sumf (fun s => if kd s then evq_boltzmann_factor s else zero)))
             (reqd_sum_minus S sumf sum_ext sum_add sum_linear
                evq_boltzmann_factor
                (fun s => if kd s then evq_boltzmann_factor s else zero))).
  - apply sum_ext.
    intro s.
    destruct (kd s) as [Hk | Hk].
    + (* kd s: f - f == 0 *)
      exact (req_minus_self_zero (evq_boltzmann_factor s) (evq_boltzmann_factor s)
                                 (req_refl (evq_boltzmann_factor s))).
    + (* not kd s: f - 0 == f (batch-2 reqd_minus_zero_r use site) *)
      exact (reqd_minus_zero_r (evq_boltzmann_factor s)).
Qed.

End EvictIdReq.

(* ---- Extraction check (G3 gate object; the extracted output is scanned
   for unsafe primitives and the files removed once verified) ----
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "b4b_evictid_g3.ml" req_evicted_db_products
  req_eviction_db_breaking_zero req_evicted_boltzmann_steady_exact
  req_evicted_boltzmann_steady_full_keep req_eviction_steady_deviation_zero
  req_eviction_partition_increment req_eviction_partition_le_full_exact.
*)

(* -- Assumption-face self-audit of the replaced items (slice six; all ten listed items should report Closed under the global context) -- *)
Print Assumptions eviction_db_breaking_zero.
Print Assumptions evicted_boltzmann_steady_exact.
Print Assumptions evicted_transition_row_sum_one.
Print Assumptions evicted_boltzmann_steady_full_keep.
Print Assumptions eviction_steady_deviation_zero.
Print Assumptions opp_zero_u.
Print Assumptions minus_zero_r_u.
Print Assumptions req_eviction_db_breaking_zero.
Print Assumptions req_eviction_steady_deviation_zero.
Print Assumptions req_eviction_steady_deviation_le_zero.
