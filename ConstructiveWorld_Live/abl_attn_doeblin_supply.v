(* ==========================================================================)
   abl_attn_doeblin_supply.v - AT1 AttnDoeblin pilot group (supply wave 5,
   non-frozen best start): Doeblin contraction data slots + smooth-kernel
   construction family, 8 supply theorems.
   Mission.  Pilot supply of the coverage-graph AttnDoeblin row (order
     L16: 37 slots = constructible 7 / green 2 / yellow 14 / white 14);
     the per-slot four-step triage takes all 7 white slots (:154 u_norm,
     :156 delta_lt_one, :158 transition_nonneg, :159 transition_row,
     :160 minorization, :467 z_lb, :468 z_ub) plus 5 param slots by
     constructive values (:153 u, :155 delta, :157 transition, :466 z,
     :460 enum): 12 total.  Shape A direct witness (sigT boxed: delta-one
     instance, uniform normalization, zero-band z); shape B full-argument
     feed (kernel three certificates - nonneg / row stochastic /
     minorization; the marker theorem feeds the kernel to u_tv_contraction
     for the 1-delta contraction, minorization discharged at the premise
     face; plus the Part A master witness, real_expf_realizable Part C
     role).  temp(:462)/expf(:471) unconstructed; :161/:165 yellow and
     :472-476 expf five = adjacent yellow, no duplicate supply.
   Dependencies.  S01_BaseRing .. S15_TailFEPUp + AttnDoeblin, read-only,
     originals zero-byte untouched, zero cascade; real uses of AttnDoeblin
     exports nat_to_R / nat_to_R_pos / delta_absorb_u / u_tv_contraction
     (non-nominal Require).
   References.  Forms per the pool recipe notes; full anchor, duplicate-
     supply and build registrations in the blocks below; u_tv_contraction
     exit-section order machine-read (eleven args, no transition_nonneg).
   Constructivity.  A zero-admission file: no admission statements, no
     suspended premises, no classical logic; details in the block below.
   Build.  env.sh sourced, COQLIB/ROCQLIB unset, stack 65532 pre-set, rocq
     process gate <= 1 then single-lane compile; full recipe below.
   ========================================================================== *)

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
Require Import AttnDoeblin.

(* ============================================================ *)
(* Anchor and duplicate-supply registration block (no duplicate  *)
(* supply claims, per the wave-1 registration precedent):        *)
(*   (1) archive :164 abs_ge_zero_id_cc and :482 bs_abs are      *)
(*   verbatim-same to ali_abs_ge_zero_id@AbsLeId.v:42, already   *)
(*   supplied (chain fa53 piece 3); this file touches neither;   *)
(*   anchor comparison in the delivery report.                   *)
(*   (2) archive :472-476 expf five slots are covered by the     *)
(*   in-service master witness real_expf_realizable@             *)
(*   AttnDoeblin.v:771 plus the uabl_attn_full_instance.v Part A *)
(*   instance face; zero touch (likewise the adjacent yellow slots             *)
(*   :161/:165 - no duplicate establishment, the same in-service face          *)
(*   covers them).                                                             *)
(*   (3) archive :479/:482/:483 three interface pieces and the   *)
(*   :461/:463/:465/:492 world certificate slots are the uabl    *)
(*   Part B/C nineteen-field instance face in service (Fin2),    *)
(*   zero duplication; the Id-face conditional form is the uabl  *)
(*   Part E form (DO premise accompanying) in service.           *)
(*   (4) archive :154/:156/:158/:159/:160/:467/:468 seven white  *)
(*   proposition slots are this file's territory; no in-service  *)
(*   same-statement supply (coverage-graph white-14 family-level *)
(*   verdict plus this file's per-slot archive triage, double    *)
(*   registered).                                                *)
(* ============================================================ *)
(* Registration supplements.  Constructivity detail: statement   *)
(*   faces all Set-layer (Id/le/lt/Or/And are S01 Set-valued     *)
(*   definitions; sigT/And boxing per the real_expf_realizable   *)
(*   style); the smooth-kernel family premises u_norm / u_nonneg *)
(*   / delta_nonneg / delta_lt_one / transition_nonneg /         *)
(*   transition_row are the explicit preservation of the         *)
(*   slot-family general-form data obligations (declared, no     *)
(*   hard proofs); the marker theorem takes the three interface  *)
(*   pieces :161/:164/:165 as explicit premises (slot faces      *)
(*   verbatim); every conclusion Qed genuinely closed; Print     *)
(*   Assumptions over eleven names all Closed (name list = Qed   *)
(*   count = 11, zero diff); extraction Obj.magic segmented      *)
(*   counts declared (G3 control scope: u_tv_contraction         *)
(*   extracted alone = the library-layer closure control arm).   *)
(*   Build recipe: source Live/toolchain/env.sh && unset COQLIB  *)
(*   ROCQLIB && ulimit -s 65532, then rocq process count <= 1,   *)
(*   single lane: nice -19 rocq c -native-compiler no -Q <unified*)
(*   cache root> "" abl_attn_doeblin_supply.v; green set: EXIT=0 *)
(*   / true-error lines 0 / .vo head 8 bytes 436f7121 00015ff4 / *)
(*   .vo newer than .v; fifth certificate rocqchk -o with module *)
(*   name abl_attn_doeblin_supply.  Delivery claim: a zero-      *)
(*   admission file - no admission statements, no suspended      *)
(*   premises, no classical logic, every conclusion Qed closed.  *)
(* ============================================================ *)

(* ============================================================ *)
(* Zone 1: delta_lt_one slot (:156) one-instance witness - the   *)
(*   step-2 instance supply takes the zero instance, one shot    *)
(*   via one_pos; statement face = sigT witness form (Set layer, *)
(*   layer red line clear).                                      *)
(* ============================================================ *)

Section AblaDeltaSlot.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Theorem abla_delta_lt_one_witness : sigT (fun d : R => lt d one).
Proof.
  exact (existT _ zero one_pos).
Qed.

End AblaDeltaSlot.

(* ============================================================ *)
(* Zone 2: u_norm slot (:154) uniform-distribution normalization *)
(*   witness - generic S form (cons-form nonemptiness, tspu_p7b3 *)
(*   recipe); the list sum is restated in-file (abla_list_sum;   *)
(*   66-piece pool rule: no reuse of in-file Section-local       *)
(*   Fixpoints, double-registered); nat_to_R / nat_to_R_pos from *)
(*   the AttnDoeblin export face (signatures machine-pinned by   *)
(*   the probe file).                                            *)
(* ============================================================ *)

Section AblaUnifWitness.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Fixpoint abla_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (abla_list_sum f t)
  end.

Lemma abla_list_sum_const : forall (c : R) (l : list S),
  Id (abla_list_sum (fun _ : S => c) l) (mult (nat_to_R (length l)) c).
Proof.
  intros c l. induction l as [| x t IH].
  - apply (id_sym (id_trans (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : Id (plus c (abla_list_sum (fun _ : S => c) t))
                       (plus (mult c one) (mult c (nat_to_R (length t))))).
    { exact (id_cong2 plus (id_sym (mult_one c))
                           (id_trans IH (mult_comm (nat_to_R (length t)) c))). }
    apply (id_trans Hstep).
    apply (id_trans (id_sym (distrib c one (nat_to_R (length t))))).
    apply (mult_comm c (plus one (nat_to_R (length t)))).
Qed.

(* Supply 1: u_norm slot (:154) witness form - on any nonempty   *)
(*   finite world (cons-form enum + the pinned-sum axiom), the   *)
(*   uniform distribution fun _ => 1/|enum| is a constructive    *)
(*   witness of normalization.                                   *)
Theorem abla_unif_norm_witness :
  forall (x : S) (rest : list S),
    (forall g : S -> R, Id (sum_over_S g) (abla_list_sum g (x :: rest))) ->
    sigT (fun uu : S -> R => Id (sum_over_S uu) one).
Proof.
  intros x rest Hsum_eq.
  assert (HnR : lt zero (nat_to_R (length (x :: rest)))).
  { exact (nat_to_R_pos (length rest)). }
  exists (fun _ : S => inv_pos (nat_to_R (length (x :: rest))) HnR).
  apply (id_trans (Hsum_eq (fun _ : S => inv_pos (nat_to_R (length (x :: rest))) HnR))).
  apply (id_trans (abla_list_sum_const
                    (inv_pos (nat_to_R (length (x :: rest))) HnR) (x :: rest))).
  exact (inv_pos_correct (nat_to_R (length (x :: rest))) HnR).
Qed.

End AblaUnifWitness.

(* ============================================================ *)
(* Zone 3: transition three slots (:158/:159/:160) smooth-kernel *)
(*   construction family + marker theorem - Doeblin smoothing:   *)
(*   T_delta := (1-delta)*T + delta*u.  The six premises are the *)
(*   explicit preservation of the general-form data obligations  *)
(*   (incl. delta_nonneg needed for nonnegativity of delta*u;    *)
(*   declared); conclusions = the constructed kernel satisfies   *)
(*   the three slots slot-by-slot; the marker theorem feeds the  *)
(*   constructed kernel to u_tv_contraction (full exit-section   *)
(*   arguments, probe-machine-read order), discharging the       *)
(*   minorization slot at the marker premise face (shape B feed, *)
(*   reduced form, rta_ precedent).                              *)
(* ============================================================ *)

Section AblaSmoothFamily.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable u_nonneg : forall s : S, le zero (u s).
Variable delta : R.
Variable delta_nonneg : le zero delta.
Variable delta_lt_one : lt delta one.
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s' : S, le zero (transition s s').
Variable transition_row : forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Let omd := minus one delta.

Definition abla_smooth_kernel (s s' : S) : R :=
  plus (mult omd (transition s s')) (mult delta (u s')).

Lemma abla_omd_nonneg : le zero omd.
Proof.
  exact (le_minus_nonneg delta one (lt_le_iff delta one (inl delta_lt_one))).
Qed.

Lemma abla_delta_plus_omd : Id (plus delta omd) one.
Proof.
  apply (id_trans (id_sym (id_cong2 plus (mult_one delta) (mult_one omd)))
                  (delta_absorb_u delta one)).
Qed.

(* Supply 3: transition_nonneg slot (:158) constructed form -    *)
(*   the smooth kernel is pointwise nonnegative.                 *)
Theorem abla_smooth_nonneg : forall s s' : S, le zero (abla_smooth_kernel s s').
Proof.
  intros s s'. unfold abla_smooth_kernel.
  apply (le_id_l zero (plus zero zero)
         (plus (mult omd (transition s s')) (mult delta (u s')))
         (id_sym (plus_zero zero))).
  apply (le_plus_compat zero (mult omd (transition s s'))
                        zero (mult delta (u s'))).
  - exact (le_mult_nonneg_t12 omd (transition s s')
             abla_omd_nonneg (transition_nonneg s s')).
  - exact (le_mult_nonneg_t12 delta (u s') delta_nonneg (u_nonneg s')).
Qed.

(* Supply 4: transition_row slot (:159) constructed form - the   *)
(*   smooth kernel is row stochastic.                            *)
Theorem abla_smooth_row :
  forall s : S, Id (sum_over_S (fun s' : S => abla_smooth_kernel s s')) one.
Proof.
  intro s. unfold abla_smooth_kernel.
  apply (id_trans (sum_over_S_add (fun s' : S => mult omd (transition s s'))
                                  (fun s' : S => mult delta (u s')))).
  apply (id_trans (id_cong2 plus
    (id_trans (sum_over_S_linear omd (fun s' : S => transition s s'))
              (id_cong (fun w : R => mult omd w) (transition_row s)))
    (id_trans (sum_over_S_linear delta u)
              (id_cong (fun w : R => mult delta w) u_norm)))).
  apply (id_trans (id_cong2 plus (mult_one omd) (mult_one delta))).
  apply (id_trans (plus_comm omd delta)).
  exact abla_delta_plus_omd.
Qed.

(* Supply 5: minorization slot (:160) constructed form -         *)
(*   delta*u <= (1-delta)*T + delta*u.  The general slot form    *)
(*   (minorization over an arbitrary transition) is a genuine-   *)
(*   premise data obligation; this file supplies its N3          *)
(*   constructive-instance route: the smooth kernel satisfies    *)
(*   minorization unconditionally.                               *)
Theorem abla_smooth_minorization :
  forall s s' : S, le (mult delta (u s')) (abla_smooth_kernel s s').
Proof.
  intros s s'. unfold abla_smooth_kernel.
  apply (le_id_l (mult delta (u s')) (plus (mult delta (u s')) zero)
         (plus (mult omd (transition s s')) (mult delta (u s')))
         (id_sym (plus_zero (mult delta (u s'))))).
  exact (le_id_l (plus (mult delta (u s')) zero) (plus zero (mult delta (u s')))
                 (plus (mult omd (transition s s')) (mult delta (u s')))
                 (plus_comm (mult delta (u s')) zero)
                 (le_plus_compat zero (mult omd (transition s s'))
                                 (mult delta (u s')) (mult delta (u s'))
                   (le_mult_nonneg_t12 omd (transition s s')
                      abla_omd_nonneg (transition_nonneg s s'))
                   (le_refl (mult delta (u s'))))).
Qed.

(* Supply 8 (marker theorem): shape B full-argument feed -       *)
(*   instantiate u_tv_contraction with the smooth kernel; the    *)
(*   premise face excludes minorization (fed in by Supply 5);    *)
(*   u_norm / delta_lt_one and the three interface pieces stay   *)
(*   explicit premises.  The target file's export face is really *)
(*   used (non-nominal Require).                                 *)
Theorem abla_smooth_tv_contraction : forall (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv_dist (@attention_step RI SS SO abla_smooth_kernel mu)
              (@attention_step RI SS SO abla_smooth_kernel nu))
     (mult (minus one delta) (tv_dist mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (@u_tv_contraction RI SS SO u u_norm delta delta_lt_one
           abla_smooth_kernel abla_smooth_row abla_smooth_minorization
           sum_swap_cc abs_ge_zero_id_cc lt_plus_compat_lt_le_h
           mu nu Hmu Hnu).
Qed.

End AblaSmoothFamily.

(* ============================================================ *)
(* Zone 4: Part A interface data master witness - the sigT box   *)
(*   for the three transition slots holding simultaneously under *)
(*   the copy kernel T(s,s') := u(s') (the Part A counterpart in *)
(*   the real_expf_realizable style).                            *)
(* ============================================================ *)

Section AblaUconInhabitant.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable u_nonneg : forall s : S, le zero (u s).
Variable delta : R.
Variable delta_lt_one : lt delta one.

Theorem abla_ucon_data_realizable :
  sigT (fun T : S -> S -> R =>
    And (forall s s' : S, le zero (T s s'))
        (And (forall s : S, Id (sum_over_S (fun s' : S => T s s')) one)
             (forall s s' : S, le (mult delta (u s')) (T s s')))).
Proof.
  exists (fun (_ s' : S) => u s').
  assert (Hnn : forall s s' : S, le zero (u s')).
  { intros _ s'. exact (u_nonneg s'). }
  assert (Hrow : forall s : S, Id (sum_over_S (fun s' : S => u s')) one).
  { intro s.
    exact (id_trans (sum_over_S_ext (fun s' : S => u s') u
                       (fun s2 : S => id_refl)) u_norm). }
  assert (Hmin : forall s s' : S, le (mult delta (u s')) (u s')).
  { intros _ s'.
    exact (le_trans (mult delta (u s')) (mult (u s') one) (u s')
             (le_id_l (mult delta (u s')) (mult (u s') delta)
                      (mult (u s') one)
                      (mult_comm delta (u s'))
                      (le_mult_compat_r (u s') delta one
                         (u_nonneg s')
                         (lt_le_iff delta one (inl delta_lt_one))))
             (le_id_l (mult (u s') one) (u s') (u s')
                      (mult_one (u s')) (le_refl (u s')))). }
  exact (pair Hnn (pair Hrow Hmin)).
Qed.

End AblaUconInhabitant.

(* ============================================================ *)
(* Zone 5: z_lb/z_ub twin slots (:467/:468) zero-band z witness  *)
(*   - z0 := fun _ _ => zero satisfies both bounds for any       *)
(*   positive Delta (general-Delta form, stronger than the tspy  *)
(*   one-pinned form); class-field four steps: lt_le_iff left    *)
(*   branch + opp_le_compat + opp_zero_t13 + le_id_r.            *)
(* ============================================================ *)

Section AblaZBand.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

Theorem abla_z_band_zero_witness :
  forall Delta : R, lt zero Delta ->
  sigT (fun z : S -> S -> R =>
    And (forall s s' : S, le (opp Delta) (z s s'))
        (forall s s' : S, le (z s s') Delta)).
Proof.
  intros Delta HDelta.
  exists (fun (_ _ : S) => zero).
  assert (Hlb : forall s s' : S, le (opp Delta) zero).
  { intros _ _.
    exact (le_id_r (opp Delta) (opp zero) zero opp_zero_t13
                   (opp_le_compat zero Delta
                      (lt_le_iff zero Delta (inl HDelta)))). }
  assert (Hub : forall s s' : S, le zero Delta).
  { intros _ _. exact (lt_le_iff zero Delta (inl HDelta)). }
  exact (pair Hlb Hub).
Qed.

End AblaZBand.

(* ============================================================ *)
(* Audit segment (Check read faces + per-item Closed reading)    *)
(* ============================================================ *)

Check abla_delta_lt_one_witness.
Check abla_unif_norm_witness.
Check abla_smooth_nonneg.
Check abla_smooth_row.
Check abla_smooth_minorization.
Check abla_smooth_tv_contraction.
Check abla_ucon_data_realizable.
Check abla_z_band_zero_witness.
Check (@u_tv_contraction).
Check (@nat_to_R).
Check (@nat_to_R_pos).
Check (@delta_absorb_u).

(* Premise-face audit (per-item all-Closed criterion; name list  *)
(*   = Qed count = 11, zero diff)                                *)
Print Assumptions abla_delta_lt_one_witness.
Print Assumptions abla_list_sum_const.
Print Assumptions abla_unif_norm_witness.
Print Assumptions abla_omd_nonneg.
Print Assumptions abla_delta_plus_omd.
Print Assumptions abla_smooth_nonneg.
Print Assumptions abla_smooth_row.
Print Assumptions abla_smooth_minorization.
Print Assumptions abla_smooth_tv_contraction.
Print Assumptions abla_ucon_data_realizable.
Print Assumptions abla_z_band_zero_witness.

(* ============================================================ *)
(* Extraction check area (criterion = segmented Obj.magic counts *)
(*   declared; G3 control scope: the last command extracts       *)
(*   u_tv_contraction alone = the library-closure control arm)   *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction abla_delta_lt_one_witness abla_unif_norm_witness
  abla_smooth_nonneg abla_smooth_row abla_smooth_minorization
  abla_smooth_tv_contraction abla_ucon_data_realizable
  abla_z_band_zero_witness.
Recursive Extraction u_tv_contraction.
