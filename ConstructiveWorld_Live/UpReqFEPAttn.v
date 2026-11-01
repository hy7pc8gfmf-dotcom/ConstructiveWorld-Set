(* ===================================================================== *)
(*  UpReqFEPAttn.v -- request-layer Free Energy Principle for attention:  *)
(*  four FEP pieces plus one row-view piece, Set-level statement face.    *)
(*  Mission.  Formalize the stated theorem and lemma surfaces: attention  *)
(*    is the unique minimizer of the variational free energy              *)
(*    (req_attention_minimizes_free_energy_unique) with partition,        *)
(*    alignment and F extensionality limbs, the row view                  *)
(*    (req_bs_kernel_row_is_softmax_temp), and the logZ quadruple.        *)
(*  Dependencies.  S01_BaseRing S02_CauchyComplete S03_QExp               *)
(*    S04_RealExpLogConv S05_AlignmentGRPO S06_DiffSamplingGibbs          *)
(*    S07_RealSetoidExpLog S08_RealMainlineDPO S09_EntropyReal            *)
(*    S10_KVQuantTrig S11_TP3B5 S12_B5RecycleSF S13_NLiveAudit            *)
(*    S14_B5BatchBlock S15_TailFEPUp UpReqAlgebra UpReqDist;              *)
(*    RealInterfaceEnhancedMod (world-tree library files).                *)
(*  References.  the Id-side originals: Section FEPAttention and Section  *)
(*    RowView of G01_CoreMicro; Module UpExtras219 Section FEPLogZ.       *)
(*  Constructivity.  purely constructive, zero admitted pieces; statement *)
(*    surface entirely Set-level (real_eq / real_lt / real_le valued over *)
(*    the global Cauchy Real; conjunctions via And := A * B); term-mode   *)
(*    proofs (req_trans chains + compat bridges); every piece closes by   *)
(*    Qed; no magic escapes, no Prop-ification.  Honest boundary: statements *)
(*    carried from the req/lt/le face to the current unparameterized      *)
(*    interface face, and the UpReqDist consumption sites re-targeted to  *)
(*    the discharged signatures; log keeps its positivity premise.        *)
(*  Build.  rocq c -native-compiler no -Q <world> "" (cpu_guard wrapped;  *)
(*    ulimit -s 65532).                                                   *)
(* ===================================================================== *)

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
(* The interface class in this tree is unparameterized; its carrier is the global Real. *)
Notation R := Real.

(* ############ Section ReqFEPAttn: the four FEPAttention pieces ######### *)
(*   Pointwise real_eq-isomorphic to the Id originals; the interface = the *)
(*   summation and log premises below plus the temperature variables.      *)

Section ReqFEPAttn.
Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero ->
    forall s : S, real_eq (f s) zero.

Hypothesis log_inv_one_inv :
  forall (x : R) (Hx : real_lt zero x) (Hi : real_lt zero (inv_pos x Hx)),
    real_eq (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis log_exp_neg :
  forall u : R, real_eq (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis log_le_linear :
  forall (x : R) (Hx : real_lt zero x), real_le (log x Hx) (req_minus x one).
Hypothesis log_eq_linear :
  forall (x : R) (Hx : real_lt zero x),
    real_eq (log x Hx) (req_minus x one) -> real_eq x one.

(* The Real-instance witness real_log_wd satisfies this; instantiation is  *)
(* deferred to the interface extension batch.                              *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : real_lt zero x) (Hy : real_lt zero y),
    real_eq x y -> real_eq (log x Hx) (log y Hy).

(* ---- temperature softmax instance positions (Id Section Variables z/T/T_pos) ---- *)
Variable z : S -> R.
Variable T : R.
Variable T_pos : real_lt zero T.

(* ---- section-local definitions (Id Let base/invT/Zf/Zf_pos/F_attn, isomorphic) ---- *)
Definition base : S -> R := fun s : S => opp (z s).
Definition invT : R := inv_pos T T_pos.
Definition Zf : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult invT (z s))).

Lemma Zf_pos : real_lt zero Zf.
Proof.
  unfold Zf, exp_pos_fn_setoid. apply sum_pos.
  intro s. apply exp_neg_pos.
Qed.

Definition softmax_z (s : S) : R :=
  mult (exp_pos_fn_setoid (mult invT (z s))) (inv_pos Zf Zf_pos).
Definition boltz_z (s : S) : R :=
  mult (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))).
Definition F_attn (p : S -> R) (Hp : forall s : S, real_lt zero (p s)) : R :=
  plus (sumf (fun s : S => mult (p s) (base s)))
       (mult T (sumf (fun s : S => mult (p s) (log (p s) (Hp s))))).

(* ---- piece 1/9: partition condition (Id fep_partition_condition) ---- *)
(*   Z equals the sum of exp over s: pointwise opp_mult_l reshaping +     *)
(*   exp compat bridge.                                                   *)
Theorem req_fep_partition_condition :
  real_eq Zf (sumf (fun s : S => exp_neg (mult invT (base s)))).
Proof.
  unfold Zf, base, exp_pos_fn_setoid.
  apply (sum_ext _ _ (fun s : S =>
    exp_neg_req_compat_setoid _ _ (req_sym _ _ (req_opp_mult_l invT (z s))))).
Qed.

(* ---- piece 2/9: alignment lemma (Id fep_align) ---- *)
(*   Boltzmann (energy -z, temperature T) pointwise equals temperature    *)
(*   softmax: product commutation + numerator exp compat reshaping        *)
(*   (Id proof chain req_trans replay).                                   *)
Theorem req_fep_align : forall s : S, real_eq (boltz_z s) (softmax_z s).
Proof.
  intro s. unfold boltz_z, softmax_z, base, exp_pos_fn_setoid.
  apply (req_trans
    (mult (inv_pos Zf Zf_pos) (exp_neg (mult invT (opp (z s)))))
    (mult (exp_neg (mult invT (opp (z s)))) (inv_pos Zf Zf_pos))
    (mult (exp_neg (opp (mult invT (z s)))) (inv_pos Zf Zf_pos))).
  - exact (mult_comm _ _).
  - apply (req_mult_compat _ _ _ _
      (exp_neg_req_compat_setoid _ _ (req_opp_mult_l invT (z s)))
      (req_refl (inv_pos Zf Zf_pos))).
Qed.

(* ---- helper: softmax normalization (used by the main theorem's         *)
(*      premise surface; linear factor extraction + partition fold-back   *)
(*      + inverse)                                                        ---- *)
Lemma req_softmax_z_normalized : real_eq (sumf softmax_z) one.
Proof.
  unfold softmax_z.
  apply (req_trans
    (sumf (fun s : S => mult (exp_pos_fn_setoid (mult invT (z s)))
                             (inv_pos Zf Zf_pos)))
    (mult (inv_pos Zf Zf_pos) Zf) one).
  - apply (req_trans
      (sumf (fun s : S => mult (exp_pos_fn_setoid (mult invT (z s)))
                               (inv_pos Zf Zf_pos)))
      (sumf (fun s : S => mult (inv_pos Zf Zf_pos)
                               (exp_pos_fn_setoid (mult invT (z s)))))
      (mult (inv_pos Zf Zf_pos)
            (sumf (fun s : S => exp_pos_fn_setoid (mult invT (z s)))))).
    + apply (sum_ext _ _ (fun s : S => mult_comm _ _)).
    + exact (sum_linear (inv_pos Zf Zf_pos)
               (fun s : S => exp_pos_fn_setoid (mult invT (z s)))).
  - apply (req_trans (mult (inv_pos Zf Zf_pos) Zf)
                     (mult Zf (inv_pos Zf Zf_pos)) one).
    + exact (mult_comm _ _).
    + exact (inv_pos_correct Zf Zf_pos).
Qed.

(* ---- piece 3/9: F extensionality (Id fep_F_ext) ---- *)
(*   Pointwise-equal distributions give equal free energy; log takes the  *)
(*   pointwise positivity premise; pointwise log reshaping goes through   *)
(*   log_req_compat; the Id normalization premise stays in raw form.      *)
Theorem req_fep_F_ext :
  forall (p q : S -> R)
         (Hp : forall s : S, real_lt zero (p s))
         (Hq : forall s : S, real_lt zero (q s)),
    real_eq (sumf p) one -> real_eq (sumf q) one ->
    (forall s : S, real_eq (p s) (q s)) ->
    real_eq (F_attn p Hp) (F_attn q Hq).
Proof.
  intros p q Hp Hq Hnp1 Hnp2 Hpt. unfold F_attn.
  apply (req_plus_compat _ _ _ _).
  - apply (sum_ext _ _ (fun s : S =>
      req_mult_compat _ _ _ _ (Hpt s) (req_refl (base s)))).
  - apply (req_mult_compat _ _ _ _ (req_refl T)
      (sum_ext _ _ (fun s : S =>
        req_mult_compat _ _ _ _ (Hpt s)
          (log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpt s))))).
Qed.

(* ---- helper: pointwise positivity of softmax (quoted in the main statement) ---- *)
Lemma softmax_z_pos : forall s : S, real_lt zero (softmax_z s).
Proof.
  intro s. unfold softmax_z, exp_pos_fn_setoid. apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* ---- piece 4/9 main theorem: attention is the unique minimizer of the  *)
(*      variational free energy                                           *)
(*      (Id attention_minimizes_free_energy_unique).                      *)
(*   Usage chain: req_fep_F_ext (softmax-boltzmann reshaping, Id HFsb     *)
(*   step) -> UpReqDist req_min_free_energy_is_boltzmann (le limb) /      *)
(*   req_free_energy_min_unique (uniqueness limb) + req_fep_align.        *)
Theorem req_attention_minimizes_free_energy_unique :
  forall (p : S -> R) (Hp : forall s : S, real_lt zero (p s)),
    real_eq (sumf p) one ->
    And (real_le (F_attn softmax_z softmax_z_pos) (F_attn p Hp))
        (real_eq (F_attn p Hp) (F_attn softmax_z softmax_z_pos) ->
          forall s : S, real_eq (p s) (softmax_z s)).
Proof.
  intros p Hp Hnp.
  assert (Hpinv : real_eq (inv_pos Zf Zf_pos)
                    (inv_pos Zf (@Z_pos S sumf sum_pos
                                   base T T_pos Zf req_fep_partition_condition))).
  { apply (req_mult_cancel_l Zf _ _ Zf_pos).
    apply (req_trans _ _ _ (inv_pos_correct Zf Zf_pos)
             (req_sym _ _ (inv_pos_correct Zf
                (@Z_pos S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition)))). }
  assert (Hpt : forall s : S,
            real_eq (boltz_z s)
                (@reqd_boltzmann_dist S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition s)).
  { intro s. apply (req_mult_compat _ _ _ _ Hpinv
             (req_refl (exp_neg (mult invT (base s))))). }
  assert (Hnboltz : real_eq (sumf boltz_z) one).
  { assert (Hn : reqd_normalized S sumf
                   (@reqd_boltzmann_dist S sumf sum_pos base T T_pos Zf
                      req_fep_partition_condition))
      by exact (@req_boltzmann_normalized S sumf sum_linear sum_pos
                  base T T_pos Zf req_fep_partition_condition).
    unfold reqd_normalized in Hn.
    apply (req_trans _ _ _ (sum_ext _ _ Hpt) Hn). }
  assert (Hposbz : forall s : S, real_lt zero (boltz_z s)).
  { intro s. apply (lt_id_r zero _ _ (req_sym _ _ (Hpt s))).
    exact (@req_boltzmann_positive S sumf sum_pos
             base T T_pos Zf req_fep_partition_condition s). }
  assert (HFsb : real_eq (F_attn softmax_z softmax_z_pos)
                     (F_attn boltz_z Hposbz))
    by exact (req_fep_F_ext softmax_z boltz_z softmax_z_pos
               Hposbz
               req_softmax_z_normalized Hnboltz
               (fun s : S => req_sym _ _ (req_fep_align s))).
  assert (Hmin : real_le (F_attn (@reqd_boltzmann_dist S sumf sum_pos
                               base T T_pos Zf req_fep_partition_condition)
                            (@req_boltzmann_positive S sumf sum_pos
                               base T T_pos Zf req_fep_partition_condition))
                   (F_attn p Hp))
    by exact (@req_min_free_energy_is_boltzmann S sumf sum_ext sum_add sum_linear
                sum_pos sum_le base T T_pos Zf req_fep_partition_condition
                log_inv_one_inv log_exp_neg log_le_linear p Hp Hnp).
  assert (HFcong : forall (d1 d2 : S -> R) (Hd1 : forall s : S, real_lt zero (d1 s))
                     (Hd2 : forall s : S, real_lt zero (d2 s)),
             (forall s : S, real_eq (d1 s) (d2 s)) ->
             real_eq (F_attn d1 Hd1) (F_attn d2 Hd2)).
  { intros d1 d2 Hd1 Hd2 H. unfold F_attn. apply req_plus_compat.
    - apply (sum_ext _ _). intro s. apply req_mult_compat.
      + apply H.
      + apply req_refl.
    - apply (req_mult_compat _ _ _ _ (req_refl T) (sum_ext _ _ (fun s =>
        req_mult_compat _ _ _ _ (H s)
          (log_req_compat (d1 s) (d2 s) (Hd1 s) (Hd2 s) (H s))))). }
  assert (Hle : real_le (F_attn boltz_z Hposbz) (F_attn p Hp)).
  { apply (le_id_l _ _ _
             (req_sym _ _ (HFcong
                (@reqd_boltzmann_dist S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition)
                boltz_z
                (@req_boltzmann_positive S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition) Hposbz
                (fun s0 : S => req_sym _ _ (Hpt s0))))
             Hmin). }
  split.
  - exact (le_id_l _ _ _ HFsb Hle).
  - intros Heq s.
    apply (req_trans _ _ _
      (@req_free_energy_min_unique S sumf sum_ext sum_add sum_linear
        sum_pos sum_zero_nonneg base T T_pos Zf req_fep_partition_condition
        log_inv_one_inv log_exp_neg log_le_linear log_eq_linear
        p Hp Hnp
        (req_trans _ _ _ Heq
           (HFcong softmax_z
              (@reqd_boltzmann_dist S sumf sum_pos base T T_pos Zf
                 req_fep_partition_condition)
              softmax_z_pos
              (@req_boltzmann_positive S sumf sum_pos base T T_pos Zf
                 req_fep_partition_condition)
              (fun s0 : S =>
                 req_trans _ _ _ (req_sym _ _ (req_fep_align s0)) (Hpt s0))))
        s)
      (req_trans _ _ _ (req_sym _ _ (Hpt s)) (req_fep_align s))).
Qed.

End ReqFEPAttn.

(* ############ Section ReqRowView: the row-view piece ################### *)
(*   real_eq-isomorphic to the Id RowView original (bs_kernel_row_is_     *)
(*   softmax_temp). Argument-position pruning per the header registry;    *)
(*   the expf mini-interface consistency premise uses the real_eq         *)
(*   signature (expf_agree).                                              *)
Section ReqRowView.
Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).

Variable temp : R.
Variable temp_pos : real_lt zero temp.
Variable z2 : S -> S -> R.
Variable expf : R -> R.
Hypothesis expf_pos : forall x : R, real_lt zero (expf x).
Hypothesis expf_agree : forall x : R, real_eq (expf x) (exp_pos_fn_setoid x).

(* ---- row partition function (Id Zrow: sum over s0 of expf((1/T)*z2 s s0)) ---- *)
Definition req_Zrow (s : S) : R :=
  sumf (fun s0 : S => expf (mult (inv_pos temp temp_pos) (z2 s s0))).

Lemma req_Zrow_pos : forall s : S, real_lt zero (req_Zrow s).
Proof.
  intro s. unfold req_Zrow. apply sum_pos. intro s0. apply expf_pos.
Qed.

(* ---- single-query row softmax side (Id partition_function_temp /        *)
(*      softmax_temp instantiated at (fun s0 => z2 s s0))                 ---- *)
Definition req_row_partition (s : S) : R :=
  sumf (fun s0 : S => exp_pos_fn_setoid (mult (inv_pos temp temp_pos) (z2 s s0))).

Lemma req_row_partition_pos : forall s : S, real_lt zero (req_row_partition s).
Proof.
  intro s. unfold req_row_partition, exp_pos_fn_setoid.
  apply sum_pos. intro s0. apply exp_neg_pos.
Qed.

Definition req_row_softmax (s s' : S) : R :=
  mult (exp_pos_fn_setoid (mult (inv_pos temp temp_pos) (z2 s s')))
       (inv_pos (req_row_partition s) (req_row_partition_pos s)).

(* ---- row kernel (Id bs_kernel usage surface: numerator expf row entry + *)
(*      inverse row partition)                                             *)
Definition req_bs_kernel (s s' : S) : R :=
  mult (expf (mult (inv_pos temp temp_pos) (z2 s s')))
       (inv_pos (req_Zrow s) (req_Zrow_pos s)).

(* ---- piece 5/9: row view (Id bs_kernel_row_is_softmax_temp) ---- *)
(*   Each kernel row equals the single-query temperature softmax: the HZ  *)
(*   step (row partition fold-back, sum_ext + pointwise expf_agree) +     *)
(*   numerator expf_agree + inverse via inv_pos_ext normalization.        *)
Theorem req_bs_kernel_row_is_softmax_temp : forall s s' : S,
  real_eq (req_bs_kernel s s') (req_row_softmax s s').
Proof.
  intros s s'.
  assert (HZ : real_eq (req_Zrow s) (req_row_partition s)).
  { unfold req_Zrow, req_row_partition.
    apply (sum_ext _ _ (fun s0 : S =>
      expf_agree (mult (inv_pos temp temp_pos) (z2 s s0)))). }
  unfold req_bs_kernel, req_row_softmax.
  exact (req_mult_compat _ _ _ _
    (expf_agree (mult (inv_pos temp temp_pos) (z2 s s')))
    (inv_pos_ext (req_Zrow s) (req_row_partition s)
                 (req_Zrow_pos s) (req_row_partition_pos s) HZ)).
Qed.

End ReqRowView.

(* ############ Section ReqFEPLogZ: the four FEPLogZ pieces ############## *)
(*   real_eq-isomorphic to the Id originals (Module UpExtras219 Section   *)
(*   FEPLogZ; same shape as Section ReqFEPAttn; fep_F_ext is the weaker   *)
(*   form without a normalization premise; the main theorem               *)
(*   req_free_energy_softmax_eq_neg_T_logZ goes through                   *)
(*   req_free_energy_boltzmann). lz_ prefixes prevent cross-section       *)
(*   shadowing at top level.                                              *)
Section ReqFEPLogZ.
Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).

Hypothesis log_inv_one_inv :
  forall (x : R) (Hx : real_lt zero x) (Hi : real_lt zero (inv_pos x Hx)),
    real_eq (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis log_exp_neg :
  forall u : R, real_eq (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : real_lt zero x) (Hy : real_lt zero y),
    real_eq x y -> real_eq (log x Hx) (log y Hy).

Variable z : S -> R.
Variable T : R.
Variable T_pos : real_lt zero T.

Definition lz_base : S -> R := fun s : S => opp (z s).
Definition lz_invT : R := inv_pos T T_pos.
Definition lz_Zf : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult lz_invT (z s))).

Lemma lz_Zf_pos : real_lt zero lz_Zf.
Proof.
  unfold lz_Zf, exp_pos_fn_setoid. apply sum_pos.
  intro s. apply exp_neg_pos.
Qed.

Definition lz_softmax_z (s : S) : R :=
  mult (exp_pos_fn_setoid (mult lz_invT (z s))) (inv_pos lz_Zf lz_Zf_pos).
Definition lz_boltz_z (s : S) : R :=
  mult (inv_pos lz_Zf lz_Zf_pos) (exp_neg (mult lz_invT (lz_base s))).
Definition lz_F_attn (p : S -> R) (Hp : forall s : S, real_lt zero (p s)) : R :=
  plus (sumf (fun s : S => mult (p s) (lz_base s)))
       (mult T (sumf (fun s : S => mult (p s) (log (p s) (Hp s))))).

(* ---- piece 6/9: partition condition at FEPLogZ ---- *)
Theorem req_fep_partition_condition_logz :
  real_eq lz_Zf (sumf (fun s : S => exp_neg (mult lz_invT (lz_base s)))).
Proof.
  unfold lz_Zf, lz_base, exp_pos_fn_setoid.
  apply (sum_ext _ _ (fun s : S =>
    exp_neg_req_compat_setoid _ _ (req_sym _ _ (req_opp_mult_l lz_invT (z s))))).
Qed.

(* ---- piece 7/9: alignment lemma at FEPLogZ ---- *)
Theorem req_fep_align_logz : forall s : S, real_eq (lz_boltz_z s) (lz_softmax_z s).
Proof.
  intro s. unfold lz_boltz_z, lz_softmax_z, lz_base, exp_pos_fn_setoid.
  apply (req_trans
    (mult (inv_pos lz_Zf lz_Zf_pos) (exp_neg (mult lz_invT (opp (z s)))))
    (mult (exp_neg (mult lz_invT (opp (z s)))) (inv_pos lz_Zf lz_Zf_pos))
    (mult (exp_neg (opp (mult lz_invT (z s)))) (inv_pos lz_Zf lz_Zf_pos))).
  - exact (mult_comm _ _).
  - apply (req_mult_compat _ _ _ _
      (exp_neg_req_compat_setoid _ _ (req_opp_mult_l lz_invT (z s)))
      (req_refl (inv_pos lz_Zf lz_Zf_pos))).
Qed.

(* ---- piece 8/9: F extensionality at FEPLogZ (weaker form, no           *)
(*      normalization premise)                                            ---- *)
Theorem req_fep_F_ext_logz :
  forall (p q : S -> R)
         (Hp : forall s : S, real_lt zero (p s))
         (Hq : forall s : S, real_lt zero (q s)),
    (forall s : S, real_eq (p s) (q s)) ->
    real_eq (lz_F_attn p Hp) (lz_F_attn q Hq).
Proof.
  intros p q Hp Hq Hpt. unfold lz_F_attn.
  apply (req_plus_compat _ _ _ _).
  - apply (sum_ext _ _ (fun s : S =>
      req_mult_compat _ _ _ _ (Hpt s) (req_refl (lz_base s)))).
  - apply (req_mult_compat _ _ _ _ (req_refl T)
      (sum_ext _ _ (fun s : S =>
        req_mult_compat _ _ _ _ (Hpt s)
          (log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpt s))))).
Qed.

(* ---- helper: pointwise positivity of softmax (quoted in the main statement) ---- *)
Lemma lz_softmax_z_pos : forall s : S, real_lt zero (lz_softmax_z s).
Proof.
  intro s. unfold lz_softmax_z, exp_pos_fn_setoid. apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* ---- piece 9/9 main theorem (Id free_energy_softmax_eq_neg_T_logZ).    *)
(*   Chain: F extensionality (pointwise softmax-boltzmann reshaping) ->   *)
(*   UpReqDist req_free_energy_boltzmann.                                 *)
Theorem req_free_energy_softmax_eq_neg_T_logZ :
  real_eq (lz_F_attn lz_softmax_z lz_softmax_z_pos)
      (mult (opp T) (log lz_Zf lz_Zf_pos)).
Proof.
  assert (Hpinv : real_eq (inv_pos lz_Zf lz_Zf_pos)
                      (inv_pos lz_Zf (@Z_pos S sumf sum_pos
                                       lz_base T T_pos lz_Zf
                                       req_fep_partition_condition_logz))).
  { apply (req_mult_cancel_l lz_Zf _ _ lz_Zf_pos).
    apply (req_trans _ _ _ (inv_pos_correct lz_Zf lz_Zf_pos)
             (req_sym _ _ (inv_pos_correct lz_Zf
                (@Z_pos S sumf sum_pos lz_base T T_pos lz_Zf
                   req_fep_partition_condition_logz)))). }
  assert (Hpt : forall s : S,
            real_eq (lz_boltz_z s)
                (@reqd_boltzmann_dist S sumf sum_pos lz_base T T_pos lz_Zf
                   req_fep_partition_condition_logz s)).
  { intro s. apply (req_mult_compat _ _ _ _ Hpinv
             (req_refl (exp_neg (mult lz_invT (lz_base s))))). }
  assert (Hpos : forall s : S, real_lt zero (lz_boltz_z s)).
  { intro s. apply (lt_id_r zero _ _ (req_sym _ _ (Hpt s))).
    exact (@req_boltzmann_positive S sumf sum_pos
             lz_base T T_pos lz_Zf req_fep_partition_condition_logz s). }
  exact (req_trans _ _ _
    (req_trans _ _ _
      (req_trans _ _ _
        (req_fep_F_ext_logz lz_softmax_z lz_boltz_z lz_softmax_z_pos Hpos
           (fun s : S => req_sym _ _ (req_fep_align_logz s)))
        (req_fep_F_ext_logz lz_boltz_z
           (@reqd_boltzmann_dist S sumf sum_pos lz_base T T_pos lz_Zf
              req_fep_partition_condition_logz)
           Hpos
           (@req_boltzmann_positive S sumf sum_pos lz_base T T_pos lz_Zf
              req_fep_partition_condition_logz)
           Hpt))
      (@req_free_energy_boltzmann S sumf sum_ext sum_add sum_linear
        sum_pos lz_base T T_pos lz_Zf req_fep_partition_condition_logz
        log_inv_one_inv log_exp_neg))
    (req_mult_compat _ _ _ _ (req_refl (opp T))
       (log_req_compat lz_Zf lz_Zf
          (@Z_pos S sumf sum_pos lz_base T T_pos lz_Zf
             req_fep_partition_condition_logz)
          lz_Zf_pos (req_refl lz_Zf)))).
Qed.

End ReqFEPLogZ.

(*
   Inventory:
   FEPAttention: req_fep_partition_condition, req_fep_align,
     req_fep_F_ext, req_attention_minimizes_free_energy_unique (main).
   RowView: req_bs_kernel_row_is_softmax_temp.
   FEPLogZ: req_fep_partition_condition_logz, req_fep_align_logz,
     req_fep_F_ext_logz, req_free_energy_softmax_eq_neg_T_logZ (main).
   Helpers (supplied at proof position, not explicit premises):
     Zf_pos, softmax_z_pos, req_softmax_z_normalized, req_Zrow_pos,
     req_row_partition_pos, lz_Zf_pos, lz_softmax_z_pos.
*)
