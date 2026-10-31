(* ==========================================================================
   UpReqSampling.v -- req-layer replica of the sampling kernel: Doeblin
   contraction with explicit iteration budgets.

   Mission. Formalization of the properties stated by the theorem/lemma
     declarations: two-point TV contraction (rsq_u_tv_contraction /
     rsq_u_tv_iter; bounded-softmax pair rsq_bounded_softmax_tv_contraction /
     rsq_bounded_softmax_tv_iter) on the iteration kernels rsq_u_titer /
     rsq_bs_kernel and the one-step decomposition rsq_u_tr_decomp.
   Dependencies. CW_ConstructiveWorld_219 (Require-imports S01_BaseRing ..
     S15_TailFEPUp), UpReqAlgebra (req_minus family), UpReqDist
     (ReqSoftmaxDual: reqd_sum_minus, reqd_minus_compat, reqd_nat_to_R,
     reqd_softmax_scaled), Stdlib List.
   References. Id originals in CW_ConstructiveWorld_219.v: Section UContraction
     L95737-96039 (11 results), Section BoundedSoftmax L96043-96356 (23 results),
     migrated name-for-name to the req signature; anchors: UpReqAlgebra, UpReqDist
     ReqSoftmaxDual, exp_neg_req_compat_setoid (L66223).
   Constructivity. Purely constructive: every proof ends in Qed via explicit
     term-mode req_trans chains and compat bridges (no Morphisms, no rewrite,
     no classical logic); statements are Set-level (req/lt/le Set-valued);
     the summation honest-interface slots stand in place as Variables; the real face binds the unparameterized class over the global Real (bridge below).
     direct proofs: rsq_u_tv_contraction, rsq_u_tv_iter, rsq_bs_minorization,
     rsq_bs_lo_hi_eq, rsq_bs_lo_lt_hi, rsq_bs_inv_hi_lo, the epp_* family,
     aux_le_mult_nonneg_t12, aux_delta_plus_omd, bs_kernel_eq_reqd_scaled;
     the rest replay the Id req_trans chains; the Id expf interface yields to
     eight concrete rsq_exp_pos_fn properties.
   Build. Rocq 9.1, direct: rocq c -native-compiler no -q -Q <source-seat
     world> "" (the seventeen dependency .vo files reused read-only from
     that world), wrapped by cpu_guard load control.
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
Require Import UpReqAlgebra.
Require Import UpReqDist.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* Set-carrier completion: the interface class in this tree is unparameterized
   with carrier Real (cf. UpReqAlgebra/UpReqDist); R is bridged to the global
   Real, and the operations resolve to the global instance RealEnhancedReal. *)
Notation R := Real.

(* req_r_pow: setoid rebinding of the Id r_pow (L14071) -- signature change 6 *)
Fixpoint req_r_pow (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (req_r_pow x m)
  end.

(* ============================================================ *)
(* Section ReqUContraction: req migration of the UContraction section (11 results) *)
(*   Id originals L95737-96039. The summation honest interface = the req replica of the Id SumOver class fields (L1400-1441); the section is self-contained *)
(*   (its declaration slots are carried locally). *)

(* ============================================================ *)
Section ReqUContraction.
(* Unparameterized binding: R is the global Real via the Notation bridge above;
   the operations resolve to the global instance RealEnhancedReal. *)

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- The summation honest interface (field-by-field req replica of the Id SumOver fields) ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
(* Summation triangle: |sum f| <= sum |f| (req replica of the Id SumOver abs_sum_le field) *)
Hypothesis abs_sum_le_h :
  forall f : S -> R, real_le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

(* sum(f - g) == sum f - sum g: via UpReqDist reqd_sum_minus (zero new assumption slots; signature change 1) *)
Let sum_minus :=
  reqd_sum_minus S sumf sum_ext sum_add sum_linear.

Variable u : S -> R.
Variable u_norm : real_eq (sumf u) one.
Variable delta : R.
Variable delta_lt_one : real_lt delta one.
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s' : S, real_le zero (transition s s').
Variable transition_row :
  forall s : S, real_eq (sumf (fun s' : S => transition s s')) one.
Variable minorization : forall s s' : S, real_le (mult delta (u s')) (transition s s').
Variable sum_swap_cc : forall f : S -> S -> R,
  real_eq (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Variable abs_ge_zero_req : forall a : R, real_le zero a -> real_eq (abs a) a.
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  real_lt a b -> real_le c d -> real_lt (plus a c) (plus b d).

Let omd := req_minus one delta.

(* 1 - delta > 0 (first leg of the idempotent-delta duality: the req_refl branch of the omd delta expansion) *)
Lemma rsq_u_omd_pos_next : real_lt zero omd.
Proof.
  apply (lt_id_l zero (plus delta (opp delta)) omd
                 (req_sym _ _ (plus_opp delta))
                 (lt_plus_compat_lt_le_h delta one (opp delta) (opp delta)
                                         delta_lt_one (le_refl (opp delta)))).
Qed.

Let inv_omd := inv_pos omd rsq_u_omd_pos_next.

(* aux_delta_plus_omd: delta + (1 - delta) == one (shared tail chain of delta_absorb_u / u_step_norm) *)
Lemma aux_delta_plus_omd : real_eq (plus delta omd) one.
Proof.
  apply (req_trans _ (plus (plus delta one) (opp delta)) _).
  - exact (plus_assoc delta one (opp delta)).
  - apply (req_trans (plus (plus delta one) (opp delta))
                     (plus (plus one delta) (opp delta)) _).
    + exact (req_plus_compat (plus delta one) (plus one delta)
                (opp delta) (opp delta)
                (plus_comm delta one) (req_refl (opp delta))).
    + apply (req_trans (plus (plus one delta) (opp delta))
                       (plus one (plus delta (opp delta))) _).
      * exact (req_sym _ _ (plus_assoc one delta (opp delta))).
      * apply (req_trans (plus one (plus delta (opp delta)))
                         (plus one zero) one).
        -- exact (req_plus_compat one one (plus delta (opp delta)) zero
                     (req_refl one) (plus_opp delta)).
        -- exact (plus_zero one).
Qed.

(* Helper (direct proof): lt-plus-le product of two nonnegative factors (req rebuild of the Id
   interface result le_mult_nonneg_t12; UpReqAlgebra has no ready-made one -- le_mult_compat_weak at the right-multiplication slot + two req substitutions) *)
Lemma aux_le_mult_nonneg_t12 :
  forall a b : R, real_lt zero a -> real_le zero b -> real_le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_r zero (mult b a) (mult a b) (mult_comm b a)).
  apply (le_id_l zero (mult zero a) (mult b a)).
  - exact (req_sym (mult zero a) zero
             (req_trans (mult zero a) (mult a zero) zero
                        (mult_comm zero a) (mult_zero a))).
  - exact (le_mult_compat_weak zero b a (lt_le_iff zero a (inl Ha)) Hb).
Qed.

Definition rsq_u_r_kernel (s s' : S) : R :=
  mult inv_omd (req_minus (transition s s') (mult delta (u s'))).

(* The R kernel is pointwise nonnegative (from the minorization slot) *)
Lemma rsq_u_r_nonneg : forall s s' : S, real_le zero (rsq_u_r_kernel s s').
Proof.
  intros s s'. unfold rsq_u_r_kernel.
  apply (aux_le_mult_nonneg_t12 inv_omd
                                (req_minus (transition s s') (mult delta (u s')))).
  - exact (inv_pos_pos omd rsq_u_omd_pos_next).
  - exact (req_le_minus_nonneg (mult delta (u s')) (transition s s')
                               (minorization s s')).
Qed.

(* The R kernel rows are normalized (assembly: segment-by-segment replay of the Id req_trans chain) *)
Lemma rsq_u_r_norm : forall s : S, real_eq (sumf (fun s' : S => rsq_u_r_kernel s s')) one.
Proof.
  intro s. unfold rsq_u_r_kernel.
  apply (req_trans _ (mult inv_omd
         (sumf (fun s' : S => req_minus (transition s s') (mult delta (u s'))))) _).
  - exact (sum_linear inv_omd
            (fun s' : S => req_minus (transition s s') (mult delta (u s')))).
  - apply (req_trans _ (mult inv_omd
           (req_minus (sumf (fun s' : S => transition s s'))
                      (sumf (fun s' : S => mult delta (u s'))))) _).
    + exact (req_mult_compat inv_omd inv_omd
               (sumf (fun s' : S => req_minus (transition s s') (mult delta (u s'))))
               (req_minus (sumf (fun s' : S => transition s s'))
                          (sumf (fun s' : S => mult delta (u s'))))
               (req_refl inv_omd)
               (sum_minus (fun s' : S => transition s s')
                          (fun s' : S => mult delta (u s')))).
    + apply (req_trans _ (mult inv_omd (req_minus one (mult delta one))) _).
      * exact (req_mult_compat inv_omd inv_omd
                 (req_minus (sumf (fun s' : S => transition s s'))
                            (sumf (fun s' : S => mult delta (u s'))))
                 (req_minus one (mult delta one))
                 (req_refl inv_omd)
                 (reqd_minus_compat (sumf (fun s' : S => transition s s')) one
                                    (sumf (fun s' : S => mult delta (u s')))
                                    (mult delta one)
                                    (transition_row s)
                                    (req_trans (sumf (fun s' : S => mult delta (u s')))
                                               (mult delta (sumf u)) (mult delta one)
                                               (sum_linear delta u)
                                               (req_mult_compat delta delta (sumf u) one
                                                                (req_refl delta) u_norm)))).
      * apply (req_trans _ (mult inv_omd omd) _).
        -- exact (req_mult_compat inv_omd inv_omd
                    (req_minus one (mult delta one)) omd
                    (req_refl inv_omd)
                    (reqd_minus_compat one one (mult delta one) delta
                                       (req_refl one) (mult_one delta))).
        -- exact (req_trans (mult inv_omd omd) (mult omd inv_omd) one
                   (mult_comm inv_omd omd)
                   (inv_pos_correct omd rsq_u_omd_pos_next)).
Qed.

(* T == delta*u + (1 - delta)*R (the kernel definition unfolded) *)
Lemma rsq_u_tr_decomp : forall s s' : S,
  real_eq (transition s s')
      (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))).
Proof.
  intros s s'. unfold rsq_u_r_kernel.
  assert (Habs : real_eq (mult omd (mult inv_omd
                          (req_minus (transition s s') (mult delta (u s')))))
                     (req_minus (transition s s') (mult delta (u s')))).
  { apply (req_trans _ (mult (mult omd inv_omd)
           (req_minus (transition s s') (mult delta (u s')))) _).
    - exact (mult_assoc omd inv_omd
               (req_minus (transition s s') (mult delta (u s')))).
    - apply (req_trans _ (mult one
             (req_minus (transition s s') (mult delta (u s')))) _).
      + exact (req_mult_compat (mult omd inv_omd) one
                  (req_minus (transition s s') (mult delta (u s')))
                  (req_minus (transition s s') (mult delta (u s')))
                  (inv_pos_correct omd rsq_u_omd_pos_next) (req_refl _)).
      + exact (req_mult_one_l (req_minus (transition s s') (mult delta (u s')))). }
  assert (H1 : real_eq (transition s s')
                   (plus (mult delta (u s'))
                         (req_minus (transition s s') (mult delta (u s'))))).
  { exact (req_sym _ _ (req_minus_plus_cancel (mult delta (u s')) (transition s s'))). }
  assert (H2 : real_eq (plus (mult delta (u s'))
                         (req_minus (transition s s') (mult delta (u s'))))
                  (plus (mult delta (u s'))
                        (mult omd (mult inv_omd
                           (req_minus (transition s s') (mult delta (u s'))))))).
  { apply (req_plus_compat (mult delta (u s')) (mult delta (u s'))).
    - exact (req_refl _).
    - exact (req_sym _ _ Habs). }
  exact (req_trans _ _ _ H1 H2).
Qed.

(* delta*a + (1 - delta)*a == a (depends on aux_delta_plus_omd) *)
Lemma rsq_delta_absorb_u : forall a : R,
  real_eq (plus (mult delta a) (mult omd a)) a.
Proof.
  intro a.
  apply (req_trans _ (plus (mult a delta) (mult a omd)) _).
  - exact (req_plus_compat (mult delta a) (mult a delta)
              (mult omd a) (mult a omd)
              (mult_comm delta a) (mult_comm omd a)).
  - apply (req_trans _ (mult a (plus delta omd)) _).
    + exact (req_sym _ _ (distrib a delta omd)).
    + apply (req_trans _ (mult a one) _).
      * exact (req_mult_compat a a (plus delta omd) one (req_refl a)
                 aux_delta_plus_omd).
      * exact (mult_one a).
Qed.

Let u_step (mu : S -> R) (s' : S) : R :=
  sumf (fun s : S => mult (mu s) (transition s s')).

(* One-step decomposition: T mu == delta*u + (1 - delta)*R mu (applied pointwise under the sum) *)
Lemma rsq_u_step_decomp : forall (mu : S -> R) (s' : S),
  real_eq (sumf mu) one ->
  real_eq (u_step mu s')
      (plus (mult delta (u s'))
            (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))).
Proof.
  intros mu s' Hmu. unfold u_step.
  apply (req_trans _ (sumf (fun s : S => mult (mu s)
         (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))))) _).
  - exact (sum_ext (fun s : S => mult (mu s) (transition s s'))
                   (fun s : S => mult (mu s)
                      (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))))
                   (fun s : S => req_mult_compat (mu s) (mu s) (transition s s')
                      (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s')))
                      (req_refl (mu s)) (rsq_u_tr_decomp s s'))).
  - apply (req_trans _ (sumf (fun s : S =>
           plus (mult (mu s) (mult delta (u s')))
                (mult (mu s) (mult omd (rsq_u_r_kernel s s'))))) _).
    + exact (sum_ext (fun s : S => mult (mu s)
                        (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))))
                     (fun s : S => plus (mult (mu s) (mult delta (u s')))
                                        (mult (mu s) (mult omd (rsq_u_r_kernel s s'))))
                     (fun s : S => distrib (mu s) (mult delta (u s'))
                                           (mult omd (rsq_u_r_kernel s s')))).
    + apply (req_trans _ (plus (sumf (fun s : S => mult (mu s) (mult delta (u s'))))
                               (sumf (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s'))))) _).
      * exact (sum_add (fun s : S => mult (mu s) (mult delta (u s')))
                       (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s')))).
      * assert (Hfirst : real_eq (sumf (fun s : S => mult (mu s) (mult delta (u s'))))
                             (mult delta (u s'))).
        { apply (req_trans _ (sumf (fun s : S => mult (mult (mu s) delta) (u s'))) _).
          - exact (sum_ext (fun s : S => mult (mu s) (mult delta (u s')))
                           (fun s : S => mult (mult (mu s) delta) (u s'))
                           (fun s : S => mult_assoc (mu s) delta (u s'))).
          - apply (req_trans _ (sumf (fun s : S => mult (mult delta (mu s)) (u s'))) _).
            + exact (sum_ext (fun s : S => mult (mult (mu s) delta) (u s'))
                             (fun s : S => mult (mult delta (mu s)) (u s'))
                             (fun s : S => req_mult_compat (mult (mu s) delta)
                                (mult delta (mu s)) (u s') (u s')
                                (mult_comm (mu s) delta) (req_refl _))).
            + apply (req_trans _ (sumf (fun s : S => mult delta (mult (mu s) (u s')))) _).
              * exact (sum_ext (fun s : S => mult (mult delta (mu s)) (u s'))
                               (fun s : S => mult delta (mult (mu s) (u s')))
                               (fun s : S => req_sym _ _ (mult_assoc delta (mu s) (u s')))).
              * apply (req_trans _ (mult delta (sumf (fun s : S => mult (mu s) (u s')))) _).
                -- exact (sum_linear delta (fun s : S => mult (mu s) (u s'))).
                -- apply (req_mult_compat delta delta
                             (sumf (fun s : S => mult (mu s) (u s'))) (u s')
                             (req_refl delta)).
                   apply (req_trans (sumf (fun s : S => mult (mu s) (u s')))
                                    (mult (u s') (sumf mu)) _).
                   ++ apply (req_trans (sumf (fun s : S => mult (mu s) (u s')))
                                       (sumf (fun s : S => mult (u s') (mu s))) _).
                      ** exact (sum_ext (fun s : S => mult (mu s) (u s'))
                                        (fun s : S => mult (u s') (mu s))
                                        (fun s : S => mult_comm (mu s) (u s'))).
                      ** exact (sum_linear (u s') mu).
                   ++ apply (req_trans _ (mult one (u s')) _).
                      ** exact (req_trans (mult (u s') (sumf mu))
                                 (mult (sumf mu) (u s')) (mult one (u s'))
                                 (mult_comm (u s') (sumf mu))
                                 (req_mult_compat (sumf mu) one (u s') (u s')
                                                  Hmu (req_refl _))).
                      ** exact (req_trans (mult one (u s')) (mult (u s') one) (u s')
                                 (mult_comm one (u s')) (mult_one (u s'))). }
        exact (req_plus_compat (sumf (fun s : S => mult (mu s) (mult delta (u s'))))
                               (mult delta (u s'))
                               (sumf (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s'))))
                               (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                               Hfirst
                               (req_trans
                                  (sumf (fun s : S =>
                                     mult (mu s) (mult omd (rsq_u_r_kernel s s'))))
                                  (sumf (fun s : S =>
                                     mult omd (mult (mu s) (rsq_u_r_kernel s s'))))
                                  (mult omd
                                     (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                                  (sum_ext
                                     (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s')))
                                     (fun s : S => mult omd (mult (mu s) (rsq_u_r_kernel s s')))
                                     (fun s : S =>
                                        req_trans
                                          (mult (mu s) (mult omd (rsq_u_r_kernel s s')))
                                          (mult (mult (mu s) omd) (rsq_u_r_kernel s s'))
                                          (mult omd (mult (mu s) (rsq_u_r_kernel s s')))
                                          (mult_assoc (mu s) omd (rsq_u_r_kernel s s'))
                                          (req_trans
                                             (mult (mult (mu s) omd) (rsq_u_r_kernel s s'))
                                             (mult (mult omd (mu s)) (rsq_u_r_kernel s s'))
                                             (mult omd (mult (mu s) (rsq_u_r_kernel s s')))
                                             (req_mult_compat (mult (mu s) omd)
                                                (mult omd (mu s)) (rsq_u_r_kernel s s')
                                                (rsq_u_r_kernel s s')
                                                (mult_comm (mu s) omd) (req_refl _))
                                             (req_sym _ _
                                                (mult_assoc omd (mu s) (rsq_u_r_kernel s s'))))))
                                  (sum_linear omd
                                     (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))).
Qed.

(* One step preserves normalization (feeds on the one-step decomposition) *)
Lemma rsq_u_step_norm : forall mu : S -> R,
  real_eq (sumf mu) one -> real_eq (sumf (fun s' : S => u_step mu s')) one.
Proof.
  intros mu Hmu.
  apply (req_trans _ (sumf (fun s' : S =>
        plus (mult delta (u s'))
             (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))) _).
  - exact (sum_ext (fun s' : S => u_step mu s') (fun s' : S =>
        plus (mult delta (u s'))
             (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
        (fun s' : S => rsq_u_step_decomp mu s' Hmu)).
  - apply (req_trans _ (plus (sumf (fun s' : S => mult delta (u s')))
        (sumf (fun s' : S => mult omd
                 (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))) _).
    + exact (sum_add (fun s' : S => mult delta (u s'))
                     (fun s' : S => mult omd
                        (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))).
    + assert (HL : real_eq (sumf (fun s' : S => mult delta (u s'))) (mult delta one)).
      { exact (req_trans (sumf (fun s' : S => mult delta (u s')))
                         (mult delta (sumf u)) (mult delta one)
                         (sum_linear delta u)
                         (req_mult_compat delta delta (sumf u) one
                                          (req_refl delta) u_norm)). }
      assert (HR : real_eq (sumf (fun s' : S => mult omd
                          (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
                     (mult omd (sumf mu))).
      { apply (req_trans _ (mult omd
               (sumf (fun s' : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))) _).
        - exact (sum_linear omd
                   (fun s' : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))).
        - apply (req_mult_compat omd omd
                    (sumf (fun s' : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                    (sumf mu) (req_refl omd)).
          apply (req_trans (sumf (fun s2 : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s2))))
                           (sumf (fun s : S => sumf (fun s2 : S => mult (mu s) (rsq_u_r_kernel s s2)))) _).
          * exact (req_sym _ _
                      (sum_swap_cc (fun s s2 : S => mult (mu s) (rsq_u_r_kernel s s2)))).
          * apply (req_trans _ (sumf (fun s : S =>
                mult (mu s) (sumf (fun s2 : S => rsq_u_r_kernel s s2)))) _).
            + exact (sum_ext (fun s : S => sumf (fun s2 : S => mult (mu s) (rsq_u_r_kernel s s2)))
                             (fun s : S => mult (mu s) (sumf (fun s2 : S => rsq_u_r_kernel s s2)))
                             (fun s : S => sum_linear (mu s) (fun s2 : S => rsq_u_r_kernel s s2))).
            + apply (req_trans _ (sumf (fun s : S => mult (mu s) one)) _).
              -- exact (sum_ext (fun s : S => mult (mu s) (sumf (fun s2 : S => rsq_u_r_kernel s s2)))
                               (fun s : S => mult (mu s) one)
                               (fun s : S => req_mult_compat (mu s) (mu s)
                                  (sumf (fun s2 : S => rsq_u_r_kernel s s2)) one
                                  (req_refl (mu s)) (rsq_u_r_norm s))).
              -- exact (sum_ext (fun s : S => mult (mu s) one) (fun s : S => mu s)
                               (fun s : S => mult_one (mu s))). }
      apply (req_trans _ (plus (mult delta one) (mult omd (sumf mu))) _).
      * exact (req_plus_compat _ _ _ _ HL HR).
      * apply (req_trans _ (plus delta (mult omd (sumf mu))) _).
        -- exact (req_plus_compat (mult delta one) delta
                      (mult omd (sumf mu)) (mult omd (sumf mu))
                      (mult_one delta) (req_refl _)).
        -- apply (req_trans _ (plus delta omd) _).
           ++ exact (req_plus_compat delta delta
                        (mult omd (sumf mu)) omd (req_refl delta)
                        (req_trans (mult omd (sumf mu)) (mult omd one) omd
                                   (req_mult_compat omd omd (sumf mu) one
                                                    (req_refl omd) Hmu)
                                   (mult_one omd))).
           ++ exact (aux_delta_plus_omd).
Qed.

(* |sum (f*R)| <= sum |f|*R (the summation triangle face) *)
Lemma rsq_u_abs_row : forall (f : S -> R) (s' : S),
  real_le (abs (sumf (fun s : S => mult (f s) (rsq_u_r_kernel s s'))))
     (sumf (fun s : S => mult (abs (f s)) (rsq_u_r_kernel s s'))).
Proof.
  intros f s'.
  apply (le_id_r (abs (sumf (fun s : S => mult (f s) (rsq_u_r_kernel s s'))))
                 (sumf (fun s : S => abs (mult (f s) (rsq_u_r_kernel s s'))))
                 (sumf (fun s : S => mult (abs (f s)) (rsq_u_r_kernel s s')))).
  - exact (sum_ext (fun s : S => abs (mult (f s) (rsq_u_r_kernel s s')))
                   (fun s : S => mult (abs (f s)) (rsq_u_r_kernel s s'))
                   (fun s : S =>
                      req_trans (abs (mult (f s) (rsq_u_r_kernel s s')))
                                (mult (abs (f s)) (abs (rsq_u_r_kernel s s')))
                                (mult (abs (f s)) (rsq_u_r_kernel s s'))
                                (abs_mult (f s) (rsq_u_r_kernel s s'))
                                (req_mult_compat (abs (f s)) (abs (f s))
                                   (abs (rsq_u_r_kernel s s')) (rsq_u_r_kernel s s')
                                   (req_refl (abs (f s)))
                                   (abs_ge_zero_req (rsq_u_r_kernel s s')
                                                    (rsq_u_r_nonneg s s'))))).
  - exact (abs_sum_le_h (fun s : S => mult (f s) (rsq_u_r_kernel s s'))).
Qed.

Let inv_two := inv_pos (plus one one) req_two_pos.
Let tv_req (mu nu : S -> R) : R :=
  mult inv_two (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).

(* ========== Main theorem A: two-point TV contraction (no stationarity needed) [main theorem 1].
   Direct proof: the pointwise chain Hpt (reqd_minus_compat swaps in the id_cong2 minus;
   req_minus_plus_congr_l / req_minus_factor / req_minus_factor_pt swap in the Id minus family)
   + the abs witness slot (abs_mult + abs_ge_zero_req) + the Hsum swap chain. ========== *)
Lemma rsq_u_tv_contraction : forall (mu nu : S -> R),
  real_eq (sumf mu) one -> real_eq (sumf nu) one ->
  real_le (tv_req (u_step mu) (u_step nu)) (mult omd (tv_req mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  assert (Hge : real_le zero omd).
  { exact (req_le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one))). }
  assert (Hpt : forall s' : S,
    real_le (abs (req_minus (u_step mu s') (u_step nu s')))
       (mult omd (sumf (fun s : S =>
          mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))).
  { intro s'.
    assert (Hd : real_eq (req_minus (u_step mu s') (u_step nu s'))
                     (mult omd (sumf (fun s : S =>
                        mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))).
    { apply (req_trans (req_minus (u_step mu s') (u_step nu s'))
             (req_minus (plus (mult delta (u s'))
                              (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
                        (plus (mult delta (u s'))
                              (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))))) _).
      - exact (reqd_minus_compat (u_step mu s')
                  (plus (mult delta (u s'))
                        (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
                  (u_step nu s')
                  (plus (mult delta (u s'))
                        (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))))
                  (rsq_u_step_decomp mu s' Hmu) (rsq_u_step_decomp nu s' Hnu)).
      - apply (req_trans _ (req_minus (mult omd
                  (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                  (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))) _).
        + exact (req_minus_plus_congr_l (mult delta (u s'))
                    (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                    (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))).
        + apply (req_trans _ (mult omd (req_minus
                    (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                    (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))) _).
          * exact (req_minus_factor omd
                      (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                      (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))).
          * apply (req_mult_compat omd omd
                       (req_minus (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                                  (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))
                       (sumf (fun s : S =>
                          mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))
                       (req_refl omd)).
            apply (req_trans (req_minus (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                                        (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))
                             (sumf (fun s : S =>
                                req_minus (mult (mu s) (rsq_u_r_kernel s s'))
                                          (mult (nu s) (rsq_u_r_kernel s s')))) _).
            -- exact (req_sym _ _ (sum_minus (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))
                                            (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))).
            -- exact (sum_ext (fun s : S =>
                     req_minus (mult (mu s) (rsq_u_r_kernel s s')) (mult (nu s) (rsq_u_r_kernel s s')))
                              (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))
                              (fun s : S => req_minus_factor_pt (mu s) (nu s) (rsq_u_r_kernel s s'))).
    }
    apply (le_id_l (abs (req_minus (u_step mu s') (u_step nu s')))
                   (mult omd (abs (sumf (fun s : S =>
                      mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))))
                   (mult omd (sumf (fun s : S =>
                      mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))).
    - apply (req_trans (abs (req_minus (u_step mu s') (u_step nu s')))
                       (abs (mult omd (sumf (fun s : S =>
                          mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))) _).
      + exact (req_abs_compat (req_minus (u_step mu s') (u_step nu s'))
                  (mult omd (sumf (fun s : S =>
                     mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))) Hd).
      + exact (req_trans (abs (mult omd (sumf (fun s : S =>
                   mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))))
              (mult (abs omd) (abs (sumf (fun s : S =>
                 mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))) _
              (abs_mult omd (sumf (fun s : S =>
                 mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
              (req_mult_compat (abs omd) omd
                 (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
                 (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
                 (abs_ge_zero_req omd Hge) (req_refl _))).
    - exact (req_le_mult_compat_r omd
               (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
               (sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))
               Hge (rsq_u_abs_row (fun s : S => req_minus (mu s) (nu s)) s')). }
  assert (Hsum : real_le (sumf (fun s' : S => abs (req_minus (u_step mu s') (u_step nu s'))))
                   (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))).
  { apply (le_id_r (sumf (fun s' : S => abs (req_minus (u_step mu s') (u_step nu s'))))
                   (sumf (fun s' : S => mult omd
                            (sumf (fun s : S =>
                               mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))))
                   (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))).
    - apply (req_trans _ (mult omd (sumf (fun s' : S =>
           sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))) _).
      + exact (sum_linear omd (fun s' : S =>
            sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))).
      + apply (req_mult_compat omd omd
                  (sumf (fun s' : S =>
                     sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))
                  (sumf (fun s : S => abs (req_minus (mu s) (nu s))))
                  (req_refl omd)).
        apply (req_trans (sumf (fun s' : S =>
                   sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))
                         (sumf (fun s : S =>
                   sumf (fun s' : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))) _).
        * exact (req_sym _ _
                    (sum_swap_cc (fun s s' : S =>
                       mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))).
        * apply (req_trans _ (sumf (fun s : S =>
              mult (abs (req_minus (mu s) (nu s)))
                   (sumf (fun s' : S => rsq_u_r_kernel s s')))) _).
          -- exact (sum_ext (fun s : S =>
                   sumf (fun s' : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))
                            (fun s : S =>
                   mult (abs (req_minus (mu s) (nu s))) (sumf (fun s' : S => rsq_u_r_kernel s s')))
                            (fun s : S => sum_linear (abs (req_minus (mu s) (nu s)))
                                          (fun s' : S => rsq_u_r_kernel s s'))).
          -- apply (req_trans _ (sumf (fun s : S =>
                   mult (abs (req_minus (mu s) (nu s))) one)) _).
             ++ exact (sum_ext (fun s : S =>
                    mult (abs (req_minus (mu s) (nu s))) (sumf (fun s' : S => rsq_u_r_kernel s s')))
                               (fun s : S => mult (abs (req_minus (mu s) (nu s))) one)
                               (fun s : S => req_mult_compat (abs (req_minus (mu s) (nu s)))
                                  (abs (req_minus (mu s) (nu s)))
                                  (sumf (fun s' : S => rsq_u_r_kernel s s')) one
                                  (req_refl (abs (req_minus (mu s) (nu s)))) (rsq_u_r_norm s))).
             ++ exact (sum_ext (fun s : S => mult (abs (req_minus (mu s) (nu s))) one)
                               (fun s : S => abs (req_minus (mu s) (nu s)))
                               (fun s : S => mult_one (abs (req_minus (mu s) (nu s))))).
    - exact (sum_le _ _ Hpt). }
  apply (le_trans _ (mult inv_two
             (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s))))))).
  - exact (req_le_mult_compat_r inv_two
             (sumf (fun s' : S => abs (req_minus (u_step mu s') (u_step nu s'))))
             (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))
             (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) req_two_pos))) Hsum).
  - assert (Hswap : real_eq (mult inv_two
                          (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s))))))
                        (mult omd (mult inv_two
                          (sumf (fun s : S => abs (req_minus (mu s) (nu s))))))).
    { apply (req_trans _ (mult (mult inv_two omd)
             (sumf (fun s : S => abs (req_minus (mu s) (nu s))))) _).
      + exact (mult_assoc inv_two omd
                 (sumf (fun s : S => abs (req_minus (mu s) (nu s))))).
      + apply (req_trans _ (mult (mult omd inv_two)
               (sumf (fun s : S => abs (req_minus (mu s) (nu s))))) _).
        * exact (req_mult_compat (mult inv_two omd) (mult omd inv_two)
                    (sumf (fun s : S => abs (req_minus (mu s) (nu s))))
                    (sumf (fun s : S => abs (req_minus (mu s) (nu s))))
                    (mult_comm inv_two omd) (req_refl _)).
        * exact (req_sym _ _ (mult_assoc omd inv_two
                    (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))). }
    apply (le_id_l _ _ _ Hswap).
    exact (le_refl _).
Qed.

(* ========== Iterated contraction: geometric rate (1 - delta)^n ========== *)
Fixpoint rsq_u_titer (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => u_step (rsq_u_titer m mu)
  end.

Lemma rsq_u_titer_norm : forall (n : nat) (mu : S -> R),
  real_eq (sumf mu) one -> real_eq (sumf (rsq_u_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu H.
  - exact H.
  - exact (rsq_u_step_norm (rsq_u_titer n mu) (IH mu H)).
Qed.

(* ========== Iterated TV contraction [main theorem 2] (direct proof: the base case
   reroutes the req scalar-one unit; the recursive step aligns via req_le_mult_compat_r) ========== *)
Theorem rsq_u_tv_iter : forall (n : nat) (mu nu : S -> R),
  real_eq (sumf mu) one -> real_eq (sumf nu) one ->
  real_le (tv_req (rsq_u_titer n mu) (rsq_u_titer n nu))
     (mult (req_r_pow omd n) (tv_req mu nu)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu Hmu Hnu.
  - exact (le_id_l _ _ _
             (req_trans (tv_req mu nu) (mult (tv_req mu nu) one)
                        (mult one (tv_req mu nu))
                        (req_sym _ _ (mult_one (tv_req mu nu)))
                        (mult_comm (tv_req mu nu) one))
             (le_refl (mult one (tv_req mu nu)))).
  - apply (le_trans _ (mult omd (tv_req (rsq_u_titer n mu) (rsq_u_titer n nu)))).
    + exact (rsq_u_tv_contraction (rsq_u_titer n mu) (rsq_u_titer n nu)
              (rsq_u_titer_norm n mu Hmu) (rsq_u_titer_norm n nu Hnu)).
    + exact (le_id_r _ _ _
              (mult_assoc omd (req_r_pow omd n) (tv_req mu nu))
              (req_le_mult_compat_r omd (tv_req (rsq_u_titer n mu) (rsq_u_titer n nu))
                (mult (req_r_pow omd n) (tv_req mu nu))
                (req_le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one)))
                (IH mu nu Hmu Hnu))).
Qed.

End ReqUContraction.

(* ============================================================ *)
(* Section ReqBoundedSoftmax: req migration of the BoundedSoftmax section (23 results) *)
(*   Id originals L96043-96356. The expf mini-interface is realized concretely as exp_pos_fn *)
(*   (= exp_neg (opp x)), so the interface instances dissolve; the list summation machinery reroutes *)
(*   to reqd_nat_to_R; anchors = UpReqDist ReqSoftmaxDual reqd_softmax_*. *)
(* ============================================================ *)
Section ReqBoundedSoftmax.
(* Unparameterized binding: R is the global Real via the Notation bridge above;
   the operations resolve to the global instance RealEnhancedReal. *)

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- The summation honest interface (the minimal set this section needs) ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis abs_sum_le_h :
  forall f : S -> R, real_le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

(* ---- Finite-world data (the Id Variables carried over to req form) ---- *)
Variable enum : list S.
Variable enum_nonempty : Not (enum = nil).
Variable temp : R.
Variable temp_pos : real_lt zero temp.
Variable Delta : R.
Variable Delta_pos : real_lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, real_le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, real_le (z s s') Delta.

(* Three honest-interface results (same slots as the Id bs_swap/bs_abs/bs_lpc) *)
Variable bs_swap : forall f : S -> S -> R,
  real_eq (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Variable bs_abs : forall a : R, real_le zero a -> real_eq (abs a) a.
Variable bs_lpc : forall a b c d : R, real_lt a b -> real_le c d -> real_lt (plus a c) (plus b d).

Fixpoint rsq_bs_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (rsq_bs_list_sum f t)
  end.

(* Enumerated-sum normalization (req form of the Id Variable sum_eq_list: signature change 7) *)
Variable sum_eq_list : forall g : S -> R, real_eq (sumf g) (rsq_bs_list_sum g enum).

(* ---- Constructive exponential: the exp_neg realization (signature change 8; the epp_* helper family carries direct proofs) ---- *)
Definition rsq_exp_pos_fn (x : R) : R := exp_neg (opp x).

Lemma epp_pos : forall x : R, real_lt zero (rsq_exp_pos_fn x).
Proof. intro x. exact (exp_neg_pos (opp x)). Qed.

Lemma epp_ext : forall x y : R, real_eq x y -> real_eq (rsq_exp_pos_fn x) (rsq_exp_pos_fn y).
Proof.
  intros x y H.
  exact (exp_neg_req_compat_setoid (opp x) (opp y) (req_opp_compat x y H)).
Qed.

Lemma epp_zero : real_eq (rsq_exp_pos_fn zero) one.
Proof.
  exact (req_trans _ _ _
           (exp_neg_req_compat_setoid (opp zero) zero reqd_opp_zero)
           (exp_neg_zero)).
Qed.

Lemma epp_plus : forall a b : R,
  real_eq (rsq_exp_pos_fn (plus a b)) (mult (rsq_exp_pos_fn a) (rsq_exp_pos_fn b)).
Proof.
  intros a b.
  apply (req_trans _ (exp_neg (plus (opp a) (opp b))) _).
  - exact (exp_neg_req_compat_setoid (opp (plus a b)) (plus (opp a) (opp b))
                                      (req_opp_plus a b)).
  - exact (exp_neg_plus (opp a) (opp b)).
Qed.

Lemma epp_mono_lt : forall a b : R, real_lt a b -> real_lt (rsq_exp_pos_fn a) (rsq_exp_pos_fn b).
Proof.
  intros a b H. exact (exp_neg_decr (opp b) (opp a) (opp_lt_compat a b H)).
Qed.

Lemma epp_mono_le : forall a b : R, real_le a b -> real_le (rsq_exp_pos_fn a) (rsq_exp_pos_fn b).
Proof.
  intros a b H. exact (exp_neg_le_decr (opp b) (opp a) (opp_le_compat a b H)).
Qed.

(* ---- List summation machinery (Id L96104/L96121; assembled in place) ---- *)

Lemma rsq_bs_list_const_sum : forall (c : R) (l : list S),
  real_eq (rsq_bs_list_sum (fun _ : S => c) l) (mult (reqd_nat_to_R (length l)) c).
Proof.
  intros c l. induction l as [| x t IH].
  - exact (req_sym _ _ (req_trans (mult zero c) (mult c zero) zero
             (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : real_eq (plus c (rsq_bs_list_sum (fun _ : S => c) t))
                        (plus (mult c one) (mult c (reqd_nat_to_R (length t))))).
    { exact (req_plus_compat c (mult c one) (rsq_bs_list_sum (fun _ : S => c) t)
                             (mult c (reqd_nat_to_R (length t)))
                             (req_sym _ _ (mult_one c))
                             (req_trans _ _ _ IH
                                (mult_comm (reqd_nat_to_R (length t)) c))). }
    apply (req_trans _ (plus (mult c one) (mult c (reqd_nat_to_R (length t)))) _).
    + exact Hstep.
    + apply (req_trans _ (mult c (plus one (reqd_nat_to_R (length t)))) _).
      * exact (req_sym _ _ (distrib c one (reqd_nat_to_R (length t)))).
      * exact (mult_comm c (plus one (reqd_nat_to_R (length t)))).
Qed.

Lemma rsq_bs_list_le_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, real_le (f x) c) ->
  real_le (rsq_bs_list_sum f l) (mult (reqd_nat_to_R (length l)) c).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_r zero zero (mult zero c)
             (req_sym _ _ (req_trans (mult zero c) (mult c zero) zero
                        (mult_comm zero c) (mult_zero c)))
             (le_refl zero)).
  - apply (le_id_r (plus (f x) (rsq_bs_list_sum f t))
                   (plus c (mult c (reqd_nat_to_R (length t))))
                   (mult (plus one (reqd_nat_to_R (length t))) c)).
    + exact (req_sym _ _ (req_trans
              (mult (plus one (reqd_nat_to_R (length t))) c)
              (mult c (plus one (reqd_nat_to_R (length t))))
              (plus c (mult c (reqd_nat_to_R (length t))))
              (mult_comm (plus one (reqd_nat_to_R (length t))) c)
              (req_trans (mult c (plus one (reqd_nat_to_R (length t))))
                         (plus (mult c one) (mult c (reqd_nat_to_R (length t))))
                         (plus c (mult c (reqd_nat_to_R (length t))))
                         (distrib c one (reqd_nat_to_R (length t)))
                         (req_plus_compat (mult c one) c
                            (mult c (reqd_nat_to_R (length t)))
                            (mult c (reqd_nat_to_R (length t)))
                            (mult_one c) (req_refl _))))).
    + exact (le_plus_compat (f x) c (rsq_bs_list_sum f t)
                            (mult c (reqd_nat_to_R (length t)))
                            (H x)
                            (le_id_r _ _ _ (mult_comm (reqd_nat_to_R (length t)) c)
                                       IH)).
Qed.

Lemma rsq_bs_list_ge_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, real_le c (f x)) ->
  real_le (mult (reqd_nat_to_R (length l)) c) (rsq_bs_list_sum f l).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_l (mult zero c) zero zero
             (req_trans (mult zero c) (mult c zero) zero
                        (mult_comm zero c) (mult_zero c))
             (le_refl zero)).
  - apply (le_id_l (mult (plus one (reqd_nat_to_R (length t))) c)
                   (plus c (mult c (reqd_nat_to_R (length t))))
                   (plus (f x) (rsq_bs_list_sum f t))).
    + exact (req_trans
              (mult (plus one (reqd_nat_to_R (length t))) c)
              (mult c (plus one (reqd_nat_to_R (length t))))
              (plus c (mult c (reqd_nat_to_R (length t))))
              (mult_comm (plus one (reqd_nat_to_R (length t))) c)
              (req_trans (mult c (plus one (reqd_nat_to_R (length t))))
                         (plus (mult c one) (mult c (reqd_nat_to_R (length t))))
                         (plus c (mult c (reqd_nat_to_R (length t))))
                         (distrib c one (reqd_nat_to_R (length t)))
                         (req_plus_compat (mult c one) c
                            (mult c (reqd_nat_to_R (length t)))
                            (mult c (reqd_nat_to_R (length t)))
                            (mult_one c) (req_refl _)))).
    + exact (le_plus_compat c (f x) (mult c (reqd_nat_to_R (length t)))
                            (rsq_bs_list_sum f t)
                            (H x)
                            (le_id_l _ _ _ (req_sym _ _
                               (mult_comm (reqd_nat_to_R (length t)) c)) IH)).
Qed.

Let nR := reqd_nat_to_R (length enum).

Lemma rsq_bs_nR_pos : real_lt zero nR.
Proof.
  destruct enum as [| x t].
  - destruct (enum_nonempty eq_refl).
  - exact (reqd_nat_to_R_pos (length t)).
Qed.

Let invT := inv_pos temp temp_pos.
Let factor (s s' : S) : R := rsq_exp_pos_fn (mult invT (z s s')).
Let lo := rsq_exp_pos_fn (mult invT (opp Delta)).
Let hi := rsq_exp_pos_fn (mult invT Delta).
Let delta_star := mult lo lo.

Lemma rsq_bs_lo_pos : real_lt zero lo.
Proof. exact (epp_pos (mult invT (opp Delta))). Qed.

Lemma rsq_bs_hi_pos : real_lt zero hi.
Proof. exact (epp_pos (mult invT Delta)). Qed.

(* opp Delta < Delta (from Delta > 0) *)
Lemma rsq_bs_opp_lt : real_lt (opp Delta) Delta.
Proof.
  apply (le_lt_trans (opp Delta) zero Delta).
  - exact (le_id_r (opp Delta) (opp zero) zero reqd_opp_zero
             (opp_le_compat zero Delta (lt_le_iff _ _ (inl Delta_pos)))).
  - exact Delta_pos.
Qed.

Lemma rsq_bs_lo_lt_hi : real_lt lo hi.
Proof.
  apply (epp_mono_lt (mult invT (opp Delta)) (mult invT Delta)).
  apply (lt_id_l _ (mult (opp Delta) invT) _ (mult_comm invT (opp Delta))).
  apply (req_lt_id_r_loc _ _ _ (mult_comm Delta invT)).
  exact (lt_mult_compat (opp Delta) Delta invT
                        (inv_pos_pos temp temp_pos) rsq_bs_opp_lt).
Qed.

(* lo*hi == one (exponential homomorphism; direct proof) *)
Lemma rsq_bs_lo_hi_eq : real_eq (mult lo hi) one.
Proof.
  apply (req_trans (mult lo hi)
                   (rsq_exp_pos_fn (plus (mult invT (opp Delta)) (mult invT Delta))) _).
  - exact (req_sym _ _ (epp_plus (mult invT (opp Delta)) (mult invT Delta))).
  - apply (req_trans _ (rsq_exp_pos_fn (mult invT (plus (opp Delta) Delta))) _).
    + exact (epp_ext _ _ (req_sym _ _ (distrib invT (opp Delta) Delta))).
    + apply (req_trans _ (rsq_exp_pos_fn (mult invT zero)) _).
      * exact (epp_ext _ _ (req_mult_compat invT invT (plus (opp Delta) Delta)
                               zero (req_refl invT)
                               (req_trans (plus (opp Delta) Delta)
                                          (plus Delta (opp Delta)) zero
                                          (plus_comm (opp Delta) Delta)
                                          (plus_opp Delta)))).
      * apply (req_trans _ (rsq_exp_pos_fn zero) _).
        -- exact (epp_ext _ _ (mult_zero invT)).
        -- exact (req_trans (rsq_exp_pos_fn zero) (exp_neg zero) one
                   (exp_neg_req_compat_setoid (opp zero) zero reqd_opp_zero)
                   (exp_neg_zero)).
Qed.

Lemma rsq_bs_delta_star_lt_one : real_lt delta_star one.
Proof.
  apply (req_lt_id_r_loc _ _ _ (rsq_bs_lo_hi_eq)).
  apply (req_lt_id_r_loc _ _ _ (mult_comm hi lo)).
  exact (lt_mult_compat lo hi lo rsq_bs_lo_pos rsq_bs_lo_lt_hi).
Qed.

Lemma rsq_bs_inv_hi_lo : real_eq (inv_pos hi rsq_bs_hi_pos) lo.
Proof.
  assert (Hcancel : real_eq (mult hi (inv_pos hi rsq_bs_hi_pos)) (mult hi lo)).
  { exact (req_trans (mult hi (inv_pos hi rsq_bs_hi_pos)) one (mult hi lo)
                     (inv_pos_correct hi rsq_bs_hi_pos)
                     (req_sym _ _ (req_trans (mult hi lo) (mult lo hi) one
                                (mult_comm hi lo) rsq_bs_lo_hi_eq))). }
  assert (Hlb : real_eq (mult (inv_pos hi rsq_bs_hi_pos) (mult hi (inv_pos hi rsq_bs_hi_pos)))
                    (inv_pos hi rsq_bs_hi_pos)).
  { apply (req_trans (mult (inv_pos hi rsq_bs_hi_pos) (mult hi (inv_pos hi rsq_bs_hi_pos)))
                     (mult (mult (inv_pos hi rsq_bs_hi_pos) hi) (inv_pos hi rsq_bs_hi_pos))
                     (inv_pos hi rsq_bs_hi_pos)).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos hi rsq_bs_hi_pos) hi) (inv_pos hi rsq_bs_hi_pos))
                       (mult one (inv_pos hi rsq_bs_hi_pos))
                       (inv_pos hi rsq_bs_hi_pos)).
      + apply (req_mult_compat (mult (inv_pos hi rsq_bs_hi_pos) hi) one
                               (inv_pos hi rsq_bs_hi_pos) (inv_pos hi rsq_bs_hi_pos)
                               (req_trans (mult (inv_pos hi rsq_bs_hi_pos) hi)
                                          (mult hi (inv_pos hi rsq_bs_hi_pos)) one
                                          (mult_comm (inv_pos hi rsq_bs_hi_pos) hi)
                                          (inv_pos_correct hi rsq_bs_hi_pos))
                               (req_refl (inv_pos hi rsq_bs_hi_pos))).
      + apply req_mult_one_l. }
  assert (Hrc : real_eq (mult (inv_pos hi rsq_bs_hi_pos) (mult hi lo)) lo).
  { apply (req_trans (mult (inv_pos hi rsq_bs_hi_pos) (mult hi lo))
                     (mult (mult (inv_pos hi rsq_bs_hi_pos) hi) lo) lo).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos hi rsq_bs_hi_pos) hi) lo)
                       (mult one lo) lo).
      + apply (req_mult_compat (mult (inv_pos hi rsq_bs_hi_pos) hi) one lo lo
                               (req_trans (mult (inv_pos hi rsq_bs_hi_pos) hi)
                                          (mult hi (inv_pos hi rsq_bs_hi_pos)) one
                                          (mult_comm (inv_pos hi rsq_bs_hi_pos) hi)
                                          (inv_pos_correct hi rsq_bs_hi_pos))
                               (req_refl lo)).
      + apply req_mult_one_l. }
  apply (req_trans (inv_pos hi rsq_bs_hi_pos)
                   (mult (inv_pos hi rsq_bs_hi_pos) (mult hi (inv_pos hi rsq_bs_hi_pos))) lo).
  - apply (req_sym (mult (inv_pos hi rsq_bs_hi_pos) (mult hi (inv_pos hi rsq_bs_hi_pos)))
                   (inv_pos hi rsq_bs_hi_pos)). exact Hlb.
  - apply (req_trans (mult (inv_pos hi rsq_bs_hi_pos) (mult hi (inv_pos hi rsq_bs_hi_pos)))
                     (mult (inv_pos hi rsq_bs_hi_pos) (mult hi lo)) lo).
    + apply (req_mult_compat (inv_pos hi rsq_bs_hi_pos) (inv_pos hi rsq_bs_hi_pos)
                             (mult hi (inv_pos hi rsq_bs_hi_pos)) (mult hi lo)
                             (req_refl (inv_pos hi rsq_bs_hi_pos)) Hcancel).
    + exact Hrc.
Qed.

(* Factor bounds (Id L96211) *)
Lemma rsq_bs_factor_ge_lo : forall s s' : S, real_le lo (factor s s').
Proof.
  intros s s'.
  apply (epp_mono_le (mult invT (opp Delta)) (mult invT (z s s'))).
  exact (req_le_mult_compat_r invT (opp Delta) (z s s')
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_lb s s')).
Qed.

Lemma rsq_bs_factor_le_hi : forall s s' : S, real_le (factor s s') hi.
Proof.
  intros s s'.
  apply (epp_mono_le (mult invT (z s s')) (mult invT Delta)).
  exact (req_le_mult_compat_r invT (z s s') Delta
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_ub s s')).
Qed.

Definition rsq_Zrow (s : S) : R := sumf (fun s' : S => factor s s').

Lemma rsq_bs_Zrow_ge : forall s : S, real_le (mult nR lo) (rsq_Zrow s).
Proof.
  intro s.
  apply (le_id_r (mult nR lo) (rsq_bs_list_sum (fun s' : S => factor s s') enum)
                 (rsq_Zrow s)
                 (req_sym _ _ (sum_eq_list (fun s' : S => factor s s')))).
  exact (rsq_bs_list_ge_const (fun s' : S => factor s s') lo enum
                          (fun x : S => rsq_bs_factor_ge_lo s x)).
Qed.

Lemma rsq_bs_Zrow_le : forall s : S, real_le (rsq_Zrow s) (mult nR hi).
Proof.
  intro s.
  apply (le_id_l (rsq_Zrow s) (rsq_bs_list_sum (fun s' : S => factor s s') enum)
                 (mult nR hi)).
  - exact (sum_eq_list (fun s' : S => factor s s')).
  - exact (rsq_bs_list_le_const (fun s' : S => factor s s') hi enum
                            (fun x : S => rsq_bs_factor_le_hi s x)).
Qed.

Lemma rsq_bs_Zrow_pos : forall s : S, real_lt zero (rsq_Zrow s).
Proof.
  intro s.
  exact (lt_le_trans zero (mult nR lo) (rsq_Zrow s)
                     (mult_positive nR lo rsq_bs_nR_pos rsq_bs_lo_pos) (rsq_bs_Zrow_ge s)).
Qed.

(* The softmax kernel (temperature T; the req-shaped definition) *)
Definition rsq_bs_kernel (s s' : S) : R :=
  mult (factor s s') (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)).

Lemma rsq_bs_kernel_pos : forall s s' : S, real_lt zero (rsq_bs_kernel s s').
Proof.
  intros s s'. exact (mult_positive (factor s s')
                        (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                        (epp_pos (mult invT (z s s')))
                        (inv_pos_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))).
Qed.

Lemma rsq_bs_kernel_nonneg : forall s s' : S, real_le zero (rsq_bs_kernel s s').
Proof.
  intros s s'. exact (lt_le_iff _ _ (inl (rsq_bs_kernel_pos s s'))).
Qed.

Lemma rsq_bs_kernel_row : forall s : S, real_eq (sumf (fun s' : S => rsq_bs_kernel s s')) one.
Proof.
  intro s. unfold rsq_bs_kernel.
  apply (req_trans _ (sumf (fun s' : S =>
        mult (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) (factor s s'))) _).
  - exact (sum_ext
             (fun s' : S => mult (factor s s') (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))
             (fun s' : S => mult (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) (factor s s'))
             (fun s' : S => mult_comm (factor s s')
                                      (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))).
  - apply (req_trans _
             (mult (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                   (sumf (fun s' : S => factor s s'))) _).
    + exact (sum_linear (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                        (fun s' : S => factor s s')).
    + exact (req_trans _ _ _
               (mult_comm (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) (rsq_Zrow s))
               (inv_pos_correct (rsq_Zrow s) (rsq_bs_Zrow_pos s))).
Qed.

(* The uniform distribution U = 1/nR over the enumeration *)
Let Unif : S -> R := fun _ : S => inv_pos nR rsq_bs_nR_pos.

Lemma rsq_bs_Unif_norm : real_eq (sumf Unif) one.
Proof.
  apply (req_trans _ (rsq_bs_list_sum Unif enum) _).
  - exact (sum_eq_list Unif).
  - apply (req_trans _
             (mult (reqd_nat_to_R (length enum)) (inv_pos nR rsq_bs_nR_pos)) _).
    + exact (rsq_bs_list_const_sum (inv_pos nR rsq_bs_nR_pos) enum).
    + exact (inv_pos_correct nR rsq_bs_nR_pos).
Qed.

(* ---- Anchor: via UpReqDist ReqSoftmaxDual reqd_softmax_scaled ----
   (the idempotent-delta dual + the witness-slot bridge; e^(z/T) = e^(-((-z)/T)) as a direct proof chain) *)
Lemma bs_kernel_eq_reqd_scaled :
  forall s s' : S,
    real_eq (rsq_bs_kernel s s')
        (reqd_softmax_scaled S sumf sum_pos invT (fun s0 : S => opp (z s s0)) s').
Proof.
  intros s s'.
  apply (req_trans _ (mult (exp_neg (opp (mult invT (z s s'))))
                           (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))) _).
  - exact (req_refl (mult (exp_neg (opp (mult invT (z s s'))))
                          (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))).
  - apply (req_mult_compat _ _ _ _).
    + apply (exp_neg_req_compat_setoid _ _).
      exact (req_sym _ _ (req_opp_mult_l invT (z s s'))).
    + apply (inv_pos_ext (rsq_Zrow s)
                         (sumf (fun s0 : S => exp_neg (mult invT (opp (z s s0)))))
                         (rsq_bs_Zrow_pos s)
                         (sum_pos (fun s0 : S => exp_neg (mult invT (opp (z s s0))))
                                  (fun s0 : S => exp_neg_pos (mult invT (opp (z s s0)))))).
      apply (sum_ext (fun s'0 : S => factor s s'0)
                     (fun s0 : S => exp_neg (mult invT (opp (z s s0))))).
      intro s0.
      exact (req_trans (rsq_exp_pos_fn (mult invT (z s s0)))
                       (exp_neg (opp (mult invT (z s s0))))
                       (exp_neg (mult invT (opp (z s s0))))
                       (req_refl _)
                       (exp_neg_req_compat_setoid (opp (mult invT (z s s0)))
                          (mult invT (opp (z s s0)))
                          (req_sym _ _ (req_opp_mult_l invT (z s s0))))).
Qed.

(* ===== Main core: the explicit Doeblin lower bound =====
   P(s,s') >= delta_star*U(s'), delta_star := lo*lo = e^(-2D/T) (exact, no loss; direct proof) *)
Lemma rsq_bs_minorization : forall s s' : S,
  real_le (mult delta_star (Unif s')) (rsq_bs_kernel s s').
Proof.
  intros s s'.
  assert (Hchain : real_le (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)))
                      (rsq_bs_kernel s s')).
  { apply (le_trans _ (mult lo (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))).
    - exact (req_le_mult_compat_r lo
                (inv_pos (mult nR hi) (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos))
                (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                (lt_le_iff _ _ (inl rsq_bs_lo_pos))
                (inv_pos_le_compat (rsq_Zrow s) (mult nR hi) (rsq_bs_Zrow_pos s)
                                   (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)
                                   (rsq_bs_Zrow_le s))).
    - unfold rsq_bs_kernel.
      exact (le_id_l _ _ _ (mult_comm lo (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))
               (le_id_r _ _ _
                 (req_sym _ _ (mult_comm (factor s s')
                                         (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))))
                 (req_le_mult_compat_r (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) lo
                                   (factor s s')
                                   (lt_le_iff _ _ (inl (inv_pos_pos (rsq_Zrow s)
                                                        (rsq_bs_Zrow_pos s))))
                                   (rsq_bs_factor_ge_lo s s')))). }
  assert (Heq : real_eq (mult delta_star (Unif s'))
                   (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)))).
  { assert (Hd1 : real_eq (mult lo (inv_pos (mult nR hi)
                                   (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)))
                      (mult lo (mult (inv_pos nR rsq_bs_nR_pos)
                                     (inv_pos hi rsq_bs_hi_pos)))).
    { exact (req_mult_compat lo lo _ _
               (req_refl lo) (req_inv_pos_mult_distr nR hi rsq_bs_nR_pos rsq_bs_hi_pos)). }
    assert (Hd2 : real_eq (mult lo (mult (inv_pos nR rsq_bs_nR_pos) (inv_pos hi rsq_bs_hi_pos)))
                      (mult (mult lo lo) (inv_pos nR rsq_bs_nR_pos))).
    { apply (req_trans
                (mult lo (mult (inv_pos nR rsq_bs_nR_pos) (inv_pos hi rsq_bs_hi_pos)))
                (mult lo (mult (inv_pos nR rsq_bs_nR_pos) lo)) _).
      - exact (req_mult_compat lo lo _ _ (req_refl lo)
                 (req_mult_compat (inv_pos nR rsq_bs_nR_pos) (inv_pos nR rsq_bs_nR_pos)
                    (inv_pos hi rsq_bs_hi_pos) lo (req_refl _) rsq_bs_inv_hi_lo)).
      - apply (req_trans
                  (mult lo (mult (inv_pos nR rsq_bs_nR_pos) lo))
                  (mult lo (mult lo (inv_pos nR rsq_bs_nR_pos)))
                  (mult (mult lo lo) (inv_pos nR rsq_bs_nR_pos))
                  (req_mult_compat lo lo _ _
                     (req_refl lo) (mult_comm (inv_pos nR rsq_bs_nR_pos) lo))
                  (mult_assoc lo lo (inv_pos nR rsq_bs_nR_pos))). }
    exact (req_sym _ _ (req_trans _ _ _ Hd1 Hd2)). }
  exact (le_id_l _ _ _ Heq Hchain).
Qed.

Let inv_two := inv_pos (plus one one) req_two_pos.
Let tv_req (mu nu : S -> R) : R :=
  mult inv_two (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).
Let k_step (mu : S -> R) (s' : S) : R :=
  sumf (fun s : S => mult (mu s) (rsq_bs_kernel s s')).
Fixpoint k_titer (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => k_step (k_titer m mu)
  end.

(* ===== Main theorem 1: two-point TV contraction of the bounded softmax kernel =====
   Explicit rate: 1 - e^(-2D/T) (checked against the fully applied form) *)
Theorem rsq_bounded_softmax_tv_contraction : forall (mu nu : S -> R),
  real_eq (sumf mu) one -> real_eq (sumf nu) one ->
  real_le (tv_req (k_step mu) (k_step nu))
     (mult (req_minus one delta_star) (tv_req mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (rsq_u_tv_contraction S sumf sum_ext sum_linear sum_add sum_le abs_sum_le_h
           Unif rsq_bs_Unif_norm delta_star rsq_bs_delta_star_lt_one
           rsq_bs_kernel rsq_bs_kernel_row rsq_bs_minorization
           bs_swap bs_abs bs_lpc mu nu Hmu Hnu).
Qed.

(* ===== Main theorem 2: iterated contraction, explicit geometric rate (1 - e^(-2D/T))^n ===== *)
Theorem rsq_bounded_softmax_tv_iter : forall (n : nat) (mu nu : S -> R),
  real_eq (sumf mu) one -> real_eq (sumf nu) one ->
  real_le (tv_req (k_titer n mu) (k_titer n nu))
     (mult (req_r_pow (req_minus one delta_star) n) (tv_req mu nu)).
Proof.
  intros n mu nu Hmu Hnu.
  exact (rsq_u_tv_iter S sumf sum_ext sum_linear sum_add sum_le abs_sum_le_h
           Unif rsq_bs_Unif_norm delta_star rsq_bs_delta_star_lt_one
           rsq_bs_kernel rsq_bs_kernel_row rsq_bs_minorization
           bs_swap bs_abs bs_lpc n mu nu Hmu Hnu).
Qed.

End ReqBoundedSoftmax.
