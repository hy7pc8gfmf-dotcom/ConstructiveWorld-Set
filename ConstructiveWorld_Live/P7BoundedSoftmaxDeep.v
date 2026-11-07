(* ConstructiveWorld-Set — Deep derivability study of the BoundedSoftmax interface premises of AttnDoeblin. *)
(** * P7BoundedSoftmaxDeep: deriving the certificate-class premises of the BoundedSoftmax section from more basic principles.

    Mission.  From the 19-[Variable] interface of the AttnDoeblin [BoundedSoftmax]
      section, the eleven certificate-class premises are examined for derivability from
      more basic in-library principles: [bs_swap] is derivable from [sum_eq_list] plus
      pure list combinatorics (the list-Fubini theorem), so the field face drops to 18
      and the two main theorems are restated without [bs_swap]
      ([p7d_tv_contraction_no_swap], [p7d_tv_iter_no_swap]); [enum_nonempty] is
      equivalent to its product [nR > 0] ([p7d_enum_nonempty_gives_nR_pos],
      [p7d_nR_pos_gives_enum_nonempty]); scale products [p7d_hi_gt_one] and
      [p7d_one_le_hi_sq]; the factor-reciprocal identity [p7d_factor_over_hi]; the
      independent kernel upper band [p7d_kernel_le_hi_over_nRlo] (the per-premise
      verdict table is the appendix at the end of this file).

    Dependencies.  Stdlib [List]; requires [S01_BaseRing] through [S15_TailFEPUp]
      and [AttnDoeblin] of this development ([bs_nR_pos], [bs_lo_hi_eq], [bs_lo_lt_hi],
      [bs_hi_pos], [bs_inv_hi_lo], [bs_Zrow_pos], [bs_Zrow_ge], [bs_factor_le_hi],
      [bs_kernel], [Zrow], [nat_to_R], [plus_exchange], and the two main theorems).

    References.  The two main theorems of [AttnDoeblin] (restated here without
      [bs_swap]); the S01_BaseRing ordered-field lemma face ([lt_irrefl],
      [mult_positive], [inv_pos_le_compat], and their peers).

    Constructivity.  Purely constructive with nothing admitted; statements are
      [Set]-layer and all proofs close with [Qed]; the closing [Print Assumptions]
      block is expected [Closed] throughout.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" P7BoundedSoftmaxDeep.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]. *)

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

(* ################ Section 1. list-Fubini combinatorics (the foundation of the bs_swap derivations) ################
   Pointwise congruence, additive linearity, and double-sum exchange on the section
   machine [AttnDoeblin.bs_list_sum]. *)

Section P7DListSum.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* Pointwise Id implies the list sums are Id (the list counterpart of [sum_over_S_ext] for [bs_list_sum]) *)
Theorem p7d_lsum_ext : forall (f g : S -> R) (l : list S),
  (forall x : S, Id (f x) (g x)) ->
  Id (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 plus (H x) IH).
Qed.

(* Additive linearity of the list sum (the list version of [sum_over_S_add]) *)
Theorem p7d_lsum_add : forall (f g : S -> R) (l : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => plus (f s) (g s)) l)
     (plus (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (id_sym (plus_zero zero)).
  - simpl.
    apply (id_trans (id_cong (fun w : R => plus (plus (f x) (g x)) w) IH)).
    exact (AttnDoeblin.plus_exchange (f x) (AttnDoeblin.bs_list_sum f t)
                                     (g x) (AttnDoeblin.bs_list_sum g t)).
Qed.

(* The list sum of the zero function is zero (via the base [bs_list_const_sum] and the zero element of mult) *)
Theorem p7d_lsum_zero : forall l : list S,
  Id zero (AttnDoeblin.bs_list_sum (fun _ : S => zero) l).
Proof.
  intro l.
  exact (id_sym (id_trans (AttnDoeblin.bs_list_const_sum zero l)
                  (mult_zero (AttnDoeblin.nat_to_R (length l))))).
Qed.

(* Exchange of double list sums (general form with the inner and outer lists separate; the core of the Fubini combinatorics) *)
Theorem p7d_lsum_fubini_gen : forall (f : S -> S -> R) (l1 l2 : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => AttnDoeblin.bs_list_sum (f s) l2) l1)
     (AttnDoeblin.bs_list_sum (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') l1) l2).
Proof.
  intros f l1. induction l1 as [| x t IH]; intro l2.
  - apply (id_trans (p7d_lsum_zero l2)).
    exact (p7d_lsum_ext (fun _ : S => zero)
                        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') nil)
                        l2 (fun s' : S => id_refl)).
  - apply (id_trans (id_cong (fun w : R => plus (AttnDoeblin.bs_list_sum (f x) l2) w)
                             (IH l2))).
    apply (id_sym (p7d_lsum_add (fun s' : S => f x s')
              (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') t) l2)).
Qed.

End P7DListSum.

(* ################ Section 2. The bs_swap derivation proper ################
   [bs_swap], the first of the interface's structural certificates, is derivable
   outright under [sum_eq_list] (the enumerated-sum normalization, itself a closed
   slot): it is not an independent interface position. *)

Section P7DSwap.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).

Theorem p7d_swap_of_sum_eq_list : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  intro f.
  apply (id_trans (sum_eq_list (fun s : S => sum_over_S (fun s' : S => f s s')))).
  apply (id_trans (p7d_lsum_ext
            (fun s : S => sum_over_S (fun s' : S => f s s'))
            (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum
            (fun s : S => sum_eq_list (fun s' : S => f s s')))).
  apply (id_trans (p7d_lsum_fubini_gen f enum enum)).
  apply (id_trans (id_sym (p7d_lsum_ext
            (fun s' : S => sum_over_S (fun s : S => f s s'))
            (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum
            (fun s' : S => sum_eq_list (fun s : S => f s s'))))).
  exact (id_sym (sum_eq_list (fun s' : S => sum_over_S (fun s : S => f s s')))).
Qed.

End P7DSwap.

(* ################ Section 3. The field face 19→18 — the two main theorems restated without bs_swap ################ *)

Section P7DNoSwap.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable bs_abs : forall a : R, le zero a -> Id (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).
(* Note: this Section does not contain bs_swap — 18 fields. *)

(* Main theorem 1 (the single-step TV contraction) holds under the field face without bs_swap: the swap position is filled by [p7d_swap_of_sum_eq_list]. *)
Theorem p7d_tv_contraction_no_swap : forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv_dist (@attention_step RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) mu)
              (@attention_step RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) nu))
     (mult (minus one
              (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                    (expf (mult (inv_pos temp temp_pos) (opp Delta)))))
           (tv_dist mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (@AttnDoeblin.bounded_softmax_tv_contraction
           RI SS SO enum enum_nonempty temp temp_pos Delta Delta_pos
           z z_lb z_ub expf expf_pos expf_zero expf_plus expf_mono_lt
           expf_mono_le (p7d_swap_of_sum_eq_list enum sum_eq_list)
           bs_abs bs_lpc sum_eq_list mu nu Hmu Hnu).
Qed.

(* Main theorem 2 (the iterated geometric rate (1−e^{−2Δ/T})ⁿ), restated the same way without bs_swap. *)
Theorem p7d_tv_iter_no_swap : forall (n : nat) (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv_dist (@u_titer RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) n mu)
              (@u_titer RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) n nu))
     (mult (@r_pow RI
              (minus one
                (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                      (expf (mult (inv_pos temp temp_pos) (opp Delta))))) n)
           (tv_dist mu nu)).
Proof.
  intros n mu nu Hmu Hnu.
  exact (@AttnDoeblin.bounded_softmax_tv_iter
           RI SS SO enum enum_nonempty temp temp_pos Delta Delta_pos
           z z_lb z_ub expf expf_pos expf_zero expf_plus expf_mono_lt
           expf_mono_le (p7d_swap_of_sum_eq_list enum sum_eq_list)
           bs_abs bs_lpc sum_eq_list n mu nu Hmu Hnu).
Qed.

End P7DNoSwap.

(* ################ Section 4. enum_nonempty ⟷ nR>0 (certificate-product equivalence) ################ *)

Section P7DEnum.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* Forward direction: a use-wrapper of the base [bs_nR_pos] (certificate implies product) *)
Theorem p7d_enum_nonempty_gives_nR_pos :
  forall (enum : list S) (enum_nonempty : Not (Id enum nil))
         (sel : forall g : S -> R, Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum)),
  lt zero (AttnDoeblin.nat_to_R (length enum)).
Proof.
  intros enum enum_nonempty sel.
  exact (AttnDoeblin.bs_nR_pos enum enum_nonempty sel).
Qed.

(* Reverse direction (new proof): product implies certificate.  The entire content of
   enum_nonempty is exactly nR>0 — the interface could switch to the analytic
   statement without loss. *)
Theorem p7d_nR_pos_gives_enum_nonempty :
  forall enum : list S,
  lt zero (AttnDoeblin.nat_to_R (length enum)) -> Not (Id enum nil).
Proof.
  intros enum HnR Heq.
  exact (lt_irrefl zero
           (lt_id_r zero (AttnDoeblin.nat_to_R (length enum))
              (AttnDoeblin.nat_to_R (length nil))
              (id_cong (fun l : list S => AttnDoeblin.nat_to_R (length l)) Heq)
              HnR)).
Qed.

End P7DEnum.

(* ################ Section 5. Temperature/Δ product deepenings ################
   The base already gives lo = e^{−Δ/T} < 1 ([bs_lo_lt_hi]); this section adds the
   dual hi = e^{Δ/T} > 1 and the spread 1 ≤ hi², completing the softmax scale
   sandwich lo < 1 < hi ≤ hi². *)

Section P7DScale.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* The dual companion: hi = e^{Δ/T} > 1 (from 0 < Δ/T with the strict monotonicity of expf, plus expf_zero) *)
Theorem p7d_hi_gt_one :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  lt one (expf (mult (inv_pos temp temp_pos) Delta)).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_mono_lt.
  exact (lt_id_r one (expf (mult Delta (inv_pos temp temp_pos)))
           (expf (mult (inv_pos temp temp_pos) Delta))
           (id_cong expf (mult_comm Delta (inv_pos temp temp_pos)))
           (lt_id_l one (expf zero)
              (expf (mult Delta (inv_pos temp temp_pos)))
              (id_sym expf_zero)
              (expf_mono_lt zero (mult Delta (inv_pos temp temp_pos))
                 (mult_positive Delta (inv_pos temp temp_pos) Delta_pos
                    (inv_pos_pos temp temp_pos))))).
Qed.

(* The spread theorem: 1 ≤ hi² = e^{2Δ/T} (using hi ≥ lo > 0 and hi·lo = 1) *)
Theorem p7d_one_le_hi_sq :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) Delta))).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_plus expf_mono_lt.
  apply (le_trans _ (mult (expf (mult (inv_pos temp temp_pos) Delta))
                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))).
  - apply (le_id_r one one
             (mult (expf (mult (inv_pos temp temp_pos) Delta))
                   (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (id_sym (id_trans (mult_comm (expf (mult (inv_pos temp temp_pos) Delta))
                                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))
                               (AttnDoeblin.bs_lo_hi_eq temp temp_pos Delta expf
                                                        expf_zero expf_plus)))
             (le_refl one)).
  - exact (le_mult_compat_r (expf (mult (inv_pos temp temp_pos) Delta))
             (expf (mult (inv_pos temp temp_pos) (opp Delta)))
             (expf (mult (inv_pos temp temp_pos) Delta))
             (lt_le_iff _ _ (inl (expf_pos (mult (inv_pos temp temp_pos) Delta))))
             (lt_le_iff _ _ (inl (AttnDoeblin.bs_lo_lt_hi temp temp_pos Delta Delta_pos
                                    expf expf_mono_lt)))).
Qed.

End P7DScale.

(* ################ Section 6. expf field products — the factor-reciprocal identity ################ *)

Section P7DExpfShape.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* Multiplicative splitting at a common temperature: e^{k·a}·e^{k·b} = e^{k·(a+b)} *)
Theorem p7d_expf_plus_mult_l :
  forall (k a b : R) (expf : R -> R)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b))),
  Id (mult (expf (mult k a)) (expf (mult k b))) (expf (mult k (plus a b))).
Proof.
  intros k a b expf expf_plus.
  apply (id_trans (id_sym (expf_plus (mult k a) (mult k b)))).
  exact (id_cong expf (id_sym (distrib k a b))).
Qed.

(* The factor-reciprocal identity: e^{z/T}·(e^{Δ/T})⁻¹ = e^{(z−Δ)/T} —
   the homomorphic property of expf reduces the ratio structure of kernel values
   to a logit difference. *)
Theorem p7d_factor_over_hi :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R)
         (a b : R) (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b))),
  Id (mult (expf (mult (inv_pos temp temp_pos) a))
           (inv_pos (expf (mult (inv_pos temp temp_pos) Delta))
                    (AttnDoeblin.bs_hi_pos temp temp_pos Delta expf expf_pos)))
     (expf (mult (inv_pos temp temp_pos) (plus a (opp Delta)))).
Proof.
  intros temp temp_pos Delta a b expf expf_pos expf_zero expf_plus.
  apply (id_trans (id_cong2 mult
            (id_refl : Id (expf (mult (inv_pos temp temp_pos) a))
                          (expf (mult (inv_pos temp temp_pos) a)))
            (AttnDoeblin.bs_inv_hi_lo temp temp_pos Delta expf
                                     expf_pos expf_zero expf_plus))).
  exact (p7d_expf_plus_mult_l (inv_pos temp temp_pos) a (opp Delta) expf expf_plus).
Qed.

End P7DExpfShape.

(* ################ Section 7. Products of the z bounds — an independent kernel upper band ################
   The base inlines the lower band lo ≤ K ≤ ... inside the bs_minorization proof;
   this section derives the independent upper band K(s,s') ≤ hi/(nR·lo) (using the
   Zrow lower bound). *)

Section P7DKernelBand.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).

Let invT := inv_pos temp temp_pos.
Let nR := AttnDoeblin.nat_to_R (length enum).
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

Lemma p7d_nR_pos : lt zero nR.
Proof. exact (AttnDoeblin.bs_nR_pos enum enum_nonempty sum_eq_list). Qed.

Lemma p7d_lo_pos : lt zero lo.
Proof. exact (expf_pos (mult invT (opp Delta))). Qed.

Lemma p7d_hi_pos : lt zero hi.
Proof. exact (expf_pos (mult invT Delta)). Qed.

Theorem p7d_kernel_le_hi_over_nRlo : forall (s s' : S) (HnRlo : lt zero (mult nR lo)),
  le (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s')
     (mult hi (inv_pos (mult nR lo) HnRlo)).
Proof.
  intros s s' HnRlo.
  assert (Hinvle : le (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                        (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                           Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
                      (inv_pos (mult nR lo) HnRlo)).
  { exact (inv_pos_le_compat (mult nR lo) (AttnDoeblin.Zrow temp temp_pos z expf s)
             HnRlo
             (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)
             (AttnDoeblin.bs_Zrow_ge enum temp temp_pos Delta z z_lb
                expf expf_mono_le sum_eq_list s)). }
  apply (le_trans _ (mult hi
           (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
              (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                 Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))).
  - apply (le_id_l _
             (mult (expf (mult invT (z s s')))
                   (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                      (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                         Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))
             _).
    + exact id_refl.
    + exact (le_mult_compat_weak
               (expf (mult invT (z s s'))) hi
               (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                  (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                     Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
               (lt_le_iff _ _ (inl (inv_pos_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                  (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                     Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))))
               (AttnDoeblin.bs_factor_le_hi temp temp_pos Delta z z_ub
                  expf expf_mono_le s s')).
  - exact (le_mult_compat_r hi
               (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                  (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                     Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
               (inv_pos (mult nR lo) HnRlo)
               (lt_le_iff _ _ (inl p7d_hi_pos)) Hinvle).
Qed.

(* The instantiated form: nR·lo > 0 supplied in closed form by [mult_positive] *)
Theorem p7d_kernel_le_hi_over_nRlo_pos : forall s s' : S,
  le (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s')
     (mult hi (inv_pos (mult nR lo) (mult_positive nR lo p7d_nR_pos p7d_lo_pos))).
Proof.
  intros s s'.
  exact (p7d_kernel_le_hi_over_nRlo s s' (mult_positive nR lo p7d_nR_pos p7d_lo_pos)).
Qed.

End P7DKernelBand.

(* ################ Print Assumptions ################ *)
Print Assumptions p7d_lsum_ext.
Print Assumptions p7d_lsum_add.
Print Assumptions p7d_lsum_fubini_gen.
Print Assumptions p7d_lsum_zero.
Print Assumptions p7d_swap_of_sum_eq_list.
Print Assumptions p7d_tv_contraction_no_swap.
Print Assumptions p7d_tv_iter_no_swap.
Print Assumptions p7d_enum_nonempty_gives_nR_pos.
Print Assumptions p7d_nR_pos_gives_enum_nonempty.
Print Assumptions p7d_hi_gt_one.
Print Assumptions p7d_one_le_hi_sq.
Print Assumptions p7d_expf_plus_mult_l.
Print Assumptions p7d_factor_over_hi.
Print Assumptions p7d_kernel_le_hi_over_nRlo.
Print Assumptions p7d_kernel_le_hi_over_nRlo_pos.

(* ################ Appendix: the per-premise verdict table ################
   Field (AttnDoeblin.v L444-476, vorebuild line numbers)   | Verdict    | Constructed here
   ---------------------------------------------------------+------------+---------
   enum(:444)          data position: a list value supplied by the instance | design face | — (its combinatorics live in Sections 1-2)
   enum_nonempty(:445) certificate position | derivable | Section 4 (the ⟷ nR>0 equivalence, two theorems)
   temp(:446)          data position | design face | —
   temp_pos(:447)      certificate position | derivable | Section 5 (the invT positivity products hi>1, 1≤hi²)
   Delta(:448)         data position | design face | —
   Delta_pos(:449)     certificate position | derivable | Section 5 (the same, via Δ>0)
   z(:450)             data position | design face | —
   z_lb(:451)          certificate position | derivable | Section 7 (the lower band plus the new upper band)
   z_ub(:452)          certificate position | derivable | Section 7 (the main use of the upper band)
   expf(:464)          data position (its satisfiability is discharged by the instantiated instance) | derivable | Section 6 (the factor-reciprocal identity)
   bs_swap(:472)       structural certificate position | ablatable | Sections 2-3 (derived from the sum_eq_list slot, 19→18)
   Design face total: 4 — enum/temp/Delta/z (pure data, supplied by the instance, not proof obligations);
   derivable/ablatable: 7 — enum_nonempty, temp_pos, Delta_pos, z_lb, z_ub, expf, bs_swap. *)
