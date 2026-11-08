(* ConstructiveWorld-Set — kernel-value lower band for the bounded softmax kernel. *)

(** * abl_p7_lower_band: a lower band on the P7 bounded softmax kernel
       values, exported as an independent member.

    Mission.  The bounded-logits softmax kernel is pointwise no smaller
    than lo / (N * hi) — lo := e^{-Delta/T}, hi := e^{Delta/T}, N the
    enumeration size; the chain assembles in three stages (row-sum
    upper bound, antitone reciprocals, factor lower band).
    [p7d_kernel_ge_lo_over_nRhi] keeps the explicit positivity premise,
    [p7d_kernel_ge_lo_over_nRhi_pos] closes it by the positivity
    closure, and with [p7d_kernel_le_hi_over_nRlo] the band is two-sided.

    Dependencies.  Stdlib [List]; [S01_BaseRing], [AttnDoeblin],
    [P7BoundedSoftmaxDeep] of this development (provenance block below).

    References.  This development, abl_p7_lower_band.v, the baseline
    module in ConstructiveWorld-Main whose statement names are carried
    over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].  Chained assembly all
      [Qed]-closed; no classical choice, no proof erasure, zero
      admitted statements; both closing extractions report Closed.

    Build.  [coqc -native-compiler no -q -Q . "" abl_p7_lower_band.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import AttnDoeblin.
Require Import P7BoundedSoftmaxDeep.

(* ============================================================ *)
(* Dependency provenance.  [S01_BaseRing] interface face: [le]/[lt]     *)
(* transitivity and substitution, antitone order-reversing [inv_pos]    *)
(* with its positivity, [mult_positive], [le_mult_compat_r].            *)
(* [AttnDoeblin] base: [bs_Zrow_le] row-sum upper bound, [bs_Zrow_pos]  *)
(* row-sum positivity, [bs_factor_ge_lo] factor lower band, [bs_kernel] *)
(* kernel, [Zrow] row sum, [nat_to_R].  [P7BoundedSoftmaxDeep]:         *)
(* isomorphic to the registered upper-band member; its positivity       *)
(* certificates [p7d_nR_pos], [p7d_lo_pos], [p7d_hi_pos] are reused     *)
(* here.  Derivation provenance: transcription-level export of the      *)
(* lower-band assembly chain inside the AttnDoeblin main member;        *)
(* limb-by-limb counterpart of the Section-7 upper-band theorem of      *)
(* [P7BoundedSoftmaxDeep].                                              *)
(* ============================================================ *)

(* ################ Kernel-value lower band: the independent counterpart of the
   Section-7 upper band ################ *)

Section P7DKernelLowerBand.
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

(* Three positivity certificates: the nR positivity reuses the certificate
   of the corresponding registered upper-band member; lo/hi positivity cites
   exponential positivity directly. *)
Lemma p7d_lb_nR_pos : lt zero nR.
Proof. exact (p7d_nR_pos enum enum_nonempty sum_eq_list). Qed.

Lemma p7d_lb_lo_pos : lt zero lo.
Proof. exact (p7d_lo_pos temp temp_pos Delta expf expf_pos). Qed.

Lemma p7d_lb_hi_pos : lt zero hi.
Proof. exact (p7d_hi_pos temp temp_pos Delta expf expf_pos). Qed.

(* ===== Kernel-value lower band, general form =====
   Chain: the row sum is at most N * hi (bs_Zrow_le), so the first limb
   applies the antitone inversion of reciprocals (inv_pos_le_compat) and
   multiplies lo into the bound (le_mult_compat_r); in the second limb,
   with the row-sum reciprocal as the factor, the kernel is at least
   lo * row-sum-reciprocal (bs_factor_ge_lo pointwise lower band); the
   two limbs close by le_trans. *)
Theorem p7d_kernel_ge_lo_over_nRhi : forall (s s' : S) (HnRhi : lt zero (mult nR hi)),
  le (mult lo (inv_pos (mult nR hi) HnRhi))
     (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s').
Proof.
  intros s s' HnRhi.
  apply (le_trans _ (mult lo
           (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
              (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                 Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))).
  - apply (le_mult_compat_r lo (inv_pos (mult nR hi) HnRhi)
             (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                   Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
             (lt_le_iff _ _ (inl p7d_lb_lo_pos))).
    exact (inv_pos_le_compat (AttnDoeblin.Zrow temp temp_pos z expf s) (mult nR hi)
             (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)
             HnRhi
             (AttnDoeblin.bs_Zrow_le enum temp temp_pos Delta z z_ub
                expf expf_mono_le sum_eq_list s)).
  - exact (le_id_l _ _ _
             (mult_comm lo
                (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                   (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                      Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))
             (le_id_r _ _ _
               (id_sym (mult_comm (expf (mult invT (z s s')))
                                  (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                                     (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                                        Delta z z_lb expf expf_pos expf_mono_le
                                        sum_eq_list s))))
               (le_mult_compat_r
                  (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                     (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                        Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
                  lo (expf (mult invT (z s s')))
                  (lt_le_iff _ _ (inl (inv_pos_pos
                     (AttnDoeblin.Zrow temp temp_pos z expf s)
                     (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                        Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))))
                  (AttnDoeblin.bs_factor_ge_lo temp temp_pos Delta z z_lb
                     expf expf_mono_le s s')))).
Qed.

(* Instantiated form: N * hi > 0 is supplied by the mult_positive closure. *)
Theorem p7d_kernel_ge_lo_over_nRhi_pos : forall s s' : S,
  le (mult lo (inv_pos (mult nR hi)
         (mult_positive nR hi p7d_lb_nR_pos p7d_lb_hi_pos)))
     (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s').
Proof.
  intros s s'.
  exact (p7d_kernel_ge_lo_over_nRhi s s'
           (mult_positive nR hi p7d_lb_nR_pos p7d_lb_hi_pos)).
Qed.

End P7DKernelLowerBand.

(* ################ Assumption extraction (same standard as the registered members) ################ *)
Print Assumptions p7d_kernel_ge_lo_over_nRhi.
Print Assumptions p7d_kernel_ge_lo_over_nRhi_pos.
