(* ConstructiveWorld-Set -- req-layer transcription modules of upstream miscellany families. *)

(** * UpReqMisc5B: req-layer miscellany bundle over the enhanced real interface.

    Mission.  The req-layer miscellany bundle in three faces: the vector-world class layer [reqStateSpace], [reqStateSpaceExt],
      [reqHilbertSpace], [reqSumOver]; the thermodynamic, convergence, language-model, GRPO, and differentiable-algebra statements
      [req_core_claim5_holds], [req_gradient_step_recurrence], [req_sum_exp_positive], [req_grpo_uniform_mass],
      [req_dpo_loss_diff_decomp]; and the Hilbert-space orthogonal decomposition pair [req_orthogonal_decomposition_exists],
      [req_orthogonal_decomposition_unique].  Beyond these three faces it also carries the Part 9 Gram-Schmidt family [req_gram_schmidt_step], [req_gram_schmidt_pair] and the Part 10 multivariable differentiable-algebra family.

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing] through [S15_TailFEPUp] and [UpReqAlgebra], [UpReqDist] of this development.  This tree's interface class
      [RealInterfaceEnhancedSetoid] is unparameterized (the [UpReqDist] precedent), so the Main-tree binder pair [(R : Set)] [(RIS : RealInterfaceEnhancedSetoid R)] is carrier-ized
      away ([R := Real]; statement faces at the concrete [real_eq]/[real_lt]/[real_le] relations of that canon, definitionally the same propositions at the instance;
      extraction at [Obj.magic] = 0); statement names are carried over verbatim.

    References.  This development, UpReqMisc5B.v, the baseline module in ConstructiveWorld-Main whose
      statement names are carried over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set] (decidable Q-carriers and
      boolean identity carriers); statements extract with [Obj.magic] = 0 and no erasure; [coqchk]
      reports [Axioms: none].  Honest-boundary disclosure: [rprojection_idempotent], [rmv_adjoint]
      and [rop_lipschitz] are declared as section variables (same-shape slots of their Id-world
      counterparts, kept in place) rather than proven in this file; consumed slots bind as
      explicit function arguments once their enclosing sections close.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqMisc5B.v] compiles cleanly (exit 0);
      the artifact starts with [436f7121 000160bc] (this tree's Rocq 9.3.0 toolchain magic). *)
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
From Stdlib Require Import List.
Import ListNotations.
(* The interface class in this tree is unparameterized (the UpReqDist precedent);
   its carrier is the global Cauchy real [Real]. *)
Abbreviation R := Real.

(* ============================================================ *)
(* Part 1: the vector-world class transcription layer *)
(* Equality-face selection: the req field of the req interface is defined  *)
(* only on R (interface L40471, [req : R -> R -> Set]); equality at        *)
(* R-valued positions is [req] (checked piecewise), while equality at      *)
(* vector-carrier positions stays [Id] (Leibniz, polymorphic, L69; the     *)
(* carrier has no setoid equality to transport along, which is no          *)
(* downgrade: [Id] is the inductive-family constructive equality).         *)
(* ============================================================ *)

(* req copy of the Id-world StateSpace (L1160-1187), field by field: 21 fields. *)
Class reqStateSpace := {
  rSS : Set;
  rszero : rSS;
  rsplus : rSS -> rSS -> rSS;
  rsmult : R -> rSS -> rSS;
  rsopp : rSS -> rSS;

  rsplus_assoc : forall a b c : rSS,
    Id (rsplus a (rsplus b c)) (rsplus (rsplus a b) c);
  rsplus_comm : forall a b : rSS, Id (rsplus a b) (rsplus b a);
  rsplus_zero : forall a : rSS, Id (rsplus a rszero) a;
  rsplus_opp : forall a : rSS, Id (rsplus a (rsopp a)) rszero;
  rsmult_one : forall a : rSS, Id (rsmult one a) a;
  rsmult_assoc : forall (a b : R) (x : rSS),
    Id (rsmult a (rsmult b x)) (rsmult (mult a b) x);
  rsmult_distrib_r : forall (a : R) (x y : rSS),
    Id (rsmult a (rsplus x y)) (rsplus (rsmult a x) (rsmult a y));
  rsmult_distrib_l : forall (a b : R) (x : rSS),
    Id (rsmult (plus a b) x) (rsplus (rsmult a x) (rsmult b x));

  rsmetric : rSS -> rSS -> R;
  rsmetric_sym : forall a b : rSS, real_eq(rsmetric a b) (rsmetric b a);
  (* The plain [le] of the Id-world smetric_pos (L1177) is kept position      *)
  (* for position; the setoid-interface counterpart field carries the eps     *)
  (* form, so the plain form is the honest interface slot (RestB Part 4       *)
  (* precedent). *)
  rsmetric_pos : forall a b : rSS, real_le(zero) (rsmetric a b);
  rsmetric_zero : forall a b : rSS,
    real_eq(rsmetric a b) (zero) -> Id a b;
  (* The plain [le] of the Id-world smetric_triangle (L1180) is kept position for position, as above. *)
  rsmetric_triangle : forall a b c : rSS,
    real_le(rsmetric a c) (plus(rsmetric a b) (rsmetric b c));

  rclim : (nat -> rSS) -> rSS -> Set;
  rclim_unique : forall u l1 l2, rclim u l1 -> rclim u l2 -> Id l1 l2;
  rcauchy_complete_S :
    forall (u : nat -> rSS),
      (forall eps : R, real_lt(zero) eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n -> real_lt(rsmetric (u m) (u n)) eps)) ->
      sigT (fun l : rSS => rclim u l)
}.


(* Same-shape transcription of the Id-world sminus (L15525) as a transparent [rsminus] definition. *)
Definition rsminus (SS : reqStateSpace)
    (a b : @rSS SS) : @rSS SS :=
  @rsplus SS a (@rsopp SS b).

(* req copy of the Id-world StateSpaceExtended (L24738-24758), field by     *)
(* field: 9 fields; the :> inheritance of Id becomes an explicit            *)
(* [rsse_base] slot plus an explicit unpack of the dependent module, with   *)
(* zero semantic difference. *)
Class reqStateSpaceExt := {
  rsse_base : reqStateSpace;
  rsmult_zero : forall x : @rSS rsse_base,
    Id (@rsmult rsse_base (zero) x) (@rszero rsse_base);
  rsmult_opp : forall (a : R) (x : @rSS rsse_base),
    Id (@rsmult rsse_base (opp a) x)
       (@rsopp rsse_base (@rsmult rsse_base a x));
  rsmult_splus_distrib : forall (a : R) (x y : @rSS rsse_base),
    Id (@rsmult rsse_base a (@rsplus rsse_base x y))
       (@rsplus rsse_base (@rsmult rsse_base a x) (@rsmult rsse_base a y));
  rsnorm : @rSS rsse_base -> R;
  rsnorm_pos : forall x : @rSS rsse_base, real_le(zero) (rsnorm x);
  rsnorm_zero : forall x : @rSS rsse_base,
    real_eq(rsnorm x) (zero) -> Id x (@rszero rsse_base);
  rsnorm_smult : forall (a : R) (x : @rSS rsse_base),
    real_eq(rsnorm (@rsmult rsse_base a x))
        (mult(abs a) (rsnorm x));
  rsnorm_triangle : forall x y : @rSS rsse_base,
    real_le(rsnorm (@rsplus rsse_base x y))
       (plus(rsnorm x) (rsnorm y));
  rsmetric_snorm : forall u v : @rSS rsse_base,
    real_eq(@rsmetric rsse_base u v)
        (rsnorm (@rsminus rsse_base u v))
}.

(* req copy of the Id-world HilbertSpace (L1260-1276), field by field: 9 fields. *)
Class reqHilbertSpace (SS : reqStateSpace) : Set := {
  rinner : @rSS SS -> @rSS SS -> R;
  rinner_sym : forall x y : @rSS SS,
    real_eq(rinner x y) (rinner y x);
  rinner_pos : forall x : @rSS SS, real_le(zero) (rinner x x);
  rinner_definite : forall x : @rSS SS,
    real_eq(rinner x x) (zero) -> Id x (@rszero SS);
  rinner_splus_l : forall x y z : @rSS SS,
    real_eq(rinner (@rsplus SS x y) z)
        (plus(rinner x z) (rinner y z));
  rinner_smult_l : forall (a : R) (x y : @rSS SS),
    real_eq(rinner (@rsmult SS a x) y) (mult a(rinner x y));
  rproj : @rSS SS -> @rSS SS -> @rSS SS;
  rproj_linear : forall u v w : @rSS SS,
    Id (rproj u (@rsplus SS v w))
       (@rsplus SS (rproj u v) (rproj u w));
  rproj_orthogonal : forall u v : @rSS SS,
    real_eq(rinner (@rsplus SS v (@rsopp SS (rproj u v))) u) (zero)
}.

(* req copy of the Id-world SumOver (L1408-1452), field by field: 8 fields. *)
Class reqSumOver (SS : reqStateSpace) : Set := {
  rsum_over_S : (@rSS SS -> R) -> R;
  rsum_over_S_linear : forall (a : R) (f : @rSS SS -> R),
    real_eq(rsum_over_S (fun s => mult a(f s))) (mult a(rsum_over_S f));
  rsum_over_S_add : forall f g : @rSS SS -> R,
    real_eq(rsum_over_S (fun s => plus(f s) (g s)))
        (plus(rsum_over_S f) (rsum_over_S g));
  rsum_over_S_ext : forall f g : @rSS SS -> R,
    (forall s, real_eq(f s) (g s)) -> real_eq(rsum_over_S f) (rsum_over_S g);
  rsum_over_S_le : forall f g : @rSS SS -> R,
    (forall s, real_le(f s) (g s)) -> real_le(rsum_over_S f) (rsum_over_S g);
  rsum_over_S_nonneg : forall f : @rSS SS -> R,
    (forall s, real_le(zero) (f s)) -> real_le(zero) (rsum_over_S f);
  rsum_over_S_zero_nonneg : forall f : @rSS SS -> R,
    (forall s, real_le(zero) (f s)) -> real_eq(rsum_over_S f) (zero) ->
      forall s, real_eq(f s) (zero);
  rabs_sum_le : forall f : @rSS SS -> R,
    real_le(abs(rsum_over_S f)) (rsum_over_S (fun s => abs(f s)))
}.

(* ============================================================ *)
(* Part 2: the four PropositionConvergenceCore pieces (Id L1454-1700 dependence face) *)
(* ============================================================ *)
Section ReqPropConvCore.
Context {SS : reqStateSpace} {SO : reqSumOver SS}.

Let S : Set := @rSS SS.
Let sumS := @rsum_over_S SS SO.

(* Definition transcriptions of the Id-world Proposition (L1490), boltzmann_factor (L1568), and boltzmann_prob (L1572). *)
Variable rZ : R.
Variable rZ_pos : real_lt zero rZ.
Variable rD : R.
Variable rD_pos : real_lt zero rD.
Variable rk_B : R.
Variable rk_B_pos : real_lt zero rk_B.

Definition rboltzmann_factor (L : S -> R) (s : S) : R :=
  exp_neg (mult (inv_pos rD rD_pos) (L s)).

Definition rboltzmann_prob (L : S -> R) (s : S) : R :=
  mult (inv_pos rZ rZ_pos) (rboltzmann_factor L s).

(* The Id-world partition_condition (L1576): the sum_over_S position is [rsum_over_S] and the statement face goes from Id to req. *)
Definition rpartition_condition (L : S -> R) : Set :=
  real_eq rZ (sumS (rboltzmann_factor L)).

(* The Id-world CoreClaim5 (L1608): the ExistsT position is carried         *)
(* verbatim, while the function-equality face becomes pointwise ([req] is   *)
(* defined only on R): [Id p (boltzmann_prob L)] turns into                 *)
(* [forall s, req (p s) (rboltzmann_prob L s)] with a same-shape witness.   *)
Definition rCoreClaim5 : Set :=
  forall L : S -> R, rpartition_condition L ->
    ExistsT (fun p : S -> R => forall s : S, real_eq (p s) (rboltzmann_prob L s)).

(* The Id-world core_claim5_holds (L1619): a witness plus reflexivity, closing at the definition level. *)
Theorem req_core_claim5_holds : rCoreClaim5.
Proof.
  unfold rCoreClaim5. intros L _.
  exists (fun s => mult (inv_pos rZ rZ_pos)
                        (exp_neg (mult (inv_pos rD rD_pos) (L s)))).
  intro s. unfold rboltzmann_prob, rboltzmann_factor.
  apply req_refl.
Qed.

(* The Id-world boltzmann_factor_pos (L1628) by direct use of the [exp_neg_pos] field. *)
Theorem req_boltzmann_factor_pos :
  forall (L : S -> R) (s : S), real_lt zero (rboltzmann_factor L s).
Proof.
  intros L s. unfold rboltzmann_factor. apply exp_neg_pos.
Qed.

(* The Id-world boltzmann_prob_pos (L1637), assembled from [mult_positive], [inv_pos_pos], and [exp_neg_pos]. *)
Theorem req_boltzmann_prob_pos :
  forall (L : S -> R) (s : S), real_lt zero (rboltzmann_prob L s).
Proof.
  intros L s. unfold rboltzmann_prob, rboltzmann_factor.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* The Id-world prediction_fluctuation_scale (L1671), assembled from
   [exp_neg_le_decr], [le_mult_compat_weak], [lt_le_iff],
   [req_le_plus_nonneg_r], and [one_pos]. *)
Theorem req_prediction_fluctuation_scale : forall N : R,
  real_le (exp_neg (mult (plus N one) (inv_pos rk_B rk_B_pos)))
     (exp_neg (mult N (inv_pos rk_B rk_B_pos))).
Proof.
  intro N.
  apply exp_neg_le_decr.
  apply (le_mult_compat_weak N (plus N one) (inv_pos rk_B rk_B_pos)).
  - apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - apply (req_le_plus_nonneg_r N one (lt_le_iff _ _ (inl one_pos))).
Qed.

End ReqPropConvCore.

(* ============================================================ *)
(* Part 3: the two ThermodynamicsInstance pieces (Id L2906-3040 dependence face) *)
(* ============================================================ *)
Section ReqThermoInstance.

Variable rMicrostate : Set.
Variable rE_total : R.

(* The Id-world E_B (L2918) with [minus] rewritten to [req_minus]. *)
Definition rE_B (E_A : R) : R := req_minus rE_total E_A.

Variable rtemperature_A : R -> R.
Variable rtemperature_B : R -> R.
Variable rtemperature_A_pos : forall E_A, real_lt zero (rtemperature_A E_A).
Variable rtemperature_B_pos : forall E_A, real_lt zero (rtemperature_B E_A).

(* Definition transcription of the Id-world entropy_gradient (L2984) with [minus] rewritten to [req_minus]. *)
Definition rentropy_gradient (E_A : R) : R :=
  req_minus (inv_pos (rtemperature_A E_A) (rtemperature_A_pos E_A))
            (inv_pos (rtemperature_B (rE_B E_A)) (rtemperature_B_pos (rE_B E_A))).

(* The Id-world CoreClaim3 (L3018) with [minus] rewritten to [req_minus] on the statement face. *)
Definition rCoreClaim3 : Set := forall E_A,
  real_eq (rentropy_gradient E_A)
      (req_minus (inv_pos (rtemperature_A E_A) (rtemperature_A_pos E_A))
                 (inv_pos (rtemperature_B (rE_B E_A)) (rtemperature_B_pos (rE_B E_A)))).

(* The Id-world core_claim3_holds (L3025): reflexivity after definition unfolding. *)
Theorem req_thermo_core_claim3_holds : rCoreClaim3.
Proof.
  unfold rCoreClaim3, rentropy_gradient. intro E_A. apply req_refl.
Qed.

Variable rHamiltonian : rMicrostate -> R.
Variable rbeta : R.
Variable rpartition_function_t : R.
Variable rpartition_positive_t : real_lt zero rpartition_function_t.

(* Definition transcription of the Id-world boltzmann_prob (L3000). *)
Definition rboltzmann_prob_t (x : rMicrostate) : R :=
  mult (inv_pos rpartition_function_t rpartition_positive_t)
       (exp_neg (mult rbeta (rHamiltonian x))).

(* Id CoreClaim5 L3026 *)
Definition rCoreClaim5t : Set := forall x : rMicrostate,
  real_eq (rboltzmann_prob_t x)
      (mult (inv_pos rpartition_function_t rpartition_positive_t)
            (exp_neg (mult rbeta (rHamiltonian x)))).

(* The Id-world core_claim5_holds (L3032): reflexivity after definition unfolding. *)
Theorem req_thermo_core_claim5_holds : rCoreClaim5t.
Proof.
  unfold rCoreClaim5t, rboltzmann_prob_t. intro x. apply req_refl.
Qed.

End ReqThermoInstance.

(* ============================================================ *)
(* Part 4: the remaining three ConvergenceTheorem pieces (Id L13837-14010) *)
(* Statement-level agreement check:                                        *)
(*   req_iterate_step_diff<-13880 req_iterate_step_abs_diff<-13929 *)
(*   [req_gradient_abs_mono] (<-13982) is already proven in UpReqCauchy.v.  *)


(*   the single-point step-difference companion [req_step_diff_point] is   *)
(*   self-contained within this Section).                                  *)
(* ============================================================ *)
Section ReqConvTheorem.

Variable rentropy_gradient : R -> R.
Variable rdynamics : R -> R.
Variable reta : R.
Variable rdynamics_gradient_step : forall x : R,
  real_eq (rdynamics x) (plus x (mult reta (rentropy_gradient x))).
Variable rstrict_concavity : forall x y : R, real_lt x y -> real_lt (rentropy_gradient y) (rentropy_gradient x).
Variable rL : R.
Variable rgradient_lipschitz : forall x y : R,
  real_le (abs (req_minus (rentropy_gradient x) (rentropy_gradient y)))
     (mult rL (abs (req_minus x y))).

(* Single-point step difference (a req-shaped supply; the Id-world
   iterate_step_diff L13880 base-case pattern): x_{n+1} − x_n == η·g(x_n)
   at an arbitrary point x, in req form *)
Lemma req_step_diff_point : forall x : R,
  real_eq (req_minus (rdynamics x) x) (mult reta (rentropy_gradient x)).
Proof.
  intro x. unfold req_minus.
  exact (req_trans _ _ _
    (req_plus_compat (rdynamics x)
                     (plus x (mult reta (rentropy_gradient x)))
                     (opp x) (opp x)
                     (rdynamics_gradient_step x) (req_refl (opp x)))
    (req_minus_plus_cancel_r x (mult reta (rentropy_gradient x)))).
Qed.

(* The Id-world entropy_gradient_strict_mono (L13912): an alias of the [strict_concavity] slot, transported by [exact]. *)
Theorem req_entropy_gradient_strict_mono : forall x y : R,
  real_lt x y -> real_lt (rentropy_gradient y) (rentropy_gradient x).
Proof.
  intros x y Hxy. exact (rstrict_concavity x y Hxy).
Qed.

(* The Id-world gradient_diff_from_zero (L13920): the gradient_lipschitz slot specialized at y := zero. *)
Theorem req_gradient_diff_from_zero : forall x : R,
  real_le (abs (req_minus (rentropy_gradient x) (rentropy_gradient zero)))
     (mult rL (abs (req_minus x zero))).
Proof.
  intro x. exact (rgradient_lipschitz x zero).
Qed.

(* The Id-world gradient_step_recurrence (L13944):
   |g(x_{n+1}) − g(x_n)| ≤ (L·|η|)·|g(x_n)|.  The iterate position reduces at
   the definition level onto [req_step_diff_point] (iterate f (S n) x ≡
   f (iterate f n x)), and the |·| change of face goes through the
   [abs_compat] and [abs_mult] fields (zero cross-module Require). *)
Theorem req_gradient_step_recurrence : forall (E_A : R) (n : nat),
  real_le (abs (req_minus (rentropy_gradient (iterate rdynamics (Datatypes.S n) E_A))
                     (rentropy_gradient (iterate rdynamics n E_A))))
     (mult (mult rL (abs reta)) (abs (rentropy_gradient (iterate rdynamics n E_A)))).
Proof.
  intros E_A n.
  assert (Hdiff : real_eq (req_minus (iterate rdynamics (Datatypes.S n) E_A)
                                 (iterate rdynamics n E_A))
                      (mult reta (rentropy_gradient (iterate rdynamics n E_A))))
    by exact (req_step_diff_point (iterate rdynamics n E_A)).
  assert (Habsd : real_eq (abs (req_minus (iterate rdynamics (Datatypes.S n) E_A)
                                      (iterate rdynamics n E_A)))
                      (mult (abs reta) (abs (rentropy_gradient (iterate rdynamics n E_A)))))
    by exact (req_trans _ _ _
               (req_abs_compat _ _ Hdiff)
               (abs_mult reta (rentropy_gradient (iterate rdynamics n E_A)))).
  apply (le_trans _ (mult rL (mult (abs reta) (abs (rentropy_gradient (iterate rdynamics n E_A))))) _).
  - exact (le_id_r _ _ _
            (req_mult_compat rL rL _ _ (req_refl rL) Habsd)
            (rgradient_lipschitz (iterate rdynamics (Datatypes.S n) E_A)
                                 (iterate rdynamics n E_A))).
  - exact (le_id_r _ _ _
            (mult_assoc rL (abs reta)
               (abs (rentropy_gradient (iterate rdynamics n E_A))))
            (le_refl _)).
Qed.

End ReqConvTheorem.

(* ============================================================ *)
(* Part 5: the single SumExpPositive piece (Id KeyProofs region, L15240-15284) *)
(* Twin-note: this file also proves the LanguageModelInstance twin
   [sum_exp_positive] (Id L1875); the same statement carries the same proof. *)
(* ============================================================ *)
Section ReqSumExpPos.

Variable rToken : Set.
Variable rneg_log_prob : list rToken -> rToken -> R.

(* Definition transcription of the Id-world sum_exp (L15257): the carrier is rebuilt at the definition level. *)
Fixpoint req_sum_exp (prefix : list rToken) (l : list rToken) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (exp_neg (rneg_log_prob prefix w)) (req_sum_exp prefix rest)
  end.

(* The Id-world sum_exp_positive (L15266): induction with an [lt_id_r]
   change of face and [plus_positive]; the premise [Not (Id l nil)] is kept
   as-is in its list-layer slot. *)
Lemma req_sum_exp_positive :
  forall (prefix l : list rToken), Not (Id l nil) -> real_lt zero (req_sum_exp prefix l).
Proof.
  intros prefix l. induction l as [| w rest IH].
  - intros Hnil. contradiction Hnil. apply id_refl.
  - intros _. cbn [req_sum_exp].
    destruct rest as [| w' rest'].
    + exact (lt_id_r _ _ _
               (req_sym _ _ (plus_zero (exp_neg (rneg_log_prob prefix w))))
               (exp_neg_pos (rneg_log_prob prefix w))).
    + apply plus_positive.
      * apply exp_neg_pos.
      * apply IH. intro H. inversion H.
Qed.

End ReqSumExpPos.

(* ============================================================ *)
(* Part 6: the six LanguageModelInstance pieces (Id L1777-2000 dependence  *)
(*         face; the sum_exp_positive twin at L1875 is already proven by   *)
(*         Part 5) *)
(* Signature change: the Id-world loss_of_proposition uses a premise-free  *)
(*   log_inv, while the req form of log_inv carries an [lt zero] premise,  *)
(*   so three positivity slots are added *)
(*   rhas_verb_pos/rsemantics_coherent_pos/rstyle_appropriate_pos  *)
(*   as listed.  The core_claim3 proof body is a purely algebraic chain    *)
(*   (it does not unfold [rtotal_loss]); the slots enter the statement     *)
(*   signature only. *)
(* ============================================================ *)
Section ReqLangModelInstance.

Variable rToken : Set.
Variable rvocab : list rToken.
Variable rvocab_nonempty : Not (Id rvocab nil).
Variable rneg_log_prob : list rToken -> rToken -> R.
Variable rhas_verb : list rToken -> R.
Variable rsemantics_coherent : list rToken -> R.
Variable rstyle_appropriate : list rToken -> R.
Variable ralpha_grammar : R.
Variable ralpha_semantics : R.
Variable ralpha_style : R.
Variable rprop_pos : forall (P : list rToken -> R) (s : list rToken), real_lt zero (P s).
Variable rhas_verb_pos : forall s : list rToken, real_lt zero (rhas_verb s).
Variable rsemantics_coherent_pos : forall s : list rToken, real_lt zero (rsemantics_coherent s).
Variable rstyle_appropriate_pos : forall s : list rToken, real_lt zero (rstyle_appropriate s).

(* The Id-world loss_of_proposition (L1807) with the log premise made explicit. *)
Definition rloss_of_prop (c : list rToken -> R) (s : list rToken)
    (Hc : real_lt zero (c s)) : R := log_inv (c s) Hc.

(* Definition transcriptions of the Id-world sequence_loss_prefix (L1796) and sequence_loss (L1801). *)
Fixpoint rsequence_loss_prefix (prefix : list rToken) (s : list rToken) : R :=
  match s with
  | nil => zero
  | w :: rest => plus (rneg_log_prob prefix w) (rsequence_loss_prefix (prefix ++ [w]) rest)
  end.

Definition rsequence_loss (s : list rToken) : R := rsequence_loss_prefix nil s.

(* Definition transcription of the Id-world total_loss (L1818) with the positivity premises made explicit. *)
Definition rtotal_loss (s : list rToken) : R :=
  plus (rsequence_loss s)
       (plus (mult ralpha_grammar (rloss_of_prop rhas_verb s (rhas_verb_pos s)))
             (plus (mult ralpha_semantics
                         (rloss_of_prop rsemantics_coherent s (rsemantics_coherent_pos s)))
                   (mult ralpha_style
                         (rloss_of_prop rstyle_appropriate s (rstyle_appropriate_pos s))))).

(* Definition transcription of the Id-world force (L1822) with [minus] rewritten to [req_minus]. *)
Definition rforce (s : list rToken) (w : rToken) : R :=
  opp (req_minus (rtotal_loss (s ++ [w])) (rtotal_loss s)).

(* Id LangProp L1803 / partition_function L1868 / partition_positive L1889 /
   normalized_prob (L1975) as definitions; the sum_exp position is the
   closed name [req_sum_exp] of Part 5. *)
Definition rLangProp : Set := list rToken -> R.

Definition rpartition_function (prefix : list rToken) : R :=
  req_sum_exp rToken rneg_log_prob prefix rvocab.

Definition rpartition_positive (prefix : list rToken) :
    real_lt zero (rpartition_function prefix) :=
  req_sum_exp_positive rToken rneg_log_prob prefix rvocab rvocab_nonempty.

Definition rnormalized_prob (prefix : list rToken) (w : rToken) : R :=
  mult (exp_neg (rneg_log_prob prefix w))
       (inv_pos (rpartition_function prefix) (rpartition_positive prefix)).

(* The Id-world exp_neg_positive (L1872): a one-line transport of the [exp_neg_pos] field. *)
Lemma req_exp_neg_positive : forall x : R, real_lt zero (exp_neg x).
Proof. intro x. apply exp_neg_pos. Qed.

(* The Id-world core_claim1_holds (L1931): same-shape to the [prop_pos] slot, transported by [exact]. *)
Theorem req_core_claim1_lm_holds :
  forall (P : rLangProp) (s : list rToken), real_lt zero (P s).
Proof. exact rprop_pos. Qed.

(* The Id-world core_claim3_holds (L1938): a three-step chain of
   [req_opp_plus], [req_double_neg], and [plus_comm]; after [minus] is
   rewritten to [req_minus] and unfolded, the steps match directly. *)
Theorem req_core_claim3_lm_holds : forall (s : list rToken) (w : rToken),
  real_eq (rforce s w) (req_minus (rtotal_loss s) (rtotal_loss (s ++ [w]))).
Proof.
  intros s w. unfold rforce, req_minus.
  assert (Hopp : real_eq (opp (plus (rtotal_loss (s ++ [w])) (opp (rtotal_loss s))))
                     (plus (opp (rtotal_loss (s ++ [w]))) (opp (opp (rtotal_loss s))))).
  { exact (req_opp_plus (rtotal_loss (s ++ [w])) (opp (rtotal_loss s))). }
  assert (Hneg : real_eq (plus (opp (rtotal_loss (s ++ [w]))) (opp (opp (rtotal_loss s))))
                     (plus (opp (rtotal_loss (s ++ [w]))) (rtotal_loss s))).
  { exact (req_plus_compat (opp (rtotal_loss (s ++ [w]))) (opp (rtotal_loss (s ++ [w])))
                           (opp (opp (rtotal_loss s))) (rtotal_loss s)
                           (req_refl (opp (rtotal_loss (s ++ [w]))))
                           (req_double_neg (rtotal_loss s))). }
  exact (req_trans _ _ _ Hopp
    (req_trans _ _ _ Hneg
      (plus_comm (opp (rtotal_loss (s ++ [w]))) (rtotal_loss s)))).
Qed.

(* The Id-world core_claim5_holds (L1949): reflexivity after definition unfolding. *)
Theorem req_core_claim5_lm_holds : forall (prefix : list rToken) (w : rToken),
  real_eq (rnormalized_prob prefix w)
      (mult (exp_neg (rneg_log_prob prefix w))
            (inv_pos (rpartition_function prefix) (rpartition_positive prefix))).
Proof.
  intros prefix w. unfold rnormalized_prob. apply req_refl.
Qed.

(* The Id-world normalized_prob_pos (L1981), assembled from [mult_positive], [exp_neg_pos], and [inv_pos_pos]. *)
Theorem req_normalized_prob_pos : forall (prefix : list rToken) (w : rToken),
  real_lt zero (rnormalized_prob prefix w).
Proof.
  intros prefix w. unfold rnormalized_prob. apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* The Id-world prediction_boltzmann_sampling_holds (L1993): a named piece with the same content as core_claim5. *)
Theorem req_prediction_boltzmann_sampling_holds :
  forall (prefix : list rToken) (w : rToken),
  real_eq (rnormalized_prob prefix w)
      (mult (exp_neg (rneg_log_prob prefix w))
            (inv_pos (rpartition_function prefix) (rpartition_positive prefix))).
Proof.
  intros prefix w. apply req_refl.
Qed.

End ReqLangModelInstance.

(* ============================================================ *)
(* Part 7: the remaining four GRPONoDup pieces on the R side (Id Module UpGRPO219, L113533-113860) *)
(* The count function ([count_g]/[removeT_g]/[nodup_g]/[not_InT]/[InT]     *)
(* family) lives at the nat/list layer of the Id world and is reused       *)
(* across the interface as-is (the conclusions keep their @[Id nat] face   *)
(* with zero migration); the R-valued summation position is                *)
(* [reqd_list_sum_g] of UpReqDist (its GRPO Section is the FEP block at    *)
(* L23793, same name but a different body than this block, hence no clash). *)
(* ============================================================ *)
Section ReqGrpoMisc.

Variable rGroup : Set.
Variable rgroup_enum : list rGroup.
Variable rgrp_eq_dec : forall i j : rGroup, Or (Id i j) (Not (Id i j)).
Variable rnd_g : UpGRPO219.nodup_g rGroup rgroup_enum.

Let rG : R := reqd_of_nat (length rgroup_enum).
Variable rG_pos : real_lt zero rG.

(* ---- positivity supply group (signature-preserving; supplied externally ----
   at instantiation time).  [rG_pos] is kept as-is as an interface slot: the
   enumeration may be empty, in which case [rG] collapses to the zero element
   and strict positivity is unprovable (the counter-model is the empty
   enumeration).  The three pieces below derive positivity unconditionally
   under the non-empty condition, for direct use at instantiation time; the
   out-of-Section signature is unchanged.  The in-tree counterpart anchor is
   [reqd_of_nat_pos] (UpReqMpDomain, the S k form); this file carries its own
   same-shape proof instead, keeping the dependence face unchanged (no
   UpReqMpDomain import). *)
Lemma rgrp_of_nat_S_pos : forall k : nat, real_lt zero (reqd_of_nat (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - (* Base: [reqd_of_nat 1] is [plus one zero] at the definition level; after
       the change of face back to [one], [one_pos] closes it. *)
    apply (lt_id_r zero one (reqd_of_nat (Datatypes.S O))).
    + apply (req_trans one (plus one zero) (reqd_of_nat (Datatypes.S O))).
      * apply (req_sym (plus one zero) one). apply plus_zero.
      * apply req_refl.
    + exact one_pos.
  - (* Step: [reqd_of_nat (S (S k))] is [1 + reqd_of_nat (S k)] at the
       definition level; positivity of both summands is preserved by the
       addition. *)
    apply (lt_id_r zero (plus one (reqd_of_nat (Datatypes.S k)))
                      (reqd_of_nat (Datatypes.S (Datatypes.S k)))).
    + apply req_refl.
    + apply plus_positive. exact one_pos. exact IH.
Qed.

(* Positivity from non-emptiness: an [InT] witness gives that the length has successor form (a [sigT] witness exit). *)
Theorem rgrp_G_pos_of_nonempty :
  forall l : list rGroup,
    sigT (fun t : rGroup => InT t l) -> real_lt zero (reqd_of_nat (length l)).
Proof.
  intros l. destruct l as [| x rest].
  - (* Empty list: no [InT] witness can be built; [inversion] dismisses it. *)
    intros [t Ht]. inversion Ht.
  - (* Non-empty: the length has successor form, and positivity follows
       directly from [rgrp_of_nat_S_pos]. *)
    intros _. exact (rgrp_of_nat_S_pos (length rest)).
Qed.

(* Instantiation-time supply for the [rG_pos] slot of this Section:
   unconditional once the enumeration is non-empty. *)
Theorem rgrp_G_pos_of_nonempty_enum :
  sigT (fun t : rGroup => InT t rgroup_enum) -> real_lt zero rG.
Proof.
  intro Hne. exact (rgrp_G_pos_of_nonempty rgroup_enum Hne).
Qed.

(* The Id-world UpGRPO219.grpo_count_one (L113775): the conclusion keeps its
   @[Id nat] face and the count function is reused across the interface (a
   one-line assembly). *)
Theorem req_grpo_count_one : forall (l : list rGroup) (Hnd : UpGRPO219.nodup_g rGroup l)
    (j : rGroup), InT j l -> Id (UpGRPO219.count_g rGroup rgrp_eq_dec j l) (Datatypes.S O).
Proof.
  intros l Hnd j Hin. exact (UpGRPO219.grpo_count_one rGroup rgrp_eq_dec l Hnd j Hin).
Qed.

(* The Id-world list_sum_g_zero_fn (L113609): induction with a [plus_zero]
   change of face; the [InT] premises are kept as-is. *)
Lemma req_list_sum_g_zero_fn : forall (f : rGroup -> R) (l : list rGroup),
  (forall i : rGroup, InT i l -> real_eq (f i) zero) ->
  real_eq (reqd_list_sum_g rGroup f l) zero.
Proof.
  intros f l. induction l as [| x rest IH]; intro H.
  - apply req_refl.
  - cbn [reqd_list_sum_g].
    assert (IHrest : real_eq (reqd_list_sum_g rGroup f rest) zero).
    { apply IH. intro i. intro Hin. exact (H i (InT_next i x rest Hin)). }
    apply (req_trans _ (plus zero (reqd_list_sum_g rGroup f rest)) _).
    + apply (req_plus_compat (f x) zero (reqd_list_sum_g rGroup f rest)
                             (reqd_list_sum_g rGroup f rest)
                             (H x (InT_here x rest)) (req_refl _)).
    + exact (req_trans _ _ _
               (plus_comm zero (reqd_list_sum_g rGroup f rest))
               (req_trans _ _ _
                 (plus_zero (reqd_list_sum_g rGroup f rest))
                 IHrest)).
Qed.

(* The req-shaped supply for the Id-world split_count_one_id (L113720):
   count == 1 gives Σ l f == f j + Σ (removeT j l) f; the Id-level count fact
   is transported by destructuring substitution, with zero rewrite tactics. *)
Lemma req_split_count_one : forall (f : rGroup -> R) (j : rGroup) (l : list rGroup),
  Id (UpGRPO219.count_g rGroup rgrp_eq_dec j l) (Datatypes.S O) ->
  real_eq (reqd_list_sum_g rGroup f l)
      (plus (f j) (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j l))).
Proof.
  intros f j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [UpGRPO219.count_g] in Hc. cbn [UpGRPO219.removeT_g reqd_list_sum_g].
    destruct (rgrp_eq_dec x j) as [Hxj | Hnxj].
    + assert (Hc0 : Id (UpGRPO219.count_g rGroup rgrp_eq_dec j rest) O).
        exact (id_cong Nat.pred Hc).
      exact (req_plus_compat (f x) (f j)
               (reqd_list_sum_g rGroup f rest)
               (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))
               (match Hxj in (Id _ y) return (real_eq (f x) (f y)) with
                | id_refl => req_refl _ end)
               (match id_sym (UpGRPO219.count_zero_remove_id rGroup rgrp_eq_dec j rest Hc0)
                in (Id _ y) return
                  (real_eq (reqd_list_sum_g rGroup f rest)
                       (reqd_list_sum_g rGroup f y))
                with id_refl => req_refl _ end)).
    + destruct (rgrp_eq_dec x j) as [Hyt2 | Hnyt2].
      * exact (match Hnxj Hyt2 with end).
      * exact (req_trans _ _ _
          (req_plus_compat (f x) (f x)
             (reqd_list_sum_g rGroup f rest)
             (plus (f j)
                (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest)))
             (req_refl (f x)) (IH Hc))
          (req_trans _ _ _
            (plus_assoc (f x) (f j)
               (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest)))
            (req_trans _ _ _
              (req_plus_compat (plus (f x) (f j)) (plus (f j) (f x))
                 (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))
                 (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))
                 (plus_comm (f x) (f j)) (req_refl _))
              (req_sym _ _ (plus_assoc (f j) (f x)
                 (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))))))).
Qed.

(* The Id-world grpo_indicator_sum_one (L113793): the [grp_eq_dec] decisions
   are kept as-is and assembled in req form. *)
Theorem req_grpo_indicator_sum_one : forall j : rGroup,
  InT j rgroup_enum ->
  real_eq (reqd_list_sum_g rGroup
         (fun i : rGroup => match rgrp_eq_dec i j with
                            | inl _ => one
                            | inr _ => zero
                            end)
         rgroup_enum)
      one.
Proof.
  intro j. intro Hin.
  assert (Hc1 : Id (UpGRPO219.count_g rGroup rgrp_eq_dec j rgroup_enum) (Datatypes.S O))
    by exact (UpGRPO219.grpo_count_one rGroup rgrp_eq_dec rgroup_enum rnd_g j Hin).
  assert (Hfj : real_eq (match rgrp_eq_dec j j with
                     | inl _ => one
                     | inr _ => zero
                     end) one).
  { destruct (rgrp_eq_dec j j) as [Hjj | Hjj].
    - apply req_refl.
    - exact (match Hjj (id_refl : Id j j) with end). }
  assert (Hrest : real_eq (reqd_list_sum_g rGroup
                         (fun i : rGroup => match rgrp_eq_dec i j with
                                            | inl _ => one
                                            | inr _ => zero
                                            end)
                         (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rgroup_enum)) zero).
  { apply req_list_sum_g_zero_fn.
    intro i. intro HinR.
    destruct (rgrp_eq_dec i j) as [Hxj | Hnxj].
    - exact (match (UpGRPO219.remove_notin_aux rGroup rgrp_eq_dec j i rgroup_enum HinR) Hxj with end).
    - apply req_refl. }
  exact (req_trans _ _ _
    (req_split_count_one _ j rgroup_enum Hc1)
    (req_trans _ _ _
      (req_plus_compat _ _ _ _ Hfj Hrest)
      (plus_zero one))).
Qed.

(* The Id-world grpo_uniform_mass (L113832): [req_list_sum_g_linear] plus
   assembly; the G position is [reqd_of_nat (length rgroup_enum)] and the
   G_pos slot is same-shape. *)
Theorem req_grpo_uniform_mass : forall j : rGroup,
  InT j rgroup_enum ->
  real_eq (reqd_list_sum_g rGroup
         (fun i : rGroup => mult (inv_pos rG rG_pos)
            (match rgrp_eq_dec i j with
             | inl _ => one
             | inr _ => zero
             end))
         rgroup_enum)
      (inv_pos rG rG_pos).
Proof.
  intro j. intro Hin.
  apply (req_trans _ (mult (inv_pos rG rG_pos)
         (reqd_list_sum_g rGroup
            (fun i : rGroup => match rgrp_eq_dec i j with
                               | inl _ => one
                               | inr _ => zero
                               end)
            rgroup_enum)) _).
  - apply req_list_sum_g_linear.
  - exact (req_trans _ _ _
      (req_mult_compat (inv_pos rG rG_pos) (inv_pos rG rG_pos) _ one
         (req_refl (inv_pos rG rG_pos)) (req_grpo_indicator_sum_one j Hin))
      (mult_one (inv_pos rG rG_pos))).
Qed.

End ReqGrpoMisc.

(* ============================================================ *)
(* Part G: the eleven differentiable-lemma algebra pieces (Id L25673-26304) *)
(* statement positions with no record dependence rewrite [minus] to        *)
(* [req_minus]; log-dependent positions get explicit premises with         *)
(* same-position slots. *)

(* ============================================================ *)
Section ReqDiffAlgebra.

(* ---- Self-contained helper 1: the four-term square expansion (a req-shaped
   supply; in the Id world destruct is free) ---- *)
Lemma req_square_expand4 : forall a h : R,
  real_eq (mult (plus a h) (plus a h))
      (plus (mult a a) (plus (mult a h) (plus (mult h a) (mult h h)))).
Proof.
  intros a h.
  apply (req_trans _ (plus (mult a (plus a h)) (mult h (plus a h))) _).
  - exact (req_mult_plus_distr_r a h (plus a h)).
  - apply (req_trans _ (plus (plus (mult a a) (mult a h))
                             (plus (mult h a) (mult h h))) _).
    + apply (req_plus_compat _ _ _ _ (distrib a a h) (distrib h a h)).
    + exact (req_sym _ _ (plus_assoc (mult a a) (mult a h)
                           (plus (mult h a) (mult h h)))).
Qed.

(* ---- Self-contained helper 2: head cancellation,
   [plus (plus W T) (opp W)] == T ---- *)
Lemma req_plus_cancel_head : forall W T : R,
  real_eq (plus (plus W T) (opp W)) T.
Proof.
  intros W T.
  apply (req_trans _ (plus (opp W) (plus W T)) _).
  - exact (plus_comm (plus W T) (opp W)).
  - apply (req_trans _ (plus (plus (opp W) W) T) _).
    + exact (plus_assoc (opp W) W T).
    + apply (req_trans _ (plus zero T) _).
      * apply (req_plus_compat (plus (opp W) W) zero T T
                               (req_trans _ _ _ (plus_comm (opp W) W) (plus_opp W))
                               (req_refl T)).
      * exact (req_trans _ _ _ (plus_comm zero T) (plus_zero T)).
Qed.

(* The Id-world compose_diff_decomp (L25673): the error-decomposition core
   (pure ring; [req_minus] unfolding plus a req algebra chain). *)
Lemma req_compose_diff_decomp : forall (A B C D G g0 h : R),
  real_eq (req_minus A (plus B (mult (mult C D) h)))
      (plus (req_minus A (plus B (mult C (req_minus G g0))))
            (mult C (req_minus (req_minus G g0) (mult D h)))).
Proof.
  intros A B C D G g0 h.
  assert (Hcancel : forall Y : R, real_eq (plus (opp (plus B Y)) Y) (opp B)).
  {
    intro Y.
    apply (req_trans _ (plus (plus (opp B) (opp Y)) Y) _).
    - apply (req_plus_compat (opp (plus B Y)) (plus (opp B) (opp Y)) Y Y
                             (req_opp_plus B Y) (req_refl Y)).
    - apply (req_trans _ (plus (opp B) (plus (opp Y) Y)) _).
      + apply (req_sym _ _ (plus_assoc (opp B) (opp Y) Y)).
      + apply (req_trans _ (plus (opp B) zero) _).
        * apply (req_plus_compat (opp B) (opp B) (plus (opp Y) Y) zero
                                 (req_refl (opp B))).
          exact (req_trans _ _ _ (plus_comm (opp Y) Y) (plus_opp Y)).
        * apply plus_zero.
  }
  assert (Hre : forall Y Y2 : R,
    real_eq (plus (plus A (opp (plus B Y))) (plus Y (opp Y2)))
        (plus A (opp (plus B Y2)))).
  {
    intros Y Y2.
    apply (req_trans _ (plus A (plus (plus (opp (plus B Y)) Y) (opp Y2))) _).
    - exact (req_trans _ _ _
              (req_sym _ _ (plus_assoc A (opp (plus B Y)) (plus Y (opp Y2))))
              (req_plus_compat A A _ _
                (req_refl A) (plus_assoc (opp (plus B Y)) Y (opp Y2)))).
    - apply (req_trans _ (plus A (plus (opp B) (opp Y2))) _).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_plus_compat _ _ _ _ (Hcancel Y) (req_refl (opp Y2))).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_sym _ _ (req_opp_plus B Y2)).
  }
  unfold req_minus.
  apply (req_trans _ (plus A (opp (plus B (mult C (mult D h))))) _).
  - exact (req_plus_compat A A _ _ (req_refl A)
            (req_opp_compat (plus B (mult (mult C D) h)) (plus B (mult C (mult D h)))
              (req_plus_compat B B (mult (mult C D) h) (mult C (mult D h))
                (req_refl B)
                (req_sym (mult C (mult D h)) (mult (mult C D) h) (mult_assoc C D h))))).
  - apply req_sym.
    exact (req_trans _ _ _
      (req_plus_compat (plus A (opp (plus B (mult C (req_minus G g0)))))
                       (plus A (opp (plus B (mult C (req_minus G g0)))))
                       (mult C (plus (req_minus G g0) (opp (mult D h))))
                       (plus (mult C (req_minus G g0)) (opp (mult C (mult D h))))
                       (req_refl _)
                       (req_trans _ _ _
                         (distrib C (req_minus G g0) (opp (mult D h)))
                         (req_plus_compat (mult C (req_minus G g0))
                                          (mult C (req_minus G g0))
                                          (mult C (opp (mult D h)))
                                          (opp (mult C (mult D h)))
                                          (req_refl _)
                                          (req_opp_mult_l C (mult D h)))))
      (Hre (mult C (req_minus G g0)) (mult C (mult D h)))).
Qed.

(* The Id-world half_le_one (L25729): inv_2 ≤ 1 (the two_pos slot is
   [req_two_pos] of UpReqAlgebra). *)
Lemma req_half_le_one : real_le (inv_pos (plus one one) req_two_pos) one.
Proof.
  exact (le_id_l _ _ _
    (req_sym _ _ (mult_one (inv_pos (plus one one) req_two_pos)))
    (le_id_r _ _ _
      (req_trans _ _ _
        (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
        (inv_pos_correct (plus one one) req_two_pos))
      (req_le_mult_compat_r (inv_pos (plus one one) req_two_pos) one (plus one one)
        (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) req_two_pos)))
        (req_le_plus_nonneg_r one one (lt_le_iff _ _ (inl one_pos)))))).
Qed.

(* The Id-world half_le_self (L25748): eps/2 ≤ eps for a non-negative coefficient. *)
Lemma req_half_le_self : forall a : R, real_le zero a ->
  real_le (mult (inv_pos (plus one one) req_two_pos) a) a.
Proof.
  intros a Ha.
  apply (le_trans _ (mult one a) _).
  - exact (le_mult_compat_weak _ _ _ Ha req_half_le_one).
  - exact (le_id_l _ _ _ (req_trans _ _ _ (mult_comm one a) (mult_one a)) (le_refl a)).
Qed.

(* The Id-world minus_plus_zero_r (L26076): (a+b) − c = (a−c) + b *)
Lemma req_minus_plus_zero_r : forall a b c : R,
  real_eq (req_minus (plus a b) c) (plus (req_minus a c) b).
Proof.
  intros a b c. unfold req_minus.
  exact (req_trans _ _ _
    (req_sym _ _ (plus_assoc a b (opp c)))
    (req_trans _ _ _
      (req_plus_compat a a (plus b (opp c)) (plus (opp c) b)
                       (req_refl a) (plus_comm b (opp c)))
      (plus_assoc a (opp c) b))).
Qed.

(* The Id-world square_diff_expand (L26092):
   (x+h−t)² − ((x−t)² + 2(x−t)·h) = h².  Structure: change of face by [Hv],
   the four-term square expansion, commuting h·u, gathering the doubled
   summand, [plus_assoc], then head cancellation ([req_plus_cancel_head]). *)
Lemma req_square_diff_expand : forall x target h : R,
  real_eq (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
            (plus (mult (req_minus x target) (req_minus x target))
                  (mult (mult (plus one one) (req_minus x target)) h)))
     (mult h h).
Proof.
  intros x target h.
  assert (Hv : real_eq (req_minus (plus x h) target) (plus (req_minus x target) h))
    by exact (req_minus_plus_zero_r x h target).
  assert (Htwo : real_eq (plus (mult (req_minus x target) h)
                           (mult (req_minus x target) h))
                     (mult (mult (plus one one) (req_minus x target)) h)).
  {
    apply (req_trans _ (plus (mult one (mult (req_minus x target) h))
                             (mult one (mult (req_minus x target) h))) _).
    - apply (req_plus_compat _ _ _ _
              (req_sym (mult one (mult (req_minus x target) h)) (mult (req_minus x target) h)
                (req_mult_one_l (mult (req_minus x target) h)))
              (req_sym (mult one (mult (req_minus x target) h)) (mult (req_minus x target) h)
                (req_mult_one_l (mult (req_minus x target) h)))).
    - apply (req_trans _ (mult (plus one one) (mult (req_minus x target) h)) _).
      + exact (req_sym (mult (plus one one) (mult (req_minus x target) h))
                      (plus (mult one (mult (req_minus x target) h))
                            (mult one (mult (req_minus x target) h)))
                      (req_mult_plus_distr_r one one (mult (req_minus x target) h))).
      + exact (mult_assoc (plus one one) (req_minus x target) h).
  }
  assert (Hs1 : real_eq (plus (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (req_trans _ _ _
                     (req_mult_compat (req_minus (plus x h) target) (plus (req_minus x target) h) (req_minus (plus x h) target) (plus (req_minus x target) h) Hv Hv)
                     (req_square_expand4 (req_minus x target) h))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  assert (Hx2 : real_eq (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h))))).
  { exact (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_plus_compat (mult (req_minus x target) h) (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)) (plus (mult (req_minus x target) h) (mult h h))
                           (req_refl (mult (req_minus x target) h))
                           (req_plus_compat (mult h (req_minus x target)) (mult (req_minus x target) h) (mult h h) (mult h h)
                           (mult_comm h (req_minus x target))
                           (req_refl (mult h h))))). }
  assert (Hs2 : real_eq (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_plus_compat (mult (req_minus x target) h) (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)) (plus (mult (req_minus x target) h) (mult h h))
                           (req_refl (mult (req_minus x target) h))
                           (req_plus_compat (mult h (req_minus x target)) (mult (req_minus x target) h) (mult h h) (mult h h)
                           (mult_comm h (req_minus x target))
                           (req_refl (mult h h)))))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  assert (Hx3 : real_eq (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h)))).
  { exact (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h))) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_trans _ _ _
                     (plus_assoc (mult (req_minus x target) h) (mult (req_minus x target) h) (mult h h))
                     (req_plus_compat (plus (mult (req_minus x target) h) (mult (req_minus x target) h)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h) (mult h h)
                           Htwo
                           (req_refl (mult h h))))). }
  assert (Hs3 : real_eq (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h))) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_trans _ _ _
                     (plus_assoc (mult (req_minus x target) h) (mult (req_minus x target) h) (mult h h))
                     (req_plus_compat (plus (mult (req_minus x target) h) (mult (req_minus x target) h)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h) (mult h h)
                           Htwo
                           (req_refl (mult h h)))))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  assert (Hs4 : real_eq (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (plus_assoc (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  exact (req_trans _ _ _ Hs1 (req_trans _ _ _ Hs2 (req_trans _ _ _ Hs3 (req_trans _ _ _ Hs4 (req_plus_cancel_head (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)))))).
Qed.

Lemma req_dpo_logit_denom_pos : forall x : R, real_lt zero (plus one (exp_neg x)).
Proof.
  intro x. apply plus_positive.
  - exact one_pos.
  - apply exp_neg_pos.
Qed.

(* Definition transcription of sigmoid (the Id-world dpo_sigmoid, L26255). *)
Definition req_dpo_sigmoid (x : R) : R :=
  inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x).

(* The Id-world dpo_loss_diff_decomp (L26247): the difference equals the
   log of the quotient ([log_div] in reverse).  Same-position slot: the
   setoid interface has no log_div field, so the abstract level keeps the
   interface obligation in place (it enters the closure signature at Section
   end and is not an axiom); instantiation-time supply anchors are
   [log_req_compat_real] and the single-premise bridge [log_req_compat],
   both of UpReqU2, usable directly. *)
Variable req_log_compat_slot :
  forall (x y : R) (Hx : real_lt zero x) (Hy : real_lt zero y), real_eq x y -> real_eq (log x Hx) (log y Hy).

Theorem req_dpo_loss_diff_decomp : forall x h : R,
  real_eq (req_minus (log (plus one (exp_neg (plus x h))) (req_dpo_logit_denom_pos (plus x h)))
                 (log (plus one (exp_neg x)) (req_dpo_logit_denom_pos x)))
     (log (mult (plus one (exp_neg (plus x h)))
                (inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x)))
          (mult_positive (plus one (exp_neg (plus x h)))
                         (inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x))
                         (req_dpo_logit_denom_pos (plus x h))
                         (inv_pos_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x)))).
Proof.
  intros x h. apply req_sym.
  exact (req_log_div req_log_compat_slot
          (plus one (exp_neg (plus x h))) (plus one (exp_neg x))
          (req_dpo_logit_denom_pos (plus x h)) (req_dpo_logit_denom_pos x)).
Qed.

(* Id dpo_sigmoid_pos L26263 *)
Lemma req_dpo_sigmoid_pos : forall x : R, real_lt zero (req_dpo_sigmoid x).
Proof.
  intro x. unfold req_dpo_sigmoid. apply inv_pos_pos.
Qed.

(* The Id-world dpo_sigmoid_identity (L26269): σ(x)·(1+e^{-x}) = 1 *)
Theorem req_dpo_sigmoid_identity : forall x : R,
  real_eq (mult (req_dpo_sigmoid x) (plus one (exp_neg x))) one.
Proof.
  intro x. unfold req_dpo_sigmoid.
  exact (req_trans _ _ _
    (mult_comm (inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x))
               (plus one (exp_neg x)))
    (inv_pos_correct (plus one (exp_neg x)) (req_dpo_logit_denom_pos x))).
Qed.

(* The Id-world dpo_sigmoid_complement (L26280): σ + e^{-x}·σ = 1 *)
Theorem req_dpo_sigmoid_complement : forall x : R,
  real_eq (plus (req_dpo_sigmoid x) (mult (exp_neg x) (req_dpo_sigmoid x))) one.
Proof.
  intro x.
  assert (Hswap : real_eq (plus (mult (req_dpo_sigmoid x) one)
                          (mult (req_dpo_sigmoid x) (exp_neg x)))
                      (plus (req_dpo_sigmoid x) (mult (exp_neg x) (req_dpo_sigmoid x))))
    by exact (req_plus_compat _ _ _ _ (mult_one (req_dpo_sigmoid x))
                            (mult_comm (req_dpo_sigmoid x) (exp_neg x))).
  exact (req_trans _ _ _
    (req_sym _ _ Hswap)
    (req_trans _ _ _
      (req_sym _ _ (distrib (req_dpo_sigmoid x) one (exp_neg x)))
      (req_dpo_sigmoid_identity x))).
Qed.

(* The Id-world dpo_gradient_alt (L26298): σ − 1 = −e^{-x}·σ *)
Theorem req_dpo_gradient_alt : forall x : R,
  real_eq (req_minus (req_dpo_sigmoid x) one)
     (opp (mult (exp_neg x) (req_dpo_sigmoid x))).
Proof.
  intro x.
  assert (Hc : real_eq (plus (req_dpo_sigmoid x) (mult (exp_neg x) (req_dpo_sigmoid x))) one)
    by exact (req_dpo_sigmoid_complement x).
  assert (Hcancel : real_eq (plus (req_dpo_sigmoid x) (req_minus one (req_dpo_sigmoid x))) one)
    by exact (req_minus_plus_cancel (req_dpo_sigmoid x) one).
  assert (Hratio : real_eq (mult (exp_neg x) (req_dpo_sigmoid x))
                       (req_minus one (req_dpo_sigmoid x)))
    by exact (req_plus_cancel_l _ _ _ (req_trans _ _ _ Hc (req_sym _ _ Hcancel))).
  assert (Hreduce : real_eq (opp (req_minus one (req_dpo_sigmoid x)))
                        (req_minus (req_dpo_sigmoid x) one)).
  {
    unfold req_minus.
    exact (req_trans _ _ _
      (req_opp_plus one (opp (req_dpo_sigmoid x)))
      (req_trans _ _ _
        (plus_comm (opp one) (opp (opp (req_dpo_sigmoid x))))
        (req_plus_compat (opp (opp (req_dpo_sigmoid x))) (req_dpo_sigmoid x)
                         (opp one) (opp one)
                         (req_double_neg (req_dpo_sigmoid x)) (req_refl (opp one))))).
  }
  exact (req_sym _ _ (req_trans _ _ _ (req_opp_compat _ _ Hratio) Hreduce)).
Qed.

End ReqDiffAlgebra.

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
Import RealInterfaceEnhancedMod.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part 8: the two HilbertTheorems pieces (Id L1281-1400 dependence face) *)
(* ============================================================ *)
Section ReqHilbertTheorems.
Context {SS : reqStateSpace} {HS : reqHilbertSpace SS}.

(* Existence of the orthogonal residual (the Id-world
   orthogonal_decomposition_exists, L1306): a [sigT] witness with
   w := v − proj u v; ⟨w,u⟩=0 by the sym transport of the [proj_orthogonal]
   field, and v = proj u v + w by the vector Id algebra chain. *)
Theorem req_orthogonal_decomposition_exists :
  forall u v : @rSS SS,
    sigT (fun w : @rSS SS =>
      And (real_eq(rinner u w) (zero))
          (Id v (@rsplus SS (rproj u v) w))).
Proof.
  intros u v.
  exists (@rsplus SS v (@rsopp SS (rproj u v))).
  split.
  - exact (req_trans _ _ _
            (req_sym _ _ (rinner_sym (rsplus v (rsopp (rproj u v))) u))
            (rproj_orthogonal u v)).
  - (* v = proj u v + (v − proj u v): splus algebra (a vector Id chain). *)
    assert (Hopp : Id (@rsplus SS (rproj u v)
                                  (@rsplus SS v (@rsopp SS (rproj u v))))
                      (@rsplus SS (rproj u v)
                                  (@rsplus SS (@rsopp SS (rproj u v)) v)))
      by exact (id_cong (fun x => @rsplus SS (rproj u v) x)
                        (rsplus_comm v (@rsopp SS (rproj u v)))).
    assert (Hassoc : Id (@rsplus SS (rproj u v)
                                    (@rsplus SS (@rsopp SS (rproj u v)) v))
                        (@rsplus SS (@rsplus SS (rproj u v)
                                                     (@rsopp SS (rproj u v))) v))
      by exact (rsplus_assoc (rproj u v) (@rsopp SS (rproj u v)) v).
    assert (Hinv : Id (@rsplus SS (rproj u v) (@rsopp SS (rproj u v)))
                      (@rszero SS))
      by exact (rsplus_opp (rproj u v)).
    assert (Hzero : Id (@rsplus SS (@rszero SS) v) v)
      by exact (id_trans (rsplus_comm (@rszero SS) v) (rsplus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc
              (id_trans (id_cong (fun x => @rsplus SS x v) Hinv) Hzero)))).
Qed.

(* Uniqueness of the orthogonal decomposition (the Id-world
   orthogonal_decomposition_unique, L1344): the geometric determinacy of the
   projection, by vector Id algebra (folding a left-added sopp p). *)
Theorem req_orthogonal_decomposition_unique :
  forall (u v w1 w2 : @rSS SS),
    real_eq(rinner w1 u) (zero) ->
    Id v (@rsplus SS (rproj u v) w1) ->
    real_eq(rinner w2 u) (zero) ->
    Id v (@rsplus SS (rproj u v) w2) ->
    Id w1 w2.
Proof.
  intros u v w1 w2 _ Hv1 _ Hv2.
  assert (Heq : Id (@rsplus SS (rproj u v) w1) (@rsplus SS (rproj u v) w2))
    by exact (id_trans (id_sym Hv1) Hv2).
  assert (Hc : Id (@rsplus SS (@rsopp SS (rproj u v))
                                   (@rsplus SS (rproj u v) w1))
                  (@rsplus SS (@rsopp SS (rproj u v))
                                   (@rsplus SS (rproj u v) w2)))
    by exact (id_cong (fun x => @rsplus SS (@rsopp SS (rproj u v)) x) Heq).
  assert (Hl1 : Id (@rsplus SS (@rsopp SS (rproj u v))
                                   (@rsplus SS (rproj u v) w1)) w1).
  {
    assert (H1 : Id (@rsplus SS (@rsopp SS (rproj u v))
                                     (@rsplus SS (rproj u v) w1))
                    (@rsplus SS (@rsplus SS (@rsopp SS (rproj u v))
                                                       (rproj u v)) w1))
      by exact (rsplus_assoc (@rsopp SS (rproj u v)) (rproj u v) w1).
    assert (H2 : Id (@rsplus SS (@rsplus SS (@rsopp SS (rproj u v))
                                                       (rproj u v)) w1)
                    (@rsplus SS (@rszero SS) w1))
      by exact (id_cong (fun x => @rsplus SS x w1)
                        (id_trans (rsplus_comm (@rsopp SS (rproj u v)) (rproj u v))
                                  (rsplus_opp (rproj u v)))).
    assert (H3 : Id (@rsplus SS (@rszero SS) w1) w1)
      by exact (id_trans (rsplus_comm (@rszero SS) w1) (rsplus_zero w1)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  assert (Hl2 : Id (@rsplus SS (@rsopp SS (rproj u v))
                                   (@rsplus SS (rproj u v) w2)) w2).
  {
    assert (H1 : Id (@rsplus SS (@rsopp SS (rproj u v))
                                     (@rsplus SS (rproj u v) w2))
                    (@rsplus SS (@rsplus SS (@rsopp SS (rproj u v))
                                                       (rproj u v)) w2))
      by exact (rsplus_assoc (@rsopp SS (rproj u v)) (rproj u v) w2).
    assert (H2 : Id (@rsplus SS (@rsplus SS (@rsopp SS (rproj u v))
                                                       (rproj u v)) w2)
                    (@rsplus SS (@rszero SS) w2))
      by exact (id_cong (fun x => @rsplus SS x w2)
                        (id_trans (rsplus_comm (@rsopp SS (rproj u v)) (rproj u v))
                                  (rsplus_opp (rproj u v)))).
    assert (H3 : Id (@rsplus SS (@rszero SS) w2) w2)
      by exact (id_trans (rsplus_comm (@rszero SS) w2) (rsplus_zero w2)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  exact (id_trans (id_sym Hl1) (id_trans Hc Hl2)).
Qed.

End ReqHilbertTheorems.

(* ============================================================ *)
(* Part 9: the four GramSchmidt pieces (Id L24738-24900 dependence face;   *)
(*         the StateSpaceExtended face is [reqStateSpaceExt]) *)
(* ============================================================ *)
Section ReqGramSchmidt.
Context {SSE : reqStateSpaceExt}
        {HS : reqHilbertSpace (@rsse_base SSE)}.

Let SSx : reqStateSpace := @rsse_base SSE.
Local Existing Instance SSx.

(* The Id-world projection_idempotent (L24840) as an honest same-shape slot
   (unused by this cluster; kept in place like the source-module interface). *)
Variable rprojection_idempotent : forall u v : @rSS SSx,
  Id (rproj u (rproj u v)) (rproj u v).

(* The Id-world inner_sopp_l (L24791): ⟨−x, y⟩ = −⟨x,y⟩ (req at R-valued
   positions; the Id part of the smult_opp bridge enters the req chain via
   the match combinator, with zero rewrite tactics). *)
Lemma req_inner_sopp_l : forall x y : @rSS SSx,
  real_eq(rinner (rsopp x) y) (opp (rinner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (rsmult (opp one) x) (rsopp (rsmult one x)))
    by exact (rsmult_opp one x).
  assert (Hone : Id (rsmult one x) x)
    by exact (rsmult_one x).
  assert (Hsopp : Id (rsmult (opp one) x) (rsopp x))
    by exact (id_trans Hsm (id_cong rsopp Hone)).
  exact (req_trans _ _ _
    (match Hsopp in (Id _ z) return
        (real_eq (rinner z y) (rinner (rsmult (opp one) x) y))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (rinner_smult_l (opp one) x y)
      (req_trans _ _ _
        (req_opp_mult_r one (rinner x y))
        (req_opp_compat (mult one (rinner x y)) (rinner x y)
                        (req_mult_one_l (rinner x y)))))).
Qed.

(* The Id-world inner_szero_l (L24812): ⟨0, y⟩ = 0
   ([splus_opp] + [inner_splus_l] + [inner_sopp_l]) *)
Lemma req_inner_szero_l : forall y : @rSS SSx,
  real_eq(rinner rszero y) (zero).
Proof.
  intro y.
  assert (Hz : Id (rsplus y (rsopp y)) rszero)
    by exact (rsplus_opp y).
  exact (req_trans _ _ _
    (match Hz in (Id _ z) return (real_eq (rinner z y) (rinner (rsplus y (rsopp y)) y))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (rinner_splus_l y (rsopp y) y)
      (req_trans _ _ _
        (req_plus_compat (rinner y y) (rinner y y)
                         (rinner (rsopp y) y) (opp (rinner y y))
                         (req_refl (rinner y y)) (req_inner_sopp_l y y))
        (plus_opp (rinner y y))))).
Qed.

(* The Id-world gram_schmidt_step (L24844): a [sigT] witness of the
   orthogonal component w := v − proj u v. *)
Theorem req_gram_schmidt_step : forall u v : @rSS SSx,
  Not (Id u rszero) ->
  sigT (fun w : @rSS SSx =>
    And (real_eq (rinner u w) zero)
        (Id v (rsplus (rproj u v) w))).
Proof.
  intros u v Hu.
  exists (rsplus v (rsopp (rproj u v))).
  split.
  - exact (req_trans _ _ _
            (req_sym _ _ (rinner_sym (rsplus v (rsopp (rproj u v))) u))
            (rproj_orthogonal u v)).
  - assert (Hopp : Id (rsplus (rproj u v) (rsplus v (rsopp (rproj u v))))
                      (rsplus (rproj u v) (rsplus (rsopp (rproj u v)) v)))
      by exact (id_cong (fun x => rsplus (rproj u v) x)
                        (rsplus_comm v (rsopp (rproj u v)))).
    assert (Hassoc : Id (rsplus (rproj u v) (rsplus (rsopp (rproj u v)) v))
                        (rsplus (rsplus (rproj u v) (rsopp (rproj u v))) v))
      by exact (rsplus_assoc (rproj u v) (rsopp (rproj u v)) v).
    assert (Hinv : Id (rsplus (rproj u v) (rsopp (rproj u v))) rszero)
      by exact (rsplus_opp (rproj u v)).
    assert (Hzero : Id (rsplus rszero v) v)
      by exact (id_trans (rsplus_comm rszero v) (rsplus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc
              (id_trans (id_cong (fun x => rsplus x v) Hinv) Hzero)))).
Qed.

(* The Id-world gram_schmidt_pair (L24874): the twin named piece. *)
Theorem req_gram_schmidt_pair : forall u v : @rSS SSx,
  Not (Id u rszero) ->
  sigT (fun w : @rSS SSx =>
    And (real_eq (rinner u w) zero)
        (Id v (rsplus (rproj u v) w))).
Proof.
  intros u v Hu.
  exact (req_gram_schmidt_step u v Hu).
Qed.

End ReqGramSchmidt.

(* ============================================================ *)
(* Part 10: the fourteen multivariable-differentiable algebra pieces      *)
(* (Id L26686-27500; the DifferentiableMV/MVVec record cluster) *)
(* ============================================================ *)
Section ReqMultivar.
Context {SSE : reqStateSpaceExt}
        {HS : reqHilbertSpace (@rsse_base SSE)}.

Let SSx : reqStateSpace := @rsse_base SSE.
Local Existing Instance SSx.

(* The Id-world inner_splus_r (L26722): ⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩
   (sym transports twice) *)
Lemma req_inner_splus_r : forall x y z : @rSS SSx,
  real_eq (rinner x (rsplus y z)) (plus (rinner x y) (rinner x z)).
Proof.
  intros x y z.
  assert (H1 : real_eq (rinner x (rsplus y z)) (rinner (rsplus y z) x))
    by exact (rinner_sym x (rsplus y z)).
  assert (H2 : real_eq (rinner (rsplus y z) x) (plus (rinner y x) (rinner z x)))
    by exact (rinner_splus_l y z x).
  assert (H3 : real_eq (plus (rinner y x) (rinner z x)) (plus (rinner x y) (rinner x z)))
    by exact (req_plus_compat _ _ _ _ (rinner_sym y x) (rinner_sym z x)).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 H3)).
Qed.

(* The Id-world mv_compose_diff_decomp (L26739): reuses this file's
   [req_compose_diff_decomp], specialized at D := X and h := one, with a
   [mult_one] change of face. *)
Lemma req_mv_compose_diff_decomp : forall (A B C G g0 X : R),
  real_eq (req_minus A (plus B (mult C X)))
     (plus (req_minus A (plus B (mult C (req_minus G g0))))
           (mult C (req_minus (req_minus G g0) X))).
Proof.
  intros A B C G g0 X.
  assert (H1 : real_eq (req_minus A (plus B (mult (mult C X) one)))
                   (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (req_minus (req_minus G g0) (mult X one)))))
    by exact (req_compose_diff_decomp A B C X G g0 one).
  (* Left side: (mult C X)·one → C·X (reverse [mult_assoc] + [mult_one]). *)
  assert (Hm0 : real_eq (mult (mult C X) one) (mult C X))
    by exact (req_trans _ _ _
              (req_sym _ _ (mult_assoc C X one))
              (req_mult_compat C C (mult X one) X (req_refl C) (mult_one X))).
  assert (Hm1 : real_eq (plus B (mult (mult C X) one)) (plus B (mult C X)))
    by exact (req_plus_compat B B (mult (mult C X) one) (mult C X) (req_refl B) Hm0).
  assert (Hl : real_eq (req_minus A (plus B (mult (mult C X) one)))
                   (req_minus A (plus B (mult C X)))).
  { unfold req_minus.
    exact (req_plus_compat A A (opp (plus B (mult (mult C X) one))) (opp (plus B (mult C X)))
                           (req_refl A)
                           (req_opp_compat (plus B (mult (mult C X) one))
                                           (plus B (mult C X)) Hm1)). }
  (* Right side: mult X one → X inside [req_minus] (unfold + opp change of
     face). *)
  assert (Hsub : real_eq (plus (req_minus G g0) (opp (mult X one)))
                     (plus (req_minus G g0) (opp X)))
    by exact (req_plus_compat (req_minus G g0) (req_minus G g0)
                              (opp (mult X one)) (opp X)
                              (req_refl (req_minus G g0))
                              (req_opp_compat (mult X one) X (mult_one X))).
  unfold req_minus.
  assert (Hr : real_eq (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (plus (req_minus G g0) (opp (mult X one)))))
                    (plus (req_minus A (plus B (mult C (req_minus G g0))))
                          (mult C (plus (req_minus G g0) (opp X))))).
  { exact (req_plus_compat (req_minus A (plus B (mult C (req_minus G g0))))
                           (req_minus A (plus B (mult C (req_minus G g0))))
                           (mult C (plus (req_minus G g0) (opp (mult X one))))
                           (mult C (plus (req_minus G g0) (opp X)))
                           (req_refl (req_minus A (plus B (mult C (req_minus G g0)))))
                           (req_mult_compat C C (plus (req_minus G g0) (opp (mult X one)))
                                            (plus (req_minus G g0) (opp X))
                                            (req_refl C) Hsub)). }
  exact (req_trans _ _ _ (req_sym _ _ Hl) (req_trans _ _ _ H1 Hr)).
Qed.

(* The Id-world inner_smult_r (L27228): ⟨x, a·y⟩ = a·⟨x,y⟩
   ([inner_smult_l] + sym transport) *)
Lemma req_inner_smult_r : forall (a : R) (x y : @rSS SSx),
  real_eq (rinner x (rsmult a y)) (mult a (rinner x y)).
Proof.
  intros a x y.
  assert (H1 : real_eq (rinner x (rsmult a y)) (rinner (rsmult a y) x))
    by exact (rinner_sym x (rsmult a y)).
  assert (H2 : real_eq (rinner (rsmult a y) x) (mult a (rinner y x)))
    by exact (rinner_smult_l a y x).
  assert (H3 : real_eq (mult a (rinner y x)) (mult a (rinner x y)))
    by exact (req_mult_compat a a (rinner y x) (rinner x y)
                             (req_refl a) (rinner_sym y x)).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 H3)).
Qed.

(* The Id-world inner_sopp_r (L27242): ⟨x, −y⟩ = −⟨x,y⟩
   ([smult_opp] + [inner_smult_r]) *)
Lemma req_inner_sopp_r : forall x y : @rSS SSx,
  real_eq (rinner x (rsopp y)) (opp (rinner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (rsmult (opp one) y) (rsopp (rsmult one y)))
    by exact (rsmult_opp one y).
  assert (Hone : Id (rsmult one y) y)
    by exact (rsmult_one y).
  assert (Hsopp : Id (rsmult (opp one) y) (rsopp y))
    by exact (id_trans Hsm (id_cong rsopp Hone)).
  exact (req_trans _ _ _
    (match id_sym Hsopp in (Id _ z) return
        (real_eq (rinner x (rsopp y)) (rinner x z))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (req_inner_smult_r (opp one) x y)
      (req_trans _ _ _
        (req_opp_mult_r one (rinner x y))
        (req_opp_compat (mult one (rinner x y)) (rinner x y)
                        (req_mult_one_l (rinner x y)))))).
Qed.

(* The Id-world inner_sminus_r (L27261): ⟨x, u−v⟩ = ⟨x,u⟩ − ⟨x,v⟩ *)
Lemma req_inner_sminus_r : forall x u v : @rSS SSx,
  real_eq (rinner x (@rsminus SSx u v)) (req_minus (rinner x u) (rinner x v)).
Proof.
  intros x u v.
  unfold req_minus.
  exact (req_trans _ _ _    (req_inner_splus_r x u (rsopp v))    (req_plus_compat (rinner x u) (rinner x u)                     (rinner x (rsopp v)) (opp (rinner x v))                     (req_refl (rinner x u)) (req_inner_sopp_r x v))).
Qed.

(* The Id-world splus_sminus_cancel (L27272): a + (b − a) = b (a vector Id chain) *)
Lemma req_splus_sminus_cancel : forall a b : @rSS SSx,
  Id (rsplus a (@rsminus SSx b a)) b.
Proof.
  intros a b.
  unfold rsminus.
  assert (H1 : Id (rsplus a (rsplus b (rsopp a))) (rsplus a (rsplus (rsopp a) b)))
    by exact (id_cong (fun z => rsplus a z) (rsplus_comm b (rsopp a))).
  assert (H2 : Id (rsplus a (rsplus (rsopp a) b)) (rsplus (rsplus a (rsopp a)) b))
    by exact (rsplus_assoc a (rsopp a) b).
  assert (H3 : Id (rsplus (rsplus a (rsopp a)) b) (rsplus rszero b))
    by exact (id_cong (fun z => rsplus z b) (rsplus_opp a)).
  assert (H4 : Id (rsplus rszero b) b)
    by exact (id_trans (rsplus_comm rszero b) (rsplus_zero b)).
  exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
Qed.

(* The Id-world sopp_szero (L27290): −0 = 0 (a vector Id chain) *)
Lemma req_sopp_szero : Id (rsopp rszero) rszero.
Proof.
  assert (H1 : Id (rsopp rszero) (rsplus (rsopp rszero) rszero))
    by exact (id_sym (rsplus_zero (rsopp rszero))).
  assert (H2 : Id (rsplus (rsopp rszero) rszero) (rsplus rszero (rsopp rszero)))
    by exact (rsplus_comm (rsopp rszero) rszero).
  assert (H3 : Id (rsplus rszero (rsopp rszero)) rszero)
    by exact (rsplus_opp rszero).
  exact (id_trans H1 (id_trans H2 H3)).
Qed.

(* The Id-world sminus_sminus_szero (L27308): (u−v) − 0 = u−v (a vector Id chain) *)
Lemma req_sminus_sminus_szero : forall u v : @rSS SSx,
  Id (@rsminus SSx (@rsminus SSx u v) rszero) (@rsminus SSx u v).
Proof.
  intros u v.
  unfold rsminus.
  exact (id_trans (id_cong (fun z => rsplus (rsplus u (rsopp v)) z) req_sopp_szero)                  (rsplus_zero (rsplus u (rsopp v)))).
Qed.

(* The Id-world smetric_sminus_zero (L27324): translation invariance of the
   metric ([smetric_snorm] plus the Id fact of [req_sminus_sminus_szero]
   entering the req chain via the match combinator). *)
Theorem req_smetric_sminus_zero : forall u v : @rSS SSx,
  real_eq (rsmetric (@rsminus SSx u v) rszero) (rsmetric u v).
Proof.
  intros u v.
  exact (req_trans _ _ _    (rsmetric_snorm (@rsminus SSx u v) rszero)    (req_trans _ _ _      (match req_sminus_sminus_szero u v in (Id _ z) return          (real_eq (rsnorm (@rsminus SSx (@rsminus SSx u v) rszero)) (rsnorm z))       with id_refl => req_refl _ end)      (req_sym _ _ (rsmetric_snorm u v)))).
Qed.

(* The Id-world inner_sminus_l (L27355): ⟨a−b, c⟩ = ⟨a,c⟩ − ⟨b,c⟩ *)
Lemma req_inner_sminus_l : forall a b c : @rSS SSx,
  real_eq (rinner (@rsminus SSx a b) c) (req_minus (rinner a c) (rinner b c)).
Proof.
  intros a b c.
  unfold req_minus.
  exact (req_trans _ _ _    (rinner_splus_l a (rsopp b) c)    (req_plus_compat (rinner a c) (rinner a c)                     (rinner (rsopp b) c) (opp (rinner b c))                     (req_refl (rinner a c)) (req_inner_sopp_l b c))).
Qed.

(* The Id-world sminus_zero_cancel (L27369): a − b = 0 gives a = b (a vector
   Id chain) *)
Lemma req_sminus_zero_cancel : forall a b : @rSS SSx,
  Id (@rsminus SSx a b) rszero -> Id a b.
Proof.
  intros a b H.
  assert (H1 : Id a (rsplus b (@rsminus SSx a b)))
    by exact (id_sym (req_splus_sminus_cancel b a)).
  exact (id_trans H1 (id_trans (id_cong (fun z => rsplus b z) H) (rsplus_zero b))).
Qed.

(* The adjoint interface (the Id-world mv_adjoint, L27376, as an honest
   same-shape slot kept in place) *)
Variable rmv_adjoint : forall (L : @rSS SSx -> @rSS SSx),
  sigT (fun Lad : @rSS SSx -> @rSS SSx => forall h w : @rSS SSx,
    real_eq (rinner (L h) w) (rinner h (Lad w))).

(* The operator-norm bound (the Id-world op_lipschitz, L27384, as an honest
   same-shape slot kept in place; [And] is the Set-level product) *)
Variable rop_lipschitz : forall (L : @rSS SSx -> @rSS SSx),
  sigT (fun N : R => And (real_le zero N) (forall h : @rSS SSx,
    real_le (rsmetric (L h) rszero) (mult N (rsmetric h rszero)))).

(* The Id-world mv_adjoint_unique (L27383): uniqueness of the adjoint
   (⟨h,h'⟩ = 0 feeds [inner_definite]) *)
Lemma req_mv_adjoint_unique : forall (L : @rSS SSx -> @rSS SSx)
    (Lad1 Lad2 : @rSS SSx -> @rSS SSx),
  (forall h w : @rSS SSx, real_eq (rinner (L h) w) (rinner h (Lad1 w))) ->
  (forall h w : @rSS SSx, real_eq (rinner (L h) w) (rinner h (Lad2 w))) ->
  forall w : @rSS SSx, Id (Lad1 w) (Lad2 w).
Proof.
  intros L Lad1 Lad2 H1 H2 w.
  pose (h := @rsminus SSx (Lad1 w) (Lad2 w)).
  assert (Hinner : real_eq (rinner h h) zero).
  {
    unfold h.
    apply (req_trans _ _ _ (req_inner_sminus_r h (Lad1 w) (Lad2 w))).
    assert (Hmid : real_eq (rinner h (Lad1 w)) (rinner h (Lad2 w)))
      by exact (req_trans _ _ _ (req_sym _ _ (H1 h w)) (H2 h w)).
    unfold req_minus.
    exact (req_trans _ _ _
      (req_plus_compat (rinner h (Lad1 w)) (rinner h (Lad1 w))
                       (opp (rinner h (Lad2 w))) (opp (rinner h (Lad1 w)))
                       (req_refl (rinner h (Lad1 w)))
                       (req_opp_compat (rinner h (Lad2 w)) (rinner h (Lad1 w))
                                       (req_sym _ _ Hmid)))
      (plus_opp (rinner h (Lad1 w)))).
  }
  assert (Hhzero : Id h rszero) by exact (rinner_definite h Hinner).
  unfold h in Hhzero.
  exact (req_sminus_zero_cancel (Lad1 w) (Lad2 w) Hhzero).
Qed.

(* The Id-world op_lipschitz_compose (L27409): |L∘M h| ≤ (N_L·N_M)·|h|
   (a chain of the [le_mult_compat_weak]/[mult_zero] interface fields; the
   addition position reads off the existing proof: the Id proof has no plain
   product-nonnegativity dependence and no fresh slot is added) *)
Lemma req_op_lipschitz_compose : forall (L M : @rSS SSx -> @rSS SSx),
  sigT (fun N : R => And (real_le zero N) (forall h : @rSS SSx,
    real_le (rsmetric (L (M h)) rszero) (mult N (rsmetric h rszero)))).
Proof.
  intros L M.
  destruct (rop_lipschitz L) as [NL [HNL0 HNL]].
  destruct (rop_lipschitz M) as [NM [HNM0 HNM]].
  exists (mult NL NM).
  split.
  - (* 0 ≤ NL·NM: a [mult_zero] change of face + [le_mult_compat_weak]. *)
    apply (le_id_l _ (mult zero NM) _).
    + exact (req_trans _ _ _ (req_sym _ _ (mult_zero NM)) (mult_comm NM zero)).
    + exact (le_mult_compat_weak zero NL NM HNM0 HNL0).
  - intros h.
    apply (le_trans _ (mult NL (rsmetric (M h) rszero)) _).
    + exact (HNL (M h)).
    + apply (le_trans _ (mult NL (mult NM (rsmetric h rszero))) _).
      * apply (le_id_l _ (mult (rsmetric (M h) rszero) NL) _).
        { exact (mult_comm NL (rsmetric (M h) rszero)). }
        { apply (le_id_r _ (mult (mult NM (rsmetric h rszero)) NL) _).
          - exact (mult_comm (mult NM (rsmetric h rszero)) NL).
          - exact (le_mult_compat_weak (rsmetric (M h) rszero)
                     (mult NM (rsmetric h rszero)) NL HNL0 (HNM h)). }
      * apply (le_id_l _ (mult (mult NL NM) (rsmetric h rszero)) _).
        { exact (mult_assoc NL NM (rsmetric h rszero)). }
        { exact (le_refl (mult (mult NL NM) (rsmetric h rszero))). }
Qed.

(* The Id-world mv_vec_diff_decomp (L27450): the general error decomposition
   in two segments (Hcancel + Hre), same-shape as [req_compose_diff_decomp]
   with [req_sym] at Hre Y X. *)
Lemma req_mv_vec_diff_decomp : forall (A B X Y : R),
  real_eq (req_minus A (plus B X)) (plus (req_minus A (plus B Y)) (req_minus Y X)).
Proof.
  intros A B X Y.
  assert (Hcancel : forall Z : R, real_eq (plus (opp (plus B Z)) Z) (opp B)).
  {
    intro Z.
    apply (req_trans _ (plus (plus (opp B) (opp Z)) Z) _).
    - apply (req_plus_compat (opp (plus B Z)) (plus (opp B) (opp Z)) Z Z
                             (req_opp_plus B Z) (req_refl Z)).
    - apply (req_trans _ (plus (opp B) (plus (opp Z) Z)) _).
      + apply (req_sym _ _ (plus_assoc (opp B) (opp Z) Z)).
      + apply (req_trans _ (plus (opp B) zero) _).
        * apply (req_plus_compat (opp B) (opp B) (plus (opp Z) Z) zero
                                 (req_refl (opp B))).
          exact (req_trans _ _ _ (plus_comm (opp Z) Z) (plus_opp Z)).
        * apply plus_zero.
  }
  assert (Hre : forall Z1 Z2 : R,
    real_eq (plus (plus A (opp (plus B Z1))) (plus Z1 (opp Z2)))
        (plus A (opp (plus B Z2)))).
  {
    intros Z1 Z2.
    apply (req_trans _ (plus A (plus (plus (opp (plus B Z1)) Z1) (opp Z2))) _).
    - exact (req_trans _ _ _
              (req_sym _ _ (plus_assoc A (opp (plus B Z1)) (plus Z1 (opp Z2))))
              (req_plus_compat A A _ _
                (req_refl A) (plus_assoc (opp (plus B Z1)) Z1 (opp Z2)))).
    - apply (req_trans _ (plus A (plus (opp B) (opp Z2))) _).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_plus_compat _ _ _ _ (Hcancel Z1) (req_refl (opp Z2))).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_sym _ _ (req_opp_plus B Z2)).
  }
  unfold req_minus.
  exact (req_sym _ _ (Hre Y X)).
Qed.

End ReqMultivar.

(* Assumption audit: each named statement above, re-checked closed under the global context. *)
Print Assumptions req_core_claim5_holds.
Print Assumptions req_boltzmann_factor_pos.
Print Assumptions req_boltzmann_prob_pos.
Print Assumptions req_prediction_fluctuation_scale.
Print Assumptions req_thermo_core_claim3_holds.
Print Assumptions req_thermo_core_claim5_holds.
Print Assumptions req_step_diff_point.
Print Assumptions req_entropy_gradient_strict_mono.
Print Assumptions req_gradient_diff_from_zero.
Print Assumptions req_gradient_step_recurrence.
Print Assumptions req_sum_exp_positive.
Print Assumptions req_exp_neg_positive.
Print Assumptions req_core_claim1_lm_holds.
Print Assumptions req_core_claim3_lm_holds.
Print Assumptions req_core_claim5_lm_holds.
Print Assumptions req_normalized_prob_pos.
Print Assumptions req_prediction_boltzmann_sampling_holds.
Print Assumptions rgrp_of_nat_S_pos.
Print Assumptions rgrp_G_pos_of_nonempty.
Print Assumptions rgrp_G_pos_of_nonempty_enum.
Print Assumptions req_grpo_count_one.
Print Assumptions req_list_sum_g_zero_fn.
Print Assumptions req_split_count_one.
Print Assumptions req_grpo_indicator_sum_one.
Print Assumptions req_grpo_uniform_mass.
Print Assumptions req_square_expand4.
Print Assumptions req_plus_cancel_head.
Print Assumptions req_compose_diff_decomp.
Print Assumptions req_half_le_one.
Print Assumptions req_half_le_self.
Print Assumptions req_minus_plus_zero_r.
Print Assumptions req_square_diff_expand.
Print Assumptions req_dpo_logit_denom_pos.
Print Assumptions req_dpo_loss_diff_decomp.
Print Assumptions req_dpo_sigmoid_pos.
Print Assumptions req_dpo_sigmoid_identity.
Print Assumptions req_dpo_sigmoid_complement.
Print Assumptions req_dpo_gradient_alt.
Print Assumptions req_orthogonal_decomposition_exists.
Print Assumptions req_orthogonal_decomposition_unique.
Print Assumptions req_inner_sopp_l.
Print Assumptions req_inner_szero_l.
Print Assumptions req_gram_schmidt_step.
Print Assumptions req_gram_schmidt_pair.
Print Assumptions req_inner_splus_r.
Print Assumptions req_mv_compose_diff_decomp.
Print Assumptions req_inner_smult_r.
Print Assumptions req_inner_sopp_r.
Print Assumptions req_inner_sminus_r.
Print Assumptions req_splus_sminus_cancel.
Print Assumptions req_sopp_szero.
Print Assumptions req_sminus_sminus_szero.
Print Assumptions req_smetric_sminus_zero.
Print Assumptions req_inner_sminus_l.
Print Assumptions req_sminus_zero_cancel.
Print Assumptions req_mv_adjoint_unique.
Print Assumptions req_op_lipschitz_compose.
Print Assumptions req_mv_vec_diff_decomp.
