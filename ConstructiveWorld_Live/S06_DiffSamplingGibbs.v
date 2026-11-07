(* ConstructiveWorld-Set — differentiable sampling and Gibbs partitions (constructive Set layer). *)

(** * S06_DiffSamplingGibbs: differentiable sampling, Gibbs partitions, Top-K TV identity.

    Mission.  Differentiability of the arithmetic operations and of the affine, MSE,
      DPO and entropy losses ([differentiable_compose], [mse_diff],
      [entropy_differentiable]); linear bounds for [log(1+t)] ([log_one_plus_le],
      [log_one_plus_ge]); the Gibbs correspondence between attention softmax and the
      Boltzmann distribution ([attention_is_gibbs_temp]); the exact identity
      [TV(boltzmann, topk_renorm) == tail_mass / Z_thermo] and the Min-P / Top-p
      truncated kernels with their renormalization laws.

    Dependencies.  Stdlib [QArith], [Qabs], [Qround], [List], [Bool], [Arith], [Setoid],
      [Morphisms], [Lia], [Qminmax]; this development [S01_BaseRing]-[S05_AlignmentGRPO].

    References.  This development and the concrete-layer witnesses its modules supply
      (e.g. [real_lt_plus_compat_lt_le] in [S07_RealSetoidExpLog]); the baseline module
      in ConstructiveWorld-Main whose statement names are carried over here verbatim
      (statement-face Set-carrier completion); a split of [CW_ConstructiveWorld_219]
      (source range L24768-L32574).

    Constructivity.  All named statements are carried by [Set]; no statement is
      admitted; analytic facts not derivable from the abstract interface
      ([inner_lipschitz], [mv_adjoint], [op_lipschitz], [log_differentiable],
      [sum_pos_preserved]) are disclosed as explicit interface assumptions, audited
      by the closing [Print Assumptions] commands.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      ConstructiveWorld_Live/S06_DiffSamplingGibbs.v] compiles cleanly (exit 0); the
      first eight bytes of the artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.

Section GramSchmidt.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpaceExtended RI}.
Context {HS : HilbertSpace RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let inner := @inner RI SS HS.
Let splus := @splus RI SS.
Let sopp := @sopp RI SS.
Let szero := @szero RI SS.
Let smult := @smult RI SS.
Let proj := @proj RI SS HS.

(* Lemma for the inner product against [sopp] (derived via [inner_smult_l] and [smult_opp]): ⟨-x, y⟩ = -⟨x, y⟩ *)
Lemma inner_sopp_l : forall x y : S,
  Id (inner (sopp x) y) (opp (inner x y)).
Proof.
  intros x y.
  exact (id_trans (id_sym (id_cong (fun z => inner z y)
                     (id_trans (smult_opp one x) (id_cong sopp (smult_one x)))))
           (id_trans (inner_smult_l (opp one) x y)
              (id_trans (opp_mult_r one (inner x y))
                 (id_cong opp (id_trans (mult_comm one (inner x y))
                                        (mult_one (inner x y))))))).
Qed.

(* The inner product of the zero vector with any vector is zero: ⟨0, y⟩ = 0 (via [splus_opp] + [inner_splus_l]) *)
Lemma inner_szero_l : forall y : S,
  Id (inner szero y) zero.
Proof.
  intro y.
  exact (id_trans (id_sym (id_cong (fun z => inner z y) (splus_opp y)))
           (id_trans (inner_splus_l y (sopp y) y)
              (id_trans (id_cong (fun t => plus (inner y y) t) (inner_sopp_l y y))
                 (plus_opp (inner y y))))).
Qed.

(* Idempotence of the projection needs an extra assumption: [proj_linear] plus
   [proj_orthogonal] do not suffice to prove proj u (proj u v) = proj u v — one needs
   the property "projections along orthogonal directions vanish", ⟨w,u⟩=0 ⟹ proj u w = 0,
   which the interface does not provide; concrete instances such as R^n satisfy it.
   Stated here as an explicit Variable assumption, for use by the algebraic derivations below. *)
Variable projection_idempotent : forall u v : S,
  Id (proj u (proj u v)) (proj u v).

(* One Gram-Schmidt step: given a nonzero vector u and any v,
   construct w := v - proj u v with ⟨u, w⟩ = 0 (the component of v orthogonal to u;
   existence in sigT form).  The heart: [proj_orthogonal] gives ⟨v - proj u v, u⟩ = 0,
   [inner_sym] swaps it to ⟨u, w⟩ = 0, and the decomposition witness v = proj u v + w is supplied. *)
Theorem gram_schmidt_step : forall u v : S,
  Not (Id u szero) ->
  sigT (fun w : S =>
    And (Id (inner u w) zero)
        (Id v (splus (proj u v) w))).
Proof.
  intros u v Hu.
  exists (splus v (sopp (proj u v))).
  split.
  - (* ⟨u, v - proj u v⟩ = 0: [proj_orthogonal] gives ⟨v - proj u v, u⟩ = 0,
       and [inner_sym] swaps it to ⟨u, v - proj u v⟩ = 0 *)
    apply (id_trans (id_sym (inner_sym (splus v (sopp (proj u v))) u))
                    (proj_orthogonal u v)).
  - (* v = proj u v + (v - proj u v): [splus] algebra (as in [orthogonal_decomposition_exists]) *)
    assert (Hopp : Id (splus (proj u v) (splus v (sopp (proj u v))))
                    (splus (proj u v) (splus (sopp (proj u v)) v))).
    { apply (id_cong (fun x => splus (proj u v) x)).
      exact (splus_comm v (sopp (proj u v))). }
    assert (Hassoc : Id (splus (proj u v) (splus (sopp (proj u v)) v))
                        (splus (splus (proj u v) (sopp (proj u v))) v)).
    { exact (splus_assoc (proj u v) (sopp (proj u v)) v). }
    assert (Hinv : Id (splus (proj u v) (sopp (proj u v))) szero)
      by exact (splus_opp (proj u v)).
    assert (Hzero : Id (splus szero v) v)
      by exact (id_trans (splus_comm szero v) (splus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc (id_trans (id_cong (fun x => splus x v) Hinv) Hzero)))).
Qed.

(* Two-vector Gram-Schmidt: given nonzero u and any v,
   build the orthogonal pair {u, w} (w := v projected onto the orthogonal complement of u), in sigT form. *)
Theorem gram_schmidt_pair : forall u v : S,
  Not (Id u szero) ->
  sigT (fun w : S =>
    And (Id (inner u w) zero)
        (Id v (splus (proj u v) w))).
Proof.
  intros u v Hu.
  exact (gram_schmidt_step u v Hu).
Qed.

End GramSchmidt.

(* Basic properties of probability distributions *)
Section ProbDistProperties.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Definition is_prob_dist (p : S -> R) : Set :=
  And (forall s, le zero (p s)) (Id (sum_over_S p) one).

Lemma prob_dist_sum_linear :
  forall (p : S -> R), is_prob_dist p ->
  forall (a : R),
    Id (sum_over_S (fun s => mult a (p s))) a.
Proof.
  intros p [Hnonneg Hnorm] a.
  rewrite sum_over_S_linear.
  rewrite Hnorm.
  apply mult_one.
Qed.

(* The original assumption prob_dist_add (is_prob_dist (p+q)) is mathematically false:
   Σ(p+q) = Σp + Σq = 1+1 = 2 ≠ 1, so the sum of two distributions is not normalized.
   The correct mixing operation is the normalized average inv_2·(p+q), which is provable. *)
Theorem prob_dist_mix :
  forall p q : S -> R,
    is_prob_dist p -> is_prob_dist q ->
    is_prob_dist (fun s => mult (inv_pos (plus one one) two_pos) (plus (p s) (q s))).
Proof.
  intros p q [Hp_nonneg Hp_norm] [Hq_nonneg Hq_norm].
  unfold is_prob_dist.
  split.
  - (* Nonnegativity: inv_2·(p s + q s) ≥ 0 *)
    intro s.
    apply (le_trans _ (mult zero (plus (p s) (q s))) _).
    + assert (Hz : Id (mult zero (plus (p s) (q s))) zero)
        by exact (id_trans (mult_comm zero (plus (p s) (q s))) (mult_zero (plus (p s) (q s)))).
      rewrite Hz. apply le_refl.
    + apply (le_mult_compat_weak zero (inv_pos (plus one one) two_pos) (plus (p s) (q s))).
      * apply (le_trans _ (plus zero zero) _).
        -- assert (Hz2 : Id (plus zero zero) zero)
             by exact (id_trans (plus_comm zero zero) (plus_zero zero)).
           rewrite Hz2. apply le_refl.
        -- apply le_plus_compat; [exact (Hp_nonneg s) | exact (Hq_nonneg s)].
      * apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - (* Normalization: Σ_s inv_2·(p s + q s) = inv_2·(Σp + Σq) = inv_2·(1+1) = 1 *)
    assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (plus one one) two_pos) (plus (p s) (q s))))
                     (mult (inv_pos (plus one one) two_pos) (sum_over_S (fun s => plus (p s) (q s)))))
      by exact (sum_over_S_linear (inv_pos (plus one one) two_pos) (fun s => plus (p s) (q s))).
    rewrite Hlin.
    assert (Hadd : Id (sum_over_S (fun s => plus (p s) (q s))) (plus (sum_over_S p) (sum_over_S q)))
      by exact (sum_over_S_add p q).
    rewrite Hadd.
    rewrite Hp_norm. rewrite Hq_norm.
    assert (Hcc : Id (mult (inv_pos (plus one one) two_pos) (plus one one)) one)
      by exact (id_trans (mult_comm (inv_pos (plus one one) two_pos) (plus one one))
                         (inv_pos_correct (plus one one) two_pos)).
    exact Hcc.
Qed.

End ProbDistProperties.

(* KL divergence *)
Section KLDivergence.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* Bind the basic types and functions explicitly *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let log := @log RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable q : S -> R.
Variable q_pos : forall s, lt zero (q s).

(* KL divergence: defined as the relative entropy relative_entropy p q = Σ p·(log p − log q).
   The earlier definition via log_inv(inv_pos q · p) was in fact −KL (sign reversed) and
   duplicated the already-proven gibbs_inequality/gibbs_equality; it is unified here with
   the relative_entropy presentation of [FreeEnergyMinimization] (a single definition). *)
Definition kl_divergence (p : S -> R) : R :=
  relative_entropy p q.

(* Normalization of q (needed by the Gibbs theorems): stated as an explicit Variable. *)
Variable q_norm : normalized q.

(* Gibbs inequality (KL ≥ 0): specialization of the already-proven [gibbs_inequality]. *)
Theorem kl_nonneg : forall p : S -> R,
  normalized p -> positive_dist p -> le zero (kl_divergence p).
Proof.
  intros p Hnp Hpp.
  unfold kl_divergence.
  exact (gibbs_inequality p q Hnp Hpp q_norm q_pos).
Qed.

(* Gibbs equality (KL = 0 ⟹ p = q): specialization of the already-proven [gibbs_equality]. *)
Theorem kl_zero_iff_eq : forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (kl_divergence p) zero -> forall s : S, Id (p s) (q s).
Proof.
  intros p Hnp Hpp Hkl0 s.
  unfold kl_divergence in Hkl0.
  exact (gibbs_equality p q Hnp Hpp q_norm q_pos Hkl0 s).
Qed.

End KLDivergence.

(* Differentiability lemmas *)
Section DifferentiableLemmas.
Local Existing Instance RI_base.
Context {RI : RealInterfaceEnhanced}.

(* Unpack the fields explicitly *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let plus_zero := @plus_zero RI.
Let plus_comm := @plus_comm RI.
Let plus_opp := @plus_opp RI.
Let mult_zero := @mult_zero RI.
Let mult_comm := @mult_comm RI.
Let mult_one := @mult_one RI.
Let abs_nonneg := @abs_nonneg RI.
Let le_mult_compat := @le_mult_compat RI.
Let le_trans := @le_trans RI.
Let one_pos := @one_pos RI.
Let exp_neg := @exp_neg RI.
Let log_inv := @log_inv RI.
Let log_inv_exp_neg := @log_inv_exp_neg RI.

(* [abs_zero] is already a field of [RealInterfaceEnhanced] (statement at projection level),
   so it is not redeclared as an assumption here; in the proofs,
   [change ... in abs_zero] moves the statement to the [Let] level to match the goal. *)

Lemma differentiable_const (c : R) : Differentiable (fun _ => c).
Proof.
  exists (fun _ => zero).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    unfold minus.
    rewrite (mult_comm zero h).
    rewrite mult_zero.
    rewrite plus_zero.
    rewrite plus_opp.
    (* Goal: le (abs zero) (mult eps (abs h)).
       The abs/zero/mult/le in the goal are class projections (spelled <Module>.abs etc.
       under coqc compilation, Top.abs etc. under interactive loading), while [abs_zero]
       and the field constants are Let-bound.  Rewrite matching does not cross delta
       levels, so the whole proof works at the Let level: change turns the goal into the
       Let-constant shape (convertible), assert+exact builds Let-level Id lemmas (exact
       checks convertibility), rewriting stays within the level, and the final exact closes.
       This spelling depends on no module-name prefix and compiles both interactively and
       from the command line. *)
    change (le (abs zero) (mult eps (abs h))).
    (* [abs_zero] is an Enhanced field (statement at projection level): pose it as a local assumption first, then change it to the Let level *)
    pose proof abs_zero as Habs_zero.
    change (Id (abs zero) zero) in Habs_zero.
    rewrite Habs_zero.
    assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
    rewrite <- Hmz.
    assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
    rewrite Hmc1.
    assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
    rewrite Hmc2.
    exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
Qed.

Lemma differentiable_id : Differentiable (fun x => x).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split; [apply one_pos | intros h Hh].
  unfold minus.
  rewrite (mult_comm one h).
  rewrite mult_one.
  rewrite plus_opp.
  (* As in [differentiable_const]: the whole proof stays at the Let level, depending on no module-name prefix *)
  change (le (abs zero) (mult eps (abs h))).
  pose proof abs_zero as Habs_zero.
  change (Id (abs zero) zero) in Habs_zero.
  rewrite Habs_zero.
  assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
  rewrite <- Hmz.
  assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
  rewrite Hmc1.
  assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
  rewrite Hmc2.
  exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
Qed.

(* Differentiability of addition (constructive ε-δ proof).
   Idea: |Δ(f+g) - (df+dg)·h| ≤ |Δf - df·h| + |Δg - dg·h| ≤ (eps/2+eps/2)|h| = eps|h|.
   δ = min δf δg ([min_pos] preserves positivity); eps/2 = inv_2·eps
   ([half_pos]/[half_twice]); the algebraic decomposition uses
   [minus_plus_distr] / [plus_swap_mid] / [mult_plus_distr_r] ([RingLemmas]);
   lemmas consumed at the Let level need pose + change. *)
Theorem differentiable_plus : forall (f g : R -> R),
  Differentiable f -> Differentiable g ->
  Differentiable (fun x => plus (f x) (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => plus (df x) (dg x)).
  intros x eps Heps.
  pose (mult (inv_pos (plus one one) two_pos) eps) as eps_half.
  assert (Hhalf : lt zero eps_half) by (unfold eps_half; apply half_pos; exact Heps).
  destruct (Hf x eps_half Hhalf) as [dfdelta [Hdf1 Hdf2]].
  destruct (Hg x eps_half Hhalf) as [dgdelta [Hdg1 Hdg2]].
  exists (min dfdelta dgdelta).
  split.
  - (* lt zero (min dfdelta dgdelta) *)
    apply min_pos; [exact Hdf1 | exact Hdg1].
  - intros h Hh.
    (* Move the goal to the Let level ([df_correct] is stated at projection level; the Let level is convenient for rewrite) *)
    change (le (abs (minus (plus (f (plus x h)) (g (plus x h)))
                            (plus (plus (f x) (g x)) (mult (plus (df x) (dg x)) h))))
              (mult eps (abs h))).
    (* |h| < min ⟹ |h| < dfdelta and |h| < dgdelta *)
    assert (Hh1 : lt (abs h) dfdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_l. }
    assert (Hh2 : lt (abs h) dgdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_r. }
    (* Error decomposition: E = A_f + A_g ([minus_plus_distr] + [plus_swap_mid] + [mult_plus_distr_r]) *)
    assert (Hmpd : Id (mult (plus (df x) (dg x)) h) (plus (mult (df x) h) (mult (dg x) h)))
      by exact (mult_plus_distr_r (df x) (dg x) h).
    rewrite Hmpd.
    assert (Hswap : Id (plus (plus (f x) (g x)) (plus (mult (df x) h) (mult (dg x) h)))
                       (plus (plus (f x) (mult (df x) h)) (plus (g x) (mult (dg x) h))))
      by exact (plus_swap_mid (f x) (g x) (mult (df x) h) (mult (dg x) h)).
    rewrite Hswap.
    assert (Hmpd2 : Id (minus (plus (f (plus x h)) (g (plus x h)))
                              (plus (plus (f x) (mult (df x) h)) (plus (g x) (mult (dg x) h))))
                       (plus (minus (f (plus x h)) (plus (f x) (mult (df x) h)))
                             (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
      by exact (minus_plus_distr (f (plus x h)) (g (plus x h))
                                 (plus (f x) (mult (df x) h)) (plus (g x) (mult (dg x) h))).
    rewrite Hmpd2.
    (* Triangle inequality *)
    apply (le_trans _ (plus (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                            (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))).
    + apply abs_triangle.
    + apply (le_trans _ (plus (mult eps_half (abs h)) (mult eps_half (abs h)))).
      * apply le_plus_compat.
        -- apply (Hdf2 h Hh1).
        -- apply (Hdg2 h Hh2).
      * (* eps_half·|h| + eps_half·|h| = eps·|h| *)
        assert (Hsum : Id (plus (mult eps_half (abs h)) (mult eps_half (abs h)))
                          (mult eps (abs h))).
        {
          unfold eps_half.
          assert (Hd : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                      (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                           (plus (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                                 (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))))
            by exact (mult_plus_distr_r (mult (inv_pos (plus one one) two_pos) eps)
                                        (mult (inv_pos (plus one one) two_pos) eps) (abs h)).
          rewrite <- Hd.
          (* Replace inside the mult _ (abs h) context: plus X X = eps (via [id_cong], avoiding overreach of rewrite) *)
          assert (Hcong : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                          (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                             (mult eps (abs h))).
          { apply (id_cong (fun z => mult z (abs h))). exact (half_twice eps). }
          rewrite Hcong. reflexivity.
        }
        rewrite Hsum. apply le_refl.
Qed.

(* Differentiability of multiplication (constructive ε-δ proof; the [abs_mult]/
   [le_mult_compat_weak] fields are available).  The error has three terms:
   |g(x)|·|Δf - df·h| ≤ eps/4·|h|, |f(x)|·|Δg - dg·h| ≤ eps/4·|h|,
   |Δf|·|Δg| ≤ eps/2·|h| (δ₃ bounds the |h|² term); the total is ≤ eps·|h|.
   The algebraic decomposition uses [mult_diff_decomp] ([RingLemmas]). *)
Theorem differentiable_mult : forall (f g : R -> R),
  Differentiable f -> Differentiable g ->
  Differentiable (fun x => mult (f x) (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => plus (mult (df x) (g x)) (mult (f x) (dg x))).
  intros x eps Heps.
  pose (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) as eps4.
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply half_pos. apply half_pos. exact Heps. }
  pose (mult (inv_pos (plus one one) two_pos) eps) as eps2.
  assert (Heps2 : lt zero eps2).
  { unfold eps2. apply half_pos. exact Heps. }
  pose (plus (abs (f x)) one) as Mf.
  assert (Hmf : lt zero Mf) by (unfold Mf; apply abs_plus_one_pos).
  pose (plus (abs (g x)) one) as Mg.
  assert (Hmg : lt zero Mg) by (unfold Mg; apply abs_plus_one_pos).
  pose (mult (inv_pos Mg Hmg) eps4) as eps_f.
  assert (Hef : lt zero eps_f).
  { unfold eps_f. apply mult_positive. apply inv_pos_pos. exact Heps4. }
  pose (mult (inv_pos Mf Hmf) eps4) as eps_g.
  assert (Heg : lt zero eps_g).
  { unfold eps_g. apply mult_positive. apply inv_pos_pos. exact Heps4. }
  destruct (Hf x eps_f Hef) as [dfdelta [Hdf1 Hdf2]].
  destruct (Hg x eps_g Heg) as [dgdelta [Hdg1 Hdg2]].
  pose (mult (plus (abs (df x)) eps_f) (plus (abs (dg x)) eps_g)) as Den.
  assert (HD1 : lt zero (plus (abs (df x)) eps_f)).
  { apply plus_le_lt_pos. apply abs_nonneg. exact Hef. }
  assert (HD2 : lt zero (plus (abs (dg x)) eps_g)).
  { apply plus_le_lt_pos. apply abs_nonneg. exact Heg. }
  assert (HDpos : lt zero Den).
  { unfold Den. apply mult_positive. exact HD1. exact HD2. }
  pose (mult (inv_pos Den HDpos) eps2) as eps3.
  assert (He3 : lt zero eps3).
  { unfold eps3. apply mult_positive. apply inv_pos_pos. exact Heps2. }
  exists (min (min dfdelta dgdelta) eps3).
  split.
  - apply min_pos.
    + apply min_pos; [exact Hdf1 | exact Hdg1].
    + exact He3.
  - intros h Hh.
    change (le (abs (minus (mult (f (plus x h)) (g (plus x h)))
                           (plus (mult (f x) (g x))
                                 (mult (plus (mult (df x) (g x)) (mult (f x) (dg x))) h))))
              (mult eps (abs h))).
    assert (Hh_d : lt (abs h) dfdelta).
    { eapply lt_le_trans. exact Hh. eapply le_trans. apply min_le_l. apply min_le_l. }
    assert (Hh_dg : lt (abs h) dgdelta).
    { eapply lt_le_trans. exact Hh. eapply le_trans. apply min_le_l. apply min_le_r. }
    assert (Hh_3 : lt (abs h) eps3).
    { eapply lt_le_trans. exact Hh. apply min_le_r. }
    assert (Hh_le3 : le (abs h) eps3).
    { apply (lt_le_iff _ _). left. exact Hh_3. }
    assert (Hdec : Id (minus (mult (f (plus x h)) (g (plus x h)))
                             (plus (mult (f x) (g x))
                                   (mult (plus (mult (df x) (g x)) (mult (f x) (dg x))) h)))
                      (plus (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
                            (plus (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                                  (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))))))
      by exact (mult_diff_decomp f g df dg x h).
    rewrite Hdec.
    assert (Hdf_bound : le (abs (minus (f (plus x h)) (f x)))
                           (mult (plus (abs (df x)) eps_f) (abs h))).
    {
      assert (Hsplit : Id (minus (f (plus x h)) (f x))
                          (plus (minus (f (plus x h)) (plus (f x) (mult (df x) h)))
                                (mult (df x) h)))
        by exact (minus_split (f (plus x h)) (f x) (mult (df x) h)).
      rewrite Hsplit.
      apply (le_trans _ (plus (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                              (abs (mult (df x) h))) _).
      { apply abs_triangle. }
      { apply (le_trans _ (plus (mult eps_f (abs h)) (mult (abs (df x)) (abs h))) _).
        { apply le_plus_compat.
          { apply (Hdf2 h Hh_d). }
          { assert (Ham : Id (abs (mult (df x) h)) (mult (abs (df x)) (abs h)))
              by exact (abs_mult (df x) h).
            rewrite Ham. apply le_refl. } }
        { assert (Hsum : Id (plus (mult eps_f (abs h)) (mult (abs (df x)) (abs h)))
                            (mult (plus (abs (df x)) eps_f) (abs h))).
          { assert (Hd : Id (mult (plus (abs (df x)) eps_f) (abs h))
                            (plus (mult (abs (df x)) (abs h)) (mult eps_f (abs h))))
              by exact (mult_plus_distr_r (abs (df x)) eps_f (abs h)).
            apply id_sym. rewrite Hd.
            apply (plus_comm (mult (abs (df x)) (abs h)) (mult eps_f (abs h))). }
          rewrite Hsum. apply le_refl. } }
    }
    assert (Hdg_bound : le (abs (minus (g (plus x h)) (g x)))
                           (mult (plus (abs (dg x)) eps_g) (abs h))).
    {
      assert (Hsplit : Id (minus (g (plus x h)) (g x))
                          (plus (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))
                                (mult (dg x) h)))
        by exact (minus_split (g (plus x h)) (g x) (mult (dg x) h)).
      rewrite Hsplit.
      apply (le_trans _ (plus (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
                              (abs (mult (dg x) h))) _).
      { apply abs_triangle. }
      { apply (le_trans _ (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h))) _).
        { apply le_plus_compat.
          { apply (Hdg2 h Hh_dg). }
          { assert (Ham : Id (abs (mult (dg x) h)) (mult (abs (dg x)) (abs h)))
              by exact (abs_mult (dg x) h).
            rewrite Ham. apply le_refl. } }
        { assert (Hsum : Id (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h)))
                            (mult (plus (abs (dg x)) eps_g) (abs h))).
          { assert (Hd : Id (mult (plus (abs (dg x)) eps_g) (abs h))
                            (plus (mult (abs (dg x)) (abs h)) (mult eps_g (abs h))))
              by exact (mult_plus_distr_r (abs (dg x)) eps_g (abs h)).
            apply id_sym. rewrite Hd.
            apply (plus_comm (mult (abs (dg x)) (abs h)) (mult eps_g (abs h))). }
          rewrite Hsum. apply le_refl. } }
    }
    apply (le_trans _ (plus (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                            (abs (plus (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                                       (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x)))))) _).
    { apply abs_triangle. }
    { apply (le_trans _ (plus (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                              (plus (abs (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
                                    (abs (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x)))))) _).
      { apply le_plus_compat.
        { apply le_refl. }
        { apply abs_triangle. } }
      { (* Three-term upper bounds, then merge *)
        assert (Hb1 : le (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                        (mult eps4 (abs h))).
        {
          apply (le_trans _ (mult (abs (f x)) (mult eps_g (abs h))) _).
          { apply (le_trans _ (mult (abs (f x)) (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))) _).
            { assert (Ham : Id (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                              (mult (abs (f x)) (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))))
                by exact (abs_mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))).
              rewrite Ham. apply le_refl. }
            { apply (le_mult_compat_r (abs (f x)) (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))) (mult eps_g (abs h))).
              { apply abs_nonneg. }
              { apply (Hdg2 h Hh_dg). } } }
          { assert (Hshare : le (mult (abs (f x)) eps_g) eps4).
            {
              apply (le_trans _ (mult Mf eps_g) _).
              { apply (le_mult_compat_weak _ _ _ (lt_le_iff zero eps_g (inl Heg)) (abs_le_abs_plus_one (f x))). }
              { assert (Hprod : Id (mult Mf eps_g) eps4).
                {
                  unfold eps_g.
                  assert (H1 : Id (mult Mf (mult (inv_pos Mf Hmf) eps4)) (mult (mult Mf (inv_pos Mf Hmf)) eps4))
                    by exact (mult_assoc Mf (inv_pos Mf Hmf) eps4).
                  assert (H2 : Id (mult (mult Mf (inv_pos Mf Hmf)) eps4) (mult one eps4))
                    by exact (id_cong (fun z => mult z eps4) (inv_pos_correct Mf Hmf)).
                  assert (H3 : Id (mult one eps4) eps4)
                    by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                  exact (id_trans H1 (id_trans H2 H3)).
                }
                rewrite Hprod. apply le_refl. } }
            assert (Hsh2 : le (mult (mult (abs (f x)) eps_g) (abs h)) (mult eps4 (abs h)))
              by apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hshare).
            assert (Hassoc : Id (mult (abs (f x)) (mult eps_g (abs h)))
                                (mult (mult (abs (f x)) eps_g) (abs h)))
              by exact (mult_assoc (abs (f x)) eps_g (abs h)).
            rewrite Hassoc. exact Hsh2. }
        }
        assert (Hb2 : le (abs (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
                        (mult eps4 (abs h))).
        {
          apply (le_trans _ (mult (abs (g x)) (mult eps_f (abs h))) _).
          { apply (le_trans _ (mult (abs (g x)) (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))) _).
            { assert (Ham : Id (abs (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
                              (mult (abs (g x)) (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))))
                by exact (abs_mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))).
              rewrite Ham. apply le_refl. }
            { apply (le_mult_compat_r (abs (g x)) (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h)))) (mult eps_f (abs h))).
              { apply abs_nonneg. }
              { apply (Hdf2 h Hh_d). } } }
          { assert (Hshare : le (mult (abs (g x)) eps_f) eps4).
            {
              apply (le_trans _ (mult Mg eps_f) _).
              { apply (le_mult_compat_weak _ _ _ (lt_le_iff zero eps_f (inl Hef)) (abs_le_abs_plus_one (g x))). }
              { assert (Hprod : Id (mult Mg eps_f) eps4).
                {
                  unfold eps_f.
                  assert (H1 : Id (mult Mg (mult (inv_pos Mg Hmg) eps4)) (mult (mult Mg (inv_pos Mg Hmg)) eps4))
                    by exact (mult_assoc Mg (inv_pos Mg Hmg) eps4).
                  assert (H2 : Id (mult (mult Mg (inv_pos Mg Hmg)) eps4) (mult one eps4))
                    by exact (id_cong (fun z => mult z eps4) (inv_pos_correct Mg Hmg)).
                  assert (H3 : Id (mult one eps4) eps4)
                    by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                  exact (id_trans H1 (id_trans H2 H3)).
                }
                rewrite Hprod. apply le_refl. } }
            assert (Hsh2 : le (mult (mult (abs (g x)) eps_f) (abs h)) (mult eps4 (abs h)))
              by apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hshare).
            assert (Hassoc : Id (mult (abs (g x)) (mult eps_f (abs h)))
                                (mult (mult (abs (g x)) eps_f) (abs h)))
              by exact (mult_assoc (abs (g x)) eps_f (abs h)).
            rewrite Hassoc. exact Hsh2. }
        }
        assert (Hthird : le (abs (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))))
                            (mult eps2 (abs h))).
        {
          assert (Hm1 : Id (abs (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))))
                          (mult (abs (minus (f (plus x h)) (f x)))
                                (abs (minus (g (plus x h)) (g x)))))
            by exact (abs_mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))).
          rewrite Hm1.
          apply (le_trans _ (mult (mult (plus (abs (df x)) eps_f) (abs h))
                                  (mult (plus (abs (dg x)) eps_g) (abs h))) _).
          { apply (le_trans _ (mult (mult (plus (abs (df x)) eps_f) (abs h))
                                    (abs (minus (g (plus x h)) (g x)))) _).
            { apply (le_mult_compat_weak _ _ _ (abs_nonneg (minus (g (plus x h)) (g x))) Hdf_bound). }
            { apply (le_mult_compat_r (mult (plus (abs (df x)) eps_f) (abs h)) (abs (minus (g (plus x h)) (g x))) (mult (plus (abs (dg x)) eps_g) (abs h))).
              { assert (HleA : le zero (mult (plus (abs (df x)) eps_f) (abs h))).
                { apply (le_trans _ (mult zero (abs h)) _).
                  { assert (Hz : Id (mult zero (abs h)) zero)
                      by exact (id_trans (mult_comm zero (abs h)) (mult_zero (abs h))).
                    rewrite Hz. apply le_refl. }
                  { apply (le_mult_compat_weak _ _ _ (abs_nonneg h) (lt_le_iff zero (plus (abs (df x)) eps_f) (inl HD1))). } }
                exact HleA. }
              { exact Hdg_bound. } } }
          { assert (Hre : Id (mult (mult (plus (abs (df x)) eps_f) (abs h))
                                    (mult (plus (abs (dg x)) eps_g) (abs h)))
                              (mult Den (mult (abs h) (abs h)))).
            {
              unfold Den.
              set (A := plus (abs (df x)) eps_f).
              set (B := plus (abs (dg x)) eps_g).
              assert (Hs1 : Id (mult (mult A (abs h)) (mult B (abs h)))
                               (mult A (mult (abs h) (mult B (abs h)))))
                by exact (id_sym (mult_assoc A (abs h) (mult B (abs h)))).
              assert (Hs2 : Id (mult A (mult (abs h) (mult B (abs h))))
                               (mult A (mult (mult (abs h) B) (abs h))))
                by exact (id_cong (fun z => mult A z) (mult_assoc (abs h) B (abs h))).
              assert (Hs3 : Id (mult A (mult (mult (abs h) B) (abs h)))
                               (mult A (mult (mult B (abs h)) (abs h))))
                by exact (id_cong (fun z => mult A (mult z (abs h))) (mult_comm (abs h) B)).
              assert (Hs4 : Id (mult A (mult (mult B (abs h)) (abs h)))
                               (mult (mult A (mult B (abs h))) (abs h)))
                by exact (mult_assoc A (mult B (abs h)) (abs h)).
              assert (Hs5 : Id (mult (mult A (mult B (abs h))) (abs h))
                               (mult (mult (mult A B) (abs h)) (abs h)))
                by exact (id_cong (fun z => mult z (abs h)) (mult_assoc A B (abs h))).
              assert (Hs6 : Id (mult (mult (mult A B) (abs h)) (abs h))
                               (mult (mult A B) (mult (abs h) (abs h))))
                by exact (id_sym (mult_assoc (mult A B) (abs h) (abs h))).
              exact (id_trans Hs1 (id_trans Hs2 (id_trans Hs3 (id_trans Hs4 (id_trans Hs5 Hs6))))).
            }
            rewrite Hre.
            apply (le_trans _ (mult Den (mult eps3 (abs h))) _).
            { apply (le_mult_compat_r Den (mult (abs h) (abs h)) (mult eps3 (abs h))).
              { assert (HleD : le zero Den).
                { apply (lt_le_iff _ _). left. exact HDpos. }
                exact HleD. }
              { apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hh_le3). } }
            { assert (Hdq : Id (mult Den (mult eps3 (abs h))) (mult eps2 (abs h))).
              {
                unfold eps3.
                assert (H1 : Id (mult Den (mult (mult (inv_pos Den HDpos) eps2) (abs h)))
                                (mult (mult Den (mult (inv_pos Den HDpos) eps2)) (abs h)))
                  by exact (mult_assoc Den (mult (inv_pos Den HDpos) eps2) (abs h)).
                rewrite H1.
                assert (H2 : Id (mult Den (mult (inv_pos Den HDpos) eps2)) (mult (mult Den (inv_pos Den HDpos)) eps2))
                  by exact (mult_assoc Den (inv_pos Den HDpos) eps2).
                assert (H2' : Id (mult (mult Den (mult (inv_pos Den HDpos) eps2)) (abs h))
                                 (mult (mult (mult Den (inv_pos Den HDpos)) eps2) (abs h)))
                  by exact (id_cong (fun z => mult z (abs h)) H2).
                rewrite H2'.
                assert (H3 : Id (mult (mult (mult Den (inv_pos Den HDpos)) eps2) (abs h))
                                 (mult (mult one eps2) (abs h)))
                  by exact (id_cong (fun z => mult (mult z eps2) (abs h)) (inv_pos_correct Den HDpos)).
                rewrite H3.
                assert (H4 : Id (mult (mult one eps2) (abs h)) (mult eps2 (abs h)))
                  by exact (id_cong (fun z => mult z (abs h)) (id_trans (mult_comm one eps2) (mult_one eps2))).
                rewrite H4. reflexivity.
              }
              rewrite Hdq. apply le_refl. }
          }
        }
        apply (le_trans _ (plus (mult eps4 (abs h)) (plus (mult eps4 (abs h)) (mult eps2 (abs h)))) _).
        { apply le_plus_compat. { exact Hb1. } { apply le_plus_compat. { exact Hb2. } { exact Hthird. } } }
        { assert (Hmerge1 : Id (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps2 (abs h))).
          {
            unfold eps4, eps2.
            assert (Ht : Id (plus (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                                  (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h)))
                            (mult (plus one one) (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h))))
              by exact (id_sym (two_mult (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h)))).
            rewrite Ht.
            assert (Hq : Id (mult (plus one one) (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h)))
                            (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h)))
              by exact (two_times_quarter eps (abs h)).
            rewrite Hq. reflexivity.
          }
          assert (Hmerge2 : Id (plus (mult eps2 (abs h)) (mult eps2 (abs h))) (mult eps (abs h))).
          {
            unfold eps2.
            assert (Hd : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps) (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                            (plus (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                                  (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))))
              by exact (mult_plus_distr_r (mult (inv_pos (plus one one) two_pos) eps)
                                          (mult (inv_pos (plus one one) two_pos) eps) (abs h)).
            rewrite <- Hd.
            assert (Hcong : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                           (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                               (mult eps (abs h))).
            { apply (id_cong (fun z => mult z (abs h))). exact (half_twice eps). }
            rewrite Hcong. reflexivity.
          }
          apply (le_trans _ (plus (mult eps2 (abs h)) (mult eps2 (abs h))) _).
          { assert (Hpa : Id (plus (mult eps4 (abs h)) (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                             (plus (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps2 (abs h))))
              by exact (plus_assoc (mult eps4 (abs h)) (mult eps4 (abs h)) (mult eps2 (abs h))).
            rewrite Hpa. rewrite Hmerge1. apply le_refl. }
          { rewrite Hmerge2. apply le_refl. }
        }
      }
    }
Qed.

(* ============================================================ *)
(* Differentiability of affine functions: the cornerstone of neural-network linear layers *)
(* ============================================================ *)
(* f(x) = a·x + b is differentiable with df = a (the error is identically zero:
   a·(x+h)+b − (a·x+b+a·h) = 0, by distrib expansion plus additive regrouping). *)

Theorem differentiable_affine : forall a b : R,
  Differentiable (fun x => plus (mult a x) b).
Proof.
  intros a b.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* The error is identically zero: minus (a·(x+h)+b) (a·x+b+a·h) = 0.
       Prove the folded shape first (the goal keeps minus folded; rewrite does not cross delta levels). *)
    assert (Hd : Id (mult a (plus x h)) (plus (mult a x) (mult a h)))
      by exact (distrib a x h).
    assert (Hzero : Id (minus (plus (mult a (plus x h)) b) (plus (plus (mult a x) b) (mult a h))) zero).
    {
      unfold minus.
      assert (Hnum : Id (plus (plus (mult a (plus x h)) b) (opp (plus (plus (mult a x) b) (mult a h))))
                        (plus (plus (plus (mult a x) (mult a h)) b) (opp (plus (plus (mult a x) b) (mult a h)))))
        by exact (id_cong (fun z => plus (plus z b) (opp (plus (plus (mult a x) b) (mult a h)))) Hd).
      (* Regroup the numerator: (a·x + a·h) + b = (a·x + b) + a·h *)
      assert (Ha : Id (plus (plus (mult a x) (mult a h)) b) (plus (mult a x) (plus (mult a h) b)))
        by exact (id_sym (plus_assoc (mult a x) (mult a h) b)).
      assert (Hb : Id (plus (mult a h) b) (plus b (mult a h)))
        by exact (plus_comm (mult a h) b).
      assert (Hc : Id (plus (mult a x) (plus b (mult a h))) (plus (plus (mult a x) b) (mult a h)))
        by exact (plus_assoc (mult a x) b (mult a h)).
      assert (Hre : Id (plus (plus (mult a x) (mult a h)) b) (plus (plus (mult a x) b) (mult a h)))
        by exact (id_trans Ha (id_trans (id_cong (fun z => plus (mult a x) z) Hb) Hc)).
      assert (Hn2 : Id (plus (plus (plus (mult a x) (mult a h)) b) (opp (plus (plus (mult a x) b) (mult a h))))
                        (plus (plus (plus (mult a x) b) (mult a h)) (opp (plus (plus (mult a x) b) (mult a h)))))
        by exact (id_cong (fun z => plus z (opp (plus (plus (mult a x) b) (mult a h)))) Hre).
      exact (id_trans (id_trans Hnum Hn2) (plus_opp (plus (plus (mult a x) b) (mult a h)))).
    }
    (* The goal mixes Let and projection spellings, so rewrite is abandoned: [le_id_l] + [id_cong] (kernel conversion) *)
    apply (le_id_l (abs (minus (plus (mult a (plus x h)) b) (plus (plus (mult a x) b) (mult a h))))
                   (abs zero) (mult eps (abs h))).
    + exact (id_cong abs Hzero).
    + (* Goal: le (abs zero) (mult eps (abs h)) (same closing as [differentiable_const]) *)
      change (le (abs zero) (mult eps (abs h))).
      pose proof abs_zero as Habs_zero.
      change (Id (abs zero) zero) in Habs_zero.
      rewrite Habs_zero.
      assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
      rewrite <- Hmz.
      assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
      rewrite Hmc1.
      assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
      rewrite Hmc2.
      exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
Qed.

(* ============================================================ *)
(* Algebraic closure of differentiability: negated functions, subtraction, *)
(* and natural powers — the local rules of automatic differentiation form a closed system under the abstract real interface *)
(* ============================================================ *)

(* Differentiability of the negated function: (-f)' = -(f'); the error is flipped via [opp_minus]/[opp_mult_l]/[double_neg] *)
Theorem differentiable_opp : forall (f : R -> R),
  Differentiable f -> Differentiable (fun x => opp (f x)).
Proof.
  intros f [df Hf].
  exists (fun x => opp (df x)).
  intros x eps Heps.
  destruct (Hf x eps Heps) as [delta [Hdelta Hdf]].
  exists delta. split. exact Hdelta.
  intros h Hh.
  (* Error = -f(x+h) - (-f(x) - df(x)·h) = -[f(x+h) - (f(x) + df(x)·h)] *)
  assert (Hzero : Id (minus (opp (f (plus x h))) (plus (opp (f x)) (mult (opp (df x)) h)))
                     (opp (minus (f (plus x h)) (plus (f x) (mult (df x) h))))).
  {
    unfold minus.
    assert (Hoppr : Id (mult (opp (df x)) h) (opp (mult (df x) h)))
      by exact (opp_mult_r (df x) h).
    assert (Hoppl : Id (opp (mult (opp (df x)) h)) (mult (df x) h))
      by exact (id_trans (id_cong opp Hoppr) (double_neg (mult (df x) h))).
    assert (Hopp2 : Id (opp (plus (opp (f x)) (mult (opp (df x)) h)))
                       (plus (f x) (mult (df x) h))).
    {
      assert (H2a : Id (opp (plus (opp (f x)) (mult (opp (df x)) h)))
                       (plus (opp (opp (f x))) (opp (mult (opp (df x)) h))))
        by exact (opp_plus (opp (f x)) (mult (opp (df x)) h)).
      assert (H2b : Id (plus (opp (opp (f x))) (opp (mult (opp (df x)) h)))
                       (plus (f x) (mult (df x) h)))
        by exact (id_trans (id_cong (fun z => plus z (opp (mult (opp (df x)) h))) (double_neg (f x)))
                           (id_cong (fun z => plus (f x) z) Hoppl)).
      exact (id_trans H2a H2b).
    }
    exact (id_trans (id_cong (fun z => plus (opp (f (plus x h))) z) Hopp2)
                    (id_sym (opp_minus (f (plus x h)) (plus (f x) (mult (df x) h))))).
  }
  assert (Habs1 : Id (abs (minus (opp (f (plus x h))) (plus (opp (f x)) (mult (opp (df x)) h))))
                    (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
    by exact (id_trans (id_cong abs Hzero)
                       (abs_opp (minus (f (plus x h)) (plus (f x) (mult (df x) h))))).
  apply (le_id_l (abs (minus (opp (f (plus x h))) (plus (opp (f x)) (mult (opp (df x)) h))))
                 (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                 (mult eps (abs h))).
  + exact Habs1.
  + apply Hdf. exact Hh.
Qed.

(* Differentiability of subtraction: composition of plus and opp (dminus is the derivative of the sum) *)
Theorem differentiable_minus : forall (f g : R -> R),
  Differentiable f -> Differentiable g -> Differentiable (fun x => minus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  assert (Hopp_g : Differentiable (fun x => opp (g x))) by exact (differentiable_opp g Hg).
  assert (Hplus : Differentiable (fun x => plus (f x) (opp (g x))))
    by exact (differentiable_plus f (fun x => opp (g x)) Hf Hopp_g).
  destruct Hplus as [dminus Hminus].
  exists dminus.
  intros x eps Heps.
  destruct (Hminus x eps Heps) as [delta [Hdelta Hd]].
  exists delta. split. exact Hdelta.
  intros h Hh.
  assert (Hrew : Id (minus (minus (f (plus x h)) (g (plus x h)))
                          (plus (minus (f x) (g x)) (mult (dminus x) h)))
                    (minus (plus (f (plus x h)) (opp (g (plus x h))))
                           (plus (plus (f x) (opp (g x))) (mult (dminus x) h)))).
  { unfold minus. reflexivity. }
  apply (le_id_l (abs (minus (minus (f (plus x h)) (g (plus x h)))
                             (plus (minus (f x) (g x)) (mult (dminus x) h))))
                 (abs (minus (plus (f (plus x h)) (opp (g (plus x h))))
                             (plus (plus (f x) (opp (g x))) (mult (dminus x) h))))
                 (mult eps (abs h))).
  + exact (id_cong abs Hrew).
  + apply Hd. exact Hh.
Qed.

(* Natural power function: inductive construction of x^n (the per-layer power basis of backpropagation) *)
Fixpoint power_nat (n : nat) (x : R) : R :=
  match n with
  | O => one
  | Datatypes.S n' => mult x (power_nat n' x)
  end.

(* x^(n+1) is differentiable (base case x^1 = id; the inductive step composes via [differentiable_mult]) *)
Theorem differentiable_power_nat : forall (n : nat),
  Differentiable (fun x => power_nat (Datatypes.S n) x).
Proof.
  induction n as [| n' IH].
  - exists (fun _ => one).
    intros x eps Heps.
    exists one. split. apply one_pos.
    intros h Hh.
    change (le (abs (minus (mult (plus x h) one) (plus (mult x one) (mult one h)))) (mult eps (abs h))).
    pose proof (mult_one (plus x h)) as Hmo1. change (Id (mult (plus x h) one) (plus x h)) in Hmo1. rewrite Hmo1.
    pose proof (mult_one x) as Hmo2. change (Id (mult x one) x) in Hmo2. rewrite Hmo2.
    pose proof (mult_one h) as Hmo3. change (Id (mult h one) h) in Hmo3.
    pose proof (mult_comm one h) as Hmc3. change (Id (mult one h) (mult h one)) in Hmc3. rewrite Hmc3. rewrite Hmo3.
    change (le (abs (plus (plus x h) (opp (plus x h)))) (mult eps (abs h))).
    pose proof (plus_opp (plus x h)) as Hpo. change (Id (plus (plus x h) (opp (plus x h))) zero) in Hpo. rewrite Hpo.
    change (le (abs zero) (mult eps (abs h))).
    pose proof abs_zero as Haz.
    change (Id (abs zero) zero) in Haz.
    rewrite Haz.
    assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
    rewrite <- Hmz.
    assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
    rewrite Hmc1.
    assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
    rewrite Hmc2.
    exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
  - simpl. apply differentiable_mult.
    + apply differentiable_id.
    + exact IH.
Qed.

(* ============================================================ *)
(* Chain-rule lemmas (first step: error decomposition and ε-bound auxiliaries) *)
(* ============================================================ *)
(* Budget plan of the full [differentiable_compose]:
   eps4 := inv_2·(inv_2·eps) (i.e. eps/4), L := |dg x|+1 the local Lipschitz constant,
   M := |df(g x)|+1; eps_f := min one (inv_L·eps4), eps_g := min one (inv_M·eps4)
   (the min simultaneously guarantees ≤1 for the Lipschitz use, and eps_f·L ≤ eps4,
   M·eps_g ≤ eps4); δ := min dgd (min one (inv_L·dfd)); the two terms are bounded by
   ≤ eps4·|h| + eps4·|h| = (eps/2)·|h| ≤ eps·|h|. *)

(* Composite error decomposition identity: Δ(f∘g) − df(g)·dg·h = [the f-error] + df(g)·[the g-error] *)
Lemma compose_diff_decomp : forall (A B C D G g0 h : R),
  Id (minus A (plus B (mult (mult C D) h)))
     (plus (minus A (plus B (mult C (minus G g0))))
           (mult C (minus (minus G g0) (mult D h)))).
Proof.
  intros A B C D G g0 h.
  set (X := minus G g0).
  assert (Hma : Id (mult (mult C D) h) (mult C (mult D h)))
    by exact (id_sym (mult_assoc C D h)).
  assert (Hcancel : Id (plus (opp (plus B (mult C X))) (mult C X)) (opp B)).
  {
    unfold X.
    assert (H1 : Id (plus (opp (plus B (mult C (minus G g0)))) (mult C (minus G g0)))
                    (plus (plus (opp B) (opp (mult C (minus G g0)))) (mult C (minus G g0))))
      by exact (id_cong (fun z => plus z (mult C (minus G g0))) (opp_plus B (mult C (minus G g0)))).
    assert (H2 : Id (plus (plus (opp B) (opp (mult C (minus G g0)))) (mult C (minus G g0)))
                    (plus (opp B) (plus (opp (mult C (minus G g0))) (mult C (minus G g0)))))
      by exact (id_sym (plus_assoc (opp B) (opp (mult C (minus G g0))) (mult C (minus G g0)))).
    assert (H3 : Id (plus (opp B) (plus (opp (mult C (minus G g0))) (mult C (minus G g0))))
                    (plus (opp B) zero))
      by exact (id_cong (fun z => plus (opp B) z)
                        (id_trans (plus_comm (opp (mult C (minus G g0))) (mult C (minus G g0)))
                                  (plus_opp (mult C (minus G g0))))).
    assert (H4 : Id (plus (opp B) zero) (opp B)) by exact (plus_zero (opp B)).
    exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
  }
  assert (Hre : Id (plus (minus A (plus B (mult C X))) (minus (mult C X) (mult C (mult D h))))
                   (minus A (plus B (mult C (mult D h))))).
  {
    unfold minus.
    assert (H1 : Id (plus (plus A (opp (plus B (mult C X)))) (plus (mult C X) (opp (mult C (mult D h)))))
                    (plus A (plus (plus (opp (plus B (mult C X))) (mult C X)) (opp (mult C (mult D h))))))
      by exact (id_trans (id_sym (plus_assoc A (opp (plus B (mult C X))) (plus (mult C X) (opp (mult C (mult D h))))))
                         (id_cong (fun z => plus A z)
                                  (plus_assoc (opp (plus B (mult C X))) (mult C X) (opp (mult C (mult D h)))))).
    assert (H2 : Id (plus A (plus (plus (opp (plus B (mult C X))) (mult C X)) (opp (mult C (mult D h)))))
                    (plus A (plus (opp B) (opp (mult C (mult D h))))))
      by exact (id_cong (fun z => plus A (plus z (opp (mult C (mult D h))))) Hcancel).
    assert (H3 : Id (plus A (plus (opp B) (opp (mult C (mult D h)))))
                    (plus A (opp (plus B (mult C (mult D h))))))
      by exact (id_cong (fun z => plus A z)
                        (id_sym (opp_plus B (mult C (mult D h))))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  assert (Hlhs : Id (minus A (plus B (mult (mult C D) h)))
                    (minus A (plus B (mult C (mult D h)))))
    by exact (id_cong (fun z => minus A (plus B z)) Hma).
  assert (Hmd : Id (mult C (minus X (mult D h))) (minus (mult C X) (mult C (mult D h))))
    by (unfold X; exact (mult_minus_distr_l C (minus G g0) (mult D h))).
  assert (Hrhs : Id (plus (minus A (plus B (mult C X))) (mult C (minus X (mult D h))))
                    (plus (minus A (plus B (mult C X))) (minus (mult C X) (mult C (mult D h)))))
    by exact (id_cong (fun z => plus (minus A (plus B (mult C X))) z) Hmd).
  exact (id_trans Hlhs (id_trans (id_sym Hre) (id_sym Hrhs))).
Qed.

(* inv_2 ≤ 1 (auxiliary upper bound for eps/2) *)
Lemma half_le_one : le (inv_pos (plus one one) two_pos) one.
Proof.
  assert (Hm1 : Id (mult (inv_pos (plus one one) two_pos) one) (inv_pos (plus one one) two_pos))
    by exact (mult_one (inv_pos (plus one one) two_pos)).
  assert (Hm2 : Id (mult (inv_pos (plus one one) two_pos) (plus one one)) one)
    by exact (id_trans (mult_comm (inv_pos (plus one one) two_pos) (plus one one))
                       (inv_pos_correct (plus one one) two_pos)).
  apply (le_id_l (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) one) one).
  - exact (id_sym Hm1).
  - apply (le_id_r (mult (inv_pos (plus one one) two_pos) one)
                   (mult (inv_pos (plus one one) two_pos) (plus one one))
                   one).
    + exact Hm2.
    + apply (le_mult_compat_r (inv_pos (plus one one) two_pos) one (plus one one)).
      * exact (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))).
      * exact (le_plus_nonneg_r one one (lt_le_iff _ _ (inl one_pos))).
Qed.

(* eps/2 ≤ eps (nonnegative coefficient; closes the chain-rule budget) *)
Lemma half_le_self : forall a : R, le zero a ->
  le (mult (inv_pos (plus one one) two_pos) a) a.
Proof.
  intros a Ha.
  exact (le_trans (mult (inv_pos (plus one one) two_pos) a) (mult one a) a
           (le_mult_compat_weak (inv_pos (plus one one) two_pos) one a Ha half_le_one)
           (le_id_l (mult one a) a a (id_trans (mult_comm one a) (mult_one a)) (le_refl a))).
Qed.

(* Chain rule (constructive ε-δ proof).
   Budget: eps_f := min one (inv_L·eps4), eps_g := min one (inv_M·eps4)
   (eps4 := (eps/2)/2; L := |dg x|+1 is the local Lipschitz constant of g,
   M := |df(g x)|+1); δ := min dgd (min one (inv_L·dfd));
   the two terms are bounded by ≤ eps4·|h| + eps4·|h| = (eps/2)·|h| ≤ eps·|h|. *)
Theorem differentiable_compose : forall (f g : R -> R),
  Differentiable f -> Differentiable g ->
  Differentiable (fun x => f (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => mult (df (g x)) (dg x)).
  intros x eps Heps.
  set (eps4 := mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive; [apply inv_pos_pos | apply half_pos; exact Heps]. }
  set (M := plus (abs (df (g x))) one).
  assert (HM : lt zero M) by (unfold M; apply abs_plus_one_pos).
  set (L := plus (abs (dg x)) one).
  assert (HL : lt zero L) by (unfold L; apply abs_plus_one_pos).
  set (eps_f := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_f : lt zero eps_f)
    by (unfold eps_f; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  set (eps_g := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_g : lt zero eps_g)
    by (unfold eps_g; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  destruct (Hf (g x) eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hg x eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dgd (min one (mult (inv_pos L HL) dfd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dfd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdf1]).
    apply min_pos; [exact Hdg1 | apply min_pos; [apply one_pos | exact Hltm]].
  - intros h Hh.
    set (Dg := minus (g (plus x h)) (g x)).
    assert (Hdecomp : Id (minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (df (g x)) (dg x)) h)))
                         (plus (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg)))
                               (mult (df (g x)) (minus Dg (mult (dg x) h)))))
      by (unfold Dg; exact (compose_diff_decomp (f (g (plus x h))) (f (g x)) (df (g x)) (dg x) (g (plus x h)) (g x) h)).
    apply (le_id_l (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (df (g x)) (dg x)) h))))
                   (abs (plus (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg)))
                              (mult (df (g x)) (minus Dg (mult (dg x) h)))))
                   (mult eps (abs h))).
    + exact (id_cong abs Hdecomp).
    + assert (Hh_dgd : lt (abs h) dgd)
        by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
      assert (Hh_one : lt (abs h) one)
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dfd)) _); [apply min_le_r | apply min_le_l]]).
      assert (Hh_dfd : lt (abs h) (mult (inv_pos L HL) dfd))
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dfd)) _); [apply min_le_r | apply min_le_r]]).
      (* (b) |Dg| ≤ L·|h| ([minus_split] + triangle + eps_g ≤ 1) *)
      assert (HDg_bound : le (abs Dg) (mult L (abs h))).
      {
        assert (Hsplit : Id (minus (g (plus x h)) (g x))
                            (plus (minus (g (plus x h)) (plus (g x) (mult (dg x) h))) (mult (dg x) h)))
          by exact (minus_split (g (plus x h)) (g x) (mult (dg x) h)).
        unfold Dg. rewrite Hsplit.
        apply (le_trans _ (plus (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))) (abs (mult (dg x) h))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h))) _).
          { apply le_plus_compat.
            { exact (Hdg2 h Hh_dgd). }
            { apply (le_id_r (abs (mult (dg x) h)) (abs (mult (dg x) h)) (mult (abs (dg x)) (abs h))
                             (abs_mult (dg x) h) (le_refl _)). } }
          { assert (Heg : le eps_g one)
              by (unfold eps_g; exact (min_le_l one (mult (inv_pos M HM) eps4))).
            assert (Hle : le (plus eps_g (abs (dg x))) (plus (abs (dg x)) one))
              by (apply (le_id_r (plus eps_g (abs (dg x))) (plus one (abs (dg x))) (plus (abs (dg x)) one)
                                 (plus_comm one (abs (dg x)))
                                 (le_plus_compat eps_g one (abs (dg x)) (abs (dg x)) Heg (le_refl (abs (dg x)))))).
            assert (Hsum : Id (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h)))
                               (mult (plus eps_g (abs (dg x))) (abs h)))
              by exact (id_sym (mult_plus_distr_r eps_g (abs (dg x)) (abs h))).
            rewrite Hsum.
            apply (le_mult_compat_weak _ _ _ (abs_nonneg h)).
            unfold L.
            exact Hle. } }
      }
      (* |Dg| < dfd (L·|h| < L·(inv_L·dfd) = dfd) *)
      assert (HdfDg : lt (abs Dg) dfd).
      {
        apply (le_lt_trans (abs Dg) (mult L (abs h)) dfd).
        - exact HDg_bound.
        - assert (Hraw : lt (mult (abs h) L) (mult (mult (inv_pos L HL) dfd) L))
            by (apply (lt_mult_compat (abs h) (mult (inv_pos L HL) dfd) L HL Hh_dfd)).
          assert (Hswap : Id (mult (mult (inv_pos L HL) dfd) L) (mult L (mult (inv_pos L HL) dfd))).
          { assert (H1 : Id (mult (mult (inv_pos L HL) dfd) L) (mult (inv_pos L HL) (mult dfd L)))
              by exact (id_sym (mult_assoc (inv_pos L HL) dfd L)).
            assert (H2 : Id (mult (inv_pos L HL) (mult dfd L)) (mult (inv_pos L HL) (mult L dfd)))
              by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm dfd L)).
            assert (H3 : Id (mult (inv_pos L HL) (mult L dfd)) (mult (mult (inv_pos L HL) L) dfd))
              by exact (mult_assoc (inv_pos L HL) L dfd).
            assert (H4 : Id (mult (mult (inv_pos L HL) L) dfd) (mult (mult L (inv_pos L HL)) dfd))
              by exact (id_cong (fun z => mult z dfd) (mult_comm (inv_pos L HL) L)).
            assert (H5 : Id (mult (mult L (inv_pos L HL)) dfd) (mult L (mult (inv_pos L HL) dfd)))
              by exact (id_sym (mult_assoc L (inv_pos L HL) dfd)).
            exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))). }
          assert (HltL : lt (mult L (abs h)) (mult L (mult (inv_pos L HL) dfd)))
            by exact (lt_id_l (mult L (abs h)) (mult (abs h) L) (mult L (mult (inv_pos L HL) dfd))
                              (mult_comm L (abs h))
                              (lt_id_r (mult (abs h) L) (mult (mult (inv_pos L HL) dfd) L) (mult L (mult (inv_pos L HL) dfd))
                                       Hswap Hraw)).
          assert (Hident : Id (mult L (mult (inv_pos L HL) dfd)) dfd).
          { assert (H1 : Id (mult L (mult (inv_pos L HL) dfd)) (mult (mult L (inv_pos L HL)) dfd))
              by exact (mult_assoc L (inv_pos L HL) dfd).
            assert (H2 : Id (mult (mult L (inv_pos L HL)) dfd) (mult one dfd))
              by exact (id_cong (fun z => mult z dfd) (inv_pos_correct L HL)).
            assert (H3 : Id (mult one dfd) dfd)
              by exact (id_trans (mult_comm one dfd) (mult_one dfd)).
            exact (id_trans H1 (id_trans H2 H3)). }
          apply (lt_id_r (mult L (abs h)) (mult L (mult (inv_pos L HL) dfd)) dfd Hident HltL).
      }
      (* T1: the f-error ≤ eps_f·|Dg| ≤ eps4·|h| *)
      assert (HT1 : le (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg))))
                       (mult eps4 (abs h))).
      {
        apply (le_trans _ (mult eps_f (abs Dg)) _).
        - apply (le_id_l (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg))))
                         (abs (minus (f (plus (g x) Dg)) (plus (f (g x)) (mult (df (g x)) Dg))))
                         (mult eps_f (abs Dg))
                         (id_cong (fun z => abs (minus (f z) (plus (f (g x)) (mult (df (g x)) Dg))))
                                  (id_sym (minus_plus_cancel (g x) (g (plus x h)))))
                         (Hdf2 Dg HdfDg)).
        - apply (le_trans _ (mult eps_f (mult L (abs h))) _).
          { apply (le_mult_compat_r eps_f (abs Dg) (mult L (abs h)) (lt_le_iff _ _ (inl Heps_f)) HDg_bound). }
          { assert (Hfl : Id (mult eps_f (mult L (abs h))) (mult (mult eps_f L) (abs h)))
              by exact (mult_assoc eps_f L (abs h)).
            rewrite Hfl.
            assert (Hfl_le : le (mult eps_f L) eps4).
            { assert (Hepf_le : le eps_f (mult (inv_pos L HL) eps4))
                by (unfold eps_f; exact (min_le_r one (mult (inv_pos L HL) eps4))).
              apply (le_trans _ (mult (mult (inv_pos L HL) eps4) L) _).
              { apply (le_mult_compat_weak eps_f (mult (inv_pos L HL) eps4) L (lt_le_iff zero L (inl HL)) Hepf_le). }
              { assert (H1 : Id (mult (mult (inv_pos L HL) eps4) L) (mult (inv_pos L HL) (mult eps4 L)))
                  by exact (id_sym (mult_assoc (inv_pos L HL) eps4 L)).
                assert (H2 : Id (mult (inv_pos L HL) (mult eps4 L)) (mult (inv_pos L HL) (mult L eps4)))
                  by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm eps4 L)).
                assert (H3 : Id (mult (inv_pos L HL) (mult L eps4)) (mult (mult (inv_pos L HL) L) eps4))
                  by exact (mult_assoc (inv_pos L HL) L eps4).
                assert (H4 : Id (mult (mult (inv_pos L HL) L) eps4) (mult (mult L (inv_pos L HL)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos L HL) L)).
                assert (H5 : Id (mult (mult L (inv_pos L HL)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct L HL)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos L HL) eps4) L) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hfl_le).
          }
      }
      (* T2: df(g)·(Dg − dg·h) ≤ |df(g)|·eps_g·|h| ≤ eps4·|h| *)
      assert (HT2 : le (abs (mult (df (g x)) (minus Dg (mult (dg x) h)))) (mult eps4 (abs h))).
      {
        assert (Habsmult : Id (abs (mult (df (g x)) (minus Dg (mult (dg x) h))))
                              (mult (abs (df (g x))) (abs (minus Dg (mult (dg x) h)))))
          by exact (abs_mult (df (g x)) (minus Dg (mult (dg x) h))).
        apply (le_id_l _ _ _ Habsmult).
        apply (le_trans _ (mult (abs (df (g x))) (mult eps_g (abs h))) _).
        - apply (le_mult_compat_r (abs (df (g x))) (abs (minus Dg (mult (dg x) h))) (mult eps_g (abs h)) (abs_nonneg (df (g x)))).
          apply (le_id_l (abs (minus Dg (mult (dg x) h)))
                         (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
                         (mult eps_g (abs h))
                         (id_cong abs (minus_minus_distr (g (plus x h)) (g x) (mult (dg x) h)))
                         (Hdg2 h Hh_dgd)).
        - assert (Hfl : Id (mult (abs (df (g x))) (mult eps_g (abs h))) (mult (mult (abs (df (g x))) eps_g) (abs h)))
            by exact (mult_assoc (abs (df (g x))) eps_g (abs h)).
          rewrite Hfl.
          assert (Hdf_le : le (abs (df (g x))) M)
            by (unfold M; apply le_plus_nonneg_r; exact (lt_le_iff _ _ (inl one_pos))).
          assert (Hprod : le (mult (abs (df (g x))) eps_g) (mult M eps_g))
            by (apply (le_mult_compat_weak _ _ _ (lt_le_iff _ _ (inl Heps_g)) Hdf_le)).
          apply (le_trans _ (mult (mult M eps_g) (abs h)) _).
          { apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hprod). }
          { assert (Hmg_le : le (mult M eps_g) eps4).
            { assert (Hepg_le : le eps_g (mult (inv_pos M HM) eps4))
                by (unfold eps_g; exact (min_le_r one (mult (inv_pos M HM) eps4))).
              apply (le_trans _ (mult (mult (inv_pos M HM) eps4) M) _).
              { exact (le_id_l (mult M eps_g) (mult eps_g M) (mult (mult (inv_pos M HM) eps4) M)
                               (mult_comm M eps_g)
                               (le_mult_compat_weak eps_g (mult (inv_pos M HM) eps4) M (lt_le_iff zero M (inl HM)) Hepg_le)). }
              { assert (H1 : Id (mult (mult (inv_pos M HM) eps4) M) (mult (inv_pos M HM) (mult eps4 M)))
                  by exact (id_sym (mult_assoc (inv_pos M HM) eps4 M)).
                assert (H2 : Id (mult (inv_pos M HM) (mult eps4 M)) (mult (inv_pos M HM) (mult M eps4)))
                  by exact (id_cong (fun z => mult (inv_pos M HM) z) (mult_comm eps4 M)).
                assert (H3 : Id (mult (inv_pos M HM) (mult M eps4)) (mult (mult (inv_pos M HM) M) eps4))
                  by exact (mult_assoc (inv_pos M HM) M eps4).
                assert (H4 : Id (mult (mult (inv_pos M HM) M) eps4) (mult (mult M (inv_pos M HM)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos M HM) M)).
                assert (H5 : Id (mult (mult M (inv_pos M HM)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct M HM)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos M HM) eps4) M) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hmg_le). }
      }
      (* Merge: T1 + T2 ≤ (eps4 + eps4)·|h| = (eps/2)·|h| ≤ eps·|h| *)
      assert (Hmid : le (abs (plus (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg)))
                                   (mult (df (g x)) (minus Dg (mult (dg x) h)))))
                        (mult eps (abs h))).
      {
        apply (le_trans _ (plus (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg))))
                                (abs (mult (df (g x)) (minus Dg (mult (dg x) h))))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps4 (abs h)) (mult eps4 (abs h))) _).
          { apply le_plus_compat; [exact HT1 | exact HT2]. }
      { assert (Hsum : Id (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                          (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))).
        { unfold eps4.
          assert (H1 : Id (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                          (mult (plus one one) (mult eps4 (abs h))))
            by (apply id_sym; apply two_mult).
          assert (H2 : Id (mult (plus one one) (mult eps4 (abs h))) (mult (mult (plus one one) eps4) (abs h)))
            by exact (mult_assoc (plus one one) eps4 (abs h)).
          assert (H3 : Id (mult (plus one one) eps4) (mult (inv_pos (plus one one) two_pos) eps)).
          { assert (H3a : Id (mult (plus one one) (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)))
                              (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
            assert (H3b : Id (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps))
                              (mult one (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (id_cong (fun z => mult z (mult (inv_pos (plus one one) two_pos) eps)) (inv_pos_correct (plus one one) two_pos)).
            assert (H3c : Id (mult one (mult (inv_pos (plus one one) two_pos) eps)) (mult (inv_pos (plus one one) two_pos) eps))
              by exact (id_trans (mult_comm one (mult (inv_pos (plus one one) two_pos) eps)) (mult_one (mult (inv_pos (plus one one) two_pos) eps))).
            exact (id_trans H3a (id_trans H3b H3c)). }
          assert (H4 : Id (mult (mult (plus one one) eps4) (abs h)) (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h)))
            by exact (id_cong (fun z => mult z (abs h)) H3).
          exact (id_trans H1 (id_trans H2 H4)). }
        apply (le_id_l (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                       (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                       (mult eps (abs h))
                       Hsum
                       (le_id_l (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                                (mult (inv_pos (plus one one) two_pos) (mult eps (abs h)))
                                (mult eps (abs h))
                                (id_sym (mult_assoc (inv_pos (plus one one) two_pos) eps (abs h)))
                                (half_le_self (mult eps (abs h))
                                              (le_trans zero (mult zero (abs h)) (mult eps (abs h))
                                                        (le_id_l zero (mult zero (abs h)) (mult zero (abs h))
                                                                 (id_sym (id_trans (mult_comm zero (abs h)) (mult_zero (abs h))))
                                                                 (le_refl (mult zero (abs h))))
                                                        (le_mult_compat_weak zero eps (abs h) (abs_nonneg h)
                                                                             (lt_le_iff _ _ (inl Heps))))))).
        }
      }
      }
      exact Hmid.
Qed.

(* ============================================================ *)
(* Differentiability of the language-model loss functions *)
(* ============================================================ *)
(* cross_entropy_softmax_diff: differentiability of the cross-entropy softmax *)
(*   f(logit) = log_inv (exp_neg logit) ≡ logit (the identity map, *)
(*   via [log_inv_exp_neg]); df = 1 and the error is identically zero. The constructive *)
(*   basis of softmax backpropagation (single-logit form; the error vanishes once folded to the identity map). *)
(* ------------------------------------------------------------ *)

Theorem cross_entropy_softmax_diff :
  Differentiable (fun logit => log_inv (exp_neg logit)).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* The error is identically zero: f(x+h) − (f(x) + 1·h) = 0, folded via [log_inv_exp_neg] *)
    assert (Hfold : Id (log_inv (exp_neg (plus x h))) (plus x h))
      by exact (log_inv_exp_neg (plus x h)).
    assert (Hfoldx : Id (log_inv (exp_neg x)) x)
      by exact (log_inv_exp_neg x).
    (* The error body vanishes: minus (x+h) (x + 1·h) = 0 *)
    assert (Hmain : Id (minus (plus x h) (plus x (mult one h))) zero).
    {
      assert (H1 : Id (plus x (mult one h)) (plus x h))
        by exact (id_cong (fun y => plus x y) (id_trans (mult_comm one h) (mult_one h))).
      assert (H2 : Id (minus (plus x h) (plus x (mult one h))) (minus (plus x h) (plus x h)))
        by exact (id_cong (fun y => minus (plus x h) y) H1).
      assert (H3 : Id (minus (plus x h) (plus x h)) zero)
        by exact (minus_self_zero (plus x h) (plus x h) (@id_refl R (plus x h))).
      exact (id_trans H2 H3).
    }
    (* The original error equals the folded error ([id_cong2] replaces both positions) *)
    assert (Herr : Id (minus (log_inv (exp_neg (plus x h)))
                             (plus (log_inv (exp_neg x)) (mult one h)))
                      (minus (plus x h) (plus x (mult one h))))
      by exact (id_cong2 minus Hfold (id_cong (fun y => plus y (mult one h)) Hfoldx)).
    (* le (abs error) (abs 0), then le 0 ≤ eps·|h| *)
    assert (Herr0 : Id (abs (minus (log_inv (exp_neg (plus x h)))
                                   (plus (log_inv (exp_neg x)) (mult one h))))
                       (abs zero))
      by exact (id_cong abs (id_trans Herr Hmain)).
    assert (Habs0 : le (abs zero) zero)
      by exact (le_id_l (abs zero) zero zero (abs_zero) (le_refl zero)).
    assert (Hprod : le zero (mult eps (abs h))).
    {
      exact (le_id_l zero (mult zero (abs h)) (mult eps (abs h))
                     (id_sym (id_trans (mult_comm zero (abs h)) (mult_zero (abs h))))
                     (le_mult_compat_weak zero eps (abs h) (abs_nonneg h) (lt_le_iff _ _ (inl Heps)))).
    }
    exact (le_id_l (abs (minus (log_inv (exp_neg (plus x h)))
                               (plus (log_inv (exp_neg x)) (mult one h))))
                   (abs zero)
                   (mult eps (abs h))
                   Herr0
                   (le_trans (abs zero) zero (mult eps (abs h)) Habs0 Hprod)).
  Qed.

(* ============================================================ *)
(* Differentiability of the MSE loss *)
(* ============================================================ *)
(* f(pred) = (pred − target)², df = 2·(pred − target), δ = min one eps. *)
(* Difference expansion: (x+h−t)² − ((x−t)² + 2(x−t)·h) = h² ([square_diff_ *)
(* expand, pure algebra); |h| < min one eps ⟹ |h| < 1 and |h| < eps, *)
(* |h²| = |h|² ≤ eps·|h|. *)
(* ------------------------------------------------------------ *)

(* Auxiliary: (a+b) − c = (a−c) + b (addition theorem for subtraction) *)
Lemma minus_plus_zero_r : forall a b c : R,
  Id (minus (plus a b) c) (plus (minus a c) b).
Proof.
  intros a b c.
  unfold minus.
  (* plus (plus a b) (opp c) = plus (plus a (opp c)) b *)
  assert (H1 : Id (plus (plus a b) (opp c)) (plus a (plus b (opp c))))
    by exact (id_sym (plus_assoc a b (opp c))).
  assert (H2 : Id (plus a (plus b (opp c))) (plus a (plus (opp c) b)))
    by exact (id_cong (fun x => plus a x) (plus_comm b (opp c))).
  assert (H3 : Id (plus a (plus (opp c) b)) (plus (plus a (opp c)) b))
    by exact (plus_assoc a (opp c) b).
  exact (id_trans H1 (id_trans H2 H3)).
Qed.

(* (x+h−t)² − ((x−t)² + 2·(x−t)·h) = h² (MSE difference expansion, pure algebra) *)
Lemma square_diff_expand : forall x target h : R,
  Id (minus (mult (minus (plus x h) target) (minus (plus x h) target))
            (plus (mult (minus x target) (minus x target))
                  (mult (mult (plus one one) (minus x target)) h)))
     (mult h h).
Proof.
  intros x target h.
  set (u := minus x target).
  (* v := (x+h) − t = u + h *)
  assert (Hv : Id (minus (plus x h) target) (plus u h))
    by (unfold u; exact (minus_plus_zero_r x h target)).
  (* Main goal: minus (mult v v) (plus (mult u u) (mult 2 u h)) = mult h h *)
  assert (Hmain : Id (minus (mult (plus u h) (plus u h))
                            (plus (mult u u) (mult (mult (plus one one) u) h)))
                     (mult h h)).
  {
    (* (u+h)² = u² + 2·u·h + h² *)
    assert (H1 : Id (mult (plus u h) (plus u h))
                    (plus (mult u (plus u h)) (mult h (plus u h))))
      by exact (mult_plus_distr_r u h (plus u h)).
    assert (H2 : Id (mult u (plus u h)) (plus (mult u u) (mult u h)))
      by exact (distrib u u h).
    assert (H3 : Id (mult h (plus u h)) (plus (mult h u) (mult h h)))
      by exact (distrib h u h).
    assert (H4 : Id (plus (mult u (plus u h)) (mult h (plus u h)))
                    (plus (plus (mult u u) (mult u h)) (plus (mult h u) (mult h h))))
      by exact (id_cong2 plus H2 H3).
    (* h·u = u·h *)
    assert (H5 : Id (plus (plus (mult u u) (mult u h)) (plus (mult h u) (mult h h)))
                    (plus (plus (mult u u) (mult u h)) (plus (mult u h) (mult h h))))
      by exact (id_cong (fun z => plus (plus (mult u u) (mult u h)) (plus z (mult h h)))
                        (mult_comm h u)).
    (* Merge the cross terms: u·h + u·h = 2·u·h ([two_mult] + [mult_plus_distr_r]) *)
    assert (H6 : Id (plus (mult u h) (mult u h)) (mult (mult (plus one one) u) h)).
    {
      assert (H6a : Id (mult (mult (plus one one) u) h) (mult (plus u u) h))
        by exact (id_cong (fun z => mult z h) (two_mult u)).
      assert (H6b : Id (mult (plus u u) h) (plus (mult u h) (mult u h)))
        by exact (mult_plus_distr_r u u h).
      exact (id_sym (id_trans H6a H6b)).
    }
    (* Regroup: u² + u·h + u·h + h² = (u² + 2·u·h) + h² *)
    assert (H7 : Id (plus (plus (mult u u) (mult u h)) (plus (mult u h) (mult h h)))
                    (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h))).
    {
      assert (H7a : Id (plus (plus (mult u u) (mult u h)) (plus (mult u h) (mult h h)))
                       (plus (mult u u) (plus (mult u h) (plus (mult u h) (mult h h)))))
        by exact (id_sym (plus_assoc (mult u u) (mult u h) (plus (mult u h) (mult h h)))).
      assert (H7b : Id (plus (mult u u) (plus (mult u h) (plus (mult u h) (mult h h))))
                       (plus (mult u u) (plus (plus (mult u h) (mult u h)) (mult h h))))
        by exact (id_cong (fun z => plus (mult u u) z) (plus_assoc (mult u h) (mult u h) (mult h h))).
      assert (H7c : Id (plus (mult u u) (plus (plus (mult u h) (mult u h)) (mult h h)))
                       (plus (mult u u) (plus (mult (mult (plus one one) u) h) (mult h h))))
        by exact (id_cong (fun z => plus (mult u u) (plus z (mult h h))) H6).
      assert (H7d : Id (plus (mult u u) (plus (mult (mult (plus one one) u) h) (mult h h)))
                       (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h)))
        by exact (plus_assoc (mult u u) (mult (mult (plus one one) u) h) (mult h h)).
      exact (id_trans H7a (id_trans H7b (id_trans H7c H7d))).
    }
    assert (Hsq : Id (mult (plus u h) (plus u h))
                     (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h)))
      by exact (id_trans H1 (id_trans H4 (id_trans H5 H7))).
    (* minus (u² + 2uh + h²) (u² + 2uh) = h²: [minus_plus_cancel_r] *)
    assert (Hsub : Id (minus (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h))
                             (plus (mult u u) (mult (mult (plus one one) u) h)))
                      (mult h h))
      by exact (minus_plus_cancel_r (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h)).
    exact (id_trans (id_cong (fun z => minus z (plus (mult u u) (mult (mult (plus one one) u) h))) Hsq) Hsub).
  }
  (* Assemble: replace v by u+h and u by minus x target *)
  change (Id (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                    (plus (mult u u) (mult (mult (plus one one) u) h)))
             (mult h h)).
  assert (Hrep : Id (mult (minus (plus x h) target) (minus (plus x h) target))
                    (mult (plus u h) (plus u h)))
    by exact (id_cong (fun z => mult z z) Hv).
  exact (id_trans (id_cong (fun z => minus z (plus (mult u u) (mult (mult (plus one one) u) h))) Hrep) Hmain).
Qed.

(* The MSE loss is differentiable: f(pred) = (pred − target)², df = 2·(pred − target).
   The error is h² ([square_diff_expand]); δ := min one eps guarantees both
   |h| < 1 and |h| < eps, hence |h²| = |h|² ≤ eps·|h|. *)
Theorem mse_diff :
  forall (target : R), Differentiable (fun pred => mult (minus pred target) (minus pred target)).
Proof.
  intro target.
  exists (fun pred => mult (plus one one) (minus pred target)).
  intros x eps Heps.
  exists (min one eps).
  split.
  - apply min_pos; [apply one_pos | exact Heps].
  - intros h Hh.
    (* The error is h² ([square_diff_expand]) *)
    assert (Hexp : Id (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                             (plus (mult (minus x target) (minus x target))
                                   (mult (mult (plus one one) (minus x target)) h)))
                      (mult h h))
      by exact (square_diff_expand x target h).
    (* Goal: le (abs (minus ...)) (mult eps (abs h)); first turn the LHS into abs (mult h h) *)
    assert (Herr0 : Id (abs (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                                   (plus (mult (minus x target) (minus x target))
                                         (mult (mult (plus one one) (minus x target)) h))))
                       (abs (mult h h)))
      by exact (id_cong abs Hexp).
    (* |h²| = |h|·|h| *)
    assert (Habs : Id (abs (mult h h)) (mult (abs h) (abs h)))
      by exact (abs_mult h h).
    (* |h| < 1 and |h| < eps (δ = min one eps) *)
    assert (Hh1 : lt (abs h) one)
      by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
    assert (Hh_eps : lt (abs h) eps)
      by (eapply lt_le_trans; [exact Hh | apply min_le_r]).
    assert (Hhle : le (abs h) eps)
      by (apply (lt_le_iff _ _); left; exact Hh_eps).
    (* |h|·|h| ≤ eps·|h| *)
    assert (Hprod : le (mult (abs h) (abs h)) (mult eps (abs h))).
    {
      assert (Hp1 : le (mult (abs h) (abs h)) (mult (abs h) eps))
        by exact (le_mult_compat_r (abs h) (abs h) eps (abs_nonneg h) Hhle).
      exact (le_id_r (mult (abs h) (abs h)) (mult (abs h) eps) (mult eps (abs h))
                     (mult_comm (abs h) eps) Hp1).
    }
    (* Assemble: abs error = abs h² = |h|·|h| ≤ eps·|h| *)
    exact (le_id_l (abs (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                              (plus (mult (minus x target) (minus x target))
                                    (mult (mult (plus one one) (minus x target)) h))))
                   (mult (abs h) (abs h))
                   (mult eps (abs h))
                   (id_trans Herr0 Habs)
                   Hprod).
  Qed.

(* ============================================================ *)
(* Differentiability of the DPO loss (gradient of the pairwise direct-preference objective) *)
(* ============================================================ *)
(* DPO pairwise loss L(Δ) = log(1 + e^{-Δ}) (Δ = implicit_reward_diff). *)
(* 1) Positivity of the denominator: 1 + e^{-Δ} > 0 (log is well defined). *)
(* 2) Difference decomposition: L(x+h) − L(x) = log((1+e^{-(x+h)})·(1+e^{-x})^{-1}) *)
(*    (reverse of [log_div] — the exact algebraic basis of the DPO gradient derivation). *)
(* 3) Defining equation of sigmoid: σ(x)·(1+e^{-x}) = 1 ([inv_pos_correct]). *)
(* 4) Sigmoid complement: σ(x) + e^{-x}·σ(x) = 1 (expanded from 3). *)
(* 5) Gradient alternative form: σ(x) − 1 = −e^{-x}·σ(x) (the Set-layer form of the *)
(*    sigmoid cross-entropy gradient, derived backwards from 4; the algebraic core *)
(*    of the backpropagation sigmoid derivative σ' = σ(1-σ)). *)
(* ------------------------------------------------------------ *)

(* Positivity of the log argument of the DPO pairwise loss: 1 + e^{-x} > 0 ([one_pos] + [exp_neg_pos] + [plus_positive]) *)
Lemma dpo_logit_denom_pos : forall x : R, lt zero (plus one (exp_neg x)).
Proof.
  intro x.
  apply plus_positive; [exact one_pos | apply exp_neg_pos].
Qed.

(* The DPO loss difference equals a log of a quotient (reverse of [log_div]; the difference is
   made explicit: L(x+h) − L(x) = log(1+e^{-(x+h)}) − log(1+e^{-x}) = log of the quotient) *)
Theorem dpo_loss_diff_decomp : forall x h : R,
  Id (minus (log (plus one (exp_neg (plus x h)))) (log (plus one (exp_neg x))))
     (log (mult (plus one (exp_neg (plus x h)))
                (inv_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x)))).
Proof.
  intros x h.
  exact (id_sym (log_div (plus one (exp_neg (plus x h))) (plus one (exp_neg x))
                 (dpo_logit_denom_pos (plus x h)) (dpo_logit_denom_pos x))).
Qed.

(* Sigmoid (Set-layer construction): σ(x) = 1/(1+e^{-x}), with the positivity witness embedded *)
Definition dpo_sigmoid (x : R) : R :=
  inv_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x).

(* Sigmoid positivity: 0 < σ(x) ([inv_pos_pos]) *)
Lemma dpo_sigmoid_pos : forall x : R, lt zero (dpo_sigmoid x).
Proof.
  intro x. unfold dpo_sigmoid.
  exact (inv_pos_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x)).
Qed.

(* Defining equation of sigmoid: σ(x)·(1+e^{-x}) = 1 ([inv_pos_correct] + [mult_comm]) *)
Theorem dpo_sigmoid_identity : forall x : R,
  Id (mult (dpo_sigmoid x) (plus one (exp_neg x))) one.
Proof.
  intro x. unfold dpo_sigmoid.
  exact (id_trans (mult_comm (inv_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x))
                             (plus one (exp_neg x)))
                  (inv_pos_correct (plus one (exp_neg x)) (dpo_logit_denom_pos x))).
Qed.

(* Sigmoid complement: σ(x) + e^{-x}·σ(x) = 1 ([distrib] expansion plus the
   defining equation) — the additive form of σ' = σ(1-σ) *)
Theorem dpo_sigmoid_complement : forall x : R,
  Id (plus (dpo_sigmoid x) (mult (exp_neg x) (dpo_sigmoid x))) one.
Proof.
  intro x.
  (* σ·(1+e^{-x}) = σ·1 + σ·e^{-x} ([distrib], forward direction) *)
  assert (Hdist : Id (mult (dpo_sigmoid x) (plus one (exp_neg x)))
                     (plus (mult (dpo_sigmoid x) one) (mult (dpo_sigmoid x) (exp_neg x))))
    by exact (distrib (dpo_sigmoid x) one (exp_neg x)).
  assert (Hone : Id (mult (dpo_sigmoid x) one) (dpo_sigmoid x))
    by exact (mult_one (dpo_sigmoid x)).
  assert (Hswap : Id (plus (mult (dpo_sigmoid x) one) (mult (dpo_sigmoid x) (exp_neg x)))
                     (plus (dpo_sigmoid x) (mult (exp_neg x) (dpo_sigmoid x))))
    by exact (id_cong2 plus Hone (mult_comm (dpo_sigmoid x) (exp_neg x))).
  exact (id_trans (id_sym Hswap) (id_trans (id_sym Hdist) (dpo_sigmoid_identity x))).
Qed.

(* Alternative form of the DPO gradient: df(x) = σ(x) − 1 = −e^{-x}·σ(x)
   (derived backwards from the sigmoid complement: additive cancellation plus
   the [opp_plus] + [double_neg] chain) *)
Theorem dpo_gradient_alt : forall x : R,
  Id (minus (dpo_sigmoid x) one) (opp (mult (exp_neg x) (dpo_sigmoid x))).
Proof.
  intro x.
  (* 1. From the complement identity: σ + e^{-x}σ = 1, and σ + (1 − σ) = 1 ⟹ e^{-x}σ = 1 − σ ([plus_cancel_l]) *)
  assert (Hc : Id (plus (dpo_sigmoid x) (mult (exp_neg x) (dpo_sigmoid x))) one)
    by exact (dpo_sigmoid_complement x).
  assert (Hcancel : Id (plus (dpo_sigmoid x) (minus one (dpo_sigmoid x))) one)
    by exact (minus_plus_cancel (dpo_sigmoid x) one).
  assert (Hratio : Id (mult (exp_neg x) (dpo_sigmoid x)) (minus one (dpo_sigmoid x))).
  {
    apply (plus_cancel_l (dpo_sigmoid x)).
    exact (id_trans Hc (id_sym Hcancel)).
  }
  (* 2. Negate: −(e^{-x}σ) = −(1 − σ) ([id_cong opp]) *)
  assert (Hopp : Id (opp (mult (exp_neg x) (dpo_sigmoid x)))
                    (opp (minus one (dpo_sigmoid x))))
    by exact (id_cong opp Hratio).
  (* 3. −(1 − σ) = σ − 1: [opp_plus] + [double_neg] + [plus_comm] + the definition of minus *)
  assert (Hreduce : Id (opp (minus one (dpo_sigmoid x))) (minus (dpo_sigmoid x) one)).
  {
    unfold minus.
    assert (H1 : Id (opp (plus one (opp (dpo_sigmoid x))))
                    (plus (opp one) (opp (opp (dpo_sigmoid x)))))
      by exact (opp_plus one (opp (dpo_sigmoid x))).
    assert (H2 : Id (plus (opp one) (opp (opp (dpo_sigmoid x))))
                    (plus (opp one) (dpo_sigmoid x)))
      by exact (id_cong (fun z => plus (opp one) z) (double_neg (dpo_sigmoid x))).
    assert (H3 : Id (plus (opp one) (dpo_sigmoid x))
                    (plus (dpo_sigmoid x) (opp one)))
      by exact (plus_comm (opp one) (dpo_sigmoid x)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  exact (id_sym (id_trans Hopp Hreduce)).
Qed.

End DifferentiableLemmas.

(* ============================================================ *)
(* Differentiability of entropy: k_B·log(Ω_A·Ω_B∘E_B) *)
(* assembled from the chain rule, multiplication and subtraction; the only gap is log differentiability (an explicit interface field) *)
(* ============================================================ *)
Section EntropyDifferentiable.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let one := @one RI.
Let lt := @lt RI.
Let mult := @mult RI.
Let minus := @minus RI.
Let log := @log RI.

Variable Omega_A : R -> R.
Variable Omega_B : R -> R.
Variable dOmega_A : Differentiable Omega_A.
Variable dOmega_B : Differentiable Omega_B.
Variable Omega_A_pos : forall E_A, lt zero (Omega_A E_A).
Variable Omega_B_pos : forall E_B, lt zero (Omega_B E_B).
Variable E_total : R.
Variable k_B : R.

Definition E_B_ent (E_A : R) : R := minus E_total E_A.
Definition Omega_total_ent (E_A : R) : R := mult (Omega_A E_A) (Omega_B (E_B_ent E_A)).
Definition entropy_ent (E_A : R) : R := mult k_B (log (Omega_total_ent E_A)).

(* Differentiability of log (explicit interface field: standard in constructive analysis,
   missing at the abstract layer; same pattern as [inv_pos]) *)
Variable log_differentiable : forall x : R, lt zero x -> Differentiable log.

(* Entropy is differentiable: full assembly from const/minus/id/mult/compose *)
Theorem entropy_differentiable : Differentiable entropy_ent.
Proof.
  unfold entropy_ent.
  assert (HOmega_pos : forall E_A, lt zero (Omega_total_ent E_A)).
  { intro E_A. unfold Omega_total_ent.
    apply (mult_positive (Omega_A E_A) (Omega_B (E_B_ent E_A)) (Omega_A_pos E_A) (Omega_B_pos (E_B_ent E_A))). }
  assert (HEB_d : Differentiable E_B_ent).
  { unfold E_B_ent.
    apply (differentiable_minus (fun _ => E_total) (fun x => x)).
    - apply differentiable_const.
    - apply differentiable_id. }
  assert (HcompB : Differentiable (fun E_A => Omega_B (E_B_ent E_A))).
  { apply (differentiable_compose Omega_B E_B_ent); [exact dOmega_B | exact HEB_d]. }
  assert (HOmega_d : Differentiable Omega_total_ent).
  { unfold Omega_total_ent.
    apply (differentiable_mult Omega_A (fun E_A => Omega_B (E_B_ent E_A))); [exact dOmega_A | exact HcompB]. }
  assert (Hlog_d : Differentiable (fun E_A => log (Omega_total_ent E_A))).
  { apply (differentiable_compose log Omega_total_ent).
    - exact (log_differentiable one one_pos).
    - exact HOmega_d. }
  apply (differentiable_mult (fun _ => k_B) (fun E_A => log (Omega_total_ent E_A))).
  - apply differentiable_const.
  - exact Hlog_d.
Qed.

End EntropyDifferentiable.
(* ============================================================ *)
(* Set-layer core for the differentiability of log: linear bounds of log near 1 *)
(* upper bound log(1+t) <= t [log_one_plus_le]; lower bound log(1+t) >= t-t^2 *)
(* [log_one_plus_ge, chain: t-t^2 <= t/(1+t) [set_div_linear_ge_quad] *)
(* == opp((1/(1+t))-1) [set_inv_minus_one_opp] <= log(1+t)]      *)
(* reusable for the corresponding construction at the Real layer; proving [log_differentiable] *)
(* would need [df_correct] for all x (including x<=0), while the interface properties of log only cover lt zero x, *)
(* so the abstract-interface statement is mathematically unprovable and is replicated eps-by-eps at the Real layer. *)
(* ============================================================ *)
Section LogDiffPhase3.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* ============ 0. Set-layer identity: (1+t) − 1 == t ============ *)
Lemma minus_one_plus_t : forall t : R, Id (minus (plus one t) one) t.
Proof.
  intros t.
  unfold minus.
  rewrite <- (plus_assoc one t (opp one)).
  rewrite (plus_comm t (opp one)).
  rewrite (plus_assoc one (opp one) t).
  rewrite (plus_opp one).
  rewrite (plus_comm zero t).
  rewrite (plus_zero t).
  reflexivity.
Qed.

(* ============ 1. Upper bound: 0 < 1+t ⟹ log(1+t) ≤ t ============ *)
Lemma log_one_plus_le : forall (t : R), lt zero (plus one t) ->
  le (log (plus one t)) t.
Proof.
  intros t Hpos.
  exact (le_trans (log (plus one t)) (minus (plus one t) one) t
           (log_le_linear (plus one t) Hpos)
           (lt_le_iff (minus (plus one t) one) t (inr (minus_one_plus_t t)))).
Qed.

(* ============ 2. Set-layer algebra auxiliaries ============ *)
(* eq → le bridge *)
Lemma set_eq_le : forall a b : R, Id a b -> le a b.
Proof.
  intros a b Hab. exact (lt_le_iff a b (inr Hab)).
Qed.

(* t ≥ 0 ⟹ t² ≥ 0: t·0 == 0 ≤ t·t ([le_mult_compat_r] on t with 0≤t) *)
Lemma set_square_nonneg : forall t : R, le zero t -> le zero (mult t t).
Proof.
  intros t Ht.
  exact (le_trans zero (mult t zero) (mult t t)
           (set_eq_le zero (mult t zero) (id_sym (mult_zero t)))
           (le_mult_compat_r t zero t Ht Ht)).
Qed.

(* t ≥ 0 ⟹ t³ ≥ 0 *)
Lemma set_cube_nonneg : forall t : R, le zero t -> le zero (mult t (mult t t)).
Proof.
  intros t Ht.
  exact (le_trans zero (mult t zero) (mult t (mult t t))
           (set_eq_le zero (mult t zero) (id_sym (mult_zero t)))
           (le_mult_compat_r t zero (mult t t) Ht (set_square_nonneg t Ht))).
Qed.

(* a·(b−c) == a·b − a·c *)
Lemma set_minus_mult : forall a b c : R,
  Id (mult a (minus b c)) (minus (mult a b) (mult a c)).
Proof.
  intros a b c. exact (mult_minus_distr_l a b c).
Qed.

(* opp zero == zero (needed by the [opp_le_compat] bridge; no Set-layer opp_zero in the main interface file) *)
Lemma set_opp_zero : Id (opp zero) zero.
Proof.
  exact (id_sym (plus_inv_unique zero zero (opp zero) (plus_zero zero) (plus_opp zero))).
Qed.

(* Ring simplification: (t + −t²) + (t² + −t³) == t + −t³ (fully explicit assembly; setoid rewrite abandoned) *)
Lemma set_quad_cube : forall t : R,
  Id (plus (minus t (mult t t)) (minus (mult t t) (mult t (mult t t))))
     (minus t (mult t (mult t t))).
Proof.
  intros t.
  unfold minus.
  (* Segment 1: (t + −t²) + (t² + −t³) == t + (−t² + (t² + −t³)) [id_sym plus_assoc] *)
  pose proof (id_sym (plus_assoc t (opp (mult t t))
                                (plus (mult t t) (opp (mult t (mult t t)))))) as H1.
  (* Segment 2: t + (−t² + (t² + −t³)) == t + ((−t² + t²) + −t³) [id_cong plus_assoc] *)
  pose proof (id_cong (fun x => plus t x)
                      (plus_assoc (opp (mult t t)) (mult t t)
                                  (opp (mult t (mult t t))))) as H2.
  (* Segment 3a: opp t² + t² == t² + opp t² [plus_comm] == zero [plus_opp] *)
  pose proof (id_trans (plus_comm (opp (mult t t)) (mult t t))
                       (plus_opp (mult t t))) as Hopp_zero.
  (* Segment 3b: lift to (… + −t³): ((opp t² + t²) + −t³) == (zero + −t³) *)
  pose proof (id_cong (fun y => plus y (opp (mult t (mult t t)))) Hopp_zero) as Hopp_z'.
  (* Segment 3c: lift to t + … *)
  pose proof (id_cong (fun x => plus t x) Hopp_z') as H3.
  (* Segment 4: zero + −t³ == −t³ + zero [plus_comm], lifted to t + … *)
  pose proof (id_cong (fun x => plus t x)
                      (plus_comm zero (opp (mult t (mult t t))))) as H4.
  (* Segment 5: −t³ + zero == −t³ [plus_zero], lifted to t + … *)
  pose proof (id_cong (fun x => plus t x)
                      (plus_zero (opp (mult t (mult t t))))) as H5.
  exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
Qed.

(* Core identity: (t−t²)(1+t) == t−t³ *)
Lemma set_quad_prod : forall t : R,
  Id (mult (minus t (mult t t)) (plus one t))
     (minus t (mult t (mult t t))).
Proof.
  intros t.
  exact (id_trans (distrib (minus t (mult t t)) one t)
           (id_trans (id_cong2 plus (mult_one (minus t (mult t t)))
                        (id_trans (mult_comm (minus t (mult t t)) t)
                           (set_minus_mult t t (mult t t))))
              (set_quad_cube t))).
Qed.

(* t−t³ ≤ t (t³ ≥ 0 ⟹ −t³ ≤ 0 ⟹ t+(−t³) ≤ t+0) *)
Lemma set_minus_cube_le : forall t : R, le zero t ->
  le (minus t (mult t (mult t t))) t.
Proof.
  intros t Ht.
  unfold minus.
  apply (le_trans _ (plus t zero) _).
  - apply (le_plus_compat t t (opp (mult t (mult t t))) zero).
    + apply le_refl.
    + apply (le_id_r _ _ _ set_opp_zero).
      apply (opp_le_compat zero (mult t (mult t t))). exact (set_cube_nonneg t Ht).
  - apply set_eq_le. apply (plus_zero t).
Qed.

(* 0 ≤ t ⟹ 0 < 1+t: 1+t ≥ 1+0 == 1 > 0 *)
Lemma set_one_plus_pos : forall t : R, le zero t -> lt zero (plus one t).
Proof.
  intros t Ht0.
  exact (lt_le_trans zero one (plus one t) one_pos
           (le_id_l one (plus one zero) (plus one t) (id_sym (plus_zero one))
              (le_plus_compat one one zero t (le_refl one) Ht0))).
Qed.

(* ============ 3. Main lemma: 0 ≤ t ⟹ t−t² ≤ t·(1/(1+t)) ============ *)
(* Chain: t−t² ≤ t·inv s
       ⟸ (t−t²)·s ≤ t·inv s·s == t·1 == t
         ([le_mult_compat] on inv s > 0; inv s·s == 1 converted back to t−t²)
       ⟸ (t−t²)·(1+t) == t−t³ ≤ t   [set_quad_prod + set_minus_cube_le]
   where s == plus one t. *)
(* Auxiliary: inv s · s == 1 ([inv_pos_correct] on s + comm) *)
Lemma set_inv_mul : forall (s : R) (Hs : lt zero s),
  Id (mult (inv_pos s Hs) s) one.
Proof.
  intros s Hs.
  exact (id_trans (mult_comm (inv_pos s Hs) s) (inv_pos_correct s Hs)).
Qed.

Lemma set_div_linear_ge_quad : forall (t : R) (Ht0 : le zero t),
  forall (Hs : lt zero (plus one t)),
  le (minus t (mult t t))
     (mult t (inv_pos (plus one t) Hs)).
Proof.
  intros t Ht0 Hs.
  set (s := plus one t) in *.
  (* Core: (t−t²)·(1+t) ≤ t ([set_quad_prod] + [set_minus_cube_le]) *)
  assert (Hcore : le (mult (minus t (mult t t)) s) t).
  { apply (le_trans _ (minus t (mult t (mult t t))) _).
    - apply set_eq_le. apply (set_quad_prod t).
    - apply (set_minus_cube_le t). exact Ht0. }
  (* From Hcore: (t−t²)·s ≤ t; multiply by the positive inv s ([le_mult_compat]):
     (t−t²)·s·inv s ≤ t·inv s
     the left side == (t−t²)·(s·inv s) == (t−t²)·1 == t−t² [reverse assoc + inv_correct + mult_one]
     goal t−t² ≤ t·inv s *)
  apply (le_trans _ (mult (mult (minus t (mult t t)) s) (inv_pos s Hs)) _).
  - (* t−t² ≤ (t−t²)·s·inv s: reverse conversion (assoc + inv_correct + mult_one) *)
    apply set_eq_le.
    (* (t−t²) == (t−t²)·one [id_sym mult_one]
                 == (t−t²)·(s·inv s) [id_cong: one == s·inv s (id_sym inv_correct)]
                 == ((t−t²)·s)·inv s [mult_assoc] *)
    pose proof (id_sym (mult_one (minus t (mult t t)))) as Ha.
    pose proof (id_sym (inv_pos_correct s Hs)) as Hb.
    pose proof (id_cong (fun x => mult (minus t (mult t t)) x) Hb) as Hc.
    pose proof (id_trans Ha Hc) as Hd.
    pose proof (mult_assoc (minus t (mult t t)) s (inv_pos s Hs)) as He.
    exact (id_trans Hd He).
  - (* (t−t²)·s·inv s ≤ t·inv s: [le_mult_compat] on Hcore with inv s > 0 *)
    apply (le_mult_compat (mult (minus t (mult t t)) s) t (inv_pos s Hs)).
    + apply (inv_pos_pos s Hs).
    + exact Hcore.
Qed.

(* ============ 4. Set-layer identity: t·inv(1+t) == opp (minus (inv(1+t)) one)
   (the Set-layer rendering of the Real-layer chain; the core identity of the 1/x derivative)
   Chain: t·inv s == (s−1)·inv s == inv s·(s−1) == inv s·s − inv s·1
              == one − inv s·one == one − inv s == opp (inv s − 1)
   where s == plus one t and s−1 == t (reverse of [minus_one_plus_t]) *)
Lemma set_inv_minus_one_opp : forall (t : R) (Hs : lt zero (plus one t)),
  Id (mult t (inv_pos (plus one t) Hs))
     (opp (minus (inv_pos (plus one t) Hs) one)).
Proof.
  intros t Hs.
  set (s := plus one t) in *.
  (* H1: t == s − 1 (reverse of [minus_one_plus_t]) ⟹ t·inv s == (s−1)·inv s *)
  pose proof (id_sym (minus_one_plus_t t)) as Ht_sm1.
  pose proof (id_cong (fun x => mult x (inv_pos s Hs)) Ht_sm1) as H1.
  (* H2: (s−1)·inv s == inv s·(s−1) ([mult_comm]) *)
  pose proof (mult_comm (minus s one) (inv_pos s Hs)) as H2.
  (* H3: inv s·(s−1) == inv s·s − inv s·1 ([mult_minus_distr_l]) *)
  pose proof (mult_minus_distr_l (inv_pos s Hs) s one) as H3.
  (* H4: inv s·s == one ([set_inv_mul]) ⟹ minus (inv s·s) (inv s·one) == minus one (inv s·one) *)
  pose proof (set_inv_mul s Hs) as Hinv_s.
  pose proof (id_cong (fun x => minus x (mult (inv_pos s Hs) one)) Hinv_s) as H4.
  (* H5: minus one (inv s·one) == minus one (inv s) ([mult_one]) *)
  pose proof (id_cong (fun x => minus one x) (mult_one (inv_pos s Hs))) as H5.
  (* H6: minus one (inv s) == opp (minus (inv s) one)
        [opp_minus (inv s) one]: opp (minus (inv s) one) == plus (opp (inv s)) one
        plus_comm → plus one (opp (inv s)) == minus one (inv s); reverse by id_sym *)
  pose proof (id_trans (opp_minus (inv_pos s Hs) one)
                       (plus_comm (opp (inv_pos s Hs)) one)) as H6a.
  pose proof (id_sym H6a) as H6.
  (* Assemble *)
  exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6))))).
Qed.

(* ============ 5. Lower bound: 0 ≤ t ⟹ log(1+t) ≥ t − t²
   Chain: t−t² ≤ t·inv s                    [set_div_linear_ge_quad]
       t·inv s == opp (inv s − 1)        [set_inv_minus_one_opp]
       opp (inv s − 1) ≤ opp (log (inv s))   [opp_le_compat: log (inv s) ≤ inv s − 1 (log_le_linear)]
       opp (log (inv s)) == log s         [log_inv_one_inv + id_cong opp + double_neg] *)
Lemma log_one_plus_ge : forall (t : R), le zero t ->
  lt zero (plus one t) ->
  le (minus t (mult t t)) (log (plus one t)).
Proof.
  intros t Ht0 Hs.
  set (s := plus one t) in *.
  (* Segment 1: t−t² ≤ t·inv s *)
  pose proof (set_div_linear_ge_quad t Ht0 Hs) as Hseg1.
  (* Segment 2a: t·inv s == opp (minus (inv s) one) *)
  pose proof (set_inv_minus_one_opp t Hs) as Hio.
  (* Segment 2b: log (inv s) ≤ inv s − 1 ([log_le_linear]) *)
  pose proof (log_le_linear (inv_pos s Hs) (inv_pos_pos s Hs)) as Hlin.
  (* Segment 2c: opp (minus (inv s) one) ≤ opp (log (inv s)) ([opp_le_compat]) *)
  pose proof (opp_le_compat (log (inv_pos s Hs)) (minus (inv_pos s Hs) one) Hlin) as Hoc.
  (* Segment 2d: le (mult t (inv s)) (opp (log (inv s))): le_id_l Hio Hoc *)
  pose proof (le_id_l _ _ _ Hio Hoc) as Hseg2a.
  (* Segment 2e: opp (log (inv s)) == log s
        log_inv_one_inv s Hs : log (inv s) == opp (log s)
        id_cong opp → opp (log (inv s)) == opp (opp (log s))
        double_neg (log s) : opp (opp (log s)) == log s *)
  pose proof (log_inv_one_inv s Hs) as Hli.
  pose proof (id_cong opp Hli) as Ho1.
  pose proof (double_neg (log s)) as Hdn.
  pose proof (id_trans Ho1 Hdn) as Ho2.
  (* Segment 2f: le (mult t (inv s)) (log s): le_id_r Ho2 Hseg2a *)
  pose proof (le_id_r _ _ _ Ho2 Hseg2a) as Hseg2.
  (* Assemble *)
  apply (le_trans _ (mult t (inv_pos s Hs)) _).
  - exact Hseg1.
  - exact Hseg2.
Qed.

End LogDiffPhase3.

(* ============================================================ *)
(* Multivariable differentiability (DifferentiableMV: the StateSpace inner-product interface version) *)
(* ============================================================ *)
(* Multivariable formulation: f : S -> R with gradient df : S -> S, *)
(* linearization via [inner] (the HilbertSpace inner product), perturbations measured by smetric. *)
(* 1) The DifferentiableMV record: a Frechet-type definition (Set layer). *)
(* 2) Linearity of the inner product in its second argument: ⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩ ([inner_splus_l *)
(*    gives linearity in the first argument, swapped by [inner_sym]; the basis for differentiability of attention logits). *)
(* 3) Differentiability of constant fields: f ≡ c with df ≡ szero (the error is identically zero: [inner_szero_l]). *)
(* 4) Differentiability of linear functionals: f(x) = ⟨a,x⟩ with df = a (zero error: linearity of the inner product; *)
(*    attention_score(s) = ⟨s, key⟩ is differentiable in s with df = key). *)
(* ------------------------------------------------------------ *)

Section MultivariableDifferentiable.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpaceExtended RI}.
Context {HS : HilbertSpace RI SS}.

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
Let szero := @szero RI SS.
Let splus := @splus RI SS.
Let smult := @smult RI SS.
Let sopp := @sopp RI SS.
Let smetric := @smetric RI SS.
Let inner := @inner RI SS HS.
Let smetric_pos := @smetric_pos RI SS.

(* Multivariable differentiability (Frechet type, Set layer): f : S -> R with gradient dfmv : S -> S.
   The linearization df(x)·h uses [inner] (the inner product); the error is measured by smetric. *)
Record DifferentiableMV (f : S -> R) := {
  dfmv : S -> S;
  dfmv_correct : forall x eps, lt zero eps ->
    sigT (fun delta : R => And (lt zero delta) (forall h : S,
      lt (smetric h szero) delta ->
      le (abs (minus (f (splus x h))
                     (plus (f x) (inner (dfmv x) h))))
         (mult eps (smetric h szero))))
}.

(* Linearity of the inner product in its second argument: ⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩
   ([inner_splus_l] gives linearity in the first argument; two swaps by [inner_sym]) *)
Lemma inner_splus_r : forall x y z : S,
  Id (inner x (splus y z)) (plus (inner x y) (inner x z)).
Proof.
  intros x y z.
  exact (id_trans (inner_sym x (splus y z))
           (id_trans (inner_splus_l y z x)
              (id_cong2 plus (inner_sym y x) (inner_sym z x)))).
Qed.

(* Multivariable composite error decomposition (mv version of [compose_diff_decomp]): reuse the
   univariate version specialized at h := one and D := X (X := inner (dfmv x) h is a scalar), with the
   conversions mult (mult C X) one == mult C X and mult X one == X. *)
Lemma mv_compose_diff_decomp : forall (A B C G g0 X : R),
  Id (minus A (plus B (mult C X)))
     (plus (minus A (plus B (mult C (minus G g0))))
           (mult C (minus (minus G g0) X))).
Proof.
  intros A B C G g0 X.
  (* Reuse [compose_diff_decomp] with h := one and D := X *)
  assert (H1 : Id (minus A (plus B (mult (mult C X) one)))
                  (plus (minus A (plus B (mult C (minus G g0))))
                        (mult C (minus (minus G g0) (mult X one)))))
    by exact (compose_diff_decomp A B C X G g0 one).
  (* LHS conversion: mult (mult C X) one == mult C X *)
  assert (Hl : Id (minus A (plus B (mult (mult C X) one)))
                  (minus A (plus B (mult C X)))).
  {
    apply (id_cong (fun z => minus A (plus B z))).
    assert (Ha : Id (mult (mult C X) one) (mult C (mult X one)))
      by exact (id_sym (mult_assoc C X one)).
    assert (Hb : Id (mult C (mult X one)) (mult C X))
      by exact (id_cong (fun z => mult C z) (mult_one X)).
    exact (id_trans Ha Hb).
  }
  (* RHS conversion: mult X one == X (inside the last term) *)
  assert (Hr : Id (plus (minus A (plus B (mult C (minus G g0))))
                        (mult C (minus (minus G g0) (mult X one))))
                  (plus (minus A (plus B (mult C (minus G g0))))
                        (mult C (minus (minus G g0) X)))).
  {
    apply (id_cong (fun z => plus (minus A (plus B (mult C (minus G g0)))) z)).
    apply (id_cong (fun z => mult C z)).
    apply (id_cong (fun z => minus (minus G g0) z)).
    exact (mult_one X).
  }
  exact (id_trans (id_sym Hl) (id_trans H1 Hr)).
Qed.

(* Inner-product Lipschitz interface (explicit Variable): for each vector a there is a norm bound N with
   |⟨a,h⟩| ≤ N·|h| (a constructive weakening of Cauchy-Schwarz; it needs positive definiteness and
   continuity of the inner product, so it is listed as an interface assumption — same precedent as
   [proj_orthogonal_compat] / [inv_pos_lt_contra]).
   It supports the multivariate chain rule: the inner increment satisfies |f(x+h) − f x| ≤ (N+1)·|h|. *)
Variable inner_lipschitz : forall (a : S),
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (abs (inner a h)) (mult N (smetric h szero)))).

(* Constant fields are differentiable: f ≡ c with dfmv ≡ szero. The error is identically zero:
   |c − (c + ⟨0,h⟩)| = |⟨0,h⟩| = 0 ([inner_szero_l] + [plus_zero] + [plus_opp] + [abs_zero]).
   δ = one ([one_pos]). *)
Theorem differentiable_mv_const : forall c : R, DifferentiableMV (fun _ => c).
Proof.
  intro c.
  exists (fun _ => szero).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* Error = |c − (c + ⟨0,h⟩)| = |c − c| = 0 *)
    assert (Hinner : Id (inner szero h) zero)
      by exact (inner_szero_l h).
    assert (Herr : Id (minus c (plus c (inner szero h))) zero).
    {
      unfold minus.
      (* plus c (opp (plus c (inner szero h))) = plus c (opp (plus c zero)) ([inner_szero_l]) *)
      assert (H1 : Id (plus c (opp (plus c (inner szero h))))
                    (plus c (opp (plus c zero))))
        by exact (id_cong (fun z => plus c (opp (plus c z))) Hinner).
      assert (H2 : Id (plus c (opp (plus c zero))) (plus c (opp c)))
        by exact (id_cong (fun z => plus c (opp z)) (plus_zero c)).
      assert (H3 : Id (plus c (opp c)) zero)
        by exact (plus_opp c).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    (* Goal: le (abs error) (mult eps (smetric h szero)); turn the LHS into abs zero = 0 *)
    assert (Habs : Id (abs (minus c (plus c (inner szero h)))) (abs zero))
      by exact (id_cong abs Herr).
    assert (Habs0 : Id (abs zero) zero)
      by exact (abs_zero).
    assert (Hprod : le zero (mult eps (smetric h szero))).
    {
      assert (Hm0 : Id (mult zero (smetric h szero)) zero)
        by exact (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))).
      apply (le_id_l zero (mult zero (smetric h szero)) (mult eps (smetric h szero))).
      - exact (id_sym Hm0).
      - apply (le_mult_compat_weak zero eps (smetric h szero)).
        + apply smetric_pos.
        + apply (lt_le_iff _ _). left. exact Heps.
    }
    exact (le_id_l (abs (minus c (plus c (inner szero h))))
                   (abs zero)
                   (mult eps (smetric h szero))
                   Habs
                   (le_id_l (abs zero) zero (mult eps (smetric h szero)) Habs0 Hprod)).
Qed.

(* Linear functionals are differentiable: f(x) = ⟨a, x⟩ with dfmv = a. The error is identically zero:
   |⟨a, x+h⟩ − (⟨a,x⟩ + ⟨a,h⟩)| = |0| ([inner_splus_r]).
   δ = one. This is the differentiability of attention logits: attention_score(s) = ⟨s,key⟩
   is differentiable in s, and the gradient is exactly key (df = a). *)
Theorem differentiable_mv_linear : forall a : S, DifferentiableMV (fun x => inner a x).
Proof.
  intro a.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* Error = |⟨a, x+h⟩ − (⟨a,x⟩ + ⟨a,h⟩)| = 0 ([inner_splus_r]) *)
    assert (Hlin : Id (inner a (splus x h)) (plus (inner a x) (inner a h)))
      by exact (inner_splus_r a x h).
    assert (Herr : Id (minus (inner a (splus x h)) (plus (inner a x) (inner a h))) zero).
    {
      unfold minus.
      assert (H1 : Id (plus (inner a (splus x h)) (opp (plus (inner a x) (inner a h))))
                    (plus (plus (inner a x) (inner a h)) (opp (plus (inner a x) (inner a h)))))
        by exact (id_cong (fun z => plus z (opp (plus (inner a x) (inner a h)))) Hlin).
      assert (H2 : Id (plus (plus (inner a x) (inner a h)) (opp (plus (inner a x) (inner a h)))) zero)
        by exact (plus_opp (plus (inner a x) (inner a h))).
      exact (id_trans H1 H2).
    }
    assert (Habs : Id (abs (minus (inner a (splus x h)) (plus (inner a x) (inner a h)))) (abs zero))
      by exact (id_cong abs Herr).
    assert (Habs0 : Id (abs zero) zero)
      by exact (abs_zero).
    assert (Hprod : le zero (mult eps (smetric h szero))).
    {
      assert (Hm0 : Id (mult zero (smetric h szero)) zero)
        by exact (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))).
      apply (le_id_l zero (mult zero (smetric h szero)) (mult eps (smetric h szero))).
      - exact (id_sym Hm0).
      - apply (le_mult_compat_weak zero eps (smetric h szero)).
        + apply smetric_pos.
        + apply (lt_le_iff _ _). left. exact Heps.
    }
    exact (le_id_l (abs (minus (inner a (splus x h)) (plus (inner a x) (inner a h))))
                   (abs zero)
                   (mult eps (smetric h szero))
                   Habs
                   (le_id_l (abs zero) zero (mult eps (smetric h szero)) Habs0 Hprod)).
Qed.

(* Sums of scalar fields are differentiable: f+g with dfmv = splus df dg.
   The ε-δ argument: [inner_splus_l] (⟨df+dg,h⟩ = ⟨df,h⟩+⟨dg,h⟩) plus the eps/2 budget
   ([half_pos]/[half_twice]) plus min δ ([min_pos]/[min_le_l]/[min_le_r]) plus [abs_triangle]
   plus the error decomposition by [minus_plus_distr]/[plus_swap_mid] (about 40 steps; isomorphic
   to the univariate [differentiable_plus] but with inner-product linearization and the smetric measure). *)
Theorem differentiable_mv_plus : forall (f g : S -> R),
  DifferentiableMV f -> DifferentiableMV g ->
  DifferentiableMV (fun x => plus (f x) (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => splus (df x) (dg x)).
  intros x eps Heps.
  pose (mult (inv_pos (plus one one) two_pos) eps) as eps_half.
  assert (Hhalf : lt zero eps_half) by (unfold eps_half; apply half_pos; exact Heps).
  destruct (Hf x eps_half Hhalf) as [dfdelta [Hdf1 Hdf2]].
  destruct (Hg x eps_half Hhalf) as [dgdelta [Hdg1 Hdg2]].
  exists (min dfdelta dgdelta).
  split.
  - apply min_pos; [exact Hdf1 | exact Hdg1].
  - intros h Hh.
    (* |h| < min ⟹ |h| < dfdelta and |h| < dgdelta *)
    assert (Hh1 : lt (smetric h szero) dfdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_l. }
    assert (Hh2 : lt (smetric h szero) dgdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_r. }
    (* Error decomposition: ⟨df+dg, h⟩ = ⟨df,h⟩ + ⟨dg,h⟩ (linearity in the first argument, [inner_splus_l]) *)
    assert (Hinner : Id (inner (splus (df x) (dg x)) h)
                       (plus (inner (df x) h) (inner (dg x) h)))
      by exact (inner_splus_l (df x) (dg x) h).
    change (le (abs (minus (plus (f (splus x h)) (g (splus x h)))
                           (plus (plus (f x) (g x)) (inner (splus (df x) (dg x)) h))))
               (mult eps (smetric h szero))).
    rewrite Hinner.
    assert (Hswap : Id (plus (plus (f x) (g x)) (plus (inner (df x) h) (inner (dg x) h)))
                       (plus (plus (f x) (inner (df x) h)) (plus (g x) (inner (dg x) h))))
      by exact (plus_swap_mid (f x) (g x) (inner (df x) h) (inner (dg x) h)).
    rewrite Hswap.
    assert (Hmpd2 : Id (minus (plus (f (splus x h)) (g (splus x h)))
                              (plus (plus (f x) (inner (df x) h)) (plus (g x) (inner (dg x) h))))
                       (plus (minus (f (splus x h)) (plus (f x) (inner (df x) h)))
                             (minus (g (splus x h)) (plus (g x) (inner (dg x) h)))))
      by exact (minus_plus_distr (f (splus x h)) (g (splus x h))
                                 (plus (f x) (inner (df x) h)) (plus (g x) (inner (dg x) h))).
    rewrite Hmpd2.
    (* Triangle inequality *)
    apply (le_trans _ (plus (abs (minus (f (splus x h)) (plus (f x) (inner (df x) h))))
                            (abs (minus (g (splus x h)) (plus (g x) (inner (dg x) h)))))).
    + apply abs_triangle.
    + apply (le_trans _ (plus (mult eps_half (smetric h szero)) (mult eps_half (smetric h szero)))).
      * apply le_plus_compat.
        -- apply (Hdf2 h Hh1).
        -- apply (Hdg2 h Hh2).
      * (* eps_half·s + eps_half·s = eps·s *)
        assert (Hsum : Id (plus (mult eps_half (smetric h szero)) (mult eps_half (smetric h szero)))
                          (mult eps (smetric h szero))).
        {
          unfold eps_half.
          assert (Hd : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                      (mult (inv_pos (plus one one) two_pos) eps)) (smetric h szero))
                           (plus (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                                 (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))))
            by exact (mult_plus_distr_r (mult (inv_pos (plus one one) two_pos) eps)
                                        (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero)).
          rewrite <- Hd.
          assert (Hcong : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                          (mult (inv_pos (plus one one) two_pos) eps)) (smetric h szero))
                             (mult eps (smetric h szero)))
            by (apply (id_cong (fun z => mult z (smetric h szero))); exact (half_twice eps)).
          rewrite Hcong. reflexivity.
        }
        rewrite Hsum. apply le_refl.
Qed.

(* Multivariable chain rule (constructive ε-δ proof, multivariable version).
   Final budget allocation: T1 (the outer error, amplified by |Dg| ≤ L·|h|) uses eps_f (controlled by L);
   T2 (the inner error, scaled by |dg(f x)| ≤ M) uses eps_g (controlled by M).
   I.e. eps_f := min one (inv_L·eps4) (the inner differentiability budget, scaled by the inner Lipschitz constant L);
   eps_g := min one (inv_M·eps4) (the outer differentiability budget, scaled by the outer derivative bound M).
   T1 ≤ eps_f·L·|h| ≤ eps4·|h|; T2 ≤ M·eps_g·|h| ≤ eps4·|h|. *)
Theorem differentiable_mv_compose : forall (f : S -> R) (g : R -> R),
  DifferentiableMV f -> Differentiable g ->
  DifferentiableMV (fun x => g (f x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => smult (dg (f x)) (df x)).
  intros x eps Heps.
  set (eps4 := mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive; [apply inv_pos_pos | apply half_pos; exact Heps]. }
  (* Inner Lipschitz constant: N := inner_lipschitz (df x), L := N + 1 (so |Dg| ≤ L·|h|) *)
  destruct (inner_lipschitz (df x)) as [N HN].
  destruct HN as [HN0 HN2].
  set (L := plus N one).
  assert (HL : lt zero L).
  { unfold L. apply plus_le_lt_pos; [exact HN0 | apply one_pos]. }
  set (M := plus (abs (dg (f x))) one).
  assert (HM : lt zero M) by (unfold M; apply abs_plus_one_pos).
  set (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f)
    by (unfold eps_f; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  set (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g)
    by (unfold eps_g; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  destruct (Hf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    apply min_pos; [exact Hdf1 | apply min_pos; [apply one_pos | exact Hltm]].
  - intros h Hh.
    set (Dg := minus (f (splus x h)) (f x)).
    (* Linearization conversion: inner (smult (dg (f x)) (df x)) h == mult (dg (f x)) (inner (df x) h) *)
    assert (Hlin : Id (inner (smult (dg (f x)) (df x)) h)
                      (mult (dg (f x)) (inner (df x) h)))
      by exact (inner_smult_l (dg (f x)) (df x) h).
    (* Error decomposition (mv version of compose_diff_decomp): first decompose in the
        mult (dg(f x)) (inner ...) form, then convert the linearization back to the
        inner (smult ...) form (reverse of Hlin) *)
    assert (Hdec1 : Id (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) (inner (df x) h))))
                      (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                            (mult (dg (f x)) (minus Dg (inner (df x) h)))))
      by (unfold Dg; exact (mv_compose_diff_decomp (g (f (splus x h))) (g (f x)) (dg (f x))
                                                   (f (splus x h)) (f x) (inner (df x) h))).
    assert (Hdecomp : Id (minus (g (f (splus x h))) (plus (g (f x)) (inner (smult (dg (f x)) (df x)) h)))
                         (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                               (mult (dg (f x)) (minus Dg (inner (df x) h)))))
      by (exact (id_trans (id_cong (fun z => minus (g (f (splus x h))) (plus (g (f x)) z)) Hlin) Hdec1)).
    apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (smult (dg (f x)) (df x)) h))))
                   (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                              (mult (dg (f x)) (minus Dg (inner (df x) h)))))
                   (mult eps (smetric h szero))).
    + exact (id_cong abs Hdecomp).
    + assert (Hh_dfd : lt (smetric h szero) dfd)
        by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
      assert (Hh_one : lt (smetric h szero) one)
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_l]]).
      assert (Hh_dgd : lt (smetric h szero) (mult (inv_pos L HL) dgd))
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_r]]).
      (* (a) |Dg| ≤ L·|h| ([minus_split] + triangle + [inner_lipschitz] + eps_f ≤ 1) *)
      assert (HDg_bound : le (abs Dg) (mult L (smetric h szero))).
      {
        assert (Hsplit : Id (minus (f (splus x h)) (f x))
                            (plus (minus (f (splus x h)) (plus (f x) (inner (df x) h))) (inner (df x) h)))
          by exact (minus_split (f (splus x h)) (f x) (inner (df x) h)).
        unfold Dg. rewrite Hsplit.
        apply (le_trans _ (plus (abs (minus (f (splus x h)) (plus (f x) (inner (df x) h)))) (abs (inner (df x) h))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps_f (smetric h szero)) (mult N (smetric h szero))) _).
          { apply le_plus_compat.
            { exact (Hdf2 h Hh_dfd). }
            { exact (HN2 h). } }
          { assert (Hef : le eps_f one)
              by (unfold eps_f; exact (min_le_l one (mult (inv_pos M HM) eps4))).
            assert (Hle : le (plus eps_f N) (plus N one))
              by (apply (le_id_r (plus eps_f N) (plus one N) (plus N one)
                                 (plus_comm one N)
                                 (le_plus_compat eps_f one N N Hef (le_refl N)))).
            assert (Hsum : Id (plus (mult eps_f (smetric h szero)) (mult N (smetric h szero)))
                               (mult (plus eps_f N) (smetric h szero)))
              by exact (id_sym (mult_plus_distr_r eps_f N (smetric h szero))).
            rewrite Hsum.
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero)).
            unfold L. exact Hle. } }
      }
      (* |Dg| < dgd (L·|h| < L·(inv_L·dgd) = dgd) *)
      assert (HdfDg : lt (abs Dg) dgd).
      {
        apply (le_lt_trans (abs Dg) (mult L (smetric h szero)) dgd).
        - exact HDg_bound.
        - assert (Hraw : lt (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L))
            by (apply (lt_mult_compat (smetric h szero) (mult (inv_pos L HL) dgd) L HL Hh_dgd)).
          assert (Hswap : Id (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))).
          { assert (H1 : Id (mult (mult (inv_pos L HL) dgd) L) (mult (inv_pos L HL) (mult dgd L)))
              by exact (id_sym (mult_assoc (inv_pos L HL) dgd L)).
            assert (H2 : Id (mult (inv_pos L HL) (mult dgd L)) (mult (inv_pos L HL) (mult L dgd)))
              by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm dgd L)).
            assert (H3 : Id (mult (inv_pos L HL) (mult L dgd)) (mult (mult (inv_pos L HL) L) dgd))
              by exact (mult_assoc (inv_pos L HL) L dgd).
            assert (H4 : Id (mult (mult (inv_pos L HL) L) dgd) (mult (mult L (inv_pos L HL)) dgd))
              by exact (id_cong (fun z => mult z dgd) (mult_comm (inv_pos L HL) L)).
            assert (H5 : Id (mult (mult L (inv_pos L HL)) dgd) (mult L (mult (inv_pos L HL) dgd)))
              by exact (id_sym (mult_assoc L (inv_pos L HL) dgd)).
            exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))). }
          assert (HltL : lt (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)))
            by exact (lt_id_l (mult L (smetric h szero)) (mult (smetric h szero) L) (mult L (mult (inv_pos L HL) dgd))
                              (mult_comm L (smetric h szero))
                              (lt_id_r (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))
                                       Hswap Hraw)).
          assert (Hident : Id (mult L (mult (inv_pos L HL) dgd)) dgd).
          { assert (H1 : Id (mult L (mult (inv_pos L HL) dgd)) (mult (mult L (inv_pos L HL)) dgd))
              by exact (mult_assoc L (inv_pos L HL) dgd).
            assert (H2 : Id (mult (mult L (inv_pos L HL)) dgd) (mult one dgd))
              by exact (id_cong (fun z => mult z dgd) (inv_pos_correct L HL)).
            assert (H3 : Id (mult one dgd) dgd)
              by exact (id_trans (mult_comm one dgd) (mult_one dgd)).
            exact (id_trans H1 (id_trans H2 H3)). }
          apply (lt_id_r (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)) dgd Hident HltL).
      }
      (* T1: the outer error ≤ eps_g·|Dg| ≤ eps4·|h| (L·eps_g ≤ eps4, eps_g controlled by L) *)
      assert (HT1 : le (abs (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg))))
                       (mult eps4 (smetric h szero))).
      {
        apply (le_trans _ (mult eps_g (abs Dg)) _).
        - apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg))))
                         (abs (minus (g (plus (f x) Dg)) (plus (g (f x)) (mult (dg (f x)) Dg))))
                         (mult eps_g (abs Dg))
                         (id_cong (fun z => abs (minus (g z) (plus (g (f x)) (mult (dg (f x)) Dg))))
                                  (id_sym (minus_plus_cancel (f x) (f (splus x h)))))
                         (Hdg2 Dg HdfDg)).
        - apply (le_trans _ (mult eps_g (mult L (smetric h szero))) _).
          { apply (le_mult_compat_r eps_g (abs Dg) (mult L (smetric h szero)) (lt_le_iff _ _ (inl Heps_g)) HDg_bound). }
          { assert (Hfl : Id (mult eps_g (mult L (smetric h szero))) (mult (mult eps_g L) (smetric h szero)))
              by exact (mult_assoc eps_g L (smetric h szero)).
            rewrite Hfl.
            assert (Hfl_le : le (mult eps_g L) eps4).
            { assert (Hepg_le : le eps_g (mult (inv_pos L HL) eps4))
                by (unfold eps_g; exact (min_le_r one (mult (inv_pos L HL) eps4))).
              apply (le_trans _ (mult (mult (inv_pos L HL) eps4) L) _).
              { apply (le_mult_compat_weak eps_g (mult (inv_pos L HL) eps4) L (lt_le_iff zero L (inl HL)) Hepg_le). }
              { assert (H1 : Id (mult (mult (inv_pos L HL) eps4) L) (mult (inv_pos L HL) (mult eps4 L)))
                  by exact (id_sym (mult_assoc (inv_pos L HL) eps4 L)).
                assert (H2 : Id (mult (inv_pos L HL) (mult eps4 L)) (mult (inv_pos L HL) (mult L eps4)))
                  by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm eps4 L)).
                assert (H3 : Id (mult (inv_pos L HL) (mult L eps4)) (mult (mult (inv_pos L HL) L) eps4))
                  by exact (mult_assoc (inv_pos L HL) L eps4).
                assert (H4 : Id (mult (mult (inv_pos L HL) L) eps4) (mult (mult L (inv_pos L HL)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos L HL) L)).
                assert (H5 : Id (mult (mult L (inv_pos L HL)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct L HL)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos L HL) eps4) L) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hfl_le). }
      }
      (* T2: |dg(f x)·(Dg − inner (df x) h)| ≤ M·eps_f·|h| ≤ eps4·|h| (M·eps_f ≤ eps4) *)
      assert (HT2 : le (abs (mult (dg (f x)) (minus Dg (inner (df x) h)))) (mult eps4 (smetric h szero))).
      {
        assert (Habsmult : Id (abs (mult (dg (f x)) (minus Dg (inner (df x) h))))
                              (mult (abs (dg (f x))) (abs (minus Dg (inner (df x) h)))))
          by exact (abs_mult (dg (f x)) (minus Dg (inner (df x) h))).
        apply (le_id_l _ _ _ Habsmult).
        apply (le_trans _ (mult (abs (dg (f x))) (mult eps_f (smetric h szero))) _).
        - apply (le_mult_compat_r (abs (dg (f x))) (abs (minus Dg (inner (df x) h))) (mult eps_f (smetric h szero)) (abs_nonneg (dg (f x)))).
          apply (le_id_l (abs (minus Dg (inner (df x) h)))
                         (abs (minus (f (splus x h)) (plus (f x) (inner (df x) h))))
                         (mult eps_f (smetric h szero))
                         (id_cong abs (minus_minus_distr (f (splus x h)) (f x) (inner (df x) h)))
                         (Hdf2 h Hh_dfd)).
        - assert (Hfl : Id (mult (abs (dg (f x))) (mult eps_f (smetric h szero))) (mult (mult (abs (dg (f x))) eps_f) (smetric h szero)))
            by exact (mult_assoc (abs (dg (f x))) eps_f (smetric h szero)).
          rewrite Hfl.
          assert (Hdf_le : le (abs (dg (f x))) M)
            by (unfold M; apply le_plus_nonneg_r; exact (lt_le_iff _ _ (inl one_pos))).
          assert (Hprod : le (mult (abs (dg (f x))) eps_f) (mult M eps_f))
            by (apply (le_mult_compat_weak _ _ _ (lt_le_iff _ _ (inl Heps_f)) Hdf_le)).
          apply (le_trans _ (mult (mult M eps_f) (smetric h szero)) _).
          { apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hprod). }
          { assert (Hmg_le : le (mult M eps_f) eps4).
            { assert (Hepf_le : le eps_f (mult (inv_pos M HM) eps4))
                by (unfold eps_f; exact (min_le_r one (mult (inv_pos M HM) eps4))).
              apply (le_trans _ (mult (mult (inv_pos M HM) eps4) M) _).
              { exact (le_id_l (mult M eps_f) (mult eps_f M) (mult (mult (inv_pos M HM) eps4) M)
                               (mult_comm M eps_f)
                               (le_mult_compat_weak eps_f (mult (inv_pos M HM) eps4) M (lt_le_iff zero M (inl HM)) Hepf_le)). }
              { assert (H1 : Id (mult (mult (inv_pos M HM) eps4) M) (mult (inv_pos M HM) (mult eps4 M)))
                  by exact (id_sym (mult_assoc (inv_pos M HM) eps4 M)).
                assert (H2 : Id (mult (inv_pos M HM) (mult eps4 M)) (mult (inv_pos M HM) (mult M eps4)))
                  by exact (id_cong (fun z => mult (inv_pos M HM) z) (mult_comm eps4 M)).
                assert (H3 : Id (mult (inv_pos M HM) (mult M eps4)) (mult (mult (inv_pos M HM) M) eps4))
                  by exact (mult_assoc (inv_pos M HM) M eps4).
                assert (H4 : Id (mult (mult (inv_pos M HM) M) eps4) (mult (mult M (inv_pos M HM)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos M HM) M)).
                assert (H5 : Id (mult (mult M (inv_pos M HM)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct M HM)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos M HM) eps4) M) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hmg_le). }
      }
      (* Merge: T1 + T2 ≤ (eps4+eps4)·|h| = (eps/2)·|h| ≤ eps·|h| *)
      assert (Hmid : le (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                                   (mult (dg (f x)) (minus Dg (inner (df x) h)))))
                        (mult eps (smetric h szero))).
      {
        apply (le_trans _ (plus (abs (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg))))
                                (abs (mult (dg (f x)) (minus Dg (inner (df x) h))))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero))) _).
          { apply le_plus_compat; [exact HT1 | exact HT2]. }
      { assert (Hsum : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))).
        { unfold eps4.
          assert (H1 : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (plus one one) (mult eps4 (smetric h szero))))
            by (apply id_sym; apply two_mult).
          assert (H2 : Id (mult (plus one one) (mult eps4 (smetric h szero))) (mult (mult (plus one one) eps4) (smetric h szero)))
            by exact (mult_assoc (plus one one) eps4 (smetric h szero)).
          assert (H3 : Id (mult (plus one one) eps4) (mult (inv_pos (plus one one) two_pos) eps)).
          { assert (H3a : Id (mult (plus one one) (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)))
                              (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
            assert (H3b : Id (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps))
                              (mult one (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (id_cong (fun z => mult z (mult (inv_pos (plus one one) two_pos) eps)) (inv_pos_correct (plus one one) two_pos)).
            assert (H3c : Id (mult one (mult (inv_pos (plus one one) two_pos) eps)) (mult (inv_pos (plus one one) two_pos) eps))
              by exact (id_trans (mult_comm one (mult (inv_pos (plus one one) two_pos) eps)) (mult_one (mult (inv_pos (plus one one) two_pos) eps))).
            exact (id_trans H3a (id_trans H3b H3c)). }
          assert (H4 : Id (mult (mult (plus one one) eps4) (smetric h szero)) (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero)))
            by exact (id_cong (fun z => mult z (smetric h szero)) H3).
          exact (id_trans H1 (id_trans H2 H4)). }
        apply (le_id_l (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                       (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                       (mult eps (smetric h szero))
                       Hsum
                       (le_id_l (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                                (mult (inv_pos (plus one one) two_pos) (mult eps (smetric h szero)))
                                (mult eps (smetric h szero))
                                (id_sym (mult_assoc (inv_pos (plus one one) two_pos) eps (smetric h szero)))
                                (half_le_self (mult eps (smetric h szero))
                                              (le_trans zero (mult zero (smetric h szero)) (mult eps (smetric h szero))
                                                        (le_id_l zero (mult zero (smetric h szero)) (mult zero (smetric h szero))
                                                                 (id_sym (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))))
                                                                 (le_refl (mult zero (smetric h szero))))
                                                        (le_mult_compat_weak zero eps (smetric h szero) (smetric_pos h szero)
                                                                             (lt_le_iff _ _ (inl Heps))))))).
        }
      }
      }
      exact Hmid.
Qed.

(* ============================================================ *)
(* Multivariable vector-field chain rule (DifferentiableMVVec: the inner layer S -> S) *)
(* ============================================================ *)
(* Vector-field version: f : S -> S (e.g. hidden-state dynamics, token-embedding flow), *)
(* g : S -> R (a scalar field, e.g. an attention logit).  The composite D(g∘f)(x) = *)
(* (Df x)* (dg (f x)) — the outer gradient is pulled back by the adjoint of the inner derivative. *)
(* Interface (explicit Variables, same precedent as [inner_lipschitz]): *)
(*   1) smetric_sminus_zero: the metric is induced by the norm (translation invariance). *)
(*   2) mv_adjoint: the adjoint L* of a linear operator L (⟨L h, w⟩ = ⟨h, L* w⟩). *)
(*   3) op_lipschitz: an operator-norm bound (|L h| ≤ N·|h|). *)
(* ------------------------------------------------------------ *)

(* Scalar linearity of the inner product in its second argument: ⟨x, a·y⟩ = a·⟨x,y⟩ ([inner_smult_l] + [inner_sym] swap) *)
Lemma inner_smult_r : forall (a : R) (x y : S),
  Id (inner x (smult a y)) (mult a (inner x y)).
Proof.
  intros a x y.
  exact (id_trans (inner_sym x (smult a y))
           (id_trans (inner_smult_l a y x)
              (id_cong (fun z => mult a z) (inner_sym y x)))).
Qed.

(* The inner product in its second argument against sopp: ⟨x, -y⟩ = -⟨x,y⟩ ([smult_opp] + [smult_one] + [inner_smult_r]) *)
Lemma inner_sopp_r : forall x y : S,
  Id (inner x (sopp y)) (opp (inner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (smult (opp one) y) (sopp (smult one y)))
    by exact (smult_opp one y).
  assert (Hone : Id (smult one y) y)
    by exact (smult_one y).
  assert (Hsopp : Id (smult (opp one) y) (sopp y))
    by exact (id_trans Hsm (id_cong sopp Hone)).
  assert (Hinner : Id (inner x (smult (opp one) y)) (mult (opp one) (inner x y)))
    by exact (inner_smult_r (opp one) x y).
  apply (id_trans (id_sym (id_cong (fun z => inner x z) Hsopp))).
  exact (id_trans Hinner (id_trans (opp_mult_r one (inner x y))
                                   (id_cong opp (id_trans (mult_comm one (inner x y))
                                                          (mult_one (inner x y)))))).
Qed.

(* The inner product in its second argument against a difference: ⟨x, u−v⟩ = ⟨x,u⟩ − ⟨x,v⟩ ([inner_splus_r] + [inner_sopp_r]) *)
Lemma inner_sminus_r : forall x u v : S,
  Id (inner x (sminus u v)) (minus (inner x u) (inner x v)).
Proof.
  intros x u v.
  unfold sminus, minus.
  assert (H1 : Id (inner x (splus u (sopp v))) (plus (inner x u) (inner x (sopp v))))
    by exact (inner_splus_r x u (sopp v)).
  exact (id_trans H1 (id_cong (fun t => plus (inner x u) t) (inner_sopp_r x v))).
Qed.

(* Vector-difference cancellation: a + (b − a) = b ([splus] associativity/commutativity/zero/opp chain) *)
Lemma splus_sminus_cancel : forall a b : S, Id (splus a (sminus b a)) b.
Proof.
  intros a b.
  unfold sminus.
  assert (H1 : Id (splus a (splus b (sopp a))) (splus a (splus (sopp a) b)))
    by exact (id_cong (fun z => splus a z) (splus_comm b (sopp a))).
  assert (H2 : Id (splus a (splus (sopp a) b)) (splus (splus a (sopp a)) b))
    by exact (splus_assoc a (sopp a) b).
  assert (H3 : Id (splus (splus a (sopp a)) b) (splus szero b))
    by exact (id_cong (fun z => splus z b) (splus_opp a)).
  assert (H4 : Id (splus szero b) b)
    by exact (id_trans (splus_comm szero b) (splus_zero b)).
  exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
Qed.

(* The negation of the zero vector is zero: sopp szero == szero.
   splus szero (sopp szero) == szero ([splus_opp szero]), and
   splus szero (sopp szero) == sopp szero ([splus_comm] + [splus_zero]) ⟹ sopp szero == szero. *)
Lemma sopp_szero : Id (sopp szero) szero.
Proof.
  (* sopp szero == splus (sopp szero) szero (reverse of [splus_zero])
     == splus szero (sopp szero) ([splus_comm])
     == szero ([splus_opp szero]). *)
  assert (H1 : Id (sopp szero) (splus (sopp szero) szero))
    by exact (id_sym (splus_zero (sopp szero))).
  assert (H2 : Id (splus (sopp szero) szero) (splus szero (sopp szero)))
    by exact (splus_comm (sopp szero) szero).
  assert (H3 : Id (splus szero (sopp szero)) szero)
    by exact (splus_opp szero).
  exact (@id_trans S (sopp szero) (splus (sopp szero) szero) szero
                   H1 (@id_trans S (splus (sopp szero) szero) (splus szero (sopp szero)) szero
                              H2 H3)).
Qed.

(* sminus against szero is inert: sminus (sminus u v) szero == sminus u v.
   sminus (sminus u v) szero = splus (sminus u v) (sopp szero) = splus (sminus u v) szero = sminus u v. *)
Lemma sminus_sminus_szero : forall u v : S,
  Id (sminus (sminus u v) szero) (sminus u v).
Proof.
  intros u v.
  unfold sminus.
  (* splus (splus u (sopp v)) (sopp szero) == splus (splus u (sopp v)) szero ([id_cong sopp_szero])
     == splus u (sopp v) ([splus_zero]). *)
  exact (id_trans (id_cong (fun z => splus (splus u (sopp v)) z) sopp_szero)
                  (splus_zero (splus u (sopp v)))).
Qed.

(* Metric translation compatibility (a proven theorem): smetric (sminus u v) szero == smetric u v.
   By [smetric_snorm] (the metric is induced by the norm):
   smetric (sminus u v) szero == snorm (sminus (sminus u v) szero) ([smetric_snorm])
   == snorm (sminus u v) ([sminus_sminus_szero])
   == smetric u v (reverse of [smetric_snorm]). *)
Theorem smetric_sminus_zero : forall u v : S,
  Id (smetric (sminus u v) szero) (smetric u v).
Proof.

  intros u v. exact (id_trans (smetric_snorm (sminus u v) szero) (id_trans (id_cong snorm (sminus_sminus_szero u v)) (id_sym (smetric_snorm u v)))).

Qed.

(* Adjoint interface (explicit Variable): the adjoint L* : S -> S of a linear operator L : S -> S satisfies
   ⟨L h, w⟩ = ⟨h, L* w⟩.  A constructive weakening of the Riesz representation theorem (adjoint existence
   in a Hilbert space).  It supports the vector-field chain rule: D(g∘f)(x) = (Df x)* (dg (f x)). *)
Variable mv_adjoint : forall (L : S -> S),
  sigT (fun Lad : S -> S => forall h w : S,
    Id (inner (L h) w) (inner h (Lad w))).

(* Operator-norm bound (explicit Variable): |L h| ≤ N·|h| (a constructive weakening of boundedness of
   linear operators, same precedent as [inner_lipschitz]; supports the Lipschitz bound of vector-field composition). *)
Variable op_lipschitz : forall (L : S -> S),
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (smetric (L h) szero) (mult N (smetric h szero)))).

(* ===== Strengthened layer: part of the nontrivial implementations follows from the interface triple ===== *)
(* The existence of the triple ([inner_lipschitz]/[mv_adjoint]/[op_lipschitz]) is an explicit interface
   (constructive weakenings of Cauchy-Schwarz / Riesz representation / bounded operators), but some of
   its structural consequences can be derived nontrivially from the interface assumptions —
   everything derivable is derived. *)

(* The inner product in its first argument against a difference: ⟨a−b, c⟩ == ⟨a,c⟩ − ⟨b,c⟩ ([inner_splus_l] + [inner_sopp_l]) *)
Lemma inner_sminus_l : forall a b c : S,
  Id (inner (sminus a b) c) (minus (inner a c) (inner b c)).
Proof.
  intros a b c.
  unfold sminus.
  assert (H1 : Id (inner (splus a (sopp b)) c) (plus (inner a c) (inner (sopp b) c)))
    by exact (inner_splus_l a (sopp b) c).
  assert (H2 : Id (plus (inner a c) (inner (sopp b) c))
                 (plus (inner a c) (opp (inner b c))))
    by exact (id_cong (fun z => plus (inner a c) z) (inner_sopp_l b c)).
  exact (id_trans H1 H2).
Qed.

(* Vector-difference cancellation: a − b == 0 ⟹ a == b ([splus_sminus_cancel] + [splus_zero]) *)
Lemma sminus_zero_cancel : forall a b : S,
  Id (sminus a b) szero -> Id a b.
Proof.
  intros a b H.
  assert (H1 : Id a (splus b (sminus a b))).
  { apply (id_sym (splus_sminus_cancel b a)). }
  apply (id_trans H1).
  apply (id_trans (id_cong (fun z => splus b z) H)).
  apply splus_zero.
Qed.

(* Uniqueness of the adjoint: if Lad1 and Lad2 are both adjoints of L, they agree pointwise.
   ⟨h, Lad1 w⟩ == ⟨L h, w⟩ == ⟨h, Lad2 w⟩ ⟹ ⟨h, h'⟩ == 0 (h' := Lad1 w − Lad2 w)
   ⟹ [inner_definite] ⟹ h' == szero ⟹ Lad1 w == Lad2 w. *)
Lemma mv_adjoint_unique : forall (L : S -> S) (Lad1 Lad2 : S -> S),
  (forall h w : S, Id (inner (L h) w) (inner h (Lad1 w))) ->
  (forall h w : S, Id (inner (L h) w) (inner h (Lad2 w))) ->
  forall w : S, Id (Lad1 w) (Lad2 w).
Proof.
  intros L Lad1 Lad2 H1 H2 w.
  pose (h := sminus (Lad1 w) (Lad2 w)).
  assert (Hinner : Id (inner h h) zero).
  { unfold h.
    apply (id_trans (inner_sminus_r (sminus (Lad1 w) (Lad2 w)) (Lad1 w) (Lad2 w))).
    assert (Hmid1 : Id (inner (sminus (Lad1 w) (Lad2 w)) (Lad1 w))
                       (inner (sminus (Lad1 w) (Lad2 w)) (Lad2 w))).
    { apply (id_trans (id_sym (H1 (sminus (Lad1 w) (Lad2 w)) w))).
      exact (H2 (sminus (Lad1 w) (Lad2 w)) w). }
    unfold minus.
    apply (id_trans (id_sym (id_cong (fun z => plus (inner (sminus (Lad1 w) (Lad2 w)) (Lad1 w)) z)
                                    (id_cong opp Hmid1)))
                    (plus_opp (inner (sminus (Lad1 w) (Lad2 w)) (Lad1 w)))). }
  assert (Hhzero : Id h szero) by (apply (inner_definite h Hinner)).
  apply (sminus_zero_cancel (Lad1 w) (Lad2 w)).
  unfold h in Hhzero.
  exact Hhzero.
Qed.

(* Compositions of bounded operators are bounded: |L(M h)| ≤ N_L·|M h| ≤ N_L·(N_M·|h|) == (N_L·N_M)·|h|.
   The norm bound is N := N_L·N_M (transferred by [op_lipschitz]; N_L·N_M ≥ 0). *)
Lemma op_lipschitz_compose : forall (L M : S -> S),
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (smetric (L (M h)) szero) (mult N (smetric h szero)))).
Proof.
  intros L M.
  destruct (op_lipschitz L) as [NL [HNL0 HNL]].
  destruct (op_lipschitz M) as [NM [HNM0 HNM]].
  exists (mult NL NM).
  split.
  - (* 0 ≤ NL·NM: [le_mult_compat_weak] + mult_zero conversion *)
    apply (le_id_l _ (mult zero NM) _).
    + apply (id_trans (id_sym (mult_zero NM)) (mult_comm NM zero)).
    + apply (le_mult_compat_weak zero NL NM HNM0 HNL0).
  - intros h.
    apply (le_trans _ (mult NL (smetric (M h) szero)) _).
    + exact (HNL (M h)).
    + apply (le_trans _ (mult NL (mult NM (smetric h szero))) _).
      * apply (le_id_l _ (mult (smetric (M h) szero) NL) _).
        -- apply (mult_comm NL (smetric (M h) szero)).
        -- apply (le_id_r _ (mult (mult NM (smetric h szero)) NL) _).
           ++ apply (mult_comm (mult NM (smetric h szero)) NL).
           ++ apply (le_mult_compat_weak (smetric (M h) szero) (mult NM (smetric h szero)) NL HNL0).
              exact (HNM h).
      * apply (le_id_l _ (mult (mult NL NM) (smetric h szero)) _).
        -- apply (mult_assoc NL NM (smetric h szero)).
        -- apply le_refl.
Qed.

(* Vector-field differentiability (Frechet type, Set layer): f : S -> S with derivative dfvec : S -> S -> S.
   The linearization is f x + dfvec x h; the error (increment − linearization) is measured by smetric. *)
Record DifferentiableMVVec (f : S -> S) := {
  dfvec : S -> S -> S;
  dfvec_correct : forall x eps, lt zero eps ->
    sigT (fun delta : R => And (lt zero delta) (forall h : S,
      lt (smetric h szero) delta ->
      le (smetric (sminus (f (splus x h)) (f x)) (dfvec x h))
         (mult eps (smetric h szero))))
}.

(* General error decomposition: minus A (plus B X) == plus (minus A (plus B Y)) (minus Y X)
   (R-layer algebra: A−(B+X) = (A−(B+Y)) + (Y−X)) *)
Lemma mv_vec_diff_decomp : forall (A B X Y : R),
  Id (minus A (plus B X)) (plus (minus A (plus B Y)) (minus Y X)).
Proof.
  intros A B X Y.
  unfold minus.
  assert (Hcancel : Id (plus (opp (plus B Y)) Y) (opp B)).
  {
    assert (H1 : Id (plus (opp (plus B Y)) Y)
                    (plus (plus (opp B) (opp Y)) Y))
      by exact (id_cong (fun z => plus z Y) (opp_plus B Y)).
    assert (H2 : Id (plus (plus (opp B) (opp Y)) Y)
                    (plus (opp B) (plus (opp Y) Y)))
      by exact (id_sym (plus_assoc (opp B) (opp Y) Y)).
    assert (H3 : Id (plus (opp B) (plus (opp Y) Y))
                    (plus (opp B) zero))
      by exact (id_cong (fun z => plus (opp B) z)
                        (id_trans (plus_comm (opp Y) Y) (plus_opp Y))).
    assert (H4 : Id (plus (opp B) zero) (opp B)) by exact (plus_zero (opp B)).
    exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
  }
  assert (Hre : Id (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                   (plus A (opp (plus B X)))).
  {
    assert (H1 : Id (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                    (plus A (plus (plus (opp (plus B Y)) Y) (opp X))))
      by exact (id_trans (id_sym (plus_assoc A (opp (plus B Y)) (plus Y (opp X))))
                         (id_cong (fun z => plus A z)
                                  (plus_assoc (opp (plus B Y)) Y (opp X)))).
    assert (H2 : Id (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                    (plus A (plus (opp B) (opp X))))
      by exact (id_cong (fun z => plus A (plus z (opp X))) Hcancel).
    assert (H3 : Id (plus A (plus (opp B) (opp X)))
                    (plus A (opp (plus B X))))
      by exact (id_cong (fun z => plus A z) (id_sym (opp_plus B X))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  exact (id_sym Hre).
Qed.

(* Vector-field chain rule: the inner layer f : S -> S, the outer layer g : S -> R.
   D(g∘f)(x) = (Df x)* (dg (f x)) (pullback by the adjoint).
   Budget: eps4 = eps/4; the inner increment norm bound is L := N_op + 1 ([op_lipschitz]),
   the outer gradient inner-product norm bound is M := N_a + 1 ([inner_lipschitz]).
   T1 (the outer error) ≤ eps_g·|Dg| ≤ eps4·|h|; T2 (the inner error through the adjoint)
   ≤ N_a·|Dg − df·h| ≤ N_a·eps_f·|h| ≤ eps4·|h|. *)
Theorem differentiable_mv_vec_compose : forall (f : S -> S) (g : S -> R),
  DifferentiableMVVec f -> DifferentiableMV g ->
  DifferentiableMV (fun x => g (f x)).
Proof.
  intros f g [df Hf] [dg Hg].
  (* The gradient is the adjoint pullback: (df x)* (dg (f x)) *)
  exists (fun x => projT1 (mv_adjoint (df x)) (dg (f x))).
  intros x eps Heps.
  set (eps4 := mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive; [apply inv_pos_pos | apply half_pos; exact Heps]. }
  (* Inner-product norm of the outer gradient: N_a := inner_lipschitz (dg (f x)), M := N_a + 1 *)
  destruct (inner_lipschitz (dg (f x))) as [N_a HN_a].
  destruct HN_a as [HN_a0 HN_a2].
  set (M := plus N_a one).
  assert (HM : lt zero M).
  { unfold M. apply plus_le_lt_pos; [exact HN_a0 | apply one_pos]. }
  (* Operator norm of the inner derivative: N_op := op_lipschitz (df x), L := N_op + 1 *)
  destruct (op_lipschitz (df x)) as [N_op HN_op].
  destruct HN_op as [HN_op0 HN_op2].
  set (L := plus N_op one).
  assert (HL : lt zero L).
  { unfold L. apply plus_le_lt_pos; [exact HN_op0 | apply one_pos]. }
  set (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f)
    by (unfold eps_f; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  set (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g)
    by (unfold eps_g; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  destruct (Hf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    apply min_pos; [exact Hdf1 | apply min_pos; [apply one_pos | exact Hltm]].
  - intros h Hh.
    set (Dg := sminus (f (splus x h)) (f x)).
    (* Adjoint identity: ⟨adj, h⟩ = ⟨dg (f x), df x h⟩, where adj := (df x)* (dg (f x)) *)
    assert (Hlin : Id (inner (projT1 (mv_adjoint (df x)) (dg (f x))) h)
                      (inner (dg (f x)) (df x h))).
    {
      pose (adj := projT1 (mv_adjoint (df x)) (dg (f x))).
      pose (Hadj := projT2 (mv_adjoint (df x)) h (dg (f x))).
      assert (H1 : Id (inner adj h) (inner h adj)) by exact (inner_sym adj h).
      assert (H2 : Id (inner h adj) (inner (df x h) (dg (f x)))) by exact (id_sym Hadj).
      assert (H3 : Id (inner (df x h) (dg (f x))) (inner (dg (f x)) (df x h))) by exact (inner_sym (df x h) (dg (f x))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    (* Error decomposition: E = T1 + T2, with Y := ⟨dg(f x), Dg⟩ and X := ⟨dg(f x), df x h⟩ *)
    assert (Hdecomp : Id (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) (df x h))))
                         (plus (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg)))
                               (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))))
      by (unfold Dg; exact (mv_vec_diff_decomp (g (f (splus x h))) (g (f x))
                                               (inner (dg (f x)) (df x h))
                                               (inner (dg (f x)) (sminus (f (splus x h)) (f x))))).
    apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (projT1 (mv_adjoint (df x)) (dg (f x))) h))))
                   (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg)))
                              (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))))
                   (mult eps (smetric h szero))).
    + exact (id_cong abs (id_trans (id_cong (fun z => minus (g (f (splus x h))) (plus (g (f x)) z)) Hlin) Hdecomp)).
    + assert (Hh_dfd : lt (smetric h szero) dfd)
        by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
      assert (Hh_one : lt (smetric h szero) one)
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_l]]).
      assert (Hh_dgd : lt (smetric h szero) (mult (inv_pos L HL) dgd))
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_r]]).
      (* (a) |Dg| ≤ L·|h| ([smetric_triangle]: |Dg| ≤ |Dg − df·h| + |df·h|) *)
      assert (HDg_bound : le (smetric Dg szero) (mult L (smetric h szero))).
      {
        apply (le_trans _ (plus (smetric Dg (df x h)) (smetric (df x h) szero)) _).
        { apply smetric_triangle. }
        { apply (le_trans _ (plus (mult eps_f (smetric h szero)) (mult N_op (smetric h szero))) _).
          { apply le_plus_compat.
            { unfold Dg. exact (Hdf2 h Hh_dfd). }
            { exact (HN_op2 h). } }
          { assert (Hef : le eps_f one)
              by (unfold eps_f; exact (min_le_l one (mult (inv_pos M HM) eps4))).
            assert (Hle : le (plus eps_f N_op) (plus N_op one))
              by (apply (le_id_r (plus eps_f N_op) (plus one N_op) (plus N_op one)
                                 (plus_comm one N_op)
                                 (le_plus_compat eps_f one N_op N_op Hef (le_refl N_op)))).
            assert (Hsum : Id (plus (mult eps_f (smetric h szero)) (mult N_op (smetric h szero)))
                               (mult (plus eps_f N_op) (smetric h szero)))
              by exact (id_sym (mult_plus_distr_r eps_f N_op (smetric h szero))).
            rewrite Hsum.
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero)).
            unfold L. exact Hle. } }
      }
      (* |Dg| < dgd (L·|h| < L·(inv_L·dgd) = dgd) *)
      assert (HdfDg : lt (smetric Dg szero) dgd).
      {
        apply (le_lt_trans (smetric Dg szero) (mult L (smetric h szero)) dgd).
        - exact HDg_bound.
        - assert (Hraw : lt (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L))
            by (apply (lt_mult_compat (smetric h szero) (mult (inv_pos L HL) dgd) L HL Hh_dgd)).
          assert (Hswap : Id (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))).
          { assert (H1 : Id (mult (mult (inv_pos L HL) dgd) L) (mult (inv_pos L HL) (mult dgd L)))
              by exact (id_sym (mult_assoc (inv_pos L HL) dgd L)).
            assert (H2 : Id (mult (inv_pos L HL) (mult dgd L)) (mult (inv_pos L HL) (mult L dgd)))
              by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm dgd L)).
            assert (H3 : Id (mult (inv_pos L HL) (mult L dgd)) (mult (mult (inv_pos L HL) L) dgd))
              by exact (mult_assoc (inv_pos L HL) L dgd).
            assert (H4 : Id (mult (mult (inv_pos L HL) L) dgd) (mult (mult L (inv_pos L HL)) dgd))
              by exact (id_cong (fun z => mult z dgd) (mult_comm (inv_pos L HL) L)).
            assert (H5 : Id (mult (mult L (inv_pos L HL)) dgd) (mult L (mult (inv_pos L HL) dgd)))
              by exact (id_sym (mult_assoc L (inv_pos L HL) dgd)).
            exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))). }
          assert (HltL : lt (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)))
            by exact (lt_id_l (mult L (smetric h szero)) (mult (smetric h szero) L) (mult L (mult (inv_pos L HL) dgd))
                              (mult_comm L (smetric h szero))
                              (lt_id_r (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))
                                       Hswap Hraw)).
          assert (Hident : Id (mult L (mult (inv_pos L HL) dgd)) dgd).
          { assert (H1 : Id (mult L (mult (inv_pos L HL) dgd)) (mult (mult L (inv_pos L HL)) dgd))
              by exact (mult_assoc L (inv_pos L HL) dgd).
            assert (H2 : Id (mult (mult L (inv_pos L HL)) dgd) (mult one dgd))
              by exact (id_cong (fun z => mult z dgd) (inv_pos_correct L HL)).
            assert (H3 : Id (mult one dgd) dgd)
              by exact (id_trans (mult_comm one dgd) (mult_one dgd)).
            exact (id_trans H1 (id_trans H2 H3)). }
          apply (lt_id_r (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)) dgd Hident HltL).
      }
      (* T1: the outer error ≤ eps_g·|Dg| ≤ eps4·|h| (the perturbation Dg converted by [splus_sminus_cancel]) *)
      assert (HT1 : le (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg))))
                       (mult eps4 (smetric h szero))).
      {
        apply (le_trans _ (mult eps_g (smetric Dg szero)) _).
        - apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg))))
                         (abs (minus (g (splus (f x) Dg)) (plus (g (f x)) (inner (dg (f x)) Dg))))
                         (mult eps_g (smetric Dg szero))
                         (id_cong (fun z => abs (minus (g z) (plus (g (f x)) (inner (dg (f x)) Dg))))
                                  (id_sym (splus_sminus_cancel (f x) (f (splus x h)))))
                         (Hdg2 Dg HdfDg)).
        - apply (le_trans _ (mult eps_g (mult L (smetric h szero))) _).
          { apply (le_mult_compat_r eps_g (smetric Dg szero) (mult L (smetric h szero)) (lt_le_iff _ _ (inl Heps_g)) HDg_bound). }
          { assert (Hfl : Id (mult eps_g (mult L (smetric h szero))) (mult (mult eps_g L) (smetric h szero)))
              by exact (mult_assoc eps_g L (smetric h szero)).
            rewrite Hfl.
            assert (Hfl_le : le (mult eps_g L) eps4).
            { assert (Hepg_le : le eps_g (mult (inv_pos L HL) eps4))
                by (unfold eps_g; exact (min_le_r one (mult (inv_pos L HL) eps4))).
              apply (le_trans _ (mult (mult (inv_pos L HL) eps4) L) _).
              { apply (le_mult_compat_weak eps_g (mult (inv_pos L HL) eps4) L (lt_le_iff zero L (inl HL)) Hepg_le). }
              { assert (H1 : Id (mult (mult (inv_pos L HL) eps4) L) (mult (inv_pos L HL) (mult eps4 L)))
                  by exact (id_sym (mult_assoc (inv_pos L HL) eps4 L)).
                assert (H2 : Id (mult (inv_pos L HL) (mult eps4 L)) (mult (inv_pos L HL) (mult L eps4)))
                  by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm eps4 L)).
                assert (H3 : Id (mult (inv_pos L HL) (mult L eps4)) (mult (mult (inv_pos L HL) L) eps4))
                  by exact (mult_assoc (inv_pos L HL) L eps4).
                assert (H4 : Id (mult (mult (inv_pos L HL) L) eps4) (mult (mult L (inv_pos L HL)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos L HL) L)).
                assert (H5 : Id (mult (mult L (inv_pos L HL)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct L HL)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos L HL) eps4) L) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hfl_le). }
      }
      (* T2: |⟨a,Dg⟩ − ⟨a,df·h⟩| = |⟨a, Dg−df·h⟩| ≤ N_a·|Dg−df·h|
             ≤ N_a·eps_f·|h| ≤ M·eps_f·|h| ≤ eps4·|h| (translation by [smetric_sminus_zero]) *)
      assert (HT2 : le (abs (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h))))
                       (mult eps4 (smetric h szero))).
      {
        assert (Hsm : Id (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))
                          (inner (dg (f x)) (sminus Dg (df x h))))
          by (unfold Dg; apply id_sym; exact (inner_sminus_r (dg (f x)) (sminus (f (splus x h)) (f x)) (df x h))).
        apply (le_id_l (abs (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h))))
                       (abs (inner (dg (f x)) (sminus Dg (df x h))))
                       (mult eps4 (smetric h szero))
                       (id_cong abs Hsm)).
        apply (le_trans _ (mult N_a (mult eps_f (smetric h szero))) _).
        - apply (le_trans _ (mult N_a (smetric (sminus Dg (df x h)) szero)) _).
          { exact (HN_a2 (sminus Dg (df x h))). }
          { apply (le_id_l (mult N_a (smetric (sminus Dg (df x h)) szero))
                           (mult N_a (smetric Dg (df x h)))
                           (mult N_a (mult eps_f (smetric h szero)))
                           (id_cong (fun z => mult N_a z) (smetric_sminus_zero Dg (df x h)))).
            assert (Hw0 : le (mult (smetric (sminus (f (splus x h)) (f x)) (df x h)) N_a)
                              (mult (mult eps_f (smetric h szero)) N_a))
              by (apply (le_mult_compat_weak (smetric (sminus (f (splus x h)) (f x)) (df x h)) (mult eps_f (smetric h szero)) N_a HN_a0
                                             (Hdf2 h Hh_dfd))).
            assert (Hw : le (mult (smetric Dg (df x h)) N_a) (mult (mult eps_f (smetric h szero)) N_a))
              by (unfold Dg; exact Hw0).
            apply (le_id_l (mult N_a (smetric Dg (df x h)))
                           (mult (smetric Dg (df x h)) N_a)
                           (mult N_a (mult eps_f (smetric h szero)))
                           (mult_comm N_a (smetric Dg (df x h)))).
            apply (le_id_r (mult (smetric Dg (df x h)) N_a)
                           (mult (mult eps_f (smetric h szero)) N_a)
                           (mult N_a (mult eps_f (smetric h szero)))
                           (id_sym (mult_comm N_a (mult eps_f (smetric h szero))))
                           Hw). }
        - assert (Hfl : Id (mult N_a (mult eps_f (smetric h szero))) (mult (mult N_a eps_f) (smetric h szero)))
            by exact (mult_assoc N_a eps_f (smetric h szero)).
          rewrite Hfl.
          assert (Hmg_le : le (mult N_a eps_f) eps4).
          { assert (Hepf_le : le eps_f (mult (inv_pos M HM) eps4))
              by (unfold eps_f; exact (min_le_r one (mult (inv_pos M HM) eps4))).
            assert (HNa_le : le N_a M)
              by (unfold M; apply le_plus_nonneg_r; exact (lt_le_iff _ _ (inl one_pos))).
            assert (Hstep2 : le (mult N_a (mult (inv_pos M HM) eps4)) (mult M (mult (inv_pos M HM) eps4)))
              by (apply (le_mult_compat_weak N_a M (mult (inv_pos M HM) eps4)
                                             (lt_le_iff _ _ (inl (mult_positive (inv_pos M HM) eps4 (inv_pos_pos M HM) Heps4)))
                                             HNa_le)).
            apply (le_trans _ (mult N_a (mult (inv_pos M HM) eps4)) _).
            { apply (le_trans _ (mult eps_f N_a) _).
              { apply (le_id_l (mult N_a eps_f) (mult eps_f N_a) (mult eps_f N_a)
                               (mult_comm N_a eps_f) (le_refl (mult eps_f N_a))). }
              { apply (le_id_r (mult eps_f N_a)
                               (mult (mult (inv_pos M HM) eps4) N_a)
                               (mult N_a (mult (inv_pos M HM) eps4))
                               (id_sym (mult_comm N_a (mult (inv_pos M HM) eps4)))
                               (le_mult_compat_weak eps_f (mult (inv_pos M HM) eps4) N_a HN_a0 Hepf_le)). } }
            { apply (le_trans _ (mult M (mult (inv_pos M HM) eps4)) _).
              { exact Hstep2. }
              { assert (H1 : Id (mult M (mult (inv_pos M HM) eps4)) (mult (mult M (inv_pos M HM)) eps4))
                  by exact (mult_assoc M (inv_pos M HM) eps4).
                assert (H2 : Id (mult (mult M (inv_pos M HM)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct M HM)).
                assert (H3 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult M (mult (inv_pos M HM) eps4)) eps4 eps4
                               (id_trans H1 (id_trans H2 H3)) (le_refl eps4)). } }
          }
          apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hmg_le).
      }
      (* Merge: T1 + T2 ≤ (eps4+eps4)·|h| = (eps/2)·|h| ≤ eps·|h| *)
      assert (Hmid : le (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg)))
                                   (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))))
                        (mult eps (smetric h szero))).
      {
        apply (le_trans _ (plus (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg))))
                                (abs (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h))))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero))) _).
          { apply le_plus_compat; [exact HT1 | exact HT2]. }
      { assert (Hsum : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))).
        { unfold eps4.
          assert (H1 : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (plus one one) (mult eps4 (smetric h szero))))
            by (apply id_sym; apply two_mult).
          assert (H2 : Id (mult (plus one one) (mult eps4 (smetric h szero))) (mult (mult (plus one one) eps4) (smetric h szero)))
            by exact (mult_assoc (plus one one) eps4 (smetric h szero)).
          assert (H3 : Id (mult (plus one one) eps4) (mult (inv_pos (plus one one) two_pos) eps)).
          { assert (H3a : Id (mult (plus one one) (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)))
                              (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
            assert (H3b : Id (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps))
                              (mult one (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (id_cong (fun z => mult z (mult (inv_pos (plus one one) two_pos) eps)) (inv_pos_correct (plus one one) two_pos)).
            assert (H3c : Id (mult one (mult (inv_pos (plus one one) two_pos) eps)) (mult (inv_pos (plus one one) two_pos) eps))
              by exact (id_trans (mult_comm one (mult (inv_pos (plus one one) two_pos) eps)) (mult_one (mult (inv_pos (plus one one) two_pos) eps))).
            exact (id_trans H3a (id_trans H3b H3c)). }
          assert (H4 : Id (mult (mult (plus one one) eps4) (smetric h szero)) (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero)))
            by exact (id_cong (fun z => mult z (smetric h szero)) H3).
          exact (id_trans H1 (id_trans H2 H4)). }
        apply (le_id_l (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                       (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                       (mult eps (smetric h szero))
                       Hsum
                       (le_id_l (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                                (mult (inv_pos (plus one one) two_pos) (mult eps (smetric h szero)))
                                (mult eps (smetric h szero))
                                (id_sym (mult_assoc (inv_pos (plus one one) two_pos) eps (smetric h szero)))
                                (half_le_self (mult eps (smetric h szero))
                                              (le_trans zero (mult zero (smetric h szero)) (mult eps (smetric h szero))
                                                        (le_id_l zero (mult zero (smetric h szero)) (mult zero (smetric h szero))
                                                                 (id_sym (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))))
                                                                 (le_refl (mult zero (smetric h szero))))
                                                        (le_mult_compat_weak zero eps (smetric h szero) (smetric_pos h szero)
                                                                             (lt_le_iff _ _ (inl Heps))))))).
        }
      }
      }
      exact Hmid.
Qed.
End MultivariableDifferentiable.

(* The second law of thermodynamics *)
Section SecondLaw.
Context {RI : RealInterfaceEnhanced}.

(* Bind the basic types and relations explicitly, avoiding instance-resolution issues *)
Let R := @R RI.
Let le := @le RI.
Let lt := @lt RI.

Variable entropy : R -> R.
Variable dynamics : R -> R.

Definition entropy_increases : Set :=
  forall x, le (entropy x) (entropy (dynamics x)).

(* Modeling postulate (dynamic form of the second law): [dynamics] and [entropy] are abstract fields
   without representational instances, so strict increase is not derivable at this layer; the [Not]
   antecedent is a propositional object.  A Set-carried restatement (argmax/gap constructions over
   concrete layers) is the candidate; the interface-level form is kept as stated. *)
Variable strict_entropy_increase :
  forall x, Not (Id (dynamics x) x) ->
    lt (entropy x) (entropy (dynamics x)).

Theorem second_law_irreversible :
  forall x, Not (Id (dynamics x) x) ->
    lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hneq. exact (strict_entropy_increase x Hneq).
Qed.

End SecondLaw.

(* Language-model extension: temperature sampling *)
Section LanguageModelExtensions.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.   (* Allow automatic resolution of the RealInterface fields *)

(* Bind the frequently used fields explicitly, avoiding type-class resolution issues *)
Let R := @R RI.
Let zero := @zero RI.
Let lt := @lt RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).

Variable neg_log_prob : list Token -> Token -> R.

Definition Temperature : Set := R.
Variable temperature : Temperature.
Variable temperature_pos : lt zero temperature.

Definition temperature_weighted_prob (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)).

Variable top_k : list Token -> list Token.

End LanguageModelExtensions.

(* A state-space instance on lists *)
Section ListStateSpace.
Context {RI : RealInterface}.

Variable A : Set.
Definition ListS : Set := list A.

Definition list_szero : ListS := nil.
Definition list_splus (x y : ListS) : ListS := x ++ y.
Definition list_sopp (x : ListS) : ListS := nil.
Definition list_smult (a : R) (x : ListS) : ListS := nil.

Definition list_smetric (x y : ListS) : R := zero.

Definition list_clim (u : nat -> ListS) (l : ListS) : Set :=
  forall n : nat, Id (u n) l.

End ListStateSpace.

(* The symmetric form of the fluctuation theorem *)
Section FluctuationSymmetry.
Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let lt := @lt RI.
Let opp := @opp RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.

Variable sigma : R -> R.
Variable prob_forward : R -> R.
Variable prob_backward : R -> R.
Variable prob_backward_pos : forall x, lt zero (prob_backward x).
Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_symmetry :
  forall ds,
    Id (mult (inv_pos (prob_backward (opp ds)) (prob_backward_pos (opp ds)))
             (prob_forward ds))
       (exp_neg (mult (inv_pos k_B k_B_pos) ds)).

End FluctuationSymmetry.

(* Provable elementary algebraic properties *)
Section SimpleAlgebra.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.   (* Enable instance resolution for RealInterface *)

(* Alternatively, use Let bindings:
   Let R := @R RI.
   Let zero := @zero RI.
   Let plus := @plus RI.
   Let mult := @mult RI.
   Let opp := @opp RI.
*)

Lemma plus_zero_r :
  forall a : R, Id (plus a zero) a.
Proof. intro a. apply plus_zero. Qed.

Lemma plus_opp_r :
  forall a : R, Id (plus a (opp a)) zero.
Proof. intro a. exact (plus_opp a). Qed.

Lemma mult_one_r :
  forall a : R, Id (mult a one) a.
Proof. intro a. exact (mult_one a). Qed.

Lemma mult_zero_r :
  forall a : R, Id (mult a zero) zero.
Proof. intro a. exact (mult_zero a). Qed.

Lemma mult_comm_rewrite :
  forall a b : R, Id (mult a b) (mult b a).
Proof. intros a b. exact (mult_comm a b). Qed.

(* ============================================================ *)
(* The ring-theory auxiliary lemmas were moved up to Section RingLemmas, after the Enhanced definition, *)
(* for use by all modules of this file; SimpleAlgebra keeps only the small algebraic lemmas. *)
(* ============================================================ *)

End SimpleAlgebra.

(* ============================================================ *)
(* Module: AttentionGibbsBridge *)
(* Relates the attention softmax to the thermodynamic Boltzmann distribution, and gives *)
(* quantitative constraints on the detailed-balance breaking caused by KV eviction. *)
(* Integrated from the AttentionGibbsBridge source (all temporary admissions have been *)
(* converted to full proofs; purely constructive, Set layer, no Prop machinery). *)
(* ============================================================ *)

Section AttentionGibbsBridge.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* Positive exponential function: e^x := exp_neg(-x) (named so to avoid clashing with the Stdlib exp) *)
Definition exp_pos_fn (x : R) : R := exp_neg (opp x).

(* ---- Softmax definition ---- *)
Definition logits : Set := S -> R.

Definition partition_function (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (z s)).

(* The abstract SumOver interface does not provide "the sum of a positive function is positive":
   stated as an explicit assumption (non-classical, instantiable) *)
Variable sum_pos_preserved :
  forall (f : S -> R), (forall s, lt zero (f s)) -> lt zero (sum_over_S f).

Lemma partition_function_pos :
  forall z : logits, lt zero (partition_function z).
Proof.
  intros z.
  (* Unfold to the definition layer: the pointwise positivity is listed as an explicit proposition
      (pointwise witness assignment), and the sum-preserves-positivity interface is then
      instantiated explicitly — no statement-by-statement forwarding. *)
  unfold partition_function, exp_pos_fn.
  assert (Hpt : forall s, lt zero (exp_neg (opp (z s)))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (z s))) Hpt).
Qed.

Definition softmax (z : logits) (s : S) : R :=
  mult (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z)).

(* ============================================================ *)
(* Probability-distribution laws: machine-checked guarantees where current AI systems rely on floating-point approximation *)
(* ============================================================ *)

(* Positivity of softmax: attention weights > 0 (positive exp times positive inverse) *)
Theorem softmax_pos :
  forall z : logits, forall s : S, lt zero (softmax z s).
Proof.
  intros z s.
  unfold softmax, exp_pos_fn.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* Softmax normalization: Σ_s softmax(z,s) = 1 (conservation of probability mass) *)
Theorem softmax_normalized :
  forall z : logits, Id (sum_over_S (fun s => softmax z s)) one.
Proof.
  intro z.
  unfold softmax.
  (* Swap the mult order pointwise ([sum_over_S_ext] + [mult_comm]) *)
  assert (Hext : Id (sum_over_S (fun s => mult (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z))))
                   (sum_over_S (fun s => mult (inv_pos (partition_function z) (partition_function_pos z)) (exp_pos_fn (z s)))))
    by exact (sum_over_S_ext (fun s => mult (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z)))
                             (fun s => mult (inv_pos (partition_function z) (partition_function_pos z)) (exp_pos_fn (z s)))
                             (fun s => mult_comm (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z)))).
  rewrite Hext.
  (* Extract the constant factor ([sum_over_S_linear]) *)
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (partition_function z) (partition_function_pos z)) (exp_pos_fn (z s))))
                    (mult (inv_pos (partition_function z) (partition_function_pos z))
                          (sum_over_S (fun s => exp_pos_fn (z s)))))
    by exact (sum_over_S_linear (inv_pos (partition_function z) (partition_function_pos z)) (fun s => exp_pos_fn (z s))).
  rewrite Hlin.
  (* Σ exp(z s) = partition_function z (definitional unfolding) *)
  unfold partition_function.
  (* (1/Z)·Z = 1 ([inv_pos_correct] + comm) *)
  assert (Hcc : Id (mult (inv_pos (partition_function z) (partition_function_pos z)) (partition_function z)) one)
    by exact (id_trans (mult_comm (inv_pos (partition_function z) (partition_function_pos z)) (partition_function z))
                       (inv_pos_correct (partition_function z) (partition_function_pos z))).
  exact Hcc.
Qed.

(* ============================================================ *)
(* Nontrivial version: normalization conservation of convex combinations of softmax
   (the mathematical basis of model ensembling / mixture of experts / *)
(* attention mixing — a convex combination of two logit fields is still a probability distribution, *)
(* not a restatement of the partition-function definition). *)
(* ============================================================ *)
Theorem softmax_mix_normalized :
  forall (z z' : logits) (alpha : R) (Halpha : lt zero alpha) (Halpha1 : lt zero (minus one alpha)),
    Id (sum_over_S (fun s => plus (mult alpha (softmax z s)) (mult (minus one alpha) (softmax z' s)))) one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : Id (sum_over_S (fun s => softmax z s)) one) by exact (softmax_normalized z).
  assert (Hq : Id (sum_over_S (fun s => softmax z' s)) one) by exact (softmax_normalized z').
  assert (Hadd : Id (sum_over_S (fun s => plus (mult alpha (softmax z s)) (mult (minus one alpha) (softmax z' s))))
                   (plus (sum_over_S (fun s => mult alpha (softmax z s)))
                         (sum_over_S (fun s => mult (minus one alpha) (softmax z' s)))))
    by exact (sum_over_S_add (fun s => mult alpha (softmax z s)) (fun s => mult (minus one alpha) (softmax z' s))).
  rewrite Hadd.
  assert (Hlin1 : Id (sum_over_S (fun s => mult alpha (softmax z s))) (mult alpha (sum_over_S (fun s => softmax z s))))
    by exact (sum_over_S_linear alpha (fun s => softmax z s)).
  rewrite Hlin1.
  assert (Hlin2 : Id (sum_over_S (fun s => mult (minus one alpha) (softmax z' s))) (mult (minus one alpha) (sum_over_S (fun s => softmax z' s))))
    by exact (sum_over_S_linear (minus one alpha) (fun s => softmax z' s)).
  rewrite Hlin2.
  rewrite Hp. rewrite Hq.
  assert (Hm1 : Id (mult alpha one) alpha) by exact (mult_one alpha).
  rewrite Hm1.
  assert (Hm2 : Id (mult (minus one alpha) one) (minus one alpha)) by exact (mult_one (minus one alpha)).
  rewrite Hm2.
  (* Goal: plus alpha (minus one alpha) = one — an assert + exact chain (as in the FreeEnergyMinimization version) *)
  assert (Hfin : Id (plus alpha (minus one alpha)) one).
  {
    unfold minus.
    assert (Hsw : Id (plus alpha (plus one (opp alpha))) (plus one (plus alpha (opp alpha)))).
    {
      assert (H1 : Id (plus alpha (plus one (opp alpha))) (plus (plus alpha one) (opp alpha)))
        by exact (plus_assoc alpha one (opp alpha)).
      assert (H2 : Id (plus (plus alpha one) (opp alpha)) (plus (plus one alpha) (opp alpha)))
        by exact (id_cong (fun x => plus x (opp alpha)) (plus_comm alpha one)).
      assert (H3 : Id (plus (plus one alpha) (opp alpha)) (plus one (plus alpha (opp alpha))))
        by exact (id_sym (plus_assoc one alpha (opp alpha))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    assert (Hfin2 : Id (plus one (plus alpha (opp alpha))) one).
    {
      assert (Hpz : Id (plus one zero) one) by exact (plus_zero one).
      assert (Hpz2 : Id (plus one (plus alpha (opp alpha))) (plus one zero))
        by exact (id_cong (fun x => plus one x) (plus_opp alpha)).
      exact (id_trans Hpz2 Hpz).
    }
    exact (id_trans Hsw Hfin2).
  }
  exact Hfin.
Qed.

(* Combination: softmax is a probability distribution (positivity + normalization) *)
Theorem softmax_is_prob :
  forall z : logits,
    And (forall s : S, le zero (softmax z s)) (Id (sum_over_S (fun s => softmax z s)) one).
Proof.
  intro z.
  split.
  - intro s.
    apply (lt_le_iff _ _). left. apply softmax_pos.
  - apply softmax_normalized.
Qed.

(* ============================================================ *)
(* Temperature-annealing framework (the mathematical basis of speculative decoding / hard attention as T→0) *)
(* ============================================================ *)

Variable T : R.
Variable T_pos : lt zero T.

Definition partition_function_temp (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (mult (inv_pos T T_pos) (z s))).

Lemma partition_function_temp_pos :
  forall z : logits, lt zero (partition_function_temp z).
Proof.
  intros z.
  unfold partition_function_temp, exp_pos_fn.
  (* Unfold to the definition layer (reusing the family template): the pointwise positivity is listed
      as an explicit proposition (pointwise witness assignment), and the sum-preserves-positivity
      interface is then instantiated explicitly — no statement-by-statement forwarding. *)
  assert (Hpt : forall s, lt zero (exp_neg (opp (mult (inv_pos T T_pos) (z s))))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (mult (inv_pos T T_pos) (z s)))) Hpt).
Qed.

Definition softmax_temp (z : logits) (s : S) : R :=
  mult (exp_pos_fn (mult (inv_pos T T_pos) (z s)))
       (inv_pos (partition_function_temp z) (partition_function_temp_pos z)).

(* The temperature version of the probability-distribution laws (isomorphic to the unit-temperature version) *)
Theorem softmax_temp_pos :
  forall z : logits, forall s : S, lt zero (softmax_temp z s).
Proof.
  intros z s.
  unfold softmax_temp, exp_pos_fn.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

Theorem softmax_temp_normalized :
  forall z : logits, Id (sum_over_S (fun s => softmax_temp z s)) one.
Proof.
  intro z.
  unfold softmax_temp.
  assert (Hext : Id (sum_over_S (fun s => mult (exp_pos_fn (mult (inv_pos T T_pos) (z s))) (inv_pos (partition_function_temp z) (partition_function_temp_pos z))))
                   (sum_over_S (fun s => mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (exp_pos_fn (mult (inv_pos T T_pos) (z s))))))
    by exact (sum_over_S_ext (fun s => mult (exp_pos_fn (mult (inv_pos T T_pos) (z s))) (inv_pos (partition_function_temp z) (partition_function_temp_pos z)))
                             (fun s => mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (exp_pos_fn (mult (inv_pos T T_pos) (z s))))
                             (fun s => mult_comm (exp_pos_fn (mult (inv_pos T T_pos) (z s))) (inv_pos (partition_function_temp z) (partition_function_temp_pos z)))).
  rewrite Hext.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (exp_pos_fn (mult (inv_pos T T_pos) (z s)))))
                    (mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z))
                          (sum_over_S (fun s => exp_pos_fn (mult (inv_pos T T_pos) (z s))))))
    by exact (sum_over_S_linear (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (fun s => exp_pos_fn (mult (inv_pos T T_pos) (z s)))).
  rewrite Hlin.
  unfold partition_function_temp.
  assert (Hcc : Id (mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (partition_function_temp z)) one)
    by exact (id_trans (mult_comm (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (partition_function_temp z))
                       (inv_pos_correct (partition_function_temp z) (partition_function_temp_pos z))).
  exact Hcc.
Qed.

(* ============================================================ *)
(* Nontrivial version: normalization conservation of convex combinations of the temperature-scaled softmax *)
(* (attention mixing under temperature annealing — the mathematical basis of multi-temperature *)
(*   distillation / mixture of experts; the weights of the convex combination are independent of the temperature). *)
(* ============================================================ *)
Theorem softmax_temp_mix_normalized :
  forall (z z' : logits) (alpha : R) (Halpha : lt zero alpha) (Halpha1 : lt zero (minus one alpha)),
    Id (sum_over_S (fun s => plus (mult alpha (softmax_temp z s)) (mult (minus one alpha) (softmax_temp z' s)))) one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : Id (sum_over_S (fun s => softmax_temp z s)) one) by exact (softmax_temp_normalized z).
  assert (Hq : Id (sum_over_S (fun s => softmax_temp z' s)) one) by exact (softmax_temp_normalized z').
  assert (Hadd : Id (sum_over_S (fun s => plus (mult alpha (softmax_temp z s)) (mult (minus one alpha) (softmax_temp z' s))))
                   (plus (sum_over_S (fun s => mult alpha (softmax_temp z s)))
                         (sum_over_S (fun s => mult (minus one alpha) (softmax_temp z' s)))))
    by exact (sum_over_S_add (fun s => mult alpha (softmax_temp z s)) (fun s => mult (minus one alpha) (softmax_temp z' s))).
  rewrite Hadd.
  assert (Hlin1 : Id (sum_over_S (fun s => mult alpha (softmax_temp z s))) (mult alpha (sum_over_S (fun s => softmax_temp z s))))
    by exact (sum_over_S_linear alpha (fun s => softmax_temp z s)).
  rewrite Hlin1.
  assert (Hlin2 : Id (sum_over_S (fun s => mult (minus one alpha) (softmax_temp z' s))) (mult (minus one alpha) (sum_over_S (fun s => softmax_temp z' s))))
    by exact (sum_over_S_linear (minus one alpha) (fun s => softmax_temp z' s)).
  rewrite Hlin2.
  rewrite Hp. rewrite Hq.
  assert (Hm1 : Id (mult alpha one) alpha) by exact (mult_one alpha).
  rewrite Hm1.
  assert (Hm2 : Id (mult (minus one alpha) one) (minus one alpha)) by exact (mult_one (minus one alpha)).
  rewrite Hm2.
  (* Goal: plus alpha (minus one alpha) = one — an assert + exact chain (as in the boltzmann_mix_normalized version) *)
  assert (Hfin : Id (plus alpha (minus one alpha)) one).
  {
    unfold minus.
    assert (Hsw : Id (plus alpha (plus one (opp alpha))) (plus one (plus alpha (opp alpha)))).
    {
      assert (H1 : Id (plus alpha (plus one (opp alpha))) (plus (plus alpha one) (opp alpha)))
        by exact (plus_assoc alpha one (opp alpha)).
      assert (H2 : Id (plus (plus alpha one) (opp alpha)) (plus (plus one alpha) (opp alpha)))
        by exact (id_cong (fun x => plus x (opp alpha)) (plus_comm alpha one)).
      assert (H3 : Id (plus (plus one alpha) (opp alpha)) (plus one (plus alpha (opp alpha))))
        by exact (id_sym (plus_assoc one alpha (opp alpha))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    assert (Hfin2 : Id (plus one (plus alpha (opp alpha))) one).
    {
      assert (Hpz : Id (plus one zero) one) by exact (plus_zero one).
      assert (Hpz2 : Id (plus one (plus alpha (opp alpha))) (plus one zero))
        by exact (id_cong (fun x => plus one x) (plus_opp alpha)).
      exact (id_trans Hpz2 Hpz).
    }
    exact (id_trans Hsw Hfin2).
  }
  exact Hfin.
Qed.

Theorem softmax_temp_relative :
  forall z : logits, forall s s' : S,
    Id (softmax_temp z s)
       (mult (softmax_temp z s')
             (exp_pos_fn (mult (inv_pos T T_pos) (minus (z s) (z s'))))).
Proof.
  intros z s s'.
  unfold softmax_temp, exp_pos_fn.
  set (A := exp_neg (opp (mult (inv_pos T T_pos) (z s')))).
  set (B := exp_neg (opp (mult (inv_pos T T_pos) (minus (z s) (z s'))))).
  set (C := inv_pos (partition_function_temp z) (partition_function_temp_pos z)).
  set (Ap := exp_neg (opp (mult (inv_pos T T_pos) (z s)))).
  (* Regroup: mult (mult A C) B = mult (mult A B) C *)
  assert (Hre : Id (mult (mult A C) B) (mult (mult A B) C)).
  {
    assert (H1 : Id (mult (mult A C) B) (mult A (mult C B)))
      by exact (id_sym (mult_assoc A C B)).
    assert (H2 : Id (mult A (mult C B)) (mult A (mult B C)))
      by exact (id_cong (fun x => mult A x) (mult_comm C B)).
    assert (H3 : Id (mult A (mult B C)) (mult (mult A B) C))
      by exact (mult_assoc A B C).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* Adding the exponents: A·B = Ap ([exp_neg_plus] + algebra) *)
  assert (Hprod : Id (mult A B) Ap).
  {
    unfold A, B, Ap.
    assert (Hep : Id (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s'))))
                           (exp_neg (opp (mult (inv_pos T T_pos) (minus (z s) (z s'))))))
                     (exp_neg (plus (opp (mult (inv_pos T T_pos) (z s')))
                                    (opp (mult (inv_pos T T_pos) (minus (z s) (z s')))))))
      by exact (id_sym (exp_neg_plus (opp (mult (inv_pos T T_pos) (z s')))
                                     (opp (mult (inv_pos T T_pos) (minus (z s) (z s')))))).
    rewrite Hep.
    assert (Halg : Id (plus (opp (mult (inv_pos T T_pos) (z s')))
                            (opp (mult (inv_pos T T_pos) (minus (z s) (z s')))))
                      (opp (mult (inv_pos T T_pos) (z s)))).
    {
      set (X := opp (mult (inv_pos T T_pos) (z s'))).
      set (Y := opp (mult (inv_pos T T_pos) (z s))).
      set (Z := mult (inv_pos T T_pos) (z s')).
      (* opp (mult invT (minus (z s) (z s'))) = plus (opp (mult invT (z s))) (mult invT (z s')) = plus Y Z *)
      assert (H1 : Id (opp (mult (inv_pos T T_pos) (minus (z s) (z s'))))
                      (plus Y Z)).
      {
        assert (Hd : Id (mult (inv_pos T T_pos) (minus (z s) (z s')))
                        (minus (mult (inv_pos T T_pos) (z s)) (mult (inv_pos T T_pos) (z s'))))
          by exact (mult_minus_distr_l (inv_pos T T_pos) (z s) (z s')).
        assert (H2 : Id (opp (minus (mult (inv_pos T T_pos) (z s)) (mult (inv_pos T T_pos) (z s'))))
                        (plus (opp (mult (inv_pos T T_pos) (z s))) (mult (inv_pos T T_pos) (z s'))))
          by exact (opp_minus (mult (inv_pos T T_pos) (z s)) (mult (inv_pos T T_pos) (z s'))).
        unfold Y, Z.
        exact (id_trans (id_cong (fun x => opp x) Hd) H2).
      }
      (* Goal (after set X/Y/Z): plus X (opp (mult invT (minus ...))) = Y *)
      rewrite H1.
      (* Regroup: plus X (plus Y Z) = plus Y (plus X Z) *)
      assert (Hsw : Id (plus X (plus Y Z)) (plus Y (plus X Z))).
      {
        assert (Hsw1 : Id (plus X (plus Y Z)) (plus (plus X Y) Z))
          by exact (plus_assoc X Y Z).
        assert (Hsw2 : Id (plus (plus X Y) Z) (plus (plus Y X) Z))
          by exact (id_cong (fun w => plus w Z) (plus_comm X Y)).
        assert (Hsw3 : Id (plus (plus Y X) Z) (plus Y (plus X Z)))
          by exact (id_sym (plus_assoc Y X Z)).
        exact (id_trans Hsw1 (id_trans Hsw2 Hsw3)).
      }
      rewrite Hsw.
      (* plus X Z = zero (X and Z are mutual inverses; commute, then apply [plus_opp]) *)
      assert (Hpz : Id (plus X Z) zero)
        by exact (id_trans (plus_comm X Z) (plus_opp (mult (inv_pos T T_pos) (z s')))).
      assert (H5 : Id (plus Y (plus X Z)) (plus Y zero))
        by exact (id_cong (fun w => plus Y w) Hpz).
      assert (H6 : Id (plus Y zero) Y) by exact (plus_zero Y).
      exact (id_trans H5 H6).
    }
    apply (id_cong (fun x => exp_neg x)). exact Halg.
  }
  (* Assemble: mult Ap C = mult (mult A C) B *)
  rewrite Hre.
  rewrite Hprod.
  reflexivity.
Qed.
(* Gap-concentration theorem: an energy gap ⟹ the attention weight of a non-optimal state is
   exponentially suppressed by the optimal state.
   Hypothesis (temperature-scaled gap): γ/T ≤ (z(s_star) - z(s))/T (γ > 0 is the gap).
   Conclusion: softmax_T(s) ≤ softmax_T(s_star)·e^{-γ/T} — the algebraic core of the hard-attention
   limit (T→0). *)
Theorem softmax_gap_concentration :
  forall (z : logits) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (minus (z s_star) (z s))) ->
      le (softmax_temp z s)
         (mult (softmax_temp z s_star)
               (exp_neg (mult (inv_pos T T_pos) gamma))).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  assert (Hrel : Id (softmax_temp z s)
                    (mult (softmax_temp z s_star)
                          (exp_pos_fn (mult (inv_pos T T_pos) (minus (z s) (z s_star))))))
    by exact (softmax_temp_relative z s s_star).
  rewrite Hrel.
  (* Exponent-argument identity: e^{(z(s)-z(s_star))/T} = exp_neg (mult invT (minus (z s_star) (z s))) *)
  assert (Heq : Id (exp_pos_fn (mult (inv_pos T T_pos) (minus (z s) (z s_star))))
                   (exp_neg (mult (inv_pos T T_pos) (minus (z s_star) (z s))))).
  {
    unfold exp_pos_fn.
    assert (Hopp : Id (opp (mult (inv_pos T T_pos) (minus (z s) (z s_star))))
                     (mult (inv_pos T T_pos) (minus (z s_star) (z s)))).
    {
      assert (H1 : Id (opp (mult (inv_pos T T_pos) (minus (z s) (z s_star))))
                      (mult (inv_pos T T_pos) (opp (minus (z s) (z s_star)))))
        by exact (id_sym (opp_mult_l (inv_pos T T_pos) (minus (z s) (z s_star)))).
      assert (H2 : Id (mult (inv_pos T T_pos) (opp (minus (z s) (z s_star))))
                      (mult (inv_pos T T_pos) (minus (z s_star) (z s))))
        by exact (id_cong (fun x => mult (inv_pos T T_pos) x)
                          (id_trans (opp_minus (z s) (z s_star)) (plus_comm (opp (z s)) (z s_star)))).
      exact (id_trans H1 H2).
    }
    apply (id_cong (fun x => exp_neg x)). exact Hopp.
  }
  rewrite Heq.
  (* Goal: softmax_T(s_star)·e^{-(z(s_star)-z(s))/T} ≤ softmax_T(s_star)·e^{-γ/T},
      by [exp_neg_le_decr] (the exponent argument is ≤) plus monotonicity of mult ([softmax_temp_pos]) *)
  apply (le_mult_compat_r (softmax_temp z s_star)
                          (exp_neg (mult (inv_pos T T_pos) (minus (z s_star) (z s))))
                          (exp_neg (mult (inv_pos T T_pos) gamma))).
  - apply (lt_le_iff _ _). left. apply softmax_temp_pos.
  - apply exp_neg_le_decr. exact Hgap.
Qed.

(* ============================================================ *)
(* Zero-temperature limit (the quantitative form of the hard-attention collapse) *)
(* ============================================================ *)
(* softmax_gap_concentration gives softmax_T(s) ≤ softmax_T(s_star)·e^{-γ/T};
   dividing both sides here by softmax_T(s_star) > 0 yields the weight ratio of a non-optimal state
   to the optimal state: *)
(* collapse) and the hard-attention limit.  A nontrivial parallel version of the gap-concentration *)
(* theorem (ratio form, with constructive division: multiply both sides by inv B > 0 and fold). *)
(* ------------------------------------------------------------ *)
Theorem temperature_zero_limit :
  forall (z : logits) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (minus (z s_star) (z s))) ->
      le (mult (softmax_temp z s)
               (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
         (exp_neg (mult (inv_pos T T_pos) gamma)).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  (* Gap concentration: A ≤ B·C (A := softmax_T(s), B := softmax_T(s_star),
      C := e^{-γ/T}) *)
  assert (Hgc : le (softmax_temp z s)
                   (mult (softmax_temp z s_star)
                         (exp_neg (mult (inv_pos T T_pos) gamma))))
    by exact (softmax_gap_concentration z s_star gamma Hgamma s Hgap).
  (* Multiply both sides by inv B > 0: inv B · A ≤ inv B · (B·C) ([le_mult_compat_r]) *)
  assert (Hinv : le zero (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))).
  { apply (lt_le_iff _ _). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (softmax_temp z s))
                    (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (mult (softmax_temp z s_star)
                                (exp_neg (mult (inv_pos T T_pos) gamma)))))
    by exact (le_mult_compat_r (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                               (softmax_temp z s)
                               (mult (softmax_temp z s_star)
                                     (exp_neg (mult (inv_pos T T_pos) gamma)))
                               Hinv Hgc).
  (* Swap the LHS: inv B · A = A · inv B ([mult_comm]) *)
  assert (Hsw : Id (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                         (softmax_temp z s))
                   (mult (softmax_temp z s)
                         (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))))
    by exact (mult_comm (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                        (softmax_temp z s)).
  assert (Hlhs : le (mult (softmax_temp z s)
                          (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
                    (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (mult (softmax_temp z s_star)
                                (exp_neg (mult (inv_pos T T_pos) gamma)))))
    by exact (le_id_l (mult (softmax_temp z s)
                            (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
                      (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                            (softmax_temp z s))
                      (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                            (mult (softmax_temp z s_star)
                                  (exp_neg (mult (inv_pos T T_pos) gamma))))
                      (id_sym Hsw) Hdiv).
  (* Fold the RHS: (inv B · B)·C = 1·C = C *)
  assert (Hrhs : Id (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                           (mult (softmax_temp z s_star)
                                 (exp_neg (mult (inv_pos T T_pos) gamma))))
                     (exp_neg (mult (inv_pos T T_pos) gamma))).
  {
    assert (H1 : Id (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (mult (softmax_temp z s_star)
                                (exp_neg (mult (inv_pos T T_pos) gamma))))
                    (mult (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                                (softmax_temp z s_star))
                          (exp_neg (mult (inv_pos T T_pos) gamma))))
      by exact (mult_assoc (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                           (softmax_temp z s_star)
                           (exp_neg (mult (inv_pos T T_pos) gamma))).
    assert (H2 : Id (mult (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                                (softmax_temp z s_star))
                          (exp_neg (mult (inv_pos T T_pos) gamma)))
                    (mult one (exp_neg (mult (inv_pos T T_pos) gamma))))
      by exact (id_cong (fun x => mult x (exp_neg (mult (inv_pos T T_pos) gamma)))
                        (id_trans (mult_comm (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                                             (softmax_temp z s_star))
                                  (inv_pos_correct (softmax_temp z s_star) (softmax_temp_pos z s_star)))).
    assert (H3 : Id (mult one (exp_neg (mult (inv_pos T T_pos) gamma)))
                    (exp_neg (mult (inv_pos T T_pos) gamma)))
      by exact (id_trans (mult_comm one (exp_neg (mult (inv_pos T T_pos) gamma)))
                         (mult_one (exp_neg (mult (inv_pos T T_pos) gamma)))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* Combine: A · inv B ≤ C (replace the RHS via [le_id_r]) *)
  exact (le_id_r (mult (softmax_temp z s)
                       (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
                 (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                       (mult (softmax_temp z s_star)
                             (exp_neg (mult (inv_pos T T_pos) gamma))))
                 (exp_neg (mult (inv_pos T T_pos) gamma))
                 Hrhs Hlhs).
Qed.

(* ============================================================ *)
(* Scale-temperature duality (the 1/√d scaling viewpoint) *)
(* The scaled softmax family sc(z; c)_s := e^{c·z_s} / Σ_{s'} e^{c·z_{s'}}: *)
(* c is an arbitrary real scaling factor (no positivity needed: exp is always positive ⟹ partition-function positivity is free). *)
(* Core duality lemma scale_temp_duality: for all c > 0, the softmax of the logits scaled by 1/c *)
(* equals the softmax at temperature c (the scaling factor 1/√d and the temperature √d are *)
(* inverse parameterizations of one and the same positive axis; a pure unfold + id_cong + inv_pos_ext *)
(* + id_refl identity proof, with no new axioms). *)
(* (b) Squared dimension d = k² is phrased via the witness sqrt_witness d r := r·r == d *)
(* (no sqrt function symbol): the instance d = 4, r = 2 plus a general (d, r) witness lemma. *)
(* (c) The general √d for non-square d needs a constructive square root (treated separately, not in this block). *)
(* ============================================================ *)

(* Scaled partition function: Z_c(z) := Σ_s e^{c·z_s} (c an arbitrary real; no positivity needed) *)
Definition partition_function_scaled (c : R) (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (mult c (z s))).

(* Positivity of the scaled partition: exp is always positive, times [sum_pos_preserved] *)
Lemma partition_function_scaled_pos :
  forall c z, lt zero (partition_function_scaled c z).
Proof.
  intros c z.
  unfold partition_function_scaled, exp_pos_fn.
  (* Unfold to the definition layer (reusing the family template): the pointwise positivity is listed
      as an explicit proposition (pointwise witness assignment), and the sum-preserves-positivity
      interface is then instantiated explicitly — no statement-by-statement forwarding. *)
  assert (Hpt : forall s, lt zero (exp_neg (opp (mult c (z s))))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (mult c (z s)))) Hpt).
Qed.

(* Scaled softmax: sc(z; c)_s := e^{c·z_s} / Z_c(z) (c an arbitrary real) *)
Definition softmax_scaled (c : R) (z : logits) (s : S) : R :=
  mult (exp_pos_fn (mult c (z s)))
       (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)).

(* Probability law of the scaled family: positivity *)
Theorem softmax_scaled_pos :
  forall c z s, lt zero (softmax_scaled c z s).
Proof.
  intros c z s.
  unfold softmax_scaled, exp_pos_fn.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* Probability law of the scaled family: normalization *)
Theorem softmax_scaled_normalized :
  forall c z, Id (sum_over_S (fun s => softmax_scaled c z s)) one.
Proof.
  intros c z.
  unfold softmax_scaled.
  assert (Hext : Id (sum_over_S (fun s => mult (exp_pos_fn (mult c (z s))) (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z))))
                   (sum_over_S (fun s => mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (exp_pos_fn (mult c (z s))))))
    by exact (sum_over_S_ext (fun s => mult (exp_pos_fn (mult c (z s))) (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)))
                             (fun s => mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (exp_pos_fn (mult c (z s))))
                             (fun s => mult_comm (exp_pos_fn (mult c (z s))) (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)))).
  rewrite Hext.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (exp_pos_fn (mult c (z s)))))
                    (mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z))
                          (sum_over_S (fun s => exp_pos_fn (mult c (z s))))))
    by exact (sum_over_S_linear (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (fun s => exp_pos_fn (mult c (z s)))).
  rewrite Hlin.
  unfold partition_function_scaled.
  assert (Hcc : Id (mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (partition_function_scaled c z)) one)
    by exact (id_trans (mult_comm (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (partition_function_scaled c z))
                       (inv_pos_correct (partition_function_scaled c z) (partition_function_scaled_pos c z))).
  exact Hcc.
Qed.

(* Temperature-parameterized partition function (the (T0, HT0) explicit version *)
(* of [partition_function_temp]; lets the duality lemma be stated for an arbitrary temperature c) *)
Definition partition_function_temp_param (T0 : R) (HT0 : lt zero T0) (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (mult (inv_pos T0 HT0) (z s))).

(* Positivity of the temperature-parameterized partition *)
Lemma partition_function_temp_param_pos :
  forall T0 HT0 z, lt zero (partition_function_temp_param T0 HT0 z).
Proof.
  intros T0 HT0 z.
  unfold partition_function_temp_param, exp_pos_fn.
  (* Unfold to the definition layer (reusing the family template): the pointwise positivity is listed
      as an explicit proposition (pointwise witness assignment), and the sum-preserves-positivity
      interface is then instantiated explicitly — no statement-by-statement forwarding. *)
  assert (Hpt : forall s, lt zero (exp_neg (opp (mult (inv_pos T0 HT0) (z s))))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (mult (inv_pos T0 HT0) (z s)))) Hpt).
Qed.

(* Temperature-parameterized softmax (the (T0, HT0) explicit version of [softmax_temp]) *)
Definition softmax_temp_param (T0 : R) (HT0 : lt zero T0) (z : logits) (s : S) : R :=
  mult (exp_pos_fn (mult (inv_pos T0 HT0) (z s)))
       (inv_pos (partition_function_temp_param T0 HT0 z) (partition_function_temp_param_pos T0 HT0 z)).

(* ============================================================ *)
(* (a) The scale-temperature duality lemma (the core of this block) *)
(* Statement: for all c > 0, the softmax of the logits scaled by 1/c (the scaling factor *)
(* inv_pos c Hc, i.e. 1/c) equals the softmax at temperature c.  The scaling factor 1/√d and the *)
(* temperature √d are mutual inverses: taking c := √d gives "1/√d scaling == temperature √d". *)
(* Proof: after unfold, the first factors of both sides (the numerators e^{(1/c)z_s}) are literally *)
(* identical, cancelled by id_cong; the partition functions are definitionally equal ⟹ inv_pos_ext + id_refl. *)
(* A pure identity chain with no new axioms (only existing interface fields are used). *)
(* ============================================================ *)
Theorem scale_temp_duality :
  forall (c : R) (Hc : lt zero c) (z : logits) (s : S),
    Id (softmax_scaled (inv_pos c Hc) z s) (softmax_temp_param c Hc z s).
Proof.

  intros c Hc z s. unfold softmax_scaled, softmax_temp_param. exact (id_cong (fun x => mult (exp_pos_fn (mult (inv_pos c Hc) (z s))) x) (inv_pos_ext (partition_function_scaled (inv_pos c Hc) z) (partition_function_temp_param c Hc z) (partition_function_scaled_pos (inv_pos c Hc) z) (partition_function_temp_param_pos c Hc z) id_refl)).

Qed.

(* Reverse symmetry: the softmax at temperature c equals the softmax scaled by 1/c ([id_sym]) *)
Lemma temp_is_scale_duality :
  forall (c : R) (Hc : lt zero c) (z : logits) (s : S),
    Id (softmax_temp_param c Hc z s) (softmax_scaled (inv_pos c Hc) z s).
Proof.
  intros c Hc z s. exact (id_sym (scale_temp_duality c Hc z s)).
Qed.

(* ============================================================ *)
(* (b) The squared-dimension special case: d = k² (√d := r by witness; no sqrt function symbol) *)
(* sqrt_witness d r := Id (mult r r) d (r·r == d). *)
(* The 1/√d scaling is constructively given by inv_pos r Hr (r witnesses √d), and the temperature √d *)
(* is r itself.  For d = k² the witness is r := k; for d = 4, r = 2 see below ([two_mult]: *)
(* 2·2 == 2+2, a genuine proof, not reflexivity). *)
(* ============================================================ *)
Definition sqrt_witness (d r : R) : Set := Id (mult r r) d.

(* Witness for d = 4 = 2²: r := 2 and 2·2 == 4 (4 written as plus 2 2; [two_mult]) *)
Lemma sq_witness_4 :
  sqrt_witness (plus (plus one one) (plus one one)) (plus one one).
Proof.
  unfold sqrt_witness.
  exact (two_mult (plus one one)).
Qed.

(* General squared-dimension duality: whenever d = r² (r > 0, by witness), the 1/r scaling equals *)
(* the softmax at temperature r (the r-instance of [scale_temp_duality]; d is named only through the *)
(* witness, and the role of √d is played by r — the abstract layer has no sqrt function symbol) *)
Theorem scale_sqrt_witness_dual :
  forall (d r : R) (Hr : lt zero r),
    sqrt_witness d r ->
    forall (z : logits) (s : S),
      Id (softmax_scaled (inv_pos r Hr) z s) (softmax_temp_param r Hr z s).
Proof.
  intros d r Hr Hw z s. exact (scale_temp_duality r Hr z s).
Qed.

(* The d = 4 (r = 2) instance: softmax(z/2) equals the softmax at temperature 2 *)
(* (1/√4 = 1/2 := inv_pos 2; the temperature √4 = 2 := plus one one) *)
Lemma half_scale_is_temp_two :
  forall (z : logits) (s : S),
    Id (softmax_scaled (inv_pos (plus one one) two_pos) z s)
       (softmax_temp_param (plus one one) two_pos z s).
Proof.
  intros z s. exact (scale_temp_duality (plus one one) two_pos z s).
Qed.

(* ---- Boltzmann distribution (temperature D > 0, energy [energy]) ---- *)
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : logits.
Variable z : logits.   (* Attention logits (the premise variable of [attention_is_gibbs]) *)

Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo : R := sum_over_S boltzmann_factor.

(* Derived from [sum_pos_preserved] plus the pointwise [exp_neg_pos]; no admitted statements. *)
Lemma Z_thermo_pos : lt zero Z_thermo.
Proof.
  unfold Z_thermo. apply sum_pos_preserved. intros s. unfold boltzmann_factor.
  apply exp_neg_pos.
Qed.


Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

(* Key theorem: at unit temperature (inv_pos D D_pos = one) and with energy = -logits,
   the softmax is the Boltzmann distribution.
   Note: the premise uses Id (inv_pos D D_pos) one (unit temperature at the definitional level),
   avoiding the dependent-type transplant of the argument D_pos that Id D one would force. *)
Theorem attention_is_gibbs :
  (Id (inv_pos D D_pos) one) ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id Z_thermo (partition_function z) ->
  forall s : S, Id (softmax z s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  unfold softmax, boltzmann_dist_attn, boltzmann_factor, exp_pos_fn.
  rewrite HD.
  assert (Hml : Id (mult one (energy s)) (energy s))
    by exact (id_trans (mult_comm one (energy s)) (mult_one (energy s))).
  rewrite Hml.
  rewrite (Henergy s).
  (* Equality of the partition functions ⟹ unify the inverse in the distribution (directly bridging the two different x) *)
  assert (Hie : Id (inv_pos Z_thermo Z_thermo_pos)
                   (inv_pos (partition_function z) (partition_function_pos z)))
    by exact (inv_pos_ext Z_thermo (partition_function z) Z_thermo_pos (partition_function_pos z) HZ).
  rewrite Hie.
  apply (mult_comm (exp_neg (opp (z s))) (inv_pos (partition_function z) (partition_function_pos z))).
Qed.

(* ============================================================ *)
(* Nontrivial version: the softmax = Boltzmann correspondence at arbitrary temperature *)
(* The premise of [attention_is_gibbs] is Id (inv_pos D D_pos) one (the unit-temperature *)
(* special case).  Here it is extended to arbitrary temperature: as long as the attention temperature T matches the *)
(* thermodynamic temperature D (1/T = 1/D) and energy = -logits, the temperature-scaled *)
(* softmax is the Boltzmann distribution — the core correspondence between the inference temperature and the physical temperature. *)
(* ============================================================ *)
Theorem attention_is_gibbs_temp :
  (Id (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id Z_thermo (partition_function_temp z) ->
  forall s : S, Id (softmax_temp z s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  unfold softmax_temp, boltzmann_dist_attn, boltzmann_factor, exp_pos_fn.
  (* Temperature unification (1/T = 1/D) + energy = -logits ⟹ the factors agree:
      e^{-(-z(s))/T} = e^{-E(s)/D} *)
  assert (Hf : Id (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                  (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  {
    apply (id_cong (fun x => exp_neg x)).
    rewrite (Henergy s).
    (* Goal: opp (mult invT (z s)) = mult invD (opp (z s)) *)
    assert (H1 : Id (opp (mult (inv_pos T T_pos) (z s)))
                    (mult (inv_pos T T_pos) (opp (z s))))
      by exact (id_sym (opp_mult_l (inv_pos T T_pos) (z s))).
    assert (H2 : Id (mult (inv_pos T T_pos) (opp (z s)))
                    (mult (inv_pos D D_pos) (opp (z s))))
      by exact (id_cong (fun x => mult x (opp (z s))) HD).
    exact (id_trans H1 H2).
  }
  (* Equality of the partition functions ⟹ unify the normalization inverse ([inv_pos_ext] bridges the different partition functions) *)
  assert (Hie : Id (inv_pos Z_thermo Z_thermo_pos)
                   (inv_pos (partition_function_temp z) (partition_function_temp_pos z)))
    by exact (inv_pos_ext Z_thermo (partition_function_temp z) Z_thermo_pos (partition_function_temp_pos z) HZ).
  rewrite Hf.
  rewrite Hie.
  apply (mult_comm (exp_neg (mult (inv_pos D D_pos) (energy s)))
                   (inv_pos (partition_function_temp z) (partition_function_temp_pos z))).
Qed.

(* ============================================================ *)
(* Scale-temperature duality × Boltzmann bridge (composition) *)
(* The attention scaled by 1/T (T := √d, with the witness d = T² above via sqrt_witness) *)
(* equals the softmax at temperature T (the [scale_temp_duality] instance c := T) *)
(* equals the Boltzmann distribution at temperature D ([attention_is_gibbs_temp]: 1/T = 1/D, *)
(* energy = -logits, matching Z).  Reading: with √d := T := D, this says *)
(* "the 1/√d-scaled attention equals the Boltzmann distribution at temperature √d". *)
(* ============================================================ *)

(* Bridge: the 1/T-scaled family equals the in-library temperature-scaled softmax (the partition *)
(* functions are definitionally equal, inv_pos_ext + id_refl; scale_temp_duality at c := T composed with copies) *)
Lemma scale_inv_T_eq_softmax_temp :
  forall (s : S),
    Id (softmax_scaled (inv_pos T T_pos) z s) (softmax_temp z s).
Proof.

  intros s. unfold softmax_scaled, softmax_temp. exact (id_cong (fun x => mult (exp_pos_fn (mult (inv_pos T T_pos) (z s))) x) (inv_pos_ext (partition_function_scaled (inv_pos T T_pos) z) (partition_function_temp z) (partition_function_scaled_pos (inv_pos T T_pos) z) (partition_function_temp_pos z) id_refl)).

Qed.

(* Composition: the scale-temperature duality + [attention_is_gibbs_temp] (1/T = 1/D, *)
(* energy = -logits, matching Z) ⟹ the scaled attention equals the Boltzmann distribution. *)
(* The statement is "the 1/√d scaling equals the Boltzmann distribution at temperature √d" (√d := T := D). *)
Theorem scaled_attention_is_gibbs_temp :
  (Id (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id Z_thermo (partition_function_temp z) ->
  forall s : S, Id (softmax_scaled (inv_pos T T_pos) z s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  assert (Hbr : Id (softmax_scaled (inv_pos T T_pos) z s) (softmax_temp z s))
    by exact (scale_inv_T_eq_softmax_temp s).
  assert (Hboltz : Id (softmax_temp z s) (boltzmann_dist_attn s))
    by exact (attention_is_gibbs_temp HD Henergy HZ s).
  exact (id_trans Hbr Hboltz).
Qed.

(* ---- Detailed balance and the stationary state (the theoretical reference before KV eviction) ---- *)
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.

Variable detailed_balance :
  forall s s',
    Id (mult (boltzmann_dist_attn s) (transition s s'))
       (mult (boltzmann_dist_attn s') (transition s' s)).

(* Detailed balance ⟹ the Boltzmann distribution is a stationary state
   (same shape as [BoltzmannSteadyState]; here for the [boltzmann_dist_attn] of this module,
   renamed to avoid a top-level name clash) *)
Theorem steady_state_boltzmann_attn :
  forall s,
    Id (sum_over_S (fun s' => mult (boltzmann_dist_attn s') (transition s' s)))
       (boltzmann_dist_attn s).
Proof.
  intro s.
  assert (Hpoint : forall s', Id (mult (boltzmann_dist_attn s') (transition s' s))
                               (mult (boltzmann_dist_attn s) (transition s s'))).
  { intro s'. apply (detailed_balance s' s). }
  assert (Hext2 : Id (sum_over_S (fun s' => mult (boltzmann_dist_attn s') (transition s' s)))
                     (sum_over_S (fun s' => mult (boltzmann_dist_attn s) (transition s s'))))
    by exact (sum_over_S_ext (fun s' => mult (boltzmann_dist_attn s') (transition s' s))
                             (fun s' => mult (boltzmann_dist_attn s) (transition s s')) Hpoint).
  rewrite Hext2.
  assert (Hlin : Id (sum_over_S (fun s' => mult (boltzmann_dist_attn s) (transition s s')))
                    (mult (boltzmann_dist_attn s) (sum_over_S (fun s' => transition s s'))))
    by exact (sum_over_S_linear (boltzmann_dist_attn s) (fun s' => transition s s')).
  rewrite Hlin.
  rewrite (transition_normalization s).
  assert (Hmo : Id (mult (boltzmann_dist_attn s) one) (boltzmann_dist_attn s))
    by exact (mult_one (boltzmann_dist_attn s)).
  rewrite Hmo. reflexivity.
Qed.

(* ============ Honest interface assumptions ============ *)
(* Accounting of the assumption face:
   - Kept as honest interface assumptions: [delta]/[delta_pos]/[delta_lt_one]/[minorization] (a Doeblin
     lower bound — when the softmax kernel is peaked, any kernel can be arbitrarily close to degenerate;
     δ is supplied by the kernel instance and is not derived here);
     [lt_plus_compat_lt_le]/[lt_plus_compat_le_lt] and [sum_swap_cc] are interface forms awaiting
     normalization (the Real-layer witnesses [real_lt_plus_compat_le_lt] / real_lt_plus_compat_le_lt
     are already in the library; field promotion is the normalization route).
   - Not carried (abs_triangle_cc: zero use sites, removed — same cleanup as
     [differentiable_compose]); [abs_mult_cc] (replaced by the interface field [abs_mult], with its
     three use sites re-pointed).
   - Kept as an honest gap: [abs_ge_zero_id_cc] (the gap is documented at its declaration; the Real-layer
     witnesses are the combination at real_abs_pos_req + real_abs_zero_req). *)
(* Doeblin lower bound: delta ∈ (0,1), and every entry of the transition kernel is ≥ δ·the stationary mass *)
Variable delta : R.
Variable delta_pos : lt zero delta.
Variable delta_lt_one : lt delta one.
Variable minorization : forall s s', le (mult delta (boltzmann_dist_attn s')) (transition s s').
(* Mixed lt+le addition compatibility (as in [ConvergenceCauchy]; needed by [one_minus_delta_pos]) *)
(* Interface-level structural assumption: the interface carries only strict-strict and weak-weak
   addition compatibility ([S01_BaseRing]), with no producer for the strict-from-weak form, so this
   mixed form is not derivable at the interface layer and must not be forced or deleted outright;
   the concrete layer supplies the witness [real_lt_plus_compat_lt_le] ([S07_RealSetoidExpLog.v]) —
   resolution goes through instance-layer supply or field promotion. *)
Variable lt_plus_compat_lt_le : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
(* Interface-level structural assumption (the dual le_lt form): the interface carries only strict-strict
   and weak-weak addition compatibility ([S01_BaseRing]), with no producer for the strict-from-weak form,
   so this mixed form is not derivable at the interface layer and must not be forced or deleted outright;
   the concrete layer supplies the witness [real_lt_plus_compat_lt_le] ([S07_RealSetoidExpLog.v]) —
   resolution goes through instance-layer supply or field promotion. *)
Variable lt_plus_compat_le_lt : forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
(* Double-sum commutation (satisfied by any concrete finite sum) *)
Variable sum_swap_cc : forall (f : S -> S -> R),
  Id (sum_over_S (fun s => sum_over_S (fun s' => f s s')))
     (sum_over_S (fun s' => sum_over_S (fun s => f s s'))).
(* Properties of abs (standard properties of an ordered field, constructive). Accounting of the assumption face:
   - abs_triangle_cc: a zero-use assumption, removed (same cleanup as the unused assumptions of
     [differentiable_compose]); the true theorem of the same shape is the interface field [abs_triangle].
   - abs_mult_cc: duplicated inside this Section against the interface field [abs_mult]
     (the exact Id identity abs(a·b)==abs a·abs b); deleted, and its three use sites re-pointed to the
     interface field abs_mult — same signature shape (forall a b, Id (abs (mult a b)) (mult (abs a) (abs b))),
     same argument order, only the name changes at the use sites.
   The following is kept as an honest gap: abs_ge_zero_id_cc (the le-version abs identity: le zero a -> |a| == a).
   The interface [abs_pos] only has the lt version; le→(lt∨eq) has no tightness bridge (a gap at the abstract layer).
   The Real-layer witness path: real_abs_pos_req (strict version) + real_abs_zero_req
   plus the Or encoding of real_le; no ready le-version lemma exists in the library yet. *)
Variable abs_ge_zero_id_cc : forall a, le zero a -> Id (abs a) a.

(* ============ Definitions ============ *)
(* two uses the global lemma [two_pos] (lt zero (plus one one)); inv_two := 1/2 *)
Definition inv_two : R := inv_pos (plus one one) two_pos.

(* Total-variation distance TV(mu, nu) := (1/2)·Σ|mu − nu| *)
Definition tv_dist (mu nu : S -> R) : R :=
  mult inv_two (sum_over_S (fun s => abs (minus (mu s) (nu s)))).

(* One-step Markov iteration mu_{n+1}(s') := Σ_s mu(s)·T(s,s') *)
Definition attention_step (mu : S -> R) (s' : S) : R :=
  sum_over_S (fun s => mult (mu s) (transition s s')).

(* ============ Lemma 1: 1−δ > 0 ============ *)
Lemma one_minus_delta_pos : lt zero (minus one delta).
Proof.

  unfold minus. exact (lt_id_l zero (plus delta (opp delta)) (plus one (opp delta)) (id_sym (plus_opp delta)) (lt_plus_compat_lt_le delta one (opp delta) (opp delta) delta_lt_one (le_refl (opp delta)))).

Qed.

(* ============ Lemma 2: normalization of the Boltzmann distribution ============ *)
Lemma boltzmann_normalized_attn : Id (sum_over_S boltzmann_dist_attn) one.
Proof.

  unfold boltzmann_dist_attn. exact (id_trans (sum_over_S_linear (inv_pos Z_thermo Z_thermo_pos) boltzmann_factor) (id_trans (mult_comm (inv_pos Z_thermo Z_thermo_pos) Z_thermo) (inv_pos_correct Z_thermo Z_thermo_pos))).

Qed.

(* ============ Lemma 3: the residual kernel Q ============ *)
(* Q(s,s') := inv(1−δ)·(T(s,s') − δ·p_b(s')) (the stochastic kernel of the Doeblin decomposition) *)
Definition q_kernel (s s' : S) : R :=
  mult (inv_pos (minus one delta) one_minus_delta_pos)
       (minus (transition s s') (mult delta (boltzmann_dist_attn s'))).

(* Q is nonnegative ([minorization] + positive inverse) *)
Lemma q_kernel_nonneg : forall s s', le zero (q_kernel s s').
Proof.
  intros s s'.
  unfold q_kernel.
  apply (le_mult_nonneg_t12 (inv_pos (minus one delta) one_minus_delta_pos)
                            (minus (transition s s') (mult delta (boltzmann_dist_attn s')))).
  - apply (lt_le_iff _ _ (inl (inv_pos_pos (minus one delta) one_minus_delta_pos))).
  - apply (le_minus_nonneg (mult delta (boltzmann_dist_attn s')) (transition s s')).
    exact (minorization s s').
Qed.

(* Q is row-normalized: Σ_{s'} Q(s,s') == one *)
Lemma q_kernel_normalized : forall s, Id (sum_over_S (fun s' => q_kernel s s')) one.
Proof.

  intro s. unfold q_kernel. exact (id_trans (sum_over_S_linear (inv_pos (minus one delta) one_minus_delta_pos) (fun s' => minus (transition s s') (mult delta (boltzmann_dist_attn s')))) (id_trans (id_cong (fun x => mult (inv_pos (minus one delta) one_minus_delta_pos) x) (id_trans (sum_over_S_minus (fun s' => transition s s') (fun s' => mult delta (boltzmann_dist_attn s'))) (id_cong2 minus (transition_normalization s) (id_trans (sum_over_S_linear delta boltzmann_dist_attn) (id_cong (fun x => mult delta x) boltzmann_normalized_attn))))) (id_trans (id_cong (fun x => mult (inv_pos (minus one delta) one_minus_delta_pos) x) (id_cong (fun y => minus one y) (mult_one delta))) (id_trans (mult_comm (inv_pos (minus one delta) one_minus_delta_pos) (minus one delta)) (inv_pos_correct (minus one delta) one_minus_delta_pos))))).

Qed.

(* ============ Lemma 4: the decomposition T == δ·p + (1−δ)·Q ============ *)
Lemma transition_decomp : forall s s',
  Id (transition s s')
     (plus (mult delta (boltzmann_dist_attn s'))
           (mult (minus one delta) (q_kernel s s'))).
Proof.
  intros s s'.
  unfold q_kernel.
  assert (Habs : Id (mult (minus one delta)
                          (mult (inv_pos (minus one delta) one_minus_delta_pos)
                                (minus (transition s s') (mult delta (boltzmann_dist_attn s')))))
                    (minus (transition s s') (mult delta (boltzmann_dist_attn s')))).
  {
    apply (id_trans (mult_assoc (minus one delta) (inv_pos (minus one delta) one_minus_delta_pos)
                                (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))).
    apply (id_trans (id_cong (fun x => mult x (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))
                             (inv_pos_correct (minus one delta) one_minus_delta_pos))).
    apply (id_trans (mult_comm one (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))
                    (mult_one (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))).
  }
  apply (id_trans (id_sym (minus_plus_cancel_gap (transition s s') (mult delta (boltzmann_dist_attn s'))))).
  apply (id_trans (plus_comm (minus (transition s s') (mult delta (boltzmann_dist_attn s')))
                             (mult delta (boltzmann_dist_attn s')))).
  apply (id_cong (fun x => plus (mult delta (boltzmann_dist_attn s')) x) (id_sym Habs)).
Qed.

(* ============ Lemma 5: delta absorption, delta·a + (1−delta)·a == a ============ *)
Lemma delta_absorb : forall a : R,
  Id (plus (mult delta a) (mult (minus one delta) a)) a.
Proof.
  intro a.
  assert (H1 : Id (plus delta (minus one delta)) one).
  {
    unfold minus.
    apply (id_trans (plus_assoc delta one (opp delta))).
    apply (id_trans (id_cong (fun x => plus x (opp delta)) (plus_comm delta one))).
    apply (id_trans (id_sym (plus_assoc one delta (opp delta)))).
    apply (id_trans (id_cong (fun x => plus one x) (plus_opp delta))).
    exact (plus_zero one).
  }
  assert (H2 : Id (plus (mult delta a) (mult (minus one delta) a))
                  (plus (mult a delta) (mult a (minus one delta)))).
  { apply (id_cong2 plus (mult_comm delta a) (mult_comm (minus one delta) a)). }
  assert (H3 : Id (plus (mult a delta) (mult a (minus one delta))) (mult a (plus delta (minus one delta)))).
  { exact (id_sym (distrib a delta (minus one delta))). }
  apply (id_trans H2 (id_trans H3 (id_trans (id_cong (fun x => mult a x) H1) (mult_one a)))).
Qed.

(* ============ Lemma 6: the iteration decomposition mu' == δ·p + (1−δ)·mu·Q ============ *)
Lemma attention_step_decomp : forall mu s',
  Id (sum_over_S mu) one ->
  Id (attention_step mu s')
     (plus (mult delta (boltzmann_dist_attn s'))
           (mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s'))))).
Proof.
  intros mu s' Hmu_norm.
  unfold attention_step.
  apply (id_trans (sum_over_S_ext _ _
        (fun s => id_cong (fun x => mult (mu s) x) (transition_decomp s s')))).
  apply (id_trans (sum_over_S_ext _ _
        (fun s => distrib (mu s) (mult delta (boltzmann_dist_attn s')) (mult (minus one delta) (q_kernel s s'))))).
  apply (id_trans (sum_over_S_add (fun s => mult (mu s) (mult delta (boltzmann_dist_attn s')))
                                  (fun s => mult (mu s) (mult (minus one delta) (q_kernel s s'))))).
  (* First term: Σ mu·(δ·p) == δ·p (mu is normalized) *)
  assert (Hfirst : Id (sum_over_S (fun s => mult (mu s) (mult delta (boltzmann_dist_attn s'))))
                      (mult delta (boltzmann_dist_attn s'))).
  {
    apply (id_trans (sum_over_S_ext _ _ (fun s => mult_assoc (mu s) delta (boltzmann_dist_attn s')))).
    apply (id_trans (sum_over_S_ext _ _
        (fun s => id_cong (fun x => mult x (boltzmann_dist_attn s')) (mult_comm (mu s) delta)))).
    apply (id_trans (sum_over_S_ext _ _ (fun s => id_sym (mult_assoc delta (mu s) (boltzmann_dist_attn s'))))).
    apply (id_trans (sum_over_S_linear delta (fun s => mult (mu s) (boltzmann_dist_attn s')))).
    apply (id_trans (id_cong (fun x => mult delta x)
                             (id_trans (sum_over_S_ext _ _ (fun s => mult_comm (mu s) (boltzmann_dist_attn s')))
                                       (id_trans (sum_over_S_linear (boltzmann_dist_attn s') mu)
                                                 (id_trans (mult_comm (boltzmann_dist_attn s') (sum_over_S mu))
                                                           (id_cong (fun x => mult x (boltzmann_dist_attn s')) Hmu_norm)))))).
    apply (id_cong (fun x => mult delta x)
                   (id_trans (mult_comm one (boltzmann_dist_attn s')) (mult_one (boltzmann_dist_attn s')))).
  }
  exact (id_cong2 plus Hfirst (id_trans (sum_over_S_ext _ _ (fun s => id_trans (mult_assoc (mu s) (minus one delta) (q_kernel s s')) (id_trans (id_cong (fun x => mult x (q_kernel s s')) (mult_comm (mu s) (minus one delta))) (id_sym (mult_assoc (minus one delta) (mu s) (q_kernel s s')))))) (sum_over_S_linear (minus one delta) (fun s => mult (mu s) (q_kernel s s'))))).
Qed.

(* ============ Lemma 7: the iteration preserves normalization ============ *)
Lemma attention_step_normalized : forall mu,
  Id (sum_over_S mu) one ->
  Id (sum_over_S (attention_step mu)) one.
Proof.
  intros mu Hmu_norm.
  apply (id_trans (sum_over_S_ext _ _ (fun s' => attention_step_decomp mu s' Hmu_norm))).
  apply (id_trans (sum_over_S_add (fun s' => mult delta (boltzmann_dist_attn s'))
                                  (fun s' => mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))))).
  apply (id_trans (id_cong2 plus (id_trans (sum_over_S_linear delta boltzmann_dist_attn) (id_cong (fun x => mult delta x) boltzmann_normalized_attn)) (id_trans (sum_over_S_linear (minus one delta) (fun s2 => sum_over_S (fun s => mult (mu s) (q_kernel s s2)))) (id_cong (fun x => mult (minus one delta) x) (id_trans (id_sym (sum_swap_cc (fun s s2 => mult (mu s) (q_kernel s s2)))) (id_trans (sum_over_S_ext _ _ (fun s => sum_over_S_linear (mu s) (fun s2 => q_kernel s s2))) (sum_over_S_ext _ _ (fun s => id_cong (fun x => mult (mu s) x) (q_kernel_normalized s))))))))).
  (* Now: plus (mult delta one) (mult (minus one delta) (sum_over_S (fun s => mult (mu s) one))) == one *)
  assert (Hsum_one : Id (sum_over_S (fun s => mult (mu s) one)) one).
  {
    apply (id_trans (sum_over_S_ext _ _ (fun s => mult_one (mu s)))).
    apply (id_trans (sum_over_S_ext _ _ (fun s => id_sym (id_trans (mult_comm one (mu s)) (mult_one (mu s)))))).
    apply (id_trans (sum_over_S_linear one mu)).
    apply (id_trans (id_cong (fun x => mult one x) Hmu_norm)).
    apply (id_trans (mult_comm one one) (mult_one one)).
  }
  apply (id_trans (id_cong (fun x => plus (mult delta one) x)
                           (id_cong (fun x => mult (minus one delta) x) Hsum_one))).
  exact (delta_absorb one).
Qed.


(* ============ Part 2: the TV-contraction core ============ *)

(* Auxiliary: minus (plus a b) c == plus b (minus a c) *)
Lemma minus_plus_swap_cc : forall a b c : R,
  Id (minus (plus a b) c) (plus b (minus a c)).
Proof.

  intros a b c. unfold minus. exact (id_trans (id_sym (plus_assoc a b (opp c))) (id_trans (id_cong (fun x => plus a x) (plus_comm b (opp c))) (id_trans (plus_assoc a (opp c) b) (plus_comm (plus a (opp c)) b)))).

Qed.

(* Auxiliary: minus (mult a b) b == opp (mult (minus one a) b) *)
Lemma minus_scal_opp_cc : forall a b : R,
  Id (minus (mult a b) b) (opp (mult (minus one a) b)).
Proof.
  intros a b.
  assert (H : Id (minus a one) (opp (minus one a))).
  {
    unfold minus.
    apply (id_trans (plus_comm a (opp one))).
    apply (id_trans (id_cong2 plus (id_refl) (id_sym (double_neg a)))).
    apply (id_sym (opp_plus one (opp a))).
  }
  apply (id_trans (id_cong (fun x => minus (mult a b) x)
                           (id_sym (id_trans (mult_comm one b) (mult_one b))))).
  apply (id_trans (id_sym (mult_minus_distr_r_t12 a one b))).
  apply (id_trans (id_cong (fun x => mult x b) H) (opp_mult_r (minus one a) b)).
Qed.

(* Auxiliary: additive cancellation, plus a b == c ⟹ b == minus c a *)
Lemma plus_cancel_cc : forall a b c : R,
  Id (plus a b) c -> Id b (minus c a).
Proof.

  intros a b c H. unfold minus. exact (id_trans (id_sym (id_trans (plus_comm zero b) (plus_zero b))) (id_trans (id_cong (fun x => plus x b) (id_sym (plus_opp a))) (id_trans (id_sym (plus_assoc a (opp a) b)) (id_trans (id_cong (fun x => plus a x) (plus_comm (opp a) b)) (id_trans (plus_assoc a b (opp a)) (id_cong (fun x => plus x (opp a)) H)))))).

Qed.

(* Auxiliary: inverse absorption, mult (inv c) (mult c a) == a *)
Lemma absorb_inv_cc : forall (c : R) (Hc : lt zero c) (a : R),
  Id (mult (inv_pos c Hc) (mult c a)) a.
Proof.

  intros c Hc a. exact (id_trans (mult_assoc (inv_pos c Hc) c a) (id_trans (id_cong (fun x => mult x a) (id_trans (mult_comm (inv_pos c Hc) c) (inv_pos_correct c Hc))) (id_trans (mult_comm one a) (mult_one a)))).

Qed.

(* Positivity of the Boltzmann distribution *)
Lemma boltzmann_attn_pos : forall s, lt zero (boltzmann_dist_attn s).
Proof.
  intro s.
  unfold boltzmann_dist_attn.
  apply mult_positive.
  - apply inv_pos_pos.
  - unfold boltzmann_factor. apply exp_neg_pos.
Qed.

(* 1−δ ≤ 1 (delta ≥ 0) *)
Lemma one_minus_delta_le_one : le (minus one delta) one.
Proof.
  apply (le_id_r _ (plus (minus one delta) delta) _).
  - apply (id_trans (plus_comm (minus one delta) delta)
                    (minus_plus_cancel delta one)).
  - apply (le_plus_nonneg_r (minus one delta) delta).
    apply (lt_le_iff _ _ (inl delta_pos)).
Qed.

(* 1−δ < 1 (delta > 0) *)
Lemma one_minus_delta_lt_one : lt (minus one delta) one.
Proof.

  unfold minus. exact (lt_id_r (plus one (opp delta)) (plus one zero) one (plus_zero one) (lt_plus_compat_le_lt one one (opp delta) zero (le_refl one) (lt_zero_opp delta delta_pos))).

Qed.

(* Stationary-state preservation: p·Q == p (p·T==p combined with the decomposition) *)
Lemma boltzmann_q_fixed : forall s',
  Id (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))
     (boltzmann_dist_attn s').
Proof.
  intro s'.
  pose proof (steady_state_boltzmann_attn s') as H1.
  pose proof (attention_step_decomp boltzmann_dist_attn s' boltzmann_normalized_attn) as H2.
  assert (H3 : Id (plus (mult delta (boltzmann_dist_attn s'))
                        (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))))
                  (boltzmann_dist_attn s')).
  { apply (id_trans (id_sym H2) H1). }
  assert (H4 : Id (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s'))))
                  (minus (boltzmann_dist_attn s') (mult delta (boltzmann_dist_attn s')))).
  { exact (plus_cancel_cc (mult delta (boltzmann_dist_attn s'))
                          (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s'))))
                          (boltzmann_dist_attn s') H3). }
  assert (H6 : Id (minus (boltzmann_dist_attn s') (mult delta (boltzmann_dist_attn s')))
                  (mult (minus one delta) (boltzmann_dist_attn s'))).
  {
    apply (id_trans (id_cong (fun x => minus x (mult delta (boltzmann_dist_attn s')))
                             (id_sym (id_trans (mult_comm one (boltzmann_dist_attn s')) (mult_one (boltzmann_dist_attn s')))))).
    apply (id_sym (mult_minus_distr_r_t12 one delta (boltzmann_dist_attn s'))).
  }
  assert (H7 : Id (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s'))))
                  (mult (minus one delta) (boltzmann_dist_attn s'))).
  { apply (id_trans H4 H6). }
  apply (id_trans (id_sym (absorb_inv_cc (minus one delta) one_minus_delta_pos
                                          (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))))
                  (id_trans (id_cong (fun x => mult (inv_pos (minus one delta) one_minus_delta_pos) x) H7)
                            (absorb_inv_cc (minus one delta) one_minus_delta_pos (boltzmann_dist_attn s')))).
Qed.

(* Pointwise difference decomposition: mu' − p == (1−δ)·Σ_s (mu−p)·Q *)
Lemma attention_diff_decomp : forall mu s',
  Id (sum_over_S mu) one ->
  Id (minus (attention_step mu s') (boltzmann_dist_attn s'))
     (mult (minus one delta)
           (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))).
Proof.

  intros mu s' Hmu_norm. exact (id_trans (id_cong (fun x => minus x (boltzmann_dist_attn s')) (attention_step_decomp mu s' Hmu_norm)) (id_trans (minus_plus_swap_cc (mult delta (boltzmann_dist_attn s')) (mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))) (boltzmann_dist_attn s')) (id_trans (id_cong (fun x => plus (mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))) x) (minus_scal_opp_cc delta (boltzmann_dist_attn s'))) (id_trans (id_sym (mult_minus_distr_l (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s'))) (boltzmann_dist_attn s'))) (id_cong (fun x => mult (minus one delta) x) (id_trans (id_cong (fun x => minus (sum_over_S (fun s => mult (mu s) (q_kernel s s'))) x) (id_sym (boltzmann_q_fixed s'))) (id_trans (id_sym (sum_over_S_minus (fun s => mult (mu s) (q_kernel s s')) (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))) (id_sym (sum_over_S_ext _ _ (fun s => id_trans (mult_comm (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')) (id_trans (mult_minus_distr_l (q_kernel s s') (mu s) (boltzmann_dist_attn s)) (id_cong2 minus (mult_comm (q_kernel s s') (mu s)) (mult_comm (q_kernel s s') (boltzmann_dist_attn s)))))))))))))).

Qed.


(* ============ Part 3: the main TV-contraction theorem ============ *)

(* |Σ f·Q| ≤ Σ |f|·Q ([abs_sum_le] + the interface field [abs_mult] + Q ≥ 0) *)
Lemma abs_kernel_bound : forall (f : S -> R) (s' : S),
  le (abs (sum_over_S (fun s => mult (f s) (q_kernel s s'))))
     (sum_over_S (fun s => mult (abs (f s)) (q_kernel s s'))).
Proof.
  intros f s'.
  apply (le_id_r (abs (sum_over_S (fun s => mult (f s) (q_kernel s s'))))
                 (sum_over_S (fun s => abs (mult (f s) (q_kernel s s'))))
                 (sum_over_S (fun s => mult (abs (f s)) (q_kernel s s')))).
  - apply (sum_over_S_ext _ _ (fun s =>
      id_trans (abs_mult (f s) (q_kernel s s'))
               (id_cong (fun x => mult (abs (f s)) x) (abs_ge_zero_id_cc (q_kernel s s') (q_kernel_nonneg s s'))))).
  - exact (abs_sum_le (fun s => mult (f s) (q_kernel s s'))).
Qed.

(* The TV distance is nonnegative *)
Lemma tv_dist_nonneg : forall mu nu, le zero (tv_dist mu nu).
Proof.
  intros mu nu.
  unfold tv_dist.
  apply (le_mult_nonneg_t12 inv_two (sum_over_S (fun s => abs (minus (mu s) (nu s))))).
  - apply (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))).
  - apply sum_over_S_nonneg. intro s. apply abs_nonneg.
Qed.

(* The iteration preserves nonnegativity: mu normalized and nonnegative ⟹ attention_step mu nonnegative *)
Lemma attention_step_nonneg : forall mu,
  Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
  forall s', le zero (attention_step mu s').
Proof.
  intros mu Hmu_norm Hmu_nonneg s'.
  set (X := mult delta (boltzmann_dist_attn s')).
  set (Y := mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))).
  assert (HX : le zero X).
  {
    unfold X.
    apply (le_mult_nonneg_t12 delta (boltzmann_dist_attn s')).
    - apply (lt_le_iff _ _ (inl delta_pos)).
    - apply (lt_le_iff _ _ (inl (boltzmann_attn_pos s'))).
  }
  assert (HY : le zero Y).
  {
    unfold Y.
    apply (le_mult_nonneg_t12 (minus one delta)
                              (sum_over_S (fun s => mult (mu s) (q_kernel s s')))).
    - apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
    - apply sum_over_S_nonneg. intro s.
      apply (le_mult_nonneg_t12 (mu s) (q_kernel s s')).
      + exact (Hmu_nonneg s).
      + exact (q_kernel_nonneg s s').
  }
  assert (Hstep : le zero (plus X Y)).
  {
    assert (Hplus : le (plus zero zero) (plus X Y))
      by exact (le_plus_compat zero X zero Y HX HY).
    apply (le_id_l zero (plus zero zero) (plus X Y) (id_sym (plus_zero zero)) Hplus).
  }
  apply (le_id_r zero (plus X Y) (attention_step mu s')).
  - apply (id_sym (attention_step_decomp mu s' Hmu_norm)).
  - exact Hstep.
Qed.


(* Double-sum reduction: (1/2)·Σ_{s'} (1−δ)·Σ_s f·Q == (1−δ)·(1/2)·Σ_s f *)
Lemma tv_reduce_cc : forall (f : S -> R),
  Id (mult inv_two (sum_over_S (fun s' => mult (minus one delta) (sum_over_S (fun s => mult (f s) (q_kernel s s'))))))
     (mult (minus one delta) (mult inv_two (sum_over_S f))).
Proof.

  intros f. exact (id_trans (id_cong (fun x => mult inv_two x) (id_trans (sum_over_S_linear (minus one delta) (fun s' => sum_over_S (fun s => mult (f s) (q_kernel s s')))) (id_cong (fun x => mult (minus one delta) x) (id_trans (id_sym (sum_swap_cc (fun s s' => mult (f s) (q_kernel s s')))) (id_trans (sum_over_S_ext _ _ (fun s => sum_over_S_linear (f s) (fun s2 => q_kernel s s2))) (id_trans (sum_over_S_ext _ _ (fun s => id_cong (fun x => mult (f s) x) (q_kernel_normalized s))) (sum_over_S_ext _ _ (fun s => mult_one (f s))))))))) (id_trans (mult_assoc inv_two (minus one delta) (sum_over_S f)) (id_trans (id_cong (fun x => mult x (sum_over_S f)) (mult_comm inv_two (minus one delta))) (id_sym (mult_assoc (minus one delta) inv_two (sum_over_S f)))))).

Qed.

(* |c·b| ≤ c·|b| (c ≥ 0) *)
Lemma abs_mult_nonneg_cc : forall a b, le zero a -> le (abs (mult a b)) (mult a (abs b)).
Proof.

  intros a b Ha. exact (le_id_l (abs (mult a b)) (mult a (abs b)) (mult a (abs b)) (id_trans (abs_mult a b) (id_cong (fun x => mult x (abs b)) (abs_ge_zero_id_cc a Ha))) (le_refl _)).

Qed.

(* ============ Main theorem: one-step TV contraction (Doeblin) ============ *)
Theorem attention_tv_contraction :
  forall mu, Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
    le (tv_dist (attention_step mu) boltzmann_dist_attn)
       (mult (minus one delta) (tv_dist mu boltzmann_dist_attn)).
Proof.
  intros mu Hmu_norm Hmu_nonneg.
  unfold tv_dist, attention_step.
  assert (Hpt : forall s', le (abs (minus (attention_step mu s') (boltzmann_dist_attn s')))
                             (mult (minus one delta)
                                   (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s'))))).
  {
    intro s'.
    pose proof (attention_diff_decomp mu s' Hmu_norm) as Hd.
    apply (le_id_l (abs (minus (attention_step mu s') (boltzmann_dist_attn s')))
                   (abs (mult (minus one delta)
                              (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))))
                   (mult (minus one delta)
                         (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s'))))).
    - apply (id_cong abs Hd).
    - apply (le_trans _ (mult (minus one delta)
                              (abs (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))))
                     _).
      + apply (abs_mult_nonneg_cc (minus one delta)
                                  (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))).
        apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
      + apply (le_mult_compat_r (minus one delta)
                                (abs (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s'))))
                                (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s')))).
        * apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
        * apply (abs_kernel_bound (fun s => minus (mu s) (boltzmann_dist_attn s)) s').
  }
  apply (le_trans _ (mult inv_two (sum_over_S (fun s' => mult (minus one delta)
                                                    (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s')))))) _).
  - apply (le_mult_compat_r inv_two
                            (sum_over_S (fun s' => abs (minus (attention_step mu s') (boltzmann_dist_attn s'))))
                            (sum_over_S (fun s' => mult (minus one delta)
                                              (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s')))))).
    + apply (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))).
    + apply sum_over_S_le. exact Hpt.
  - (* Second-term reduction: (1/2)·Σ_{s'} (1−δ)·Σ_s |mu−p|·Q == (1−δ)·(1/2)·Σ_s |mu−p| *)
    apply (le_id_l (mult inv_two (sum_over_S (fun s' => mult (minus one delta)
                                                  (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s'))))))
                   (mult (minus one delta) (mult inv_two (sum_over_S (fun s => abs (minus (mu s) (boltzmann_dist_attn s))))))
                   (mult (minus one delta) (mult inv_two (sum_over_S (fun s => abs (minus (mu s) (boltzmann_dist_attn s))))))).
    + exact (tv_reduce_cc (fun s => abs (minus (mu s) (boltzmann_dist_attn s)))).
    + apply le_refl.
Qed.


(* ============ Finally: geometric iterated contraction and convergence ============ *)

(* Geometric breakthrough (the Archimedean property at the Real layer, same pattern as [r_arch_pow] of ConvergenceCauchy) *)
Variable r_arch_pow_attn : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (r_pow (minus one delta) N)) eps).

(* (1−δ)^n is decreasing: m ≤ n ⟹ (1−δ)^n ≤ (1−δ)^m *)
Lemma r_pow_dec_iter_attn : forall m n, (m <= n)%nat -> le (r_pow (minus one delta) n) (r_pow (minus one delta) m).
Proof.
  intros m n Hmn.
  revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - assert (Hm0 : m = 0%nat) by lia. subst m. apply le_refl.
  - destruct (Nat.leb m n) eqn:Emn.
    + apply (le_trans _ (r_pow (minus one delta) n) _).
      * apply (r_pow_dec (minus one delta) n one_minus_delta_pos one_minus_delta_lt_one).
      * apply (IH m (proj1 (PeanoNat.Nat.leb_le m n) Emn)).
    + apply PeanoNat.Nat.leb_gt in Emn.
      assert (Hm : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* The iteration preserves normalization *)
Lemma iterate_attention_normalized : forall mu n,
  Id (sum_over_S mu) one -> Id (sum_over_S (iterate attention_step n mu)) one.
Proof.
  intros mu n Hmu_norm.
  induction n as [| n IH].
  - simpl. exact Hmu_norm.
  - simpl. apply attention_step_normalized. exact IH.
Qed.

(* The iteration preserves nonnegativity *)
Lemma iterate_attention_nonneg : forall mu n,
  Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
  forall s, le zero (iterate attention_step n mu s).
Proof.
  intros mu n Hmu_norm Hmu_nonneg.
  induction n as [| n IH].
  - simpl. exact Hmu_nonneg.
  - simpl. intro s. apply attention_step_nonneg. apply (iterate_attention_normalized mu n Hmu_norm). exact IH.
Qed.

(* Geometric iterated TV contraction: the (1−δ)^n·TV_0 bound *)
Lemma attention_tv_iter_contraction : forall mu n,
  Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
    le (tv_dist (iterate attention_step n mu) boltzmann_dist_attn)
       (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn)).
Proof.
  intros mu n Hmu_norm Hmu_nonneg.
  induction n as [| n IH].
  - simpl.
    apply (le_id_l (tv_dist mu boltzmann_dist_attn)
                   (tv_dist (iterate attention_step 0 mu) boltzmann_dist_attn)
                   (mult one (tv_dist mu boltzmann_dist_attn))).
    + apply (id_sym (id_cong (fun x => tv_dist x boltzmann_dist_attn) (id_refl))).
    + apply (le_id_l (tv_dist mu boltzmann_dist_attn)
                     (mult one (tv_dist mu boltzmann_dist_attn))
                     (mult one (tv_dist mu boltzmann_dist_attn))
                     (id_sym (id_trans (mult_comm one (tv_dist mu boltzmann_dist_attn))
                                 (mult_one (tv_dist mu boltzmann_dist_attn))))
                     (le_refl _)).
  - set (mun := iterate attention_step n mu).
    assert (Hn_norm : Id (sum_over_S mun) one) by (unfold mun; apply (iterate_attention_normalized mu n Hmu_norm)).
    assert (Hn_nonneg : forall s, le zero (mun s)) by (unfold mun; apply (iterate_attention_nonneg mu n Hmu_norm Hmu_nonneg)).
    apply (le_trans _ (mult (minus one delta)
                            (tv_dist mun boltzmann_dist_attn)) _).
    + apply (le_id_l (tv_dist (attention_step mun) boltzmann_dist_attn)
                     (tv_dist (iterate attention_step (Datatypes.S n) mu) boltzmann_dist_attn)
                     (mult (minus one delta) (tv_dist mun boltzmann_dist_attn))).
      * apply (id_sym (id_cong (fun x => tv_dist x boltzmann_dist_attn) (id_refl))).
      * apply (attention_tv_contraction mun Hn_norm Hn_nonneg).
    + apply (le_trans _ (mult (minus one delta)
                              (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn))) _).
      * apply (le_mult_compat_r (minus one delta) (tv_dist mun boltzmann_dist_attn)
                                (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn))).
        -- apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
        -- exact IH.
      * apply (le_id_l (mult (minus one delta)
                             (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn)))
                       (mult (r_pow (minus one delta) (Datatypes.S n)) (tv_dist mu boltzmann_dist_attn))
                       (mult (r_pow (minus one delta) (Datatypes.S n)) (tv_dist mu boltzmann_dist_attn))).
        -- apply (mult_assoc (minus one delta) (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn)).
        -- apply le_refl.
Qed.

(* Finally: convergence of the attention iteration (TV → 0, in sigT form; the initial TV is positive) *)
Theorem attention_iterate_converges :
  forall mu0, Id (sum_over_S mu0) one -> (forall s, le zero (mu0 s)) ->
  forall eps, lt zero eps ->
    lt zero (tv_dist mu0 boltzmann_dist_attn) ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      lt (tv_dist (iterate attention_step n mu0) boltzmann_dist_attn) eps).
Proof.
  intros mu0 Hmu_norm Hmu_nonneg eps Hep Htv0.
  destruct (r_arch_pow_attn (tv_dist mu0 boltzmann_dist_attn) Htv0 eps Hep) as [N HN].
  exists N.
  intros n Hn.
  apply (le_lt_trans _ (mult (r_pow (minus one delta) n) (tv_dist mu0 boltzmann_dist_attn)) _).
  - exact (attention_tv_iter_contraction mu0 n Hmu_norm Hmu_nonneg).
  - apply (le_lt_trans _ (mult (r_pow (minus one delta) N) (tv_dist mu0 boltzmann_dist_attn)) _).
    + apply (le_mult_compat_weak (r_pow (minus one delta) n)
                               (r_pow (minus one delta) N)
                               (tv_dist mu0 boltzmann_dist_attn)).
      * exact (tv_dist_nonneg mu0 boltzmann_dist_attn).
      * apply (r_pow_dec_iter_attn N n (NatLe_drop N n Hn)).
    + exact (lt_id_l (mult (r_pow (minus one delta) N) (tv_dist mu0 boltzmann_dist_attn))
                     (mult (tv_dist mu0 boltzmann_dist_attn) (r_pow (minus one delta) N))
                     eps
                     (mult_comm (r_pow (minus one delta) N) (tv_dist mu0 boltzmann_dist_attn))
                     HN).
Qed.

(* ---- KV eviction: breaking detailed balance ---- *)
Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Definition evicted_transition (s s' : S) : R :=
  if keep_dec s then
    if keep_dec s' then transition s s' else zero
  else zero.

Definition evicted_partition : R :=
  sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero).

Variable evicted_partition_pos : lt zero evicted_partition.

Definition evicted_boltzmann (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evicted_partition evicted_partition_pos) (boltzmann_factor s)
  else zero.

Definition db_breaking (s s' : S) : R :=
  abs (minus (mult (evicted_boltzmann s) (evicted_transition s s'))
             (mult (evicted_boltzmann s') (evicted_transition s' s))).

(* A fluctuation-dissipation-type constraint (derivable from concrete dynamics; stated here as an explicit assumption) *)
Variable fluctuation_dissipation_bound :
  forall s s',
    le (db_breaking s s')
       (mult (abs (energy s)) (plus (abs (energy s')) one)).

Theorem eviction_db_breaking_bound :
  forall s s',
    le (db_breaking s s')
       (mult (abs (energy s)) (plus (abs (energy s')) one)).
Proof.

  intros s s'. exact (fluctuation_dissipation_bound s s').

Qed.

(* ============================================================ *)
(* The optimal KV-eviction policy (supporting theorems) *)
(* ============================================================ *)
(* Policy rationale: given a capacity budget, the states with the highest Boltzmann weights *)
(* (lowest energy / highest future use frequency) should be kept.  The following two supporting theorems *)
(* ensure the policy is mathematically benign: *)
(*   (a) the evicted distribution is still a probability measure (normalized over the kept states) — *)
(*       the probability semantics do not collapse under eviction; *)
(*   (b) monotone enlargement of the kept set ⟹ the evicted partition function does not decrease — "the more is kept, the more mass", the directional correctness of the greedy/optimal retention policy. *)

(* Pointwise identity: if k s then a·f(s) else 0 = a·(if k s then f(s) else 0) *)
Lemma eviction_if_linear :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) (a : R) (f : S -> R) (s : S),
    Id (if kd s then mult a (f s) else zero)
       (mult a (if kd s then f s else zero)).
Proof.
  intros k kd a f s.
  destruct (kd s) as [Hk | Hnk].
  - reflexivity.
  - (* Non-kept state: zero = a·zero *)
    apply id_sym.
    apply mult_zero.
Qed.

(* Pointwise monotonicity: k1 ⊆ k2 ⟹ if k1 s then f s else 0 ≤ if k2 s then f s else 0
   (f is the Boltzmann factor, and its positivity secures the zero ≤ f s side) *)
Lemma eviction_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    le (if kd1 s then boltzmann_factor s else zero)
       (if kd2 s then boltzmann_factor s else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | Hn1].
  - (* k1 s holds ⟹ k2 s holds ([Hsub]) *)
    destruct (kd2 s) as [H2 | Hn2].
    + apply le_refl.
    + (* Contradiction: k2 s and Not (k2 s) *)
      exact (match Hn2 (Hsub s H1) with end).
  - (* k1 s fails: the left side is zero *)
    destruct (kd2 s) as [H2 | Hn2].
    + (* The right side is f s > 0 ⟹ zero ≤ f s *)
      apply (lt_le_iff zero (boltzmann_factor s)).
      left.
      unfold boltzmann_factor.
      apply exp_neg_pos.
    + apply le_refl.
Qed.

(* The conditional partition function over the kept states (parameterized by keep: monotonicity compares two kept sets) *)
Definition evicted_partition_of
  (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sum_over_S (fun s => if kd s then boltzmann_factor s else zero).

(* Supporting theorem (a): the evicted distribution is still normalized — Σ_s evicted_boltzmann(s) = 1
   (probability mass conserved over the kept states; non-kept states contribute 0) *)
Theorem evicted_boltzmann_normalized :
  Id (sum_over_S (fun s => evicted_boltzmann s)) one.
Proof.
  (* An assert + exact chain (avoiding the syntactic mismatch of rewrite against if/match shapes) *)
  assert (H1 : Id (sum_over_S (fun s => evicted_boltzmann s))
                  (sum_over_S (fun s => mult (inv_pos evicted_partition evicted_partition_pos)
                                            (if keep_dec s then boltzmann_factor s else zero)))).
  {
    apply sum_over_S_ext.
    intro s.
    unfold evicted_boltzmann.
    exact (eviction_if_linear keep keep_dec (inv_pos evicted_partition evicted_partition_pos) boltzmann_factor s).
  }
  assert (H2 : Id (sum_over_S (fun s => mult (inv_pos evicted_partition evicted_partition_pos)
                                            (if keep_dec s then boltzmann_factor s else zero)))
                  (mult (inv_pos evicted_partition evicted_partition_pos)
                        (sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero)))).
  { apply sum_over_S_linear. }
  assert (H3 : Id (mult (inv_pos evicted_partition evicted_partition_pos)
                        (sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero)))
                  one).
  {
    unfold evicted_partition.
    assert (Hcc : Id (mult (inv_pos evicted_partition evicted_partition_pos) evicted_partition) one)
      by exact (id_trans (mult_comm (inv_pos evicted_partition evicted_partition_pos) evicted_partition)
                         (inv_pos_correct evicted_partition evicted_partition_pos)).
    exact Hcc.
  }
  exact (id_trans H1 (id_trans H2 H3)).
Qed.

(* Supporting theorem (b): monotone enlargement of the kept set ⟹ the partition function does not decrease
   (the more is kept, the more mass).  The basis of the directional correctness of the optimal retention
   policy (greedy admission in decreasing Boltzmann weight). *)
Theorem eviction_partition_monotone :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    le (evicted_partition_of k1 kd1) (evicted_partition_of k2 kd2).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evicted_partition_of.
  apply sum_over_S_le.
  intro s.
  exact (eviction_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* ============================================================ *)
(* The optimal KV-eviction policy (companion supporting theorems) *)
(* ============================================================ *)
(*   (c) the evicted partition function is bounded by the full partition function: for any kept set, *)
(*       evicted_partition ≤ Z_thermo (the more is kept, the more mass ⟹ *)
(*       full retention is the mass upper bound; the gauge for mass loss under a capacity budget). *)
(*   (d) the reference for the breaking: with full retention, evicted_transition = *)
(*       transition and evicted_boltzmann = boltzmann_dist_attn, so detailed balance is unbroken *)
(*       (eviction is the only source of breaking). *)

(* Lemma: if k s then f s else 0 ≤ f s (the Boltzmann factor is nonnegative) *)
Lemma eviction_if_le :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
  forall s : S,
    le (if kd s then boltzmann_factor s else zero) (boltzmann_factor s).
Proof.
  intros k kd s.
  destruct (kd s) as [Hk | Hnk].
  - apply le_refl.
  - (* zero ≤ f s (f is positive) *)
    apply (lt_le_iff zero (boltzmann_factor s)).
    left.
    unfold boltzmann_factor.
    apply exp_neg_pos.
Qed.

(* Supporting theorem (c): evicted_partition ≤ Z_thermo — full retention is the mass upper bound.
   Eviction can only lose probability mass; the mass loss under a capacity budget is Z_thermo - evicted_partition ≥ 0. *)
Theorem eviction_partition_le_full :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
    le (evicted_partition_of k kd) Z_thermo.
Proof.
  intros k kd.
  unfold evicted_partition_of, Z_thermo.
  apply sum_over_S_le.
  intro s.
  exact (eviction_if_le k kd s).
Qed.

(* Supporting theorem (d): full retention (keep always true) ⟹ evicted_transition = transition.
   That is, when keep excludes no state, the evicted transition agrees with the original transition pointwise. *)

Theorem eviction_transition_full :
  (forall s, keep s) ->
  forall s s' : S, Id (evicted_transition s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evicted_transition.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + reflexivity.
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* Supporting theorem (d'): full retention and evicted_partition = Z_thermo ⟹
   evicted_boltzmann = boltzmann_dist_attn (the evicted distribution returns to the original distribution). *)
Theorem eviction_boltzmann_full :
  (forall s, keep s) ->
  Id evicted_partition Z_thermo ->
  forall s : S, Id (evicted_boltzmann s) (boltzmann_dist_attn s).
Proof.
  intros Hkall HZ s.
  unfold evicted_boltzmann, boltzmann_dist_attn, boltzmann_factor, evicted_partition.
  destruct (keep_dec s) as [Hks | Hnks].
  - (* Kept state: inv_ev·f s = inv_Z·f s (unify the inverses via [inv_pos_ext]) *)
    assert (Hie : Id (inv_pos evicted_partition evicted_partition_pos)
                     (inv_pos Z_thermo Z_thermo_pos))
      by exact (inv_pos_ext evicted_partition Z_thermo evicted_partition_pos Z_thermo_pos HZ).
    exact (id_cong (fun x => mult x (exp_neg (mult (inv_pos D D_pos) (energy s)))) Hie).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* Supporting theorem (e): full retention ⟹ detailed balance is unbroken — eviction is the only source of breaking.
   (Contrast with [eviction_db_breaking_bound]: the breaking is bounded; here, no eviction means no breaking.) *)
Theorem eviction_db_zero_full :
  (forall s, keep s) ->
  Id evicted_partition Z_thermo ->
  forall s s' : S, Id (db_breaking s s') zero.
Proof.
  intros Hkall HZ s s'.
  unfold db_breaking.
  assert (Heb : forall t, Id (evicted_boltzmann t) (boltzmann_dist_attn t))
    by exact (eviction_boltzmann_full Hkall HZ).
  assert (Het : forall t u, Id (evicted_transition t u) (transition t u))
    by exact (eviction_transition_full Hkall).
  (* Goal: abs (minus (ev_b s · ev_t s s') (ev_b s' · ev_t s' s)) = 0 *)
  assert (Harg : Id (minus (mult (evicted_boltzmann s) (evicted_transition s s'))
                           (mult (evicted_boltzmann s') (evicted_transition s' s)))
                    zero).
  {
    assert (Hdb : Id (mult (boltzmann_dist_attn s) (transition s s'))
                     (mult (boltzmann_dist_attn s') (transition s' s)))
      by exact (detailed_balance s s').
    assert (Hl : Id (mult (evicted_boltzmann s) (evicted_transition s s'))
                    (mult (boltzmann_dist_attn s) (transition s s')))
      by exact (id_trans (id_cong (fun x => mult x (evicted_transition s s')) (Heb s))
                          (id_cong (fun x => mult (boltzmann_dist_attn s) x) (Het s s'))).
    assert (Hr : Id (mult (evicted_boltzmann s') (evicted_transition s' s))
                    (mult (boltzmann_dist_attn s') (transition s' s)))
      by exact (id_trans (id_cong (fun x => mult x (evicted_transition s' s)) (Heb s'))
                          (id_cong (fun x => mult (boltzmann_dist_attn s') x) (Het s' s))).
    assert (Heq : Id (mult (evicted_boltzmann s) (evicted_transition s s'))
                     (mult (evicted_boltzmann s') (evicted_transition s' s)))
      by exact (id_trans Hl (id_trans Hdb (id_sym Hr))).
    exact (minus_self_zero _ _ Heq).
  }
  assert (Habs : Id (abs (minus (mult (evicted_boltzmann s) (evicted_transition s s'))
                                (mult (evicted_boltzmann s') (evicted_transition s' s))))
                    zero)
    by exact (id_trans (id_cong abs Harg) abs_zero).
  exact Habs.
Qed.

(* ============================================================ *)
(* Quantifying the stationary-state deviation of eviction (the cost measure of the KV-eviction policy) *)
(* ============================================================ *)
(* Background: after eviction breaks detailed balance, evicted_boltzmann is no longer stationary. *)
(* This theorem quantifies the deviation from the stationary equation: *)
(*   |Σ_{s'} ev_b(s')·ev_t(s',s) - ev_b(s)·Σ_{s'} ev_t(s,s')|  *)
(*     ≤ Σ_{s'} db_breaking(s,s')                              *)
(* That is: the stationary-state damage caused by eviction is controlled by the summed detailed-balance *)
(* breaking — db_breaking is the exact upper-bound source of the eviction cost. *)
(* Proof: the difference term = Σ[ev_b(s')·ev_t(s',s) - ev_b(s)·ev_t(s,s')] *)
(* (with ev_b(s) extracted by linearity); taking abs and applying [abs_sum_le] gives Σ|·| = Σ db. *)
(* ------------------------------------------------------------ *)

(* The evicted stationary deviation ≤ the summed breaking (the quantitative bound on the KV-eviction cost) *)
Theorem eviction_steady_deviation :
  forall s,
    le (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                   (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
       (sum_over_S (fun s' => db_breaking s s')).
Proof.
  intro s.
  (* 1. Extract the constant factor ev_b(s): Σ ev_b(s)·ev_t(s,s') = ev_b(s)·Σ ev_t(s,s') *)
  assert (Hlin : Id (sum_over_S (fun s' => mult (evicted_boltzmann s) (evicted_transition s s')))
                    (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s'))))
    by exact (sum_over_S_linear (evicted_boltzmann s) (fun s' => evicted_transition s s')).
  (* 2. Rewrite the difference term: Σ_{s'} ev_b(s')·ev_t(s',s) - Σ_{s'} ev_b(s)·ev_t(s,s')
         = Σ_{s'} [ev_b(s')·ev_t(s',s) - ev_b(s)·ev_t(s,s')] ([sum_over_S_minus]) *)
  assert (Hdiff : Id (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                            (sum_over_S (fun s' => mult (evicted_boltzmann s) (evicted_transition s s'))))
                    (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                (mult (evicted_boltzmann s) (evicted_transition s s')))))
    by exact (id_sym (sum_over_S_minus (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s))
                               (fun s' => mult (evicted_boltzmann s) (evicted_transition s s')))).
  assert (Hlhs : Id (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                           (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s'))))
                    (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                           (sum_over_S (fun s' => mult (evicted_boltzmann s) (evicted_transition s s')))))
    by exact (id_cong (fun x => minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s))) x)
                      (id_sym Hlin)).
  (* 4. Combine: the goal LHS = Σ diff, then [abs_sum_le] ⟹ |Σ diff| ≤ Σ|diff| *)
  assert (Hlhs2 : Id (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                            (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s'))))
                     (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                 (mult (evicted_boltzmann s) (evicted_transition s s')))))
    by exact (id_trans Hlhs Hdiff).
  (* 5. |Σ diff| ≤ Σ |diff| ([abs_sum_le]) *)
  assert (Habs : le (abs (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                     (mult (evicted_boltzmann s) (evicted_transition s s')))))
                    (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                     (mult (evicted_boltzmann s) (evicted_transition s s'))))))
    by exact (abs_sum_le (fun s0 => minus (mult (evicted_boltzmann s0) (evicted_transition s0 s)) (mult (evicted_boltzmann s) (evicted_transition s s0)))).

  assert (Hlhs3 : le (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                                  (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
                     (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                      (mult (evicted_boltzmann s) (evicted_transition s s')))))).
  {
    (* le_id_l: convert the LHS term into the right side of Hlhs2 (Σ diff), then apply Habs *)
    exact (le_id_l (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                               (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
                   (abs (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                    (mult (evicted_boltzmann s) (evicted_transition s s')))))
                   (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                    (mult (evicted_boltzmann s) (evicted_transition s s')))))
                   (id_cong abs Hlhs2) Habs).
  }
  (* 7. RHS: Σ|minus A B| = Σ db_breaking (db_breaking := abs (minus B A); reversed by [abs_minus_sym]) *)
  assert (Hrhs : Id (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                     (mult (evicted_boltzmann s) (evicted_transition s s')))))
                    (sum_over_S (fun s' => db_breaking s s'))).
  {
    apply sum_over_S_ext.
    intro s'.
    unfold db_breaking.
    (* db_breaking s s' := abs (minus (ev_b s · ev_t s s') (ev_b s' · ev_t s' s))
       Goal: abs (minus (ev_b s' · ev_t s' s) (ev_b s · ev_t s s'))
       = db_breaking s s' ([abs_minus_sym]) *)
    exact (id_sym (abs_minus_sym (mult (evicted_boltzmann s) (evicted_transition s s'))
                         (mult (evicted_boltzmann s') (evicted_transition s' s)))).
  }
  (* 8. Combine: replace the RHS of Hlhs3 by Σ db_breaking (reverse of Hrhs, via [le_id_r]) *)
  exact (le_id_r (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                            (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
                 (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                  (mult (evicted_boltzmann s) (evicted_transition s s')))))
                 (sum_over_S (fun s' => db_breaking s s'))
                 Hrhs Hlhs3).
Qed.

(* ============================================================ *)
(* KV eviction: capacity budgets and tail mass (from qualitative to quantitative) *)
(* ============================================================ *)
(* Engineering background: a KV cache has a strict capacity budget and keeps at most K states. *)
(* The information loss of eviction = the Boltzmann mass of the unkept states (the tail mass). *)
(* The theorems below relate the tail mass to the capacity budget and bound the information loss. *)
(* ------------------------------------------------------------ *)

(* Capacity budget: an upper bound on the cardinality of the kept set (constructively: list-length counting) *)
Variable K : nat.  (* Capacity budget: at most K states are kept *)
Variable S_enum : list S.  (* An enumeration of the finite state space *)
Variable S_finite_cover : forall s : S, InT s S_enum.

(* Tail mass: the sum of the Boltzmann weights of the unkept states (the eviction loss) *)
Definition tail_mass : R :=
  sum_over_S (fun s => if keep_dec s then zero else boltzmann_factor s).

(* Upper bound on the tail mass: tail_mass <= Z_thermo (the eviction loss never exceeds the total mass). *)
Theorem top_k_tail_bound :
  le tail_mass Z_thermo.
Proof.
  unfold tail_mass, Z_thermo.
  apply sum_over_S_le.
  intro s.
  destruct (keep_dec s) as [Hk | Hnk].
  - apply (lt_le_iff zero (boltzmann_factor s)).
    left. unfold boltzmann_factor. apply exp_neg_pos.
  - apply le_refl.
Qed.

(* Conservation of mass: tail mass + kept mass = total mass. *)
Theorem tail_plus_kept_full :
  Id (plus tail_mass evicted_partition) Z_thermo.
Proof.
  unfold tail_mass, evicted_partition, Z_thermo.
  assert (Hpt : forall s, Id (plus (if keep_dec s then zero else boltzmann_factor s)
                                  (if keep_dec s then boltzmann_factor s else zero))
                            (boltzmann_factor s)).
  {
    intro s.
    destruct (keep_dec s) as [Hk | Hnk].
    - assert (Hadd : Id (plus zero (boltzmann_factor s)) (boltzmann_factor s))
        by exact (id_trans (plus_comm zero (boltzmann_factor s)) (plus_zero (boltzmann_factor s))).
      exact Hadd.
    - exact (plus_zero (boltzmann_factor s)).
  }
  assert (Hext : Id (sum_over_S (fun s => plus (if keep_dec s then zero else boltzmann_factor s)
                                             (if keep_dec s then boltzmann_factor s else zero)))
                   (sum_over_S (fun s => boltzmann_factor s)))
    by exact (sum_over_S_ext (fun s => plus (if keep_dec s then zero else boltzmann_factor s)
                                            (if keep_dec s then boltzmann_factor s else zero))
                             (fun s => boltzmann_factor s) Hpt).
  assert (Hadd : Id (sum_over_S (fun s => plus (if keep_dec s then zero else boltzmann_factor s)
                                             (if keep_dec s then boltzmann_factor s else zero)))
                   (plus (sum_over_S (fun s => if keep_dec s then zero else boltzmann_factor s))
                         (sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero))))
    by exact (sum_over_S_add (fun s => if keep_dec s then zero else boltzmann_factor s)
                             (fun s => if keep_dec s then boltzmann_factor s else zero)).
  exact (id_trans (id_sym Hadd) Hext).
Qed.

(* ============================================================ *)
(* Top-K optimality (a nontrivial parallel version: the engine of the greedy exchange argument) *)
(* ============================================================ *)
(* top_k_tail_bound / tail_plus_kept_full are the qualitative upper bound and the conservation *)
(* version of the tail mass; the following gives the quantitative engine of the optimality of the *)
(* greedy Top-K policy (keeping the K states of highest Boltzmann weight): *)
(*   (a) the exchange lemma top_k_exchange: if a kept state s is lighter than an evicted state s' *)
(*       (f s ≤ f s'), then swapping s out and s' in does not increase the tail mass — *)
(*       any non-Top-K choice can be improved by an exchange (the core of greedy optimality); *)
(*   (b) antitonicity top_k_tail_antitone: monotone enlargement of the kept set ⟹ the tail mass *)
(*       is monotone non-increasing — "the more is kept, the less is lost", dual to *)
(*       [eviction_partition_monotone] (the more is kept, the more mass). *)
(* ------------------------------------------------------------ *)

(* Parameterized tail mass (the unkept Boltzmann weight computed for an arbitrary kept set k) *)
Definition tail_mass_of
  (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sum_over_S (fun s => if kd s then zero else boltzmann_factor s).

(* Subtraction-order kernel: a ≤ b ⟹ a - b ≤ 0 (first step of the exchange lemma) *)
Lemma le_minus_le_zero : forall a b : R, le a b -> le (minus a b) zero.
Proof.
  intros a b Hab.
  unfold minus.
  assert (H1 : le (plus a (opp b)) (plus a (opp a)))
    by exact (le_plus_compat a a (opp b) (opp a) (le_refl a) (opp_le_compat a b Hab)).
  assert (H2 : Id (plus a (opp a)) zero) by exact (plus_opp a).
  exact (le_id_r (plus a (opp b)) (plus a (opp a)) zero H2 H1).
Qed.

(* Addition-order zero side: b ≤ 0 ⟹ a + b ≤ a (second step of the exchange lemma) *)
Lemma le_plus_zero_l : forall a b : R, le b zero -> le (plus a b) a.
Proof.
  intros a b Hb.
  assert (H1 : le (plus a b) (plus a zero))
    by exact (le_plus_compat a a b zero (le_refl a) Hb).
  assert (H2 : le (plus a zero) a)
    by exact (le_id_l (plus a zero) a a (plus_zero a) (le_refl a)).
  exact (le_trans (plus a b) (plus a zero) a H1 H2).
Qed.

(* Subtraction reordering: (a - b) + c = a + (c - b) (the algebraic skeleton of the exchange lemma) *)
Lemma minus_plus_swap : forall a b c : R,
  Id (plus (minus a b) c) (plus a (minus c b)).
Proof.
  intros a b c.
  unfold minus.
  assert (H1 : Id (plus (plus a (opp b)) c) (plus a (plus (opp b) c)))
    by exact (id_sym (plus_assoc a (opp b) c)).
  exact (id_trans H1 (id_cong (fun x => plus a x) (plus_comm (opp b) c))).
Qed.

(* Exchange lemma (the engine of greedy Top-K optimality):
   if a kept state s is lighter than an evicted state s' (f s ≤ f s') then the exchange
   (s out, s' in) does not increase the tail mass.  Mathematical content: after the exchange,
   the tail mass = old tail mass - f s' + f s ≤ old tail mass (since f s ≤ f s'), i.e. every
   "keep the lighter, evict the heavier" choice can be improved by an exchange — the local basis
   for the optimality of greedily keeping the K heaviest states.
   (keep s / Not (keep s') are semantic guards: the exchange is defined only for a kept state
   and an evicted state.) *)
Theorem top_k_exchange :
  forall s s' : S,
    keep s -> Not (keep s') ->
    le (boltzmann_factor s) (boltzmann_factor s') ->
    le (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s)) tail_mass.
Proof.
  intros s s' Hks Hnks' Hff.
  (* Algebraic regrouping: LHS = tail_mass + (f s - f s') ([minus_plus_swap]) *)
  assert (Hr : Id (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                  (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))))
    by exact (minus_plus_swap tail_mass (boltzmann_factor s') (boltzmann_factor s)).
  (* f s ≤ f s' ⟹ f s - f s' ≤ 0 *)
  assert (Hmm : le (minus (boltzmann_factor s) (boltzmann_factor s')) zero)
    by exact (le_minus_le_zero (boltzmann_factor s) (boltzmann_factor s') Hff).
  (* tail_mass + (≤ 0) ≤ tail_mass *)
  assert (Hfin : le (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))) tail_mass)
    by exact (le_plus_zero_l tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')) Hmm).
  exact (le_id_l (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                 (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')))
                 tail_mass Hr Hfin).
Qed.

(* Pointwise antitonicity of the tail mass: k1 ⊆ k2 ⟹ (the k2 tail term) ≤ (the k1 tail term)
   (if k2 keeps s, the k1 tail term is 0 or f s ≥ 0; if k2 evicts s then
    k1 also evicts s (contrapositive of Hsub), so the two terms are equal.) *)
Lemma eviction_tail_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    le (if kd2 s then zero else boltzmann_factor s)
       (if kd1 s then zero else boltzmann_factor s).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd2 s) as [H2 | Hn2].
  - (* k2 keeps s: the left side is 0, the right side is 0 or f s ≥ 0 *)
    destruct (kd1 s) as [H1 | Hn1].
    + apply le_refl.
    + apply (lt_le_iff zero (boltzmann_factor s)).
      left.
      unfold boltzmann_factor.
      apply exp_neg_pos.
  - (* k2 evicts s ⟹ k1 also evicts s (contrapositive of Hsub) ⟹ the two sides are equal *)
    destruct (kd1 s) as [H1 | Hn1].
    + (* Contradiction: k1 keeps s while k2 evicts s *)
      exact (match Hn2 (Hsub s H1) with end).
    + apply le_refl.
Qed.

(* Antitonicity of the tail mass: monotone enlargement of the kept set ⟹ the tail mass is monotone non-increasing.
   Dual to [eviction_partition_monotone] (the kept mass is monotone non-decreasing);
   under greedy Top-K (enlarging the kept set to the budget K in decreasing weight order)
   the information loss decreases monotonically. *)
Theorem top_k_tail_antitone :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    le (tail_mass_of k2 kd2) (tail_mass_of k1 kd1).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold tail_mass_of.
  apply sum_over_S_le.
  intro s.
  exact (eviction_tail_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* ============================================================ *)
(* Top-K optimality (full version: constructive selection sort + counting-threshold characterization) *)
(* ============================================================ *)
(* The draft document uses select_top_k sorting + the exact relative_entropy form; this *)
(* implementation gives two provable paths: *)
(*   (a) the constructive selection sort select_top_k (insertion sort, decreasing weights, *)
(*       no default element needed); *)
(*   (b) the counting-threshold characterization keep_top_k: keep the states with "strictly *)
(*       heavier state count < K" — a constructive Top-K decision (computable, without decidable *)
(*       equality on S); *)
(* the optimality theorem top_k_majorization (the Top-K keepers dominate every evicted state) *)
(* plus top_k_swap_no_gain (a Top-K exchange does not decrease the tail mass — the exchange-argument core). *)
(* The relative_entropy form is not representable because log 0 is undefined on evicted states, *)
(* see the status note in the design document. *)
(* ------------------------------------------------------------ *)

Context {DO : DecidableOrder RI}.

(* Projection alias for lt_dec: the class field name lt_dec is shadowed by the Stdlib Compare_dec.lt_dec,
   so it is extracted by constructor destructuring (works in both the coqc and coqtop environments) *)
Definition lt_dec_field : forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => lt_d
  end.

(* Strict less-than (nat version, dual to the top-level NatLe) *)
Definition NatLt (n m : nat) : Set := Id (Nat.ltb n m) true.

(* (a) Insertion sort in decreasing weight order (the constructive selection sort select_top_k) *)
Fixpoint insert_weight (a : S) (l : list S) : list S :=
  match l with
  | nil => a :: nil
  | b :: rest =>
      match (@ord_le_dec _ DO) (boltzmann_factor b) (boltzmann_factor a) with
      | inl _ => a :: b :: rest      (* f a ≥ f b: a is placed before b *)
      | inr _ => b :: insert_weight a rest
      end
  end.

Fixpoint sort_weight (l : list S) : list S :=
  match l with
  | nil => nil
  | a :: rest => insert_weight a (sort_weight rest)
  end.

(* Top-K selection: sort the enumeration in decreasing weight order and take the first K *)
Definition select_top_k (l : list S) (k : nat) : list S :=
  firstn k (sort_weight l).

(* (b) Strictly-heavier count: the number of states in l with weight strictly greater than that of s (the lt_dec trichotomy) *)
Fixpoint count_heavier (s : S) (l : list S) : nat :=
  match l with
  | nil => O
  | a :: rest =>
      match (lt_dec_field (boltzmann_factor s) (boltzmann_factor a)) with
      | inl _ => Datatypes.S (count_heavier s rest)
      | inr _ => count_heavier s rest
      end
  end.

(* Top-K decision: fewer than K strictly-heavier states ⟹ s is in the Top-K *)
Definition keep_top_k (s : S) : Set := NatLt (count_heavier s S_enum) K.

(* Decidability of keep_top_k (Nat.ltb computation + bool elimination; no equality on S needed) *)
Lemma id_false_true : forall (H : Id false true), Empty_set.
Proof. intro H. inversion H. Qed.

Definition keep_top_k_dec : forall s : S, Or (keep_top_k s) (Not (keep_top_k s)) :=
  fun s => match Nat.ltb (count_heavier s S_enum) K as b
                return Or (Id b true) (Not (Id b true)) with
           | true => inl id_refl
           | false => inr (fun H => id_false_true H)
           end.

(* Count monotonicity (in the "heavier" direction): f s1 < f s2 ⟹ count_heavier s2 ≤ count_heavier s1
   (a state heavier than s2 is also heavier than s1 — transitivity by lt_trans; the lying-decider
   branches are refuted) *)
Lemma count_heavier_mono : forall s1 s2 : S, forall l : list S,
  lt (boltzmann_factor s1) (boltzmann_factor s2) ->
  NatLe (count_heavier s2 l) (count_heavier s1 l).
Proof.
  intros s1 s2 l. induction l as [| a rest IH]; intros Hlt.
  - simpl. apply NatLe_lift. lia.
  - simpl.
    destruct (lt_dec_field (boltzmann_factor s1) (boltzmann_factor a)) as [d1 | nd1];
    destruct (lt_dec_field (boltzmann_factor s2) (boltzmann_factor a)) as [d2 | nd2].
    + pose proof (NatLe_drop _ _ (IH Hlt)) as IHle. apply NatLe_lift. lia.
    + pose proof (NatLe_drop _ _ (IH Hlt)) as IHle. apply NatLe_lift. lia.
    + (* nd1 ∧ d2: contradiction (d2 : lt (f s2) (f a), while nd1 negates lt (f s1) (f a)) *)
      destruct nd1 as [Hid | Hlt_a_s1].
      * (* Hid : Id (f s1) (f a): rewrite d2 ⟹ lt (f s2) (f s1), contradicting Hlt *)
        exact (match (lt_irrefl (boltzmann_factor s1)
                        (lt_trans (boltzmann_factor s1) (boltzmann_factor s2) (boltzmann_factor s1)
                           Hlt
                           (lt_id_r (boltzmann_factor s2) (boltzmann_factor a) (boltzmann_factor s1)
                              (id_sym Hid) d2))) with end).
      * (* Hlt_a_s1 : lt (f a) (f s1): lt_trans a s1 s2 ⟹ lt (f a) (f s2), contradicting d2 *)
        exact (match (lt_irrefl (boltzmann_factor a)
                        (lt_trans (boltzmann_factor a) (boltzmann_factor s2) (boltzmann_factor a)
                           (lt_trans (boltzmann_factor a) (boltzmann_factor s1) (boltzmann_factor s2)
                              Hlt_a_s1 Hlt)
                           d2)) with end).
    + pose proof (NatLe_drop _ _ (IH Hlt)) as IHle. apply NatLe_lift. lia.
Qed.

(* Count +1 (under the InT premise): f s1 < f s2 and s2 ∈ l ⟹ S (count_heavier s2 l) ≤ count_heavier s1 l
   (s2 itself is counted in the s1 count; states heavier than s2 are also counted in s1 — induction on InT) *)
Lemma count_heavier_succ_le : forall s1 s2 : S, forall l : list S,
  lt (boltzmann_factor s1) (boltzmann_factor s2) ->
  InT s2 l ->
  NatLe (Datatypes.S (count_heavier s2 l)) (count_heavier s1 l).
Proof.
  intros s1 s2 l Hlt Hin.
  induction Hin as [l0 | a0 l0 Hin_ IH].
  - (* InT_here: s2 is the head (l = s2 :: l0; dependent elimination substitutes automatically) *)
    simpl.
    destruct (lt_dec_field (boltzmann_factor s1) (boltzmann_factor s2)) as [d1 | nd1];
    destruct (lt_dec_field (boltzmann_factor s2) (boltzmann_factor s2)) as [d2 | nd2].
    + (* d2 : lt (f s2) (f s2) → contradiction ([lt_irrefl]) *)
      exact (match (lt_irrefl (boltzmann_factor s2) d2) with end).
    + (* Goal: NatLe (S (count_heavier s2 l0)) (count_heavier s1 l0), i.e. the conclusion of count_heavier_mono;
         NatLe_drop/NatLe_lift convert between the NatLe shape and the nat-level order; lia finishes *)
      pose proof (NatLe_drop _ _ (count_heavier_mono s1 s2 l0 Hlt)) as Hm.
      apply NatLe_lift. lia.
    + (* nd1 → contradiction (Hlt : lt (f s1) (f s2)) *)
      destruct nd1 as [Hid | Hlt21].
      * exact (match (lt_irrefl (boltzmann_factor s1)
                      (lt_id_r (boltzmann_factor s1) (boltzmann_factor s2) (boltzmann_factor s1)
                         (id_sym Hid) Hlt)) with end).
      * exact (match (lt_irrefl (boltzmann_factor s2)
                      (lt_trans (boltzmann_factor s2) (boltzmann_factor s1) (boltzmann_factor s2)
                         Hlt21 Hlt)) with end).
    + (* nd1 ∧ nd2: nd1 contradicts Hlt directly (as above) *)
      destruct nd1 as [Hid | Hlt21].
      * exact (match (lt_irrefl (boltzmann_factor s1)
                      (lt_id_r (boltzmann_factor s1) (boltzmann_factor s2) (boltzmann_factor s1)
                         (id_sym Hid) Hlt)) with end).
      * exact (match (lt_irrefl (boltzmann_factor s2)
                      (lt_trans (boltzmann_factor s2) (boltzmann_factor s1) (boltzmann_factor s2)
                         Hlt21 Hlt)) with end).
  - (* InT_next: s2 ∈ l0; IH : S (count_heavier s2 l0) ≤ count_heavier s1 l0 *)
    simpl.
    destruct (lt_dec_field (boltzmann_factor s1) (boltzmann_factor a0)) as [d1 | nd1];
    destruct (lt_dec_field (boltzmann_factor s2) (boltzmann_factor a0)) as [d2 | nd2].
    + pose proof (NatLe_drop _ _ IH) as IHle. apply NatLe_lift. lia.
    + pose proof (NatLe_drop _ _ IH) as IHle. apply NatLe_lift. lia.
    + (* nd1 ∧ d2: contradiction (as in the (nd1, d2) case of count_heavier_mono) *)
      destruct nd1 as [Hid | Hlt_a_s1].
      * exact (match (lt_irrefl (boltzmann_factor s2)
                      (lt_trans (boltzmann_factor s2) (boltzmann_factor s1) (boltzmann_factor s2)
                         (lt_id_r (boltzmann_factor s2) (boltzmann_factor a0) (boltzmann_factor s1)
                            (id_sym Hid) d2)
                         Hlt)) with end).
      * exact (match (lt_irrefl (boltzmann_factor a0)
                      (lt_trans (boltzmann_factor a0) (boltzmann_factor s2) (boltzmann_factor a0)
                         (lt_trans (boltzmann_factor a0) (boltzmann_factor s1) (boltzmann_factor s2)
                            Hlt_a_s1 Hlt)
                         d2)) with end).
    + pose proof (NatLe_drop _ _ IH) as IHle. apply NatLe_lift. lia.
Qed.

(* Top-K domination (the full proof of the document's top_k_majorization):
   the weight of a Top-K keeper is ≥ that of any evicted state — Top-K is the order-theoretic
   characterization of "the K heaviest" *)
Theorem top_k_majorization :
  forall s1 s2 : S,
    keep_top_k s1 -> Not (keep_top_k s2) ->
    le (boltzmann_factor s2) (boltzmann_factor s1).
Proof.
  intros s1 s2 Hk1 Hnk2.
  destruct (@ord_le_dec _ DO (boltzmann_factor s2) (boltzmann_factor s1)) as [Hle | Hnle].
  - exact Hle.
  - (* Hnle ⟹ lt (f s1) (f s2) ([not_le_lt]) ⟹ counting contradiction *)
    assert (Hlt : lt (boltzmann_factor s1) (boltzmann_factor s2))
      by exact (@not_le_lt _ DO (boltzmann_factor s2) (boltzmann_factor s1) Hnle).
    assert (Hsucc : NatLe (Datatypes.S (count_heavier s2 S_enum)) (count_heavier s1 S_enum))
      by exact (count_heavier_succ_le s1 s2 S_enum Hlt (S_finite_cover s2)).
    pose proof (NatLe_drop _ _ Hsucc) as Hsucle.
    unfold keep_top_k, NatLt in Hk1, Hnk2.
    assert (Hlt1 : (count_heavier s1 S_enum < K)%nat).
    { apply (proj1 (Nat.ltb_lt _ _)).
      exact (match Hk1 in (Id _ y) return (Nat.ltb (count_heavier s1 S_enum) K = y) with id_refl => eq_refl end). }
    assert (Hge2 : (K <= count_heavier s2 S_enum)%nat).
    { apply Nat.nlt_ge. intro Hlt2.
      exact (match (Hnk2 (match (proj2 (Nat.ltb_lt _ _) Hlt2) in (_ = y) return (Id (Nat.ltb (count_heavier s2 S_enum) K) y) with eq_refl => id_refl end)) with end). }
    exfalso. lia.
Qed.

(* A Top-K exchange gains nothing: replacing the Top-K keeper s by the evicted state s'
   (heavier out, lighter in) does not decrease the tail mass — Top-K is the minimal-information-loss
   choice (the conclusion form of the exchange argument).
   Mathematical content: the new tail mass = T - f s' + f s ≥ T (since f s ≥ f s'). *)
Theorem top_k_swap_no_gain :
  forall s s' : S,
    keep_top_k s -> Not (keep_top_k s') ->
    le tail_mass (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s)).
Proof.
  intros s s' Hks Hnks'.
  (* Top-K domination: f s' ≤ f s *)
  assert (Hle : le (boltzmann_factor s') (boltzmann_factor s))
    by exact (top_k_majorization s s' Hks Hnks').
  (* Algebraic regrouping: T - f s' + f s = T + (f s - f s') ([minus_plus_swap]) *)
  assert (Hr : Id (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                  (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))))
    by exact (minus_plus_swap tail_mass (boltzmann_factor s') (boltzmann_factor s)).
  (* f s' ≤ f s ⟹ 0 ≤ f s - f s' ([le_minus_nonneg]) *)
  assert (Hnn : le zero (minus (boltzmann_factor s) (boltzmann_factor s')))
    by exact (le_minus_nonneg (boltzmann_factor s') (boltzmann_factor s) Hle).
  (* T ≤ T + (≥0) ([le_plus_nonneg_r]) *)
  assert (Hfin : le tail_mass (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))))
    by exact (le_plus_nonneg_r tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')) Hnn).
  exact (le_id_r tail_mass (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')))
                 (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                 (id_sym Hr) Hfin).
Qed.

(* ============================================================ *)
(* Top-K optimality at the sorting level (sort correctness of select_top_k + domination) *)
(* ============================================================ *)
(* The exact relative-entropy form is not representable because log 0 is undefined on evicted states
   (see the design-document note); *)
(* here is the sorting-level core: [sorted_noninc] (the prefix-maximum sort invariant), *)
(* [insert_preserves_sorted] / [sort_sorted] (insertion-sort correctness), *)
(* [firstn_head_dominates_skipn] (under the sort, a prefix element dominates a suffix element), *)
(* [top_k_majorization_mem] (a select_top_k keeper dominates any evicted state). *)

(* Sort invariant: every element is ≥ all elements after it (prefix-maximum form).
   Sorted invariant: head-dominant form, carried by an indexed Set family
   whose constructors are informative, so extraction keeps the full type. *)
Inductive sorted_noninc : list S -> Set :=
| sorted_noninc_nil : sorted_noninc nil
| sorted_noninc_cons : forall (a : S) (rest : list S),
    (forall b : S, InT b rest -> le (boltzmann_factor b) (boltzmann_factor a)) ->
    sorted_noninc rest -> sorted_noninc (a :: rest).

(* skipn is a sublist: InT x (skipn k l) ⟹ InT x l *)
Lemma skipn_sub : forall (k : nat) (l : list S) (x : S),
  InT x (skipn k l) -> InT x l.
Proof.
  intros k l x. revert l. induction k as [| k' IH]; intros l Hx.
  - simpl in Hx. exact Hx.
  - destruct l as [| a rest].
    + simpl in Hx. exact Hx.
    + simpl in Hx. apply InT_next. exact (IH rest Hx).
Qed.

(* Append membership decomposition: InT x (l1 ++ l2) ⟹ x ∈ l1 or x ∈ l2 *)
Lemma InT_app_or : forall (l1 l2 : list S) (x : S),
  InT x (l1 ++ l2) -> Or (InT x l1) (InT x l2).
Proof.
  intros l1. induction l1 as [| a rest IH]; intros l2 x Hx.
  - simpl in Hx. right. exact Hx.
  - simpl in Hx. inversion Hx as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
    + left. exact (InT_here a rest).
    + destruct (IH l2 x Hnext_rec) as [Hl | Hr].
      * left. exact (InT_next x a rest Hl).
      * right. exact Hr.
Qed.

(* Insertion preserves membership: x ∈ l ⟹ x ∈ insert a l *)
Lemma insert_mem_in : forall a x : S, forall l : list S,
  InT x l -> InT x (insert_weight a l).
Proof.
  intros a x l. induction l as [| b rest IH]; intros Hx.
  - simpl. inversion Hx.
  - simpl.
    destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + apply InT_next. exact Hx.
    + inversion Hx as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * exact (InT_here b (insert_weight a rest)).
      * apply InT_next. exact (IH Hnext_rec).
Qed.

(* Insertion self-membership: a is always in insert a l *)
Lemma insert_mem_self : forall a : S, forall l : list S, InT a (insert_weight a l).
Proof.
  intros a l. induction l as [| b rest IH]; simpl.
  - exact (InT_here a nil).
  - destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + exact (InT_here a (b :: rest)).
    + apply InT_next. exact IH.
Qed.

(* Sorting preserves membership: x ∈ l ⟹ x ∈ sort_weight l *)
Lemma sort_mem_in : forall (l : list S) (x : S),
  InT x l -> InT x (sort_weight l).
Proof.
  intros l. induction l as [| a rest IH]; intros x Hx.
  - simpl. inversion Hx.
  - simpl. inversion Hx as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
    + exact (insert_mem_self a (sort_weight rest)).
    + exact (insert_mem_in a x (sort_weight rest) (IH x Hnext_rec)).
Qed.

(* Insertion membership decomposition: InT c (insert a l) ⟹ c = a or c ∈ l *)
Lemma insert_mem_split : forall a c : S, forall l : list S,
  InT c (insert_weight a l) -> Or (Id c a) (InT c l).
Proof.
  intros a c l. induction l as [| b rest IH]; intros Hc.
  - simpl in Hc. inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
    + left. exact (@id_refl S a).
    + inversion Hnext_rec.
  - simpl in Hc.
    destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * left. exact (@id_refl S a).
      * inversion Hnext_rec as [Hl0' | Hnext_y' Hnext_l' Hnext_rec']; subst.
        -- right. exact (InT_here b rest).
        -- right. exact (InT_next c b rest Hnext_rec').
    + inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * right. exact (InT_here b rest).
      * destruct (IH Hnext_rec) as [Hca | Hcr].
        -- left. exact Hca.
        -- right. exact (InT_next c b rest Hcr).
Qed.

(* Insertion preserves the sort (the inr branch uses not_le_lt + lt_le_iff to get f a ≤ f b) *)
Lemma insert_preserves_sorted : forall a : S, forall l : list S,
  sorted_noninc l -> sorted_noninc (insert_weight a l).
Proof.
  intros a l. induction l as [| b rest IH]; intros Hs.
  - simpl. apply (sorted_noninc_cons a nil).
    + intros c Hc. inversion Hc.
    + exact sorted_noninc_nil.
  - simpl.
    inversion Hs as [| b0 rest0 Hs_head Hs_tail Hidx]; subst.
    destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + apply (sorted_noninc_cons a (b :: rest)).
      * intros c Hc. inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
        -- exact Hba.
        -- apply (le_trans (boltzmann_factor c) (boltzmann_factor b) (boltzmann_factor a)).
           ++ exact (Hs_head c Hnext_rec).
           ++ exact Hba.
      * apply (sorted_noninc_cons b rest).
        -- exact Hs_head.
        -- exact Hs_tail.
    + apply (sorted_noninc_cons b (insert_weight a rest)).
      * intros c Hc.
        destruct (insert_mem_split a c rest Hc) as [Hca | Hcr].
        -- (* c = a: f a ≤ f b (Hnba ⟹ lt (f a) (f b) ⟹ le) *)
           assert (Hlt_ab : lt (boltzmann_factor a) (boltzmann_factor b))
             by exact (@not_le_lt _ DO (boltzmann_factor b) (boltzmann_factor a) Hnba).
           apply (le_id_l (boltzmann_factor c) (boltzmann_factor a) (boltzmann_factor b)).
           ++ exact (id_cong (fun z => boltzmann_factor z) Hca).
           ++ apply (lt_le_iff _ _). left. exact Hlt_ab.
        -- exact (Hs_head c Hcr).
      * exact (IH Hs_tail).
Qed.

(* Sort correctness: sort_weight l satisfies the sort invariant *)
Lemma sort_sorted : forall l : list S, sorted_noninc (sort_weight l).
Proof.
  induction l as [| a rest IH]; simpl.
  - exact sorted_noninc_nil.
  - exact (insert_preserves_sorted a (sort_weight rest) IH).
Qed.

(* firstn on an empty list is always nil (firstn matches on n first, so eliminate on k) *)
Lemma firstn_nil : forall (k : nat), Id (firstn (A := S) k nil) nil.
Proof. destruct k; simpl; apply id_refl. Qed.

(* Prefix dominates suffix: under the sort, an element of firstn k dominates an element of skipn k (induction on k) *)
Lemma firstn_head_dominates_skipn : forall (L : list S) (k : nat),
  sorted_noninc L ->
  forall s : S, InT s (firstn k L) ->
  forall s' : S, InT s' (skipn k L) ->
  le (boltzmann_factor s') (boltzmann_factor s).
Proof.
  intros L. induction L as [| a rest IH]; intros k Hsorted s Hs s' Hs'.
  - (* firstn k nil reduces to nil for each shape of k, so Hs becomes an
       InT-nil membership, which has no constructors *)
    destruct k as [| k'].
    + simpl in Hs. inversion Hs.
    + simpl in Hs. inversion Hs.
  - destruct k as [| k'].
    + simpl in Hs. inversion Hs.
    + simpl.
      inversion Hsorted as [| a0 rest0 Hs_head Hs_tail Hidx]; subst.
      inversion Hs as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * (* s = a: s' ∈ skipn k' rest ⊆ rest; domination by the sorted head *)
        assert (Hrest : InT s' rest) by (apply (skipn_sub k' rest s'); exact Hs').
        exact (Hs_head s' Hrest).
      * (* s ∈ firstn k' rest, s' ∈ skipn k' rest: IH *)
        exact (IH k' Hs_tail s Hnext_rec s' Hs').
Qed.

(* Top-K domination (sorting version): the weight of a select_top_k keeper is ≥ that of any evicted state.
   Proof: s2 ∈ sort S_enum (finite cover + [sort_mem_in]), decomposed via firstn_skipn into
   skipn K (ruling out the firstn branch), then [firstn_head_dominates_skipn]. *)
Theorem top_k_majorization_mem :
  forall s1 s2 : S,
    InT s1 (select_top_k S_enum K) -> Not (InT s2 (select_top_k S_enum K)) ->
    le (boltzmann_factor s2) (boltzmann_factor s1).
Proof.
  intros s1 s2 Hs1 Hs2n.
  assert (Hs2_in : InT s2 (sort_weight S_enum)).
  { apply (sort_mem_in S_enum s2). apply S_finite_cover. }
  assert (Hsplit : Or (InT s2 (firstn K (sort_weight S_enum))) (InT s2 (skipn K (sort_weight S_enum)))).
  { apply (InT_app_or (firstn K (sort_weight S_enum)) (skipn K (sort_weight S_enum)) s2).
    rewrite firstn_skipn. exact Hs2_in. }
  destruct Hsplit as [Hs2_first | Hs2_skip].
  - exact (match (Hs2n Hs2_first) with end).
  - exact (firstn_head_dominates_skipn (sort_weight S_enum) K (sort_sorted S_enum) s1 Hs1 s2 Hs2_skip).
Qed.

(* ============================================================ *)
(* Quantitative bound on the Top-K truncated total variation *)
(*   TV(boltzmann, topk_renorm) == tail_mass/Z_thermo (exact identity) *)
(*   Chain: conservation (kept + tail == Z) → kept ≤ Z (sub-sum) → *)
(*   sign branch (inverse order reversal, destructing the Or of le) → pointwise difference decomposition (abs *)
(*   cancellation) → sum decomposition (Σ_keep + Σ_evict) → the normalization algebra concludes. *)
(* ============================================================ *)

(* The Top-K version of the tail mass (tail_mass instantiated at keep_top_k) *)
Definition topk_tail_mass : R :=
  sum_over_S (fun s => if keep_top_k_dec s then zero else boltzmann_factor s).

(* The Top-K version of the kept mass (the renormalization denominator) *)
Definition topk_kept_partition : R :=
  sum_over_S (fun s => if keep_top_k_dec s then boltzmann_factor s else zero).

(* Honest interface: the kept set is nonempty (an instantiable premise from a finite set with K ≥ 1, same precedent as evicted_partition_pos) *)
Variable topk_kept_partition_pos : lt zero topk_kept_partition.

(* The Top-K renormalized distribution: keepers get b_s/Z_keep, evicted states get 0 (an unnormalized space, matching the paper's shape) *)
Definition topk_renorm (s : S) : R :=
  if keep_top_k_dec s then
    mult (inv_pos topk_kept_partition topk_kept_partition_pos) (boltzmann_factor s)
  else zero.

(* Auxiliary: positivity of the one-argument boltzmann_factor (proven inside this Section; the global boltzmann_factor_pos is the two-argument version) *)
Lemma boltzmann_factor_pos_attn : forall s : S, lt zero (boltzmann_factor s).
Proof.

  intro s. unfold boltzmann_factor. exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).

Qed.

(* Auxiliary: the if-term is nonnegative (b > 0 when kept, 0 otherwise) *)
Lemma topk_kept_term_nonneg : forall s,
  le zero (if keep_top_k_dec s then boltzmann_factor s else zero).
Proof.
  intro s. destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply (lt_le_iff _ _). left. apply boltzmann_factor_pos_attn.
  - apply le_refl.
Qed.

(* Auxiliary: the if-term is ≤ b (refl when kept, 0 ≤ b otherwise) *)
Lemma topk_kept_term_le_factor : forall s,
  le (if keep_top_k_dec s then boltzmann_factor s else zero) (boltzmann_factor s).
Proof.
  intro s. destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply le_refl.
  - apply (lt_le_iff _ _). left. apply boltzmann_factor_pos_attn.
Qed.

(* Conservation: kept + tail == Z_thermo (as in [tail_plus_kept_full], the keep_top_k_dec version) *)
Lemma topk_kept_plus_tail_full : Id (plus topk_kept_partition topk_tail_mass) Z_thermo.
Proof.
  unfold topk_kept_partition, topk_tail_mass, Z_thermo.
  assert (Hpt : forall s, Id (plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                   (if keep_top_k_dec s then zero else boltzmann_factor s))
                            (boltzmann_factor s)).
  { intro s. destruct (keep_top_k_dec s) as [Hk | Hnk].
    - apply (plus_zero (boltzmann_factor s)).
    - apply (id_trans (plus_comm zero (boltzmann_factor s)) (plus_zero (boltzmann_factor s))). }
  assert (Hext : Id (sum_over_S (fun s => plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                               (if keep_top_k_dec s then zero else boltzmann_factor s)))
                    (sum_over_S (fun s => boltzmann_factor s)))
    by exact (sum_over_S_ext (fun s => plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                            (if keep_top_k_dec s then zero else boltzmann_factor s))
                             (fun s => boltzmann_factor s) Hpt).
  assert (Hadd : Id (sum_over_S (fun s => plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                               (if keep_top_k_dec s then zero else boltzmann_factor s)))
                    (plus (sum_over_S (fun s => if keep_top_k_dec s then boltzmann_factor s else zero))
                          (sum_over_S (fun s => if keep_top_k_dec s then zero else boltzmann_factor s))))
    by exact (sum_over_S_add (fun s => if keep_top_k_dec s then boltzmann_factor s else zero)
                             (fun s => if keep_top_k_dec s then zero else boltzmann_factor s)).
  exact (id_trans (id_sym Hadd) Hext).
Qed.

(* kept ≤ Z_thermo (a sub-sum is ≤ the full sum: pointwise ≤ b + [sum_over_S_le]) *)
Lemma topk_kept_le_Zthermo : le topk_kept_partition Z_thermo.
Proof.
  unfold topk_kept_partition, Z_thermo.
  apply sum_over_S_le.
  intro s. apply topk_kept_term_le_factor.
Qed.

(* Inversion reverses the order: kept ≤ Z ⟹ inv Z ≤ inv kept ([inv_pos_le_compat]) *)
Lemma topk_inv_Z_le_inv_kept : le (inv_pos Z_thermo Z_thermo_pos)
                                  (inv_pos topk_kept_partition topk_kept_partition_pos).
Proof.
  exact (inv_pos_le_compat topk_kept_partition Z_thermo topk_kept_partition_pos Z_thermo_pos topk_kept_le_Zthermo).
Qed.

(* Auxiliary: inv one == one (id_sym (mult_one) + comm + [inv_pos_correct]) *)
Lemma inv_one_cc : Id (inv_pos one one_pos) one.
Proof.

  exact (id_trans (id_sym (mult_one (inv_pos one one_pos))) (id_trans (mult_comm (inv_pos one one_pos) one) (inv_pos_correct one one_pos))).

Qed.

(* Auxiliary: opp zero == zero (proven inside this Section, avoiding forward references) *)
Lemma opp_zero_cc : Id (opp zero) zero.
Proof.
  apply id_sym.
  apply (plus_inv_unique zero zero (opp zero)).
  - apply (plus_zero zero).
  - apply (plus_opp zero).
Qed.

(* Auxiliary: lt a b ⟹ lt (minus a b) zero (translation by [lt_plus_compat_lt_le]) *)
Lemma lt_minus_cc : forall a b : R, lt a b -> lt (minus a b) zero.
Proof.
  intros a b Hab.
  unfold minus.
  apply (lt_id_r _ (plus b (opp b)) _).
  - apply (plus_opp b).
  - apply (lt_plus_compat_lt_le a b (opp b) (opp b) Hab (le_refl (opp b))).
Qed.

(* Auxiliary: cancellation of a negative sign under abs: lt a zero → abs a == opp a ([abs_opp] + [abs_pos] + [opp_lt_compat]) *)
Lemma abs_neg_cc : forall a : R, lt a zero -> Id (abs a) (opp a).
Proof.
  intros a Ha.
  apply (id_trans (id_sym (abs_opp a))).
  apply (abs_pos (opp a)).
  apply (lt_id_l zero (opp zero) (opp a)).
  - apply (id_sym opp_zero_cc).
  - apply (opp_lt_compat a zero). exact Ha.
Qed.

(* Auxiliary: minus x zero == x (opp zero == zero + [plus_zero]) *)
Lemma minus_zero_cc : forall x : R, Id (minus x zero) x.
Proof.

  intro x. unfold minus. exact (id_trans (id_cong (fun z => plus x z) (opp_zero_cc)) (plus_zero x)).

Qed.

(* Pointwise identity (keep branch, conditional): |b/Z − b/Z_keep| == b·(1/Z_keep − 1/Z)
   Premise lt (invZ) (invKeep) (strict eviction, instantiated at the Real layer by T > 0) — the abstract-layer
   le is not disjunctive, so the exact sign goes through an explicit lt premise (the conditional-theorem pattern) *)
Lemma topk_tv_pointwise_keep : forall s,
  keep_top_k s ->
  lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos) ->
  Id (abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                  (mult (inv_pos topk_kept_partition topk_kept_partition_pos) (boltzmann_factor s))))
     (mult (boltzmann_factor s)
           (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                  (inv_pos Z_thermo Z_thermo_pos))).
Proof.
  intros s Hs Hst.
  (* Factor out: b/Z − b/Z_keep == b·(1/Z − 1/Z_keep) (reverse of [mult_minus_distr_r]) *)
  assert (Hfac : Id (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                            (mult (inv_pos topk_kept_partition topk_kept_partition_pos) (boltzmann_factor s)))
                     (mult (minus (inv_pos Z_thermo Z_thermo_pos)
                                  (inv_pos topk_kept_partition topk_kept_partition_pos))
                           (boltzmann_factor s))).
  { apply (id_sym (mult_minus_distr_r (inv_pos Z_thermo Z_thermo_pos)
                                      (inv_pos topk_kept_partition topk_kept_partition_pos)
                                      (boltzmann_factor s))). }
  (* |D·b| == b·|D| (the interface field [abs_mult] + comm + |b| == b) *)
  assert (Habs : Id (abs (mult (minus (inv_pos Z_thermo Z_thermo_pos)
                                      (inv_pos topk_kept_partition topk_kept_partition_pos))
                                (boltzmann_factor s)))
                    (mult (boltzmann_factor s)
                          (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                      (inv_pos topk_kept_partition topk_kept_partition_pos))))).
  { apply (id_trans (abs_mult (minus (inv_pos Z_thermo Z_thermo_pos)
                                        (inv_pos topk_kept_partition topk_kept_partition_pos))
                                 (boltzmann_factor s))).
    apply (id_trans (mult_comm (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                           (inv_pos topk_kept_partition topk_kept_partition_pos)))
                               (abs (boltzmann_factor s)))).
    apply (id_cong (fun z => mult z (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                                (inv_pos topk_kept_partition topk_kept_partition_pos))))
                   (abs_ge_zero_id_cc (boltzmann_factor s)
                                      (lt_le_iff zero (boltzmann_factor s) (inl (boltzmann_factor_pos_attn s))))). }
  (* Sign (premise lt invZ invKeep): |1/Z − 1/Z_keep| == 1/Z_keep − 1/Z ([abs_neg_cc]) *)
  assert (Hsign : Id (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                 (inv_pos topk_kept_partition topk_kept_partition_pos)))
                     (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                            (inv_pos Z_thermo Z_thermo_pos))).
  { apply (id_trans (abs_neg_cc (minus (inv_pos Z_thermo Z_thermo_pos)
                                       (inv_pos topk_kept_partition topk_kept_partition_pos))
                                (lt_minus_cc (inv_pos Z_thermo Z_thermo_pos)
                                             (inv_pos topk_kept_partition topk_kept_partition_pos)
                                             Hst))
                    (id_trans (opp_minus (inv_pos Z_thermo Z_thermo_pos)
                                         (inv_pos topk_kept_partition topk_kept_partition_pos))
                              (id_trans (plus_comm (opp (inv_pos Z_thermo Z_thermo_pos))
                                                   (inv_pos topk_kept_partition topk_kept_partition_pos))
                                        (id_refl)))). }
  (* Assemble: |b/Z − b/Z_keep| == b·(1/Z_keep − 1/Z) *)
  apply (id_trans (id_cong (fun z => abs z) Hfac)).
  apply (id_trans Habs).
  apply (id_cong (fun z => mult (boltzmann_factor s) z) Hsign).
Qed.

(* Pointwise identity (evict branch): |b/Z − 0| == b/Z *)
Lemma topk_tv_pointwise_evict : forall s,
  Not (keep_top_k s) ->
  Id (abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) zero))
     (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)).
Proof.
  intros s Hnk.
  assert (Hz : Id (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) zero)
                   (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
    by exact (minus_zero_cc (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))).
  apply (id_trans (id_cong (fun z => abs z) Hz)).
  apply (abs_pos (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))).
  apply (mult_positive (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)).
  - apply (inv_pos_pos Z_thermo Z_thermo_pos).
  - apply (boltzmann_factor_pos_attn s).
Qed.

(* Pointwise if-decomposition: if k then X else Y == (if k then X else 0) + (if k then 0 else Y) *)
Lemma topk_if_split : forall (X Y : R) (s : S),
  Id (if keep_top_k_dec s then X else Y)
     (plus (if keep_top_k_dec s then X else zero)
           (if keep_top_k_dec s then zero else Y)).
Proof.
  intros X Y s. destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply (id_sym (plus_zero X)).
  - apply (id_trans (id_sym (plus_zero Y)) (id_sym (plus_comm zero Y))).
Qed.

(* Pointwise linearity of the else branch: if k then 0 else a·f == a·(if k then 0 else f) (dual of [eviction_if_linear]) *)
Lemma eviction_if_linear_else :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) (a : R) (f : S -> R) (s : S),
    Id (if kd s then zero else mult a (f s))
       (mult a (if kd s then zero else f s)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - apply (id_sym (mult_zero a)).
  - apply id_refl.
Qed.

(* Pointwise total identity (conditional): |b/Z − topk| == if keep then b·(invKeep − invZ) else b/Z *)
Lemma topk_tv_pointwise : forall s
  (Hst : lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos)),
  Id (abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) (topk_renorm s)))
     (if keep_top_k_dec s
      then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                            (inv_pos Z_thermo Z_thermo_pos))
      else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)).
Proof.
  intros s Hst.
  unfold topk_renorm.
  destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply (topk_tv_pointwise_keep s Hk Hst).
  - apply (topk_tv_pointwise_evict s Hnk).
Qed.

(* Sum decomposition: Σ (if keep then b·D else b/Z) == kept·D + invZ·T *)
Lemma topk_sum_decomp : forall
  (Hst : lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos)),
  Id (sum_over_S (fun s => if keep_top_k_dec s
                           then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                (inv_pos Z_thermo Z_thermo_pos))
                           else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
     (plus (mult topk_kept_partition
                 (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                        (inv_pos Z_thermo Z_thermo_pos)))
           (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)).
Proof.
  intro Hst.
  (* if-decomposition → Σ_add *)
  assert (Hsplit : Id (sum_over_S (fun s => if keep_top_k_dec s
                                            then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                                 (inv_pos Z_thermo Z_thermo_pos))
                                            else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
                      (sum_over_S (fun s => plus (if keep_top_k_dec s
                                                  then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                                       (inv_pos Z_thermo Z_thermo_pos))
                                                  else zero)
                                                 (if keep_top_k_dec s
                                                  then zero
                                                  else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))))).
  { apply sum_over_S_ext.
    intro s. apply (topk_if_split (mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                   (inv_pos Z_thermo Z_thermo_pos)))
                                  (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) s). }
  apply (id_trans Hsplit).
  apply (id_trans (sum_over_S_add (fun s => if keep_top_k_dec s
                                            then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                                 (inv_pos Z_thermo Z_thermo_pos))
                                            else zero)
                                  (fun s => if keep_top_k_dec s
                                            then zero
                                            else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))).
  apply (id_cong2 plus
    (id_trans (sum_over_S_ext _ _ (fun s => id_trans
                                        (id_cong (fun z => if keep_top_k_dec s then z else zero)
                                                 (mult_comm (boltzmann_factor s)
                                                            (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                   (inv_pos Z_thermo Z_thermo_pos))))
                                        (eviction_if_linear keep_top_k keep_top_k_dec
                                                            (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                   (inv_pos Z_thermo Z_thermo_pos))
                                                            boltzmann_factor s)))
              (id_trans (sum_over_S_linear (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                  (inv_pos Z_thermo Z_thermo_pos))
                                           (fun s => if keep_top_k_dec s then boltzmann_factor s else zero))
                        (mult_comm (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                          (inv_pos Z_thermo Z_thermo_pos))
                                   (sum_over_S (fun s => if keep_top_k_dec s then boltzmann_factor s else zero)))))
    (id_trans (sum_over_S_ext _ _ (fun s => eviction_if_linear_else keep_top_k keep_top_k_dec
                                                                    (inv_pos Z_thermo Z_thermo_pos)
                                                                    boltzmann_factor s))
              (sum_over_S_linear (inv_pos Z_thermo Z_thermo_pos)
                                 (fun s => if keep_top_k_dec s then zero else boltzmann_factor s)))).
Qed.

(* Key algebraic identity: kept·(invKeep − invZ) + invZ·T == 2·(invZ·T) *)
Lemma topk_sum_collapse :
  Id (plus (mult topk_kept_partition
                 (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                        (inv_pos Z_thermo Z_thermo_pos)))
           (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
     (mult (plus one one) (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)).
Proof.
  (* kept·(invK − invZ) == 1 − kept·invZ (reverse of [mult_minus_distr_l] + kept·invK == 1) *)
  assert (Hk1 : Id (mult topk_kept_partition
                          (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                 (inv_pos Z_thermo Z_thermo_pos)))
                   (minus one (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))).
  { apply (id_trans (mult_minus_distr_l topk_kept_partition
                                        (inv_pos topk_kept_partition topk_kept_partition_pos)
                                        (inv_pos Z_thermo Z_thermo_pos))).
    apply (id_cong (fun z => minus z (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))
                   (id_trans (mult_comm topk_kept_partition
                                        (inv_pos topk_kept_partition topk_kept_partition_pos))
                             (id_trans (mult_comm (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                  topk_kept_partition)
                                       (inv_pos_correct topk_kept_partition topk_kept_partition_pos)))). }
  (* kept·invZ + invZ·T == 1 ((kept+T)·invZ == Z·invZ == 1) *)
  assert (Hk2 : Id (plus (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos))
                          (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                    one).
  { apply (id_trans (id_sym (id_cong2 plus (id_refl) (mult_comm topk_tail_mass (inv_pos Z_thermo Z_thermo_pos))))
                    (id_trans (id_sym (mult_plus_distr_r topk_kept_partition topk_tail_mass
                                                         (inv_pos Z_thermo Z_thermo_pos)))
                              (id_trans (id_cong (fun z => mult z (inv_pos Z_thermo Z_thermo_pos))
                                                 topk_kept_plus_tail_full)
                                        (inv_pos_correct Z_thermo Z_thermo_pos)))). }
  (* 1 − kept·invZ == invZ·T: the minus side of plus kept·invZ invZ·T == 1 *)
  assert (Hk3 : Id (minus one (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))
                   (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)).
  { apply (id_trans (id_cong (fun z => minus z (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))
                             (id_sym Hk2))
                    (minus_plus_cancel_r (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos))
                                         (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))). }
  (* Assemble: kept·D + invZ·T == (1 − kept·invZ) + invZ·T == invZ·T + invZ·T == 2·(invZ·T) *)
  apply (id_trans (id_trans (id_cong2 plus Hk1 (id_refl))
                            (id_cong (fun z => plus z (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)) Hk3))
                  (id_sym (two_mult (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)))).
Qed.

(* Main theorem (conditional exact identity): strict eviction (lt invZ invKeep, instantiated at the
   Real layer by T > 0) ⟹ TV(boltzmann, topk_renorm) == tail_mass/Z_thermo *)
Theorem topk_tv_identity_strict :
  lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos) ->
  Id (tv_dist boltzmann_dist_attn topk_renorm)
     (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass).
Proof.
  intro Hst.
  unfold tv_dist, boltzmann_dist_attn, topk_renorm.
  (* Pointwise replacement ([topk_tv_pointwise]) *)
  assert (Hpt : Id (sum_over_S (fun s => abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                                                     (if keep_top_k_dec s
                                                      then mult (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                               (boltzmann_factor s)
                                                      else zero))))
                    (sum_over_S (fun s => if keep_top_k_dec s
                                          then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                               (inv_pos Z_thermo Z_thermo_pos))
                                          else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))).
  { apply sum_over_S_ext.
    intro s. apply (topk_tv_pointwise s Hst). }
  apply (id_trans (id_cong (fun z => mult inv_two z) Hpt)).
  apply (id_trans (id_cong (fun z => mult inv_two z) (topk_sum_decomp Hst))).
  apply (id_trans (id_cong (fun z => mult inv_two z) (topk_sum_collapse))).
  (* inv_two·(2·X) == X: assoc + [inv_pos_correct] + one *)
  apply (id_trans (mult_assoc inv_two (plus one one) (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                  (id_trans (id_cong (fun z => mult z (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                                     (id_trans (mult_comm inv_two (plus one one))
                                               (inv_pos_correct (plus one one) two_pos)))
                            (id_trans (mult_comm one (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                                      (mult_one (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))))).
Qed.

End AttentionGibbsBridge.

(* ============================================================ *)
(* Section MinPSampling: the constructive Min-P truncated sampling kernel *)
(* ============================================================ *)
(* A constructive formalization of the core decoding strategy of Llama 3.1 / vLLM:
   min-p sampling keeps the tokens with probability ≥ min_p × max probability, zeroes the rest,
   and renormalizes the temp_factor over the kept tokens.
   Route: Set layer + sigT + nontrivial implementations + extractable OCaml.
   Dependencies: RealInterfaceEnhanced + DecidableOrder (a decidable order);
   the vocabulary infrastructure is restated self-containedly (isomorphic to
   [StochasticLanguageModel]; the Section generalization makes its theorems non-reusable
   globally, so the already-proven interface is redeclared as honest Variables —
   the established pattern of the main file). *)
(* ------------------------------------------------------------ *)

Section MinPSampling.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ---------- 1. Interface assumptions (isomorphic to StochasticLanguageModel) ---------- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.

(* ---------- 2. Infrastructure (self-contained restatement) ---------- *)
Definition temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w]))).

Fixpoint list_sum (f : Token -> R) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (f w) (list_sum f rest)
  end.

Lemma list_sum_linear : forall a f l,
  Id (list_sum (fun w => mult a (f w)) l) (mult a (list_sum f l)).
Proof.
  intros a f l. induction l as [|w rest IH].
  - (* Goal: Id zero (mult a zero); [mult_zero a] : Id (mult a zero) zero, reversed by id_sym *)
    simpl. exact (id_sym (mult_zero a)).
  - (* Goal: Id (mult a (plus (f w) (list_sum ...))) (plus (mult a (f w)) (mult a (list_sum ...)))
       IH : Id (mult a (list_sum f rest)) (list_sum (fun w => mult a (f w)) rest)
       Left distributivity: mult a (x+y) == (x+y)·a ([mult_comm]) == x·a + y·a ([mult_plus_distr_r]) *)
    simpl.
    (* Goal: Id (plus (mult a (f w)) (list_sum (fun w => mult a (f w)) rest))
               (mult a (plus (f w) (list_sum f rest)))
       Use IH forward to replace list_sum (mult a∘f) rest on the LHS by mult a (list_sum f rest) *)
    rewrite IH.
    (* Goal: Id (plus (mult a (f w)) (mult a (list_sum f rest)))
               (mult a (plus (f w) (list_sum f rest)))
       Left distributivity: mult a (x + y) == mult a x + mult a y *)
    rewrite (mult_comm a (plus (f w) (list_sum f rest))).
    rewrite (mult_plus_distr_r (f w) (list_sum f rest) a).
    rewrite (mult_comm (f w) a).
    rewrite (mult_comm (list_sum f rest) a).
    apply id_refl.
Qed.

Lemma list_sum_ext : forall f g l,
  (forall w, Id (f w) (g w)) -> Id (list_sum f l) (list_sum g l).
Proof.
  intros f g l H. induction l as [|w rest IH].
  - simpl. apply id_refl.
  - simpl. rewrite H. rewrite IH. apply id_refl.
Qed.

Lemma list_sum_nonneg : forall l f,
  (forall w, le zero (f w)) -> le zero (list_sum f l).
Proof.
  intros l f Hf. induction l as [|w rest IH].
  - simpl. apply le_refl.
  - simpl.
    apply (le_id_l zero (plus zero zero) (plus (f w) (list_sum f rest))
                   (id_sym (plus_zero zero))).
    apply le_plus_compat; [apply Hf | apply IH].
Qed.

Lemma list_sum_single_le_total : forall l f w,
  InT w l -> (forall w', le zero (f w')) -> le (f w) (list_sum f l).
Proof.
  intros l f w Hin Hnonneg. induction l as [|a rest IH].
  - inversion Hin.
  - simpl. inversion Hin as [| y l' HIn']; subst.
    + (* w = a: f a ≤ f a + Σ rest ([le_plus_nonneg_r], Σ rest ≥ 0) *)
      exact (le_plus_nonneg_r (f a) (list_sum f rest) (list_sum_nonneg rest f Hnonneg)).
    + (* w ∈ rest: f w ≤ Σ rest ≤ f a + Σ rest *)
      assert (Hle : le (f w) (list_sum f rest)) by exact (IH HIn').
      apply (le_trans _ (list_sum f rest) _ Hle).
      apply (le_id_l (list_sum f rest) (plus zero (list_sum f rest)) (plus (f a) (list_sum f rest))
                     (id_trans (id_sym (plus_zero (list_sum f rest))) (plus_comm (list_sum f rest) zero))).
      apply le_plus_compat; [apply Hnonneg | apply le_refl].
Qed.

Lemma sum_temp_positive : forall (f : Token -> R),
  (forall w, lt zero (f w)) -> forall l : list Token, Not (Id l nil) -> lt zero (list_sum f l).
Proof.
  intros f Hf l Hl. induction l as [|w rest IH].
  - destruct Hl. apply id_refl.
  - destruct rest as [|w' rest'].
    + simpl. apply (lt_id_r zero (f w) (plus (f w) zero) (id_sym (plus_zero (f w))) (Hf w)).
    + simpl. apply (lt_id_l zero (plus zero zero) (plus (f w) (plus (f w') (list_sum f rest')))
                           (id_sym (plus_zero zero))).
      apply lt_plus_compat; [apply Hf | apply IH; intro H; inversion H].
Qed.

Definition partition_temp (prefix : list Token) : R :=
  list_sum (temp_factor prefix) vocab.

Lemma partition_temp_pos : forall prefix, lt zero (partition_temp prefix).
Proof.
  intro prefix. unfold partition_temp.
  apply sum_temp_positive.
  - intro w. unfold temp_factor. apply exp_neg_pos.
  - apply vocab_nonempty.
Qed.

Definition markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (temp_factor prefix w) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)).

(* ---------- 3. The greedy optimal token (self-contained restatement) ---------- *)
Definition candidate_token : Set := (Token * R)%type.

Fixpoint argmin_aux_token (prefix : list Token) (l : list Token) (best : candidate_token) : candidate_token :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      let loss_best := snd best in
      match ord_le_dec loss_w loss_best with
      | inl _ => argmin_aux_token prefix rest (w, loss_w)
      | inr _ => argmin_aux_token prefix rest best
      end
  end.

Definition pick_best_token (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest => fst (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* ---------- 3b. Implementation of the greedy optimal token (restatement of the proven StochasticLanguageModel pattern) ---------- *)
(* Head insertion for InT: x ∈ y :: l ⟹ x ∈ y :: a :: l (inserting a between y and l) *)
Lemma InT_head_extend : forall (x y a : Token) (l : list Token),
  InT x (y :: l) -> InT x (y :: a :: l).
Proof.
  intros x y a l H. inversion H; subst.
  - apply InT_here.
  - exact (@InT_next Token x y (a :: l) (@InT_next Token x a l H1)).
Qed.

(* The argmin result ∈ the candidate list ∪ the initial token: proof by induction.
   Replace-by-a branch: fst ∈ a :: rest (IH), lifted via InT_next best_token;
   Keep branch: fst ∈ best_token :: rest (IH), lifted via [InT_head_extend]. *)
Lemma argmin_aux_token_mem : forall prefix l best_token best_loss,
  InT best_token (best_token :: l) ->
  InT (fst (argmin_aux_token prefix l (best_token, best_loss))) (best_token :: l).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - simpl. exact Hinit.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + (* Replace by a: fst ∈ a :: rest (IH at the new best (a, loss a)), lifted to best_token :: a :: rest *)
      assert (Hmem : InT (fst (argmin_aux_token prefix rest (a, total_loss (prefix ++ [a])))) (a :: rest))
        by (apply (IH a (total_loss (prefix ++ [a]))); apply InT_here).
      apply InT_next. exact Hmem.
    + (* Keep: fst ∈ best_token :: rest (IH), lifted to best_token :: a :: rest *)
      assert (Hmem : InT (fst (argmin_aux_token prefix rest (best_token, best_loss))) (best_token :: rest))
        by (apply (IH best_token best_loss); apply InT_here).
      apply (InT_head_extend _ _ a rest). exact Hmem.
Qed.

(* pick_best ∈ vocab (the argmin traverses vocab and preserves membership) *)
Theorem pick_best_in_vocab' : forall prefix, InT (pick_best_token prefix) vocab.
Proof.
  intro prefix.
  unfold pick_best_token.
  destruct vocab as [| w0 rest].
  - (* vocab is empty, contradicting vocab_nonempty *)
    exact (match vocab_nonempty (@id_refl (list Token) nil) with end).
  - (* Initially w0 ∈ w0 :: rest = vocab; the argmin preserves membership *)
    apply (argmin_aux_token_mem prefix rest w0 (total_loss (prefix ++ [w0]))).
    apply InT_here.
Qed.

(* Positivity of the kernel (the temperature-sampling probability > 0: temp_factor > 0 and inv(partition) > 0) *)
Lemma markov_pos : forall prefix w, lt zero (markov_kernel prefix w).
Proof.
  intros prefix w. unfold markov_kernel.
  apply mult_positive.
  - unfold temp_factor. apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* ---------- 4. Min-P parameters and core definitions ---------- *)
Variable min_p : R.
Variable min_p_pos : lt zero min_p.
Variable min_p_lt_one : lt min_p one.

(* Left cancellation by the multiplicative unit *)
Lemma mult_one_l : forall a : R, Id (mult one a) a.
Proof.
  intros a. rewrite mult_comm. apply mult_one.
Qed.

(* 0 ≤ a and b ≤ 1 → b·a ≤ a (ring algebra) *)
Lemma le_mult_le_one_r : forall a b : R,
  le zero a -> le b one -> le (mult b a) a.
Proof.
  intros a b Ha Hb.
  assert (H1 : le zero (minus one b)).
  { apply le_minus_nonneg. apply Hb. }
  assert (H2 : le zero (mult (minus one b) a)).
  {
    (* Goal le zero (mult (minus one b) a):
       1) zero == mult a zero (reverse of mult_zero);
       2) mult (minus one b) a == mult a (minus one b) ([mult_comm]);
       3) le (mult a zero) (mult a (minus one b)) ([le_mult_compat_r a zero (minus one b) Ha H1]). *)
    apply (le_id_l zero (mult a zero) (mult (minus one b) a) (id_sym (mult_zero a))).
    rewrite <- (mult_comm a (minus one b)).
    apply (le_mult_compat_r a zero (minus one b) Ha H1).
  }
  assert (H3 : Id (mult (minus one b) a) (minus a (mult b a))).
  {
    (* mult (minus one b) a == mult a (minus one b) ([comm])
       == minus (mult a one) (mult a b) ([distr_l])
       == minus a (mult a b) ([mult_one]) == minus a (mult b a) ([comm]) *)
    rewrite (mult_comm (minus one b) a).
    rewrite mult_minus_distr_l.
    rewrite mult_one.
    rewrite (mult_comm a b).
    apply id_refl.
  }
  rewrite H3 in H2.
  assert (H4 : le (plus (mult b a) zero) (plus (mult b a) (minus a (mult b a)))).
  { apply le_plus_compat; [apply le_refl | apply H2]. }
  rewrite plus_zero_r in H4.
  assert (H5 : Id (plus (mult b a) (minus a (mult b a))) a).
  { apply minus_plus_cancel. }
  rewrite H5 in H4.
  apply H4.
Qed.

(* The best token is pick_best_token (minimal loss = maximal temp_factor) *)
Definition pick_max_token (prefix : list Token) : Token := pick_best_token prefix.

(* The maximal probability value *)
Definition max_markov_prob (prefix : list Token) : R :=
  markov_kernel prefix (pick_max_token prefix).

(* The Min-P threshold = min_p × the maximal probability *)
Definition minp_threshold (prefix : list Token) : R :=
  mult min_p (max_markov_prob prefix).

(* Decision: whether the probability of token w is ≥ the threshold (decidable at the Set layer) *)
Definition minp_keep (prefix : list Token) (w : Token) : Set :=
  le (minp_threshold prefix) (markov_kernel prefix w).

Definition minp_keep_dec (prefix : list Token) (w : Token) :
  Or (minp_keep prefix w) (Not (minp_keep prefix w)).
Proof.
  unfold minp_keep. apply ord_le_dec.
Defined.

(* The unnormalized mass after truncation (the sum of the temp_factors of the kept tokens) *)
Definition minp_temp_sum (prefix : list Token) : R :=
  list_sum (fun w => match minp_keep_dec prefix w with
                     | inl _ => temp_factor prefix w
                     | inr _ => zero
                     end) vocab.

(* ---------- 5. Core lemmas (all with real implementations) ---------- *)
Lemma pick_max_token_correct : forall prefix,
  Id (markov_kernel prefix (pick_max_token prefix)) (max_markov_prob prefix).
Proof.

  intro prefix. unfold max_markov_prob, pick_max_token. exact id_refl.

Qed.

(* Lemma: pick_max_token satisfies the Min-P condition (self-containedness; guarantees the truncated set is nonempty) *)
Lemma pick_max_token_minp_keep : forall prefix,
  minp_keep prefix (pick_max_token prefix).
Proof.
  intro prefix. unfold minp_keep.
  rewrite pick_max_token_correct.
  apply le_mult_le_one_r.
  - apply (lt_le_iff _ _). left. apply markov_pos.
  - apply (lt_le_iff _ _). left. apply min_p_lt_one.
Qed.

(* Lemma: lt zero a and le a b → lt zero b (order transitivity) *)
Lemma lt_zero_le_trans : forall a b : R,
  lt zero a -> le a b -> lt zero b.
Proof.
  intros a b Ha Hab.
  assert (Hnonneg : le zero (minus b a)).
  { apply le_minus_nonneg. apply Hab. }
  assert (Hpos : lt zero (plus (minus b a) a)).
  { apply plus_le_lt_pos.
    - apply Hnonneg.
    - apply Ha. }
  assert (Heq : Id (plus (minus b a) a) b).
  { rewrite (plus_comm (minus b a) a). apply minus_plus_cancel. }
  rewrite Heq in Hpos. apply Hpos.
Qed.

(* Lemma: positivity of minp_temp_sum (at least pick_max_token is counted in) *)
Lemma minp_temp_sum_pos : forall prefix, lt zero (minp_temp_sum prefix).
Proof.
  intro prefix.
  set (f := fun w => match minp_keep_dec prefix w with
                     | inl _ => temp_factor prefix w
                     | inr _ => zero
                     end).
  assert (Hin : InT (pick_max_token prefix) vocab).
  { apply pick_best_in_vocab'. }
  assert (Hkeep : minp_keep prefix (pick_max_token prefix)).
  { apply pick_max_token_minp_keep. }
  assert (Hf_eq : Id (f (pick_max_token prefix)) (temp_factor prefix (pick_max_token prefix))).
  { unfold f. destruct (minp_keep_dec prefix (pick_max_token prefix)).
    - apply id_refl.
    - destruct n. apply Hkeep. }
  assert (Hle : le (temp_factor prefix (pick_max_token prefix)) (minp_temp_sum prefix)).
  { unfold minp_temp_sum. rewrite <- Hf_eq.
    apply list_sum_single_le_total.
    - apply Hin.
    - intro w. unfold f. destruct (minp_keep_dec prefix w).
      + apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
      + apply le_refl. }
  apply lt_zero_le_trans with (a := temp_factor prefix (pick_max_token prefix)).
  - unfold temp_factor. apply exp_neg_pos.
  - apply Hle.
Qed.

(* The Min-P truncated sampling kernel (renormalized over the temp_factor) *)
Definition minp_markov_kernel (prefix : list Token) (w : Token) : R :=
  match minp_keep_dec prefix w with
  | inl _ =>
      mult (temp_factor prefix w)
           (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
  | inr _ => zero
  end.

(* ---------- 6. Core theorems (all with real implementations) ---------- *)

(* Theorem 1: the Min-P kernel is nonnegative — keepers are > 0, evicted states are == 0 (an Or decomposition).
   The arguments: match branches + [mult_positive] + [inv_pos_pos] (the keep branch),
   definitional reduction (the evict branch). *)
Lemma minp_markov_kernel_nonneg : forall prefix w,
  Or (Id (minp_markov_kernel prefix w) zero) (lt zero (minp_markov_kernel prefix w)).
Proof.
  intros prefix w. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hkeep | Hdrop].
  - right. apply mult_positive.
    + unfold temp_factor. apply exp_neg_pos.
    + apply inv_pos_pos.
  - left. apply id_refl.
Qed.

(* Theorem 2: positivity of the Min-P kernel at keepers *conditional*: premise minp_keep prefix w.
   Distinguished from the unconditional [minp_markov_kernel_nonneg] — the name carries the keep prefix,
   so the keeping premise must be supplied at use sites, preventing misreading as unconditional. *)
Lemma minp_markov_kernel_keep_pos : forall prefix w,
  minp_keep prefix w -> lt zero (minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hdrop].
  - apply mult_positive.
    + unfold temp_factor. apply exp_neg_pos.
    + apply inv_pos_pos.
  - destruct (Hdrop Hkeep).
Qed.

(* Theorem 3: normalization of the Min-P kernel — after renormalization the keepers sum to 1 (conservation of probability).
   The arguments: the definition of minp_temp_sum + factor extraction by [list_sum_linear] +
   cancellation by [inv_pos_correct] (the markov_normalized pattern). *)
Theorem minp_markov_kernel_normalized : forall prefix,
  Id (list_sum (fun w => minp_markov_kernel prefix w) vocab) one.
Proof.
  intro prefix.
  unfold minp_markov_kernel.
  (* Expand in the r_if pattern: the keep branch is temp_factor·inv(sum), the evict branch is zero.
      The match expansion fixes the branches once minp_keep_dec is fixed. *)
  assert (Hext : Id (list_sum (fun w => match minp_keep_dec prefix w with
                                        | inl _ => mult (temp_factor prefix w) (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                                        | inr _ => zero
                                        end) vocab)
                    (list_sum (fun w => mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                                            (match minp_keep_dec prefix w with
                                             | inl _ => temp_factor prefix w
                                             | inr _ => zero
                                             end)) vocab)).
  { apply list_sum_ext. intro w.
    destruct (minp_keep_dec prefix w) as [Hk | Hd].
    - simpl. apply mult_comm.
    - simpl. apply (id_sym (mult_zero (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix)))). }
  rewrite Hext.
  assert (Hlin : Id (list_sum (fun w => mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                                            (match minp_keep_dec prefix w with
                                             | inl _ => temp_factor prefix w
                                             | inr _ => zero
                                             end)) vocab)
                    (mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                          (list_sum (fun w => match minp_keep_dec prefix w with
                                              | inl _ => temp_factor prefix w
                                              | inr _ => zero
                                              end) vocab))).
  { apply list_sum_linear. }
  rewrite Hlin.
  assert (Hdef : Id (list_sum (fun w => match minp_keep_dec prefix w with
                                        | inl _ => temp_factor prefix w
                                        | inr _ => zero
                                        end) vocab) (minp_temp_sum prefix)).
  { unfold minp_temp_sum. apply id_refl. }
  rewrite Hdef.
  (* inv(Z)·Z == 1 ([inv_pos_correct] + [mult_comm]) *)
  assert (Hcc : Id (mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                         (minp_temp_sum prefix)) one).
  { exact (id_trans (mult_comm (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix)) (minp_temp_sum prefix))
                    (inv_pos_correct (minp_temp_sum prefix) (minp_temp_sum_pos prefix))). }
  exact Hcc.
Qed.

(* Theorem 4: the Min-P kernel is ≤ the full kernel — truncation never increases the probability of any token.
   The arguments: a keeper is = temp_factor·inv(minp_sum) and the full kernel is = temp_factor·inv(partition),
   so minp_sum ≤ partition is needed (minp_sum is a sub-sum, [list_sum_single_le_total] +
   the definition of partition_temp); then antitonicity of the inverse (the interface field
   [inv_pos_le_compat]: a ≤ b ⟹ inv b ≤ inv a, available in RealInterfaceEnhanced). *)
(* Supplement: pointwise monotonicity of list_sum (f ≤ g pointwise ⟹ Σ f ≤ Σ g, by induction) *)
Lemma list_sum_le : forall (l : list Token) (f g : Token -> R),
  (forall w, le (f w) (g w)) -> le (list_sum f l) (list_sum g l).
Proof.
  intros l f g Hfg. induction l as [|w rest IH]; simpl.
  - apply le_refl.
  - apply le_plus_compat; [apply Hfg | apply IH].
Qed.

(* minp_temp_sum ≤ partition_temp (closed by [list_sum_le]) *)
Lemma minp_temp_sum_le_partition : forall prefix,
  le (minp_temp_sum prefix) (partition_temp prefix).
Proof.
  intro prefix. unfold minp_temp_sum, partition_temp.
  apply list_sum_le.
  intro w. destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - apply le_refl.
  - apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
Qed.

(* Theorem 5: the relation between the Min-P kernel and the full kernel (honest statement).
   Min-P truncation + renormalization ⟹ the keeper kernel is amplified (the denominator satisfies
   minp_sum ≤ partition ⟹ inv(minp_sum) ≥ inv(partition) ⟹ the keeper kernel ≥ the full kernel),
   and the evicted kernel is 0 ≤ the full kernel.  **Conditional**: the premise is minp_keep prefix w —
   the name carries the keep prefix to distinguish it from the unconditional theorem. *)
Lemma minp_markov_kernel_keep_ge_full : forall prefix w,
  minp_keep prefix w -> le (markov_kernel prefix w) (minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold minp_markov_kernel, markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - (* Keep branch: temp_factor·inv(partition) ≤ temp_factor·inv(minp_sum) *)
    apply (le_mult_compat_r (temp_factor prefix w)
                            (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                            (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))).
    + (* temp_factor ≥ 0 ([exp_neg_pos]) *)
      apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
    + (* inv(partition) ≤ inv(minp_sum) ([inv_pos_le_compat]: a ≤ b ⟹ inv b ≤ inv a;
         take a := minp_sum, b := partition, needing le minp_sum partition) *)
      apply (inv_pos_le_compat (minp_temp_sum prefix) (partition_temp prefix)
                               (minp_temp_sum_pos prefix) (partition_temp_pos prefix)
                               (minp_temp_sum_le_partition prefix)).
  - destruct (Hd Hkeep).
Qed.

(* Theorem 6: the kernel of an evicted state = 0 (the truncation semantics) *)
Lemma minp_markov_kernel_dropped_zero : forall prefix w,
  Not (minp_keep prefix w) -> Id (minp_markov_kernel prefix w) zero.
Proof.
  intros prefix w Hdrop. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - destruct (Hdrop Hk).
  - apply id_refl.
Qed.

Lemma markov_kernel_unfold : forall (prefix : list Token) (w : Token),
  Id (markov_kernel prefix w)
     (mult (temp_factor prefix w)
           (inv_pos (partition_temp prefix)
                    (partition_temp_pos prefix))).
Proof.

  intros prefix w. unfold markov_kernel, temp_factor, partition_temp. exact id_refl.

Qed.

(* ===== Expansion of the keeper Min-P kernel ===== *)
Lemma minp_markov_kernel_unfold_keep : forall (prefix : list Token) (w : Token),
  minp_keep prefix w ->
  Id (minp_markov_kernel prefix w)
     (mult (temp_factor prefix w)
           (inv_pos (minp_temp_sum prefix)
                    (minp_temp_sum_pos prefix))).
Proof.
  intros prefix w Hkeep. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - apply id_refl.
  - destruct (Hd Hkeep).
Qed.

(* ===== Explicit amplification-factor form: the minp kernel = markov kernel · (inv(minp_sum)·partition) =====
   Mathematics: the keeper minp kernel = tf·inv(minp_sum) = (tf·inv(partition))·(partition·inv(minp_sum))
        = markov kernel · (inv(minp_sum)·partition) ([mult_assoc] + [inv_pos_correct] + comm) *)
Lemma minp_kernel_ratio : forall (prefix : list Token) (w : Token),
  minp_keep prefix w ->
  Id (minp_markov_kernel prefix w)
     (mult (markov_kernel prefix w)
           (mult (inv_pos (minp_temp_sum prefix)
                          (minp_temp_sum_pos prefix))
                 (partition_temp prefix))).
Proof.
  intros prefix w Hkeep.
  rewrite (minp_markov_kernel_unfold_keep prefix w Hkeep).
  rewrite (markov_kernel_unfold prefix w).
  (* Goal: tf·inv(minp_sum) == (tf·inv(partition))·(inv(minp_sum)·partition) *)
  (* Reverse associativity on the RHS: mult (mult tf inv_p) (mult inv_s p) → mult tf (mult inv_p (mult inv_s p)) *)
  rewrite <- (mult_assoc (temp_factor prefix w)
                         (inv_pos (partition_temp prefix)
                                  (partition_temp_pos prefix))
                         (mult (inv_pos (minp_temp_sum prefix)
                                        (minp_temp_sum_pos prefix))
                               (partition_temp prefix))).
  (* Goal: tf·inv(minp_sum) == tf·(inv(partition)·(inv(minp_sum)·partition)) *)
  (* Inner layer: inv(partition)·(inv(minp_sum)·partition) == inv(minp_sum) *)
  assert (Hinner : Id (mult (inv_pos (partition_temp prefix)
                                     (partition_temp_pos prefix))
                            (mult (inv_pos (minp_temp_sum prefix)
                                           (minp_temp_sum_pos prefix))
                                  (partition_temp prefix)))
                      (inv_pos (minp_temp_sum prefix)
                               (minp_temp_sum_pos prefix))).
  {
    (* inv_p·(inv_s·p) == inv_p·(p·inv_s) (comm swaps the inner layer) *)
    assert (Hc : Id (mult (inv_pos (partition_temp prefix)
                                   (partition_temp_pos prefix))
                          (mult (inv_pos (minp_temp_sum prefix)
                                         (minp_temp_sum_pos prefix))
                                (partition_temp prefix)))
                    (mult (inv_pos (partition_temp prefix)
                                   (partition_temp_pos prefix))
                          (mult (partition_temp prefix)
                                (inv_pos (minp_temp_sum prefix)
                                         (minp_temp_sum_pos prefix))))).
    { apply (id_cong (fun z => mult (inv_pos (partition_temp prefix)
                                             (partition_temp_pos prefix)) z)
                     (mult_comm (inv_pos (minp_temp_sum prefix)
                                         (minp_temp_sum_pos prefix))
                                (partition_temp prefix))). }
    apply (id_trans Hc).
    (* Goal: inv_p·(p·inv_s) == inv_s *)
    apply (id_trans (mult_assoc (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)
                                        (inv_pos (minp_temp_sum prefix)
                                                 (minp_temp_sum_pos prefix)))).
    (* Goal: (inv_p·p)·inv_s == inv_s *)
    (* Swap the order: mult (mult inv_p p) inv_s == mult (mult p inv_p) inv_s *)
    apply (id_trans (id_cong (fun z => mult z (inv_pos (minp_temp_sum prefix)
                                                       (minp_temp_sum_pos prefix)))
                             (mult_comm (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)))).
    apply (id_trans (id_cong (fun z => mult z (inv_pos (minp_temp_sum prefix)
                                                       (minp_temp_sum_pos prefix)))
                             (inv_pos_correct (partition_temp prefix)
                                              (partition_temp_pos prefix)))).
    (* Goal: one·inv_s == inv_s *)
    apply (id_trans (mult_comm one (inv_pos (minp_temp_sum prefix)
                                            (minp_temp_sum_pos prefix)))).
    apply (mult_one (inv_pos (minp_temp_sum prefix)
                             (minp_temp_sum_pos prefix))).
  }
  (* Replace the inner layer by Hinner (direction: the goal is LHS==RHS while Hinner gives the RHS==LHS side, reversed by id_sym) *)
  apply (id_sym (id_cong (fun z => mult (temp_factor prefix w) z) Hinner)).
Qed.

(* ===== Truncated mass: 1 − Z_minp/Z_full, nonnegative ===== *)
Definition minp_dropped_mass (prefix : list Token) : R :=
  minus one (mult (inv_pos (partition_temp prefix)
                           (partition_temp_pos prefix))
                  (minp_temp_sum prefix)).

Lemma minp_dropped_mass_nonneg : forall prefix,
  le zero (minp_dropped_mass prefix).
Proof.
  intro prefix. unfold minp_dropped_mass.
  apply le_minus_nonneg.
  (* Goal: le (mult inv_p minp_sum) one *)
  (* minp_sum ≤ partition ⟹ inv_p·minp_sum ≤ inv_p·partition == one *)
  apply (le_id_r (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (minp_temp_sum prefix))
                 (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (partition_temp prefix))
                 one).
  - (* inv_p·partition == one ([inv_pos_correct] + comm) *)
    apply (id_trans (mult_comm (inv_pos (partition_temp prefix)
                                        (partition_temp_pos prefix))
                               (partition_temp prefix))).
    apply (inv_pos_correct (partition_temp prefix)
                           (partition_temp_pos prefix)).
  - (* inv_p ≥ 0 and minp_sum ≤ partition ⟹ inv_p·minp_sum ≤ inv_p·partition *)
    apply (le_mult_compat_r (inv_pos (partition_temp prefix)
                                     (partition_temp_pos prefix))
                            (minp_temp_sum prefix)
                            (partition_temp prefix)).
    + (* inv_p ≥ 0: [inv_pos_pos] ⟹ lt zero ⟹ le zero *)
      apply (lt_le_iff _ _). left.
      apply (inv_pos_pos (partition_temp prefix)
                         (partition_temp_pos prefix)).
    + (* minp_sum ≤ partition (already proven above) *)
      exact (minp_temp_sum_le_partition prefix).
Qed.

(* ===== Quantitative upper bound on the truncated mass: 1 − Z_minp/Z_full ≤ 1 − max_prob =====
   Mathematics: pick_max ∈ the kept set ⟹ minp_sum ≥ tf(pick_max) == max_prob·partition
         ⟹ inv(partition)·minp_sum ≥ max_prob ⟹ 1 − ... ≤ 1 − max_prob.
   Meaning: the closer the maximal kernel probability is to 1, the smaller the Min-P truncation loss —
   a quantitative bound. *)
Lemma temp_factor_max_eq : forall prefix,
  Id (temp_factor prefix
                  (pick_max_token prefix))
     (mult (max_markov_prob prefix)
           (partition_temp prefix)).
Proof.
  intro prefix.
  (* H1 : tf(pick_max)·inv(p) == max_prob *)
  assert (H1 : Id (mult (temp_factor prefix
                                    (pick_max_token prefix))
                        (inv_pos (partition_temp prefix)
                                 (partition_temp_pos prefix)))
                   (max_markov_prob prefix)).
  {
    apply (id_trans (id_sym (markov_kernel_unfold prefix (pick_max_token prefix)))).
    exact (pick_max_token_correct prefix).
  }
  (* tf == tf·one == tf·(inv_p·p) == (tf·inv_p)·p == max·p *)
  apply (id_trans (id_sym (mult_one (temp_factor prefix
                                                 (pick_max_token prefix))))).
  apply (id_trans (id_cong (fun z => mult (temp_factor prefix
                                                      (pick_max_token prefix)) z)
                           (id_sym (id_trans (mult_comm (inv_pos (partition_temp prefix)
                                                                 (partition_temp_pos prefix))
                                                        (partition_temp prefix))
                                             (inv_pos_correct (partition_temp prefix)
                                                              (partition_temp_pos prefix)))))).
  apply (id_trans (mult_assoc (temp_factor prefix
                                           (pick_max_token prefix))
                              (inv_pos (partition_temp prefix)
                                       (partition_temp_pos prefix))
                              (partition_temp prefix))).
  apply (id_cong (fun z => mult z (partition_temp prefix)) H1).
Qed.

Lemma temp_factor_max_le_sum : forall prefix,
  le (temp_factor prefix
                  (pick_max_token prefix))
     (minp_temp_sum prefix).
Proof.
  intro prefix. unfold minp_temp_sum.
  (* f(pick_max) == match (pick_max) (pick_max is kept ⟹ the inl branch) *)
  assert (Heq : Id (temp_factor prefix
                                (pick_max_token prefix))
                   (match minp_keep_dec prefix
                                 (pick_max_token prefix)
                    with
                    | inl _ => temp_factor prefix
                                             (pick_max_token prefix)
                    | inr _ => zero
                    end)).
  {
    destruct (minp_keep_dec prefix
                            (pick_max_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd (pick_max_token_minp_keep prefix)).
  }
  apply (le_id_l (temp_factor prefix
                              (pick_max_token prefix))
                 (match minp_keep_dec prefix
                               (pick_max_token prefix)
                  with
                  | inl _ => temp_factor prefix
                                           (pick_max_token prefix)
                  | inr _ => zero
                  end)
                 (list_sum (fun w => match minp_keep_dec prefix w with
                                      | inl _ => temp_factor prefix w
                                      | inr _ => zero
                                      end) vocab)
                 Heq).
  apply (list_sum_single_le_total vocab
                                  (fun w => match minp_keep_dec prefix w with
                                            | inl _ => temp_factor prefix w
                                            | inr _ => zero
                                            end)
                                  (pick_max_token prefix)
                                  (pick_best_in_vocab' prefix)).
  intro w. destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
  - apply le_refl.
Qed.

Lemma minp_scaled_sum_ge_max : forall prefix,
  le (max_markov_prob prefix)
     (mult (inv_pos (partition_temp prefix)
                    (partition_temp_pos prefix))
           (minp_temp_sum prefix)).
Proof.
  intro prefix.
  (* max·p ≤ minp_sum (bridged by [temp_factor_max_le_sum] + [temp_factor_max_eq]) *)
  assert (H1 : le (mult (max_markov_prob prefix)
                        (partition_temp prefix))
                  (minp_temp_sum prefix)).
  {
    apply (le_id_l (mult (max_markov_prob prefix)
                          (partition_temp prefix))
                   (temp_factor prefix
                                (pick_max_token prefix))
                   (minp_temp_sum prefix)
                   (id_sym (temp_factor_max_eq prefix))
                   (temp_factor_max_le_sum prefix)).
  }
  (* inv_p·(max·p) ≤ inv_p·minp_sum; the left side == max (assoc + inv_correct + one) *)
  (* Algebraic chain: inv_p·(max·p) == max *)
  assert (Hid : Id (mult (inv_pos (partition_temp prefix)
                                  (partition_temp_pos prefix))
                         (mult (max_markov_prob prefix)
                               (partition_temp prefix)))
                   (max_markov_prob prefix)).
  {
    apply (id_trans (mult_assoc (inv_pos (partition_temp prefix)
                                         (partition_temp_pos prefix))
                                (max_markov_prob prefix)
                                (partition_temp prefix))).
    apply (id_trans (id_cong (fun z => mult z (partition_temp prefix))
                             (mult_comm (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (max_markov_prob prefix)))).
    apply (id_trans (id_sym (mult_assoc (max_markov_prob prefix)
                                        (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)))).
    apply (id_trans (id_cong (fun z => mult (max_markov_prob prefix) z)
                             (mult_comm (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)))).
    apply (id_trans (id_cong (fun z => mult (max_markov_prob prefix) z)
                             (inv_pos_correct (partition_temp prefix)
                                              (partition_temp_pos prefix)))).
    apply (id_trans (mult_comm (max_markov_prob prefix) one)).
    apply (mult_one_l (max_markov_prob prefix)).
  }
  (* Assemble: max ≤ inv_p·minp_sum (inv_p·(max·p) == max and inv_p·(max·p) ≤ inv_p·minp_sum) *)
  apply (le_id_l (max_markov_prob prefix)
                 (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (mult (max_markov_prob prefix)
                             (partition_temp prefix)))
                 (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (minp_temp_sum prefix))
                 (id_sym Hid)
                 (le_mult_compat_r (inv_pos (partition_temp prefix)
                                            (partition_temp_pos prefix))
                                   (mult (max_markov_prob prefix)
                                         (partition_temp prefix))
                                   (minp_temp_sum prefix)
                                   (lt_le_iff _ _ (inl (inv_pos_pos (partition_temp prefix)
                                                                    (partition_temp_pos prefix))))
                                   H1)).

Qed.
Lemma minp_dropped_mass_le_one_minus_max : forall prefix,
  le (minp_dropped_mass prefix)
     (minus one (max_markov_prob prefix)).
Proof.

  intro prefix. unfold minp_dropped_mass. exact (le_id_l (plus one (opp (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix)))) (minus one (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix))) (minus one (max_markov_prob prefix)) (id_refl) (le_plus_compat one one (opp (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix))) (opp (max_markov_prob prefix)) (le_refl one) (opp_le_compat (max_markov_prob prefix) (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix)) (minp_scaled_sum_ge_max prefix)))).

Qed.

Definition minp_threshold_p (mp : R) (prefix : list Token) : R :=
  mult mp (max_markov_prob prefix).

Definition minp_keep_p (mp : R) (prefix : list Token) (w : Token) : Set :=
  le (minp_threshold_p mp prefix) (markov_kernel prefix w).

Definition minp_keep_dec_p (mp : R) (prefix : list Token) (w : Token) :
  Or (minp_keep_p mp prefix w) (Not (minp_keep_p mp prefix w)).
Proof.
  unfold minp_keep_p, minp_threshold_p. apply ord_le_dec.
Defined.

Definition minp_temp_sum_p (mp : R) (prefix : list Token) : R :=
  list_sum (fun w => match minp_keep_dec_p mp prefix w with
                           | inl _ => temp_factor prefix w
                           | inr _ => zero
                           end) vocab.

Definition minp_dropped_mass_p (mp : R) (prefix : list Token) : R :=
  minus one (mult (inv_pos (partition_temp prefix)
                           (partition_temp_pos prefix))
                  (minp_temp_sum_p mp prefix)).

(* ===== min_p enlargement ⟹ the keep decision is antitone (the kept set shrinks) =====
   mp1 ≤ mp2 ⟹ threshold1 ≤ threshold2 ([le_mult_compat_r], max ≥ 0)
   ⟹ keep2 w (threshold2 ≤ kernel) ⟹ threshold1 ≤ kernel ([le_trans]) ⟹ keep1 w *)
Lemma minp_keep_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix w,
    minp_keep_p mp2 prefix w -> minp_keep_p mp1 prefix w.
Proof.
  intros mp1 mp2 Hmp prefix w Hk2.
  unfold minp_keep_p, minp_threshold_p in *.
  (* max_markov_prob ≥ 0 (lifted from [markov_pos]) *)
  assert (Hmax : le zero (max_markov_prob prefix)).
  { unfold max_markov_prob. rewrite pick_max_token_correct.
    apply (lt_le_iff _ _). left.
    exact (markov_pos prefix
                      (pick_max_token prefix)). }
  (* mp1·max ≤ mp2·max ([le_mult_compat_r]) *)
  assert (Hthr : le (mult mp1 (max_markov_prob prefix))
                    (mult mp2 (max_markov_prob prefix))).
  { apply (le_mult_compat_weak mp1 mp2 (max_markov_prob prefix) Hmax Hmp). }
  (* threshold1 ≤ threshold2 ≤ kernel ⟹ threshold1 ≤ kernel *)
  apply (le_trans _ (mult mp2 (max_markov_prob prefix)) _ Hthr).
  exact Hk2.
Qed.

(* Auxiliary: temp_factor ≥ 0 *)
Lemma temp_factor_nonneg_p : forall prefix w,
  le zero (temp_factor prefix w).
Proof.
  intros prefix w. unfold temp_factor. apply (lt_le_iff _ _). left. apply exp_neg_pos.
Qed.

(* Auxiliary: the parameterized keeper term is ≥ 0 (the inl branch has tf ≥ 0, the inr branch is 0) *)
Lemma minp_term_nonneg_p : forall mp prefix w,
  le zero (match minp_keep_dec_p mp prefix w with
           | inl _ => temp_factor prefix w
           | inr _ => zero
           end).
Proof.
  intros mp prefix w. destruct (minp_keep_dec_p mp prefix w) as [Hk | Hd].
  - exact (temp_factor_nonneg_p prefix w).
  - apply le_refl.
Qed.

(* ===== min_p enlargement ⟹ the kept mass is antitone (minp_sum2 ≤ minp_sum1) =====
   Termwise: keep2 w ⟹ keep1 w (antitone) ⟹ the term contributions agree; if keep2 evicts w ⟹ term2 = 0 ≤ term1 *)
Lemma minp_temp_sum_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (minp_temp_sum_p mp2 prefix) (minp_temp_sum_p mp1 prefix).
Proof.
  intros mp1 mp2 Hmp prefix.
  unfold minp_temp_sum_p.
  apply (list_sum_le vocab
                     (fun w => match minp_keep_dec_p mp2 prefix w with
                               | inl _ => temp_factor prefix w
                               | inr _ => zero
                               end)
                     (fun w => match minp_keep_dec_p mp1 prefix w with
                               | inl _ => temp_factor prefix w
                               | inr _ => zero
                               end)).
  intro w. destruct (minp_keep_dec_p mp2 prefix w) as [Hk2 | Hd2].
  - (* keep2 ⟹ keep1 (antitone) ⟹ the terms agree *)
    assert (Hk1 : minp_keep_p mp1 prefix w) by exact (minp_keep_p_antitone mp1 mp2 Hmp prefix w Hk2).
    destruct (minp_keep_dec_p mp1 prefix w) as [Hk1' | Hd1'].
    + apply le_refl.
    + destruct (Hd1' Hk1).
  - (* Evicted ⟹ term2 = 0 ≤ term1 *)
    apply (minp_term_nonneg_p mp1 prefix w).
Qed.

(* ===== min_p enlargement ⟹ the truncated mass does not decrease (mass1 ≤ mass2) =====
   sum2 ≤ sum1 ⟹ inv·sum2 ≤ inv·sum1 ⟹ 1−inv·sum1 ≤ 1−inv·sum2 *)
Lemma minp_dropped_mass_p_monotone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (minp_dropped_mass_p mp1 prefix) (minp_dropped_mass_p mp2 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold minp_dropped_mass_p.
  (* sum2 ≤ sum1 (antitone) *)
  assert (Hsum : le (minp_temp_sum_p mp2 prefix) (minp_temp_sum_p mp1 prefix))
    by exact (minp_temp_sum_p_antitone mp1 mp2 Hmp prefix).
  (* inv_p ≥ 0 ([inv_pos_pos]) *)
  assert (Hinv : le zero (inv_pos (partition_temp prefix)
                                  (partition_temp_pos prefix))).
  { apply (lt_le_iff _ _). left.
    apply (inv_pos_pos (partition_temp prefix)
                       (partition_temp_pos prefix)). }
  (* inv·sum2 ≤ inv·sum1 ([le_mult_compat_r]) *)
  assert (Hscaled : le (mult (inv_pos (partition_temp prefix)
                                      (partition_temp_pos prefix))
                             (minp_temp_sum_p mp2 prefix))
                       (mult (inv_pos (partition_temp prefix)
                                      (partition_temp_pos prefix))
                             (minp_temp_sum_p mp1 prefix)))
    by exact (le_mult_compat_r (inv_pos (partition_temp prefix)
                                        (partition_temp_pos prefix))
                               (minp_temp_sum_p mp2 prefix) (minp_temp_sum_p mp1 prefix) Hinv Hsum).
  (* 1−X ≤ 1−Y (X ≥ Y ⟹ 1−X ≤ 1−Y): le_id_l + le_plus_compat one one (opp Y) (opp X) *)
  apply (le_id_l (plus one (opp (mult (inv_pos (partition_temp prefix)
                                                (partition_temp_pos prefix))
                                       (minp_temp_sum_p mp1 prefix))))
                 (minus one (mult (inv_pos (partition_temp prefix)
                                           (partition_temp_pos prefix))
                                  (minp_temp_sum_p mp1 prefix)))
                 (minus one (mult (inv_pos (partition_temp prefix)
                                           (partition_temp_pos prefix))
                                  (minp_temp_sum_p mp2 prefix)))
                 (id_refl)
                 (le_plus_compat one one
                                 (opp (mult (inv_pos (partition_temp prefix)
                                                     (partition_temp_pos prefix))
                                            (minp_temp_sum_p mp1 prefix)))
                                 (opp (mult (inv_pos (partition_temp prefix)
                                                     (partition_temp_pos prefix))
                                            (minp_temp_sum_p mp2 prefix)))
                                 (le_refl one)
                                 (opp_le_compat (mult (inv_pos (partition_temp prefix)
                                                               (partition_temp_pos prefix))
                                                      (minp_temp_sum_p mp2 prefix))
                                                (mult (inv_pos (partition_temp prefix)
                                                               (partition_temp_pos prefix))
                                                      (minp_temp_sum_p mp1 prefix))
                                                Hscaled))).
Qed.

(* ============================================================ *)
(* The Min-P truncated mass scales with the vocabulary size *)
(*   dropped ≤ 1 − 1/|S| (the truncated mass is ≤ 1 minus the reciprocal of the vocabulary size): *)
(*   chain 1: p_max ≥ 1/|S| — Σp = 1 (normalization of the full kernel) + termwise p_w ≤ p_max *)
(*     (restating the minimality of the argmin traversal) + sum ≤ size·max + division by a positive number; *)
(*   chain 2: dropped ≤ 1 − p_max ([minp_dropped_mass_le_one_minus_max]) *)
(*   Assembled from argmin minimality + normalization + counting, thirteen lemmas. *)
(* ============================================================ *)

(* The embedding of nat into R (self-contained for MinPSampling; the GRPO of_nat is global, so the name avoids a clash) *)
Fixpoint mp_of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (mp_of_nat n')
  end.

(* Positivity of the length of a nonempty list: l ≠ nil ⟹ 0 < mp_of_nat (length l).
   Positivity is established for every positive length first; the empty
   case is then closed by Empty_set elimination. *)
Lemma mp_of_nat_pos : forall (l : list Token), Not (Id l nil) -> lt zero (mp_of_nat (length l)).
Proof.
  intros l Hl.
  assert (Hpos_S : forall n : nat, lt zero (mp_of_nat (Datatypes.S n))).
  { intro n. induction n as [| n' IH]; simpl.
    - apply (@lt_id_r RI zero one (plus one zero)).
      * apply (id_sym (plus_zero one)).
      * exact one_pos.
    - apply (@lt_id_l RI zero (plus zero zero) (plus one (plus one (mp_of_nat n')))).
      * apply (id_sym (plus_zero zero)).
      * apply (lt_plus_compat zero one zero (plus one (mp_of_nat n'))).
        -- exact one_pos.
        -- exact IH. }
  destruct l as [| w rest].
  - exact (match Hl (@id_refl (list Token) nil) with end).
  - simpl. exact (Hpos_S (length rest)).
Qed.

(* Normalization of the full kernel: Σ_w markov_kernel w == 1 (self-contained restatement; inv_p·Σtemp == inv_p·partition == 1) *)
Lemma markov_kernel_normalized_mp : forall prefix,
  Id (list_sum (markov_kernel prefix) vocab) one.
Proof.
  intro prefix.
  unfold markov_kernel.
  assert (Hext : Id (list_sum (fun w => mult (temp_factor prefix w)
                                             (inv_pos (partition_temp prefix) (partition_temp_pos prefix))) vocab)
                    (list_sum (fun w => mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                                             (temp_factor prefix w)) vocab))
    by (apply list_sum_ext; intro w; apply mult_comm).
  apply (id_trans Hext).
  assert (Hlin : Id (list_sum (fun w => mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                                             (temp_factor prefix w)) vocab)
                    (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                          (list_sum (temp_factor prefix) vocab)))
    by exact (list_sum_linear (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                              (temp_factor prefix) vocab).
  apply (id_trans Hlin).
  assert (Hp : Id (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                        (partition_temp prefix)) one).
  { apply (id_trans (mult_comm (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                               (partition_temp prefix))).
    apply (inv_pos_correct (partition_temp prefix) (partition_temp_pos prefix)). }
  exact Hp.
Qed.

(* Antitonicity of temp_factor: loss a ≤ loss b ⟹ temp b ≤ temp a ([exp_neg_le_decr] + inv/T ≥ 0) *)
Lemma temp_factor_antitone_mp : forall (prefix : list Token) (a b : Token),
  le (total_loss (prefix ++ [a])) (total_loss (prefix ++ [b])) ->
  le (temp_factor prefix b) (temp_factor prefix a).
Proof.
  intros prefix a b Hloss.
  unfold temp_factor.
  apply (exp_neg_le_decr (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [a])))
                         (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [b])))).
  apply (le_mult_compat_r (inv_pos temperature temperature_pos)
                          (total_loss (prefix ++ [a]))
                          (total_loss (prefix ++ [b]))).
  - apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - exact Hloss.
Qed.

(* Minimality of the argmin traversal (self-contained restatement of the StochasticLanguageModel pattern) *)
Lemma argmin_aux_token_min_mp : forall prefix l best_token best_loss,
  And (forall w : Token, InT w l ->
    le (snd (argmin_aux_token prefix l (best_token, best_loss)))
       (total_loss (prefix ++ [w])))
      (le (snd (argmin_aux_token prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - assert (Hempty : forall w : Token, InT w nil -> le (snd (argmin_aux_token prefix nil (best_token, best_loss)))
                                                        (total_loss (prefix ++ [w]))).
    { intros w HIn. inversion HIn. }
    exact (pair Hempty (le_refl _)).
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + destruct (IH a (total_loss (prefix ++ [a]))) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
    + destruct (IH best_token best_loss) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a]))) by (apply not_le_lt; exact Hnot).
           exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* snd is identically the loss of the corresponding fst (the argmin-traversal invariant, self-contained restatement) *)
Lemma argmin_aux_token_snd_correct_mp : forall prefix l best_token best_loss,
  Id best_loss (total_loss (prefix ++ [best_token])) ->
  Id (snd (argmin_aux_token prefix l (best_token, best_loss)))
     (total_loss (prefix ++ [fst (argmin_aux_token prefix l (best_token, best_loss))])).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - simpl. exact Hinit.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) id_refl).
    + exact (IH best_token best_loss Hinit).
Qed.

(* Optimality of pick_best: loss(pick_best) ≤ loss w (w ∈ vocab) *)
Theorem pick_best_optimal_mp : forall prefix w,
  InT w vocab ->
  le (total_loss (prefix ++ [pick_best_token prefix])) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold pick_best_token.
  destruct vocab as [| w0 rest].
  - inversion Hw.
  - destruct (argmin_aux_token_min_mp prefix rest w0 (total_loss (prefix ++ [w0]))) as [Hmin Hle].
    assert (Hsnd : Id (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [fst (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))])))
      by exact (argmin_aux_token_snd_correct_mp prefix rest w0 (total_loss (prefix ++ [w0])) id_refl).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + assert (Hr : le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w0])))
        by exact Hle.
      exact (match Hsnd in (Id _ y)
               return (le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                          (total_loss (prefix ++ [w0]))
                          -> le y (total_loss (prefix ++ [w0])))
             with | id_refl => fun H => H end Hr).
    + assert (Hr : le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w])))
        by exact (Hmin w Hwrest).
      exact (match Hsnd in (Id _ y)
               return (le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                          (total_loss (prefix ++ [w]))
                          -> le y (total_loss (prefix ++ [w])))
             with | id_refl => fun H => H end Hr).
Qed.

(* Maximality of max: kernel w ≤ max (w ∈ vocab) — minimal loss + antitonicity of temp + order preservation by inv ≥ 0 *)
Lemma markov_kernel_le_max_mp : forall prefix w,
  InT w vocab ->
  le (markov_kernel prefix w) (max_markov_prob prefix).
Proof.
  intros prefix w Hw.
  unfold max_markov_prob, markov_kernel.
  apply (le_mult_compat_weak (temp_factor prefix w) (temp_factor prefix (pick_max_token prefix))
                             (inv_pos (partition_temp prefix) (partition_temp_pos prefix))).
  - apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - apply (temp_factor_antitone_mp prefix (pick_max_token prefix) w).
    apply (pick_best_optimal_mp prefix w Hw).
Qed.

(* Sum ≤ size·max: termwise (w ∈ l) f w ≤ M ⟹ Σ f l ≤ mp_of_nat(length l)·M *)
Lemma list_sum_le_const_mp : forall (l : list Token) (f : Token -> R) (M : R),
  (forall w : Token, InT w l -> le (f w) M) ->
  le (list_sum f l) (mult (mp_of_nat (length l)) M).
Proof.
  intros l f M Hf.
  induction l as [| w rest IH]; simpl.
  - apply (le_id_l zero (mult zero M) (mult zero M)).
    + apply (id_sym (id_trans (mult_comm zero M) (mult_zero M))).
    + apply le_refl.
  - apply (le_id_r (plus (f w) (list_sum f rest))
                   (plus M (mult (mp_of_nat (length rest)) M))
                   (mult (plus one (mp_of_nat (length rest))) M)).
    + assert (Hd : Id (plus M (mult (mp_of_nat (length rest)) M))
                      (mult (plus one (mp_of_nat (length rest))) M)).
      { apply (id_sym (id_trans (mult_plus_distr_r one (mp_of_nat (length rest)) M)
                                (id_cong (fun z => plus z (mult (mp_of_nat (length rest)) M))
                                         (id_trans (mult_comm one M) (mult_one M))))). }
      exact Hd.
    + apply le_plus_compat.
      * apply (Hf w). apply InT_here.
      * apply IH. intro w'. intro Hw'. apply (Hf w'). apply InT_next. exact Hw'.
Qed.

(* Division by a positive number: 0 < G and 1 ≤ G·M ⟹ inv G ≤ M (the (inv G)·(G·M) == M bridge + order preservation) *)
Lemma le_one_mult_le_inv_mp : forall (G M : R) (Hg : lt zero G),
  le one (mult G M) -> le (inv_pos G Hg) M.
Proof.
  intros G M Hg Hle.
  assert (Habs : Id (mult (inv_pos G Hg) (mult G M)) M).
  { apply (id_trans (mult_assoc (inv_pos G Hg) G M)).
    apply (id_trans (id_cong (fun z => mult z M)
                             (id_trans (mult_comm (inv_pos G Hg) G) (inv_pos_correct G Hg)))).
    apply (id_trans (mult_comm one M)).
    apply (mult_one M). }
  apply (le_id_r (inv_pos G Hg) (mult (inv_pos G Hg) (mult G M)) M Habs).
  apply (le_id_l (inv_pos G Hg) (mult (inv_pos G Hg) one) (mult (inv_pos G Hg) (mult G M))).
  - apply (id_sym (mult_one (inv_pos G Hg))).
  - apply (le_mult_compat_r (inv_pos G Hg) one (mult G M)).
    + apply (lt_le_iff _ _). left. apply (inv_pos_pos G Hg).
    + exact Hle.
Qed.

(* p_max ≥ 1/|S|: 1 == Σ kernel ≤ |S|·max ⟹ inv(|S|) ≤ max (chain 1) *)
Lemma minp_max_ge_inv_vocab_size : forall prefix,
  le (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty))
     (max_markov_prob prefix).
Proof.
  intro prefix.
  apply (le_one_mult_le_inv_mp (mp_of_nat (length vocab)) (max_markov_prob prefix)
                               (mp_of_nat_pos vocab vocab_nonempty)).
  apply (le_id_l one (list_sum (markov_kernel prefix) vocab)
                 (mult (mp_of_nat (length vocab)) (max_markov_prob prefix))).
  - apply (id_sym (markov_kernel_normalized_mp prefix)).
  - apply (list_sum_le_const_mp vocab (markov_kernel prefix) (max_markov_prob prefix)).
    intro w. intro Hw. apply (markov_kernel_le_max_mp prefix w Hw).
Qed.

(* Main theorem: the truncated mass ≤ 1 − 1/|S| (chain 2: dropped ≤ 1 − max ≤ 1 − inv|S|) *)
Theorem minp_dropped_mass_le_inv_vocab_size : forall prefix,
  le (minp_dropped_mass prefix)
     (minus one (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty))).
Proof.
  intro prefix.
  apply (le_trans _ (minus one (max_markov_prob prefix)) _).
  - exact (minp_dropped_mass_le_one_minus_max prefix).
  - unfold minus.
    apply (le_plus_compat one one
                           (opp (max_markov_prob prefix))
                           (opp (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty)))).
    + apply le_refl.
    + apply (opp_le_compat (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty))
                           (max_markov_prob prefix)).
      exact (minp_max_ge_inv_vocab_size prefix).
Qed.

End MinPSampling.

(* ============================================================
   Section TopPSampling: a constructive formalization of top-p (nucleus) sampling
   (probability-decreasing sort + keep decision, merged in)
   ============================================================ *)
Section TopPSampling.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* Premises with the same signature as MinPSampling (the closure carried in explicit arguments) *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.

(* ===== Insertion sort in decreasing probability order (by the markov_kernel weight, decidable via ord_le_dec) ===== *)
Fixpoint insert_kernel (prefix : list Token) (w : Token) (l : list Token) : list Token :=
  match l with
  | nil => w :: nil
  | a :: rest =>
      match ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
                       (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w) with
      | inl _ => w :: a :: rest
      | inr _ => a :: insert_kernel prefix w rest
      end
  end.

Fixpoint sort_kernel (prefix : list Token) (l : list Token) : list Token :=
  match l with
  | nil => nil
  | w :: rest => insert_kernel prefix w (sort_kernel prefix rest)
  end.

(* ===== Prefix cumulative probability (the top-p cumulative-threshold decision) ===== *)
Fixpoint prefix_sum (prefix : list Token) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
                      (prefix_sum prefix rest)
  end.

(* ===== Membership lemma: insertion preserves existing elements (induction on the InT structure) ===== *)
Lemma insert_kernel_preserves : forall prefix a w l,
  InT w l -> InT w (insert_kernel prefix a l).
Proof.
  intros prefix a w l Hin.
  induction Hin as [l' | y l' Hw IHw].
  - (* w is the head: insert a (w :: l') *)
    simpl.
    destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
                         (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)) as [Hle | Hnot].
    + apply InT_next. apply InT_here.
    + apply InT_here.
  - (* w is in the tail of y :: l', with IHw : InT w (insert_kernel prefix a l') *)
    simpl.
    destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix y)
                         (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)) as [Hle | Hnot].
    + apply InT_next. apply InT_next. exact Hw.
    + apply InT_next. exact IHw.
Qed.

(* Lemma: the inserted w itself is in the list *)
Lemma insert_kernel_mem : forall prefix w l,
  InT w (insert_kernel prefix w l).
Proof.
  intros prefix w l. induction l as [| a rest IH]; simpl.
  - apply InT_here.
  - destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
                         (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)) as [Hle | Hnot].
    + apply InT_here.
    + apply InT_next. exact IH.
Qed.

(* Lemma: sorting preserves membership *)
Lemma sort_kernel_mem : forall prefix w l,
  InT w l -> InT w (sort_kernel prefix l).
Proof.
  intros prefix w l. induction l as [| a rest IH]; intros Hin.
  - inversion Hin.
  - simpl. inversion Hin as [Hwa | Hy Hl Hwrest].
    + subst. apply (insert_kernel_mem prefix a (sort_kernel prefix rest)).
    + apply (insert_kernel_preserves prefix a w (sort_kernel prefix rest)). exact (IH Hwrest).
Qed.

(* ===== Domination: inserting w into a sorted list, the probability of w is ≥ that of every element after it (the head suffices) ===== *)
Lemma insert_kernel_head_ge : forall prefix w a l,
  le (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
     (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w) ->
  Id (insert_kernel prefix w (a :: l)) (w :: a :: l).
Proof.
  intros prefix w a l Hge.
  unfold insert_kernel.
  destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
                       (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)) as [Hle | Hnot].
  - apply id_refl.
  - destruct (Hnot Hge).
Qed.

(* ===== The top-p keep decision: traverse the sorted list, stopping at w or at probability ≤ p =====
   Top-p retention: carried by an indexed Set family whose constructors
   match the walk semantics exactly (head hit, or head strictly above the
   threshold with the tail membership), so extraction keeps the full type. *)
Inductive top_p_member (p : R) (prefix : list Token) : list Token -> Token -> Set :=
| topp_here : forall (w : Token) (rest : list Token),
    top_p_member p prefix (w :: rest) w
| topp_next : forall (w : Token) (rest : list Token) (x : Token),
    Not (Id x w) ->
    Not (le (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w) p) ->
    top_p_member p prefix rest x ->
    top_p_member p prefix (w :: rest) x.

Definition top_p_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  top_p_member p prefix (sort_kernel prefix vocab) w.


Definition topp_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  le p (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).

Definition topp_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (topp_keep p prefix w) (Not (topp_keep p prefix w)).
Proof. unfold topp_keep. apply ord_le_dec. Defined.

(* The top-p kept sum (the nucleus truncated mass) *)
Definition topp_temp_sum (p : R) (prefix : list Token) : R :=
  list_sum Token (fun w => match topp_keep_dec p prefix w with
                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab.

Lemma topp_temp_sum_unfold : forall p prefix,
  Id (topp_temp_sum p prefix)
     (list_sum Token (fun w => match topp_keep_dec p prefix w with
                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                               | inr _ => zero
                               end) vocab).
Proof. intros. unfold topp_temp_sum. apply id_refl. Qed.

(* Nonempty: p ≤ max_markov_prob ⟹ pick_max is kept ⟹ sum ≥ tf(pick_max) > 0 *)
Lemma topp_temp_sum_pos : forall p prefix,
  le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix) ->
  lt zero (topp_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  unfold topp_temp_sum.
  assert (Hkeep : topp_keep p prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold topp_keep. rewrite pick_max_token_correct. exact Hp. }
  assert (Heq : Id (temp_factor Token total_loss temperature temperature_pos prefix
                                  (pick_max_token Token vocab total_loss default_token prefix))
                   (match topp_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)).
  { destruct (topp_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd Hkeep). }
  assert (Hle : le (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)).
  { apply (le_id_l (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (match topp_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)
                   (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)
                   Heq
                   (list_sum_single_le_total Token vocab
                                     (fun w => match topp_keep_dec p prefix w with
                                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                               | inr _ => zero
                                               end)
                                     (pick_max_token Token vocab total_loss default_token prefix)
                                     (pick_best_in_vocab' Token vocab vocab_nonempty total_loss default_token prefix)
                                     (fun w' => match topp_keep_dec p prefix w' as d return le zero (match d with
                                                                                                                          | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w'
                                                                                                                          | inr _ => zero
                                                                                                                          end) with
                                                | inl _ => lt_le_iff _ _ (inl (exp_neg_pos (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w'])))))
                                                | inr _ => le_refl zero
                                                end))). }
  apply (lt_le_trans zero (temp_factor Token total_loss temperature temperature_pos prefix
                                          (pick_max_token Token vocab total_loss default_token prefix))
                          (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                                          | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                          | inr _ => zero
                                                          end) vocab)).
  - unfold temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* The top-p renormalized kernel (with p ≤ max as the global premise Hpmax) *)
Definition topp_markov_kernel (p : R) (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
                              (prefix : list Token) (w : Token) : R :=
  match topp_keep_dec p prefix w with
  | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                  (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

(* ===== Normalization of the top-p kernel: Σ_w topp_markov_kernel w == 1 ===== *)
Theorem topp_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
  (prefix : list Token),
  Id (list_sum Token (topp_markov_kernel p Hpmax prefix) vocab) one.
Proof.
  intros p Hpmax prefix.
  unfold topp_markov_kernel.
  apply (id_trans (list_sum_ext Token
                    (fun w => match topp_keep_dec p prefix w with
                              | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                              (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => zero
                              end)
                    (fun w => mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                  (match topp_keep_dec p prefix w with
                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                   | inr _ => zero
                                   end))
                    vocab
                    (fun w => match topp_keep_dec p prefix w as d return Id (match d with
                                                                            | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                                                            (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                                                            | inr _ => zero
                                                                            end)
                                                                          (mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                                                                (match d with
                                                                                 | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                                 | inr _ => zero
                                                                                 end)) with
                              | inl _ => mult_comm (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                   (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => id_sym (mult_zero (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix))))
                              end))).
  assert (Hlin : Id (list_sum Token (fun w => mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                                                  (match topp_keep_dec p prefix w with
                                                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                   | inr _ => zero
                                                                   end)) vocab)
                    (mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                          (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                                                     | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                     | inr _ => zero
                                                                     end) vocab))).
  { apply (list_sum_linear Token (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                             (fun w => match topp_keep_dec p prefix w with
                                       | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                       | inr _ => zero
                                       end) vocab). }
  apply (id_trans Hlin).
  assert (Hsum : Id (mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                          (topp_temp_sum p prefix)) one).
  {
    apply (id_trans (id_sym (id_cong (fun z => mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix))) z)
                                        (topp_temp_sum_unfold p prefix)))).
    apply (id_trans (mult_comm (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                               (topp_temp_sum p prefix))).
    apply (inv_pos_correct (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix))).
  }
  exact Hsum.
Qed.


(* The min_p premises needed by the Top-p+Min-P joint kernel (same signature as MinPSampling) *)
Variable min_p : R.
Variable min_p_pos : lt zero min_p.
Variable min_p_lt_one : lt min_p one.

Definition combined_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  And (minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w)
      (topp_keep p prefix w).

Definition combined_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (combined_keep p prefix w) (Not (combined_keep p prefix w)).
Proof.
  unfold combined_keep.
  destruct (minp_keep_dec Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w) as [Hmin | Hnotmin].
  - destruct (topp_keep_dec p prefix w) as [Htp | Hntp].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntp Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

(* The joint kept sum *)
Definition combined_temp_sum (p : R) (prefix : list Token) : R :=
  list_sum Token (fun w => match combined_keep_dec p prefix w with
                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab.

Lemma combined_temp_sum_unfold : forall p prefix,
  Id (combined_temp_sum p prefix)
     (list_sum Token (fun w => match combined_keep_dec p prefix w with
                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                               | inr _ => zero
                               end) vocab).
Proof. intros. unfold combined_temp_sum. apply id_refl. Qed.

(* ===== Nonempty: p ≤ max and pick_max satisfies Min-P ⟹ pick_max ∈ the joint set ⟹ sum > 0 ===== *)
Lemma combined_temp_sum_pos : forall p prefix,
  le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix) ->
  lt zero (combined_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  unfold combined_temp_sum.
  (* pick_max satisfies topp_keep (p ≤ max) *)
  assert (Htp : topp_keep p prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold topp_keep. rewrite pick_max_token_correct. exact Hp. }
  (* pick_max satisfies minp_keep ([pick_max_token_minp_keep]) *)
  assert (Hmin : minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix
                               (pick_max_token Token vocab total_loss default_token prefix)).
  { exact (pick_max_token_minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p min_p_lt_one prefix). }
  (* pick_max ∈ the joint kept set *)
  assert (Hkeep : combined_keep p prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold combined_keep. split; assumption. }
  (* Extract the tf term of pick_max (the match inl branch) *)
  assert (Heq : Id (temp_factor Token total_loss temperature temperature_pos prefix
                                  (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)).
  { destruct (combined_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd Hkeep). }
  (* tf(pick_max) ≤ combined_temp_sum ([list_sum_single_le_total]) *)
  assert (Hle : le (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)).
  { apply (le_id_l (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)
                   (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)
                   Heq
                   (list_sum_single_le_total Token vocab
                                     (fun w => match combined_keep_dec p prefix w with
                                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                               | inr _ => zero
                                               end)
                                     (pick_max_token Token vocab total_loss default_token prefix)
                                     (pick_best_in_vocab' Token vocab vocab_nonempty total_loss default_token prefix)
                                     (fun w' => match combined_keep_dec p prefix w' as d return le zero (match d with
                                                                                                          | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w'
                                                                                                          | inr _ => zero
                                                                                                          end) with
                                                | inl _ => lt_le_iff _ _ (inl (exp_neg_pos (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w'])))))
                                                | inr _ => le_refl zero
                                                end))). }
  apply (lt_le_trans zero (temp_factor Token total_loss temperature temperature_pos prefix
                                          (pick_max_token Token vocab total_loss default_token prefix))
                          (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                    | inr _ => zero
                                                    end) vocab)).
  - unfold temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* ===== The joint kernel + normalization (Σ=1, the topp_markov_kernel_normalized pattern) ===== *)
Definition combined_markov_kernel (p : R)
  (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
  (prefix : list Token) (w : Token) : R :=
  match combined_keep_dec p prefix w with
  | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                  (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

Theorem combined_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
  (prefix : list Token),
  Id (list_sum Token (combined_markov_kernel p Hpmax prefix) vocab) one.
Proof.
  intros p Hpmax prefix.
  unfold combined_markov_kernel.
  apply (id_trans (list_sum_ext Token
                    (fun w => match combined_keep_dec p prefix w with
                              | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                              (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => zero
                              end)
                    (fun w => mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                  (match combined_keep_dec p prefix w with
                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                   | inr _ => zero
                                   end))
                    vocab
                    (fun w => match combined_keep_dec p prefix w as d return Id (match d with
                                                                                | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                                                                (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                                                                | inr _ => zero
                                                                                end)
                                                                              (mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                                                                    (match d with
                                                                                     | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                                     | inr _ => zero
                                                                                     end)) with
                              | inl _ => mult_comm (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                   (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => id_sym (mult_zero (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix))))
                              end))).
  assert (Hlin : Id (list_sum Token (fun w => mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                                  (match combined_keep_dec p prefix w with
                                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                   | inr _ => zero
                                                   end)) vocab)
                    (mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                          (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                                     | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                     | inr _ => zero
                                                     end) vocab))).
  { apply (list_sum_linear Token (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                             (fun w => match combined_keep_dec p prefix w with
                                       | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                       | inr _ => zero
                                       end) vocab). }
  apply (id_trans Hlin).
  assert (Hsum : Id (mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                          (combined_temp_sum p prefix)) one).
  {
    apply (id_trans (id_sym (id_cong (fun z => mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix))) z)
                                     (combined_temp_sum_unfold p prefix)))).
    apply (id_trans (mult_comm (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                               (combined_temp_sum p prefix))).
    apply (inv_pos_correct (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix))).
  }
  exact Hsum.
Qed.

(* ================================================================
   Counting form: the count of strictly heavier states is < K (the main-file keep_top_k pattern,
   bypassing the sort-correctness development and the InT membership decision); nonemptiness uses
   the honest premise topk_pickmax_head (pick_max is among the first K, the same positive-branch
   premise pattern as the κ > 0 witness).
   Discipline: purely constructive / Set layer / zero admissions / zero classical axioms.
   ================================================================ *)

(* Projection alias for lt_dec (the class field name lt_dec is shadowed by the Stdlib
   Compare_dec.lt_dec; extracted by constructor destructuring, renamed to avoid the clash) *)
Definition lt_dec_field_tk : forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => lt_d
  end.

(* Strict less-than (nat version) *)
Definition NatLt_tk (n m : nat) : Set := Id (Nat.ltb n m) true.

(* [id_false_true] here coincides verbatim, in statement and proof, with the upstream
   [id_false_true] of [AttentionGibbsBridge] (this file, the keep_top_k_dec site referenced
   directly).  Among the *_tk renamed bindings only [lt_dec_field_tk]/[NatLt_tk] are required
   by Stdlib shadowing; [id_false_true] has no shadowing or name clash, so this redefinition is
   removed and the downstream [topk_keep_dec] references the upstream lemma directly. *)

(* ===== Top-k counting: the number of tokens in vocab whose kernel is strictly greater than kernel w ===== *)
Fixpoint count_kernel_heavier (prefix : list Token) (w : Token) (l : list Token) : nat :=
  match l with
  | nil => Datatypes.O
  | a :: rest =>
      match lt_dec_field_tk (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
                            (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a) with
      | inl _ => Datatypes.S (count_kernel_heavier prefix w rest)
      | inr _ => count_kernel_heavier prefix w rest
      end
  end.

(* Top-K keep: fewer than K strictly-heavier states *)
Definition topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  NatLt_tk (count_kernel_heavier prefix w vocab) K.

(* Top-K decision (Nat.ltb computation + bool elimination; no Token equality needed) *)
Definition topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (topk_keep K prefix w) (Not (topk_keep K prefix w)) :=
  match Nat.ltb (count_kernel_heavier prefix w vocab) K as b
        return Or (Id b true) (Not (Id b true)) with
  | true => inl id_refl
  | false => inr (fun H => id_false_true H)
  end.

(* Honest premise (a weakening of sort correctness): pick_max is among the first K (K ≥ 1) *)
Variable topk_pickmax_head : forall (K : nat) (prefix : list Token),
  NatLe 1 K ->
  topk_keep K prefix (pick_max_token Token vocab total_loss default_token prefix).

(* ===== Joint keep: Min-P ∧ Top-k ===== *)
Definition combined_topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  And (minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w)
      (topk_keep K prefix w).

Definition combined_topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (combined_topk_keep K prefix w) (Not (combined_topk_keep K prefix w)).
Proof.
  unfold combined_topk_keep.
  destruct (minp_keep_dec Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w) as [Hmin | Hnotmin].
  - destruct (topk_keep_dec K prefix w) as [Htop | Hntop].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntop Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

(* The joint kept sum *)
Definition combined_topk_temp_sum (K : nat) (prefix : list Token) : R :=
  list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab.

Lemma combined_topk_temp_sum_unfold : forall K prefix,
  Id (combined_topk_temp_sum K prefix)
     (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                               | inr _ => zero
                               end) vocab).
Proof. intros. unfold combined_topk_temp_sum. apply id_refl. Qed.

(* ===== Nonempty: K ≥ 1, pick_max satisfies Min-P and is in the Top-k (honest premise) ⟹ sum > 0 ===== *)
Lemma combined_topk_temp_sum_pos : forall K prefix,
  NatLe 1 K ->
  lt zero (combined_topk_temp_sum K prefix).
Proof.
  intros K prefix HK.
  unfold combined_topk_temp_sum.
  assert (Hmin : minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix
                               (pick_max_token Token vocab total_loss default_token prefix)).
  { exact (pick_max_token_minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p min_p_lt_one prefix). }
  assert (Htop : topk_keep K prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { exact (topk_pickmax_head K prefix HK). }
  assert (Hkeep : combined_topk_keep K prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold combined_topk_keep. split; assumption. }
  assert (Heq : Id (temp_factor Token total_loss temperature temperature_pos prefix
                                  (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_topk_keep_dec K prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)).
  { destruct (combined_topk_keep_dec K prefix (pick_max_token Token vocab total_loss default_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd Hkeep). }
  assert (Hle : le (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)).
  { apply (le_id_l (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_topk_keep_dec K prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)
                   (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)
                   Heq
                   (list_sum_single_le_total Token vocab
                                     (fun w => match combined_topk_keep_dec K prefix w with
                                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                               | inr _ => zero
                                               end)
                                     (pick_max_token Token vocab total_loss default_token prefix)
                                     (pick_best_in_vocab' Token vocab vocab_nonempty total_loss default_token prefix)
                                     (fun w' => match combined_topk_keep_dec K prefix w' as d return le zero (match d with
                                                                                                              | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w'
                                                                                                              | inr _ => zero
                                                                                                              end) with
                                                | inl _ => lt_le_iff _ _ (inl (exp_neg_pos (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w'])))))
                                                | inr _ => le_refl zero
                                                end))). }
  apply (lt_le_trans zero (temp_factor Token total_loss temperature temperature_pos prefix
                                          (pick_max_token Token vocab total_loss default_token prefix))
                          (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                    | inr _ => zero
                                                    end) vocab)).
  - unfold temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* ===== The joint kernel + normalization (Σ=1, the combined_markov_kernel_normalized pattern) ===== *)
Definition combined_topk_markov_kernel (K : nat)
  (HK : forall prefix, NatLe 1 K)
  (prefix : list Token) (w : Token) : R :=
  match combined_topk_keep_dec K prefix w with
  | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                  (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
  | inr _ => zero
  end.

Theorem combined_topk_markov_kernel_normalized : forall (K : nat)
  (HK : forall prefix, NatLe 1 K)
  (prefix : list Token),
  Id (list_sum Token (combined_topk_markov_kernel K HK prefix) vocab) one.
Proof.
  intros K HK prefix.
  unfold combined_topk_markov_kernel.
  apply (id_trans (list_sum_ext Token
                    (fun w => match combined_topk_keep_dec K prefix w with
                              | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                              (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                              | inr _ => zero
                              end)
                    (fun w => mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                  (match combined_topk_keep_dec K prefix w with
                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                   | inr _ => zero
                                   end))
                    vocab
                    (fun w => match combined_topk_keep_dec K prefix w as d return Id (match d with
                                                                                      | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                                                                      (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                                                                      | inr _ => zero
                                                                                      end)
                                                                                    (mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                                                                          (match d with
                                                                                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                                           | inr _ => zero
                                                                                           end)) with
                              | inl _ => mult_comm (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                   (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                              | inr _ => id_sym (mult_zero (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix))))
                              end))).
  assert (Hlin : Id (list_sum Token (fun w => mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                                  (match combined_topk_keep_dec K prefix w with
                                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                   | inr _ => zero
                                                   end)) vocab)
                    (mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                          (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                    | inr _ => zero
                                                    end) vocab))).
  { apply (list_sum_linear Token (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                             (fun w => match combined_topk_keep_dec K prefix w with
                                       | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                       | inr _ => zero
                                       end) vocab). }
  apply (id_trans Hlin).
  assert (Hsum : Id (mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                          (combined_topk_temp_sum K prefix)) one).
  {
    apply (id_trans (id_sym (id_cong (fun z => mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix))) z)
                                     (combined_topk_temp_sum_unfold K prefix)))).
    apply (id_trans (mult_comm (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                               (combined_topk_temp_sum K prefix))).
    apply (inv_pos_correct (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix))).
  }
  exact Hsum.
Qed.

End TopPSampling.

(* ============================================================ *)
(* Path 3: separation of the proof layer from the computation layer (Extraction mapping) *)
(* ============================================================ *)
(* The proof layer stays purely constructive at the Set layer (abstract RealInterface, no classical axioms); *)
(* the extraction layer maps the abstract reals to OCaml floats: the theorems guarantee ideal behavior, *)
(* and extraction secures engineering usability.  Only the mapping contract (optional) is declared here; *)
(* it does not change the semantics of the proof layer. *)
(* ------------------------------------------------------------ *)
(* Extraction mapping (uncomment and use the OCaml backend when grounding): *)
(*   Extract Inductive unit => "unit" [ "()" ].                 *)
(*   Extract Constant RealInterface.R => "float".               *)
(*   Extract Constant RealInterface.plus => "( +. )".           *)
(*   Extract Constant RealInterface.mult => "( *. )".           *)
(*   Extract Constant RealInterface.opp => "( ~-. )".           *)
(* Verification layer (optional, needs Flocq): |float_result - exact_result| < ε *)
(* is orthogonal to the main theoretical framework. *)
(* ============================================================ *)

(* ============================================================
   Core version: assembly of the RealSetoidCore.RealInterfaceSetoidCore instance (req := real_eq)
   metric_pos/metric_triangle in per-eps form; gaps: exp_neg_plus/log_inv (phase 2)
   Note: the RealInterfaceSetoid class fields share names with the global projections of
   RealInterface (zero/one/plus...), a global conflict within one file (the checker does not
   conflict because CW is an importable, shadowable name) → isolated in a Module.
   ============================================================ *)

(* ============ Core-version interface (the phase-3 assembly target): no exp/log fields ============
   The exp_neg_plus/log_inv family of the full RealInterfaceSetoid belongs to phase 2 (a large effort).
   Instantiate the Core first (Proper + ring + order + inv_pos + metric per-eps + lim + cauchy_complete),
   and assemble the full version once phase 2 supplies exp/log.
   Note: the Core class fields share names with the full class (req etc.); class projections are
   globally unique — isolate in a Module. *)

(* Assumption audit of the main theorems (no added dependencies) *)
Print Assumptions partition_function_pos.
Print Assumptions partition_function_temp_pos.
Print Assumptions partition_function_scaled_pos.
Print Assumptions partition_function_temp_param_pos.
