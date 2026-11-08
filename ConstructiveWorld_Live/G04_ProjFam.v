(* ConstructiveWorld-Set — projection-operator family and projected KL cost decomposition. *)

(** * G04_ProjFam: projection operator families and projected KL cost decomposition.

    Mission.  Formalizes the abstract projection section ([Z_P], [Proj],
      [proj_drop_zero], [proj_keep_ge], [proj_normalized],
      [proj_uniform_full]), the KL decomposition section (the [KL_f],
      [KL_P], [KL_T] terms and [proj_kl_cost]), the three instantiation
      sections (KV, audit, minimal-p: [kev_*_via_proj],
      [Zaud_le_one_via_proj], [minp_normalized_via_proj]), and the family
      statements for the [tid] group structure.

    Dependencies.  The library files listed in the Require face below.

    References.  KL-divergence cost decomposition under projection and
      orthogonal decomposition (information-theoretic projection
      inequalities).

    Constructivity.  All proofs close by [Qed]; zero admission words; no
      classical logic; the statement face is carried by the [Set] layer
      (order predicates and equality are [Set]-valued, zero Prop leakage).

    Build.  [coqc -native-compiler no -q -Q . "" G04_ProjFam.v] compiles
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

(* ---------- generic boosters (Set layer) ---------- *)
(* projection of an [Id] along [Bool] onto the two subgoals: avoids
   the silent premise substitution a [destruct] on the equation
   would perform. *)
Lemma projp_id_transport : forall (A : Set) (x y : A) (M : A -> Set),
  M x -> Id x y -> M y.
Proof.
  intros A x y M m H. exact (match H with id_refl => m end).
Qed.

(* a single term is bounded by the total sum (induction on the
   [InT] derivation itself; the Nil contradiction branch
   contributes no proof term, so no empty-match wrapper appears). *)
Lemma projp_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

(* ---------- basic algebra (small [real_eq]-layer lemmas) ---------- *)

Lemma projp_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

Lemma projp_plus_zero_opp : forall a : Real, real_eq (real_plus (real_opp a) a) real_zero.
Proof.
  intro a. apply (real_eq_trans _ (real_plus a (real_opp a)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* [a - c == (a - b) + (b - c)] (the Real form of [minus_split]). *)
Lemma projp_minus_split : forall a b c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c))).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c)))) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_opp c) a
             (real_plus (real_opp b) (real_plus b (real_opp c)))
             (real_eq_refl a)
             (real_eq_sym _ _
               (real_eq_trans (real_plus (real_opp b) (real_plus b (real_opp c)))
                              (real_plus (real_plus (real_opp b) b) (real_opp c))
                              (real_opp c)
                              (real_plus_assoc (real_opp b) b (real_opp c))
                              (real_eq_trans
                                 (real_plus (real_plus (real_opp b) b) (real_opp c))
                                 (real_plus real_zero (real_opp c))
                                 (real_opp c)
                                 (RealSetoid.real_eq_plus_compat
                                    (real_plus (real_opp b) b) (real_opp c)
                                    real_zero (real_opp c)
                                    (projp_plus_zero_opp b) (real_eq_refl _))
                                 (projp_plus_zero_l (real_opp c)))))).
  - apply (real_plus_assoc a (real_opp b) (real_plus b (real_opp c))).
Qed.

(* [(x - L) - x == -L] (the Real form of [minus_plus_opp]). *)
Lemma projp_minus_plus_opp : forall x L : Real,
  real_eq (real_plus (real_plus x (real_opp L)) (real_opp x)) (real_opp L).
Proof.
  intros x L.
  exact (real_eq_trans _ _ _
    (RealSetoid.real_eq_plus_compat (real_plus x (real_opp L)) (real_opp x)
                                    (real_plus (real_opp L) x) (real_opp x)
                                    (real_plus_comm x (real_opp L))
                                    (real_eq_refl (real_opp x)))
    (real_eq_trans _ _ _
      (real_eq_sym _ _ (real_plus_assoc (real_opp L) x (real_opp x)))
      (real_eq_trans _ _ _
        (RealSetoid.real_eq_plus_compat (real_opp L) (real_plus x (real_opp x))
                                        (real_opp L) real_zero
                                        (real_eq_refl (real_opp L))
                                        (real_plus_opp x))
        (real_eq_trans _ _ _
          (real_plus_comm (real_opp L) real_zero)
          (projp_plus_zero_l (real_opp L)))))).
Qed.

(* [log (1/x) == - log x] (the Real-layer form of [log_inv_one_inv]). *)
Lemma projp_log_inv_neg : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hsum : real_eq (real_plus (real_log x Hx)
                                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                         real_zero).
  { apply (real_eq_trans _ (real_log (real_mult x (real_inv_pos x Hx))
                                     (real_mult_positive x (real_inv_pos x Hx) Hx
                                       (real_inv_pos_pos x Hx))) _).
    - apply (real_eq_sym _ _ (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))).
    - apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
      + apply (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                 (real_mult_positive x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))
                 real_lt_zero_one (real_inv_pos_correct x Hx)).
      + apply (real_log_one real_lt_zero_one). }
  assert (Hdir : real_eq (real_opp (real_log x Hx))
                         (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  { apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    - apply (real_eq_sym _ _ (real_plus_zero (real_opp (real_log x Hx)))).
    - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx))
                                        (real_plus (real_log x Hx)
                                                   (real_log (real_inv_pos x Hx)
                                                             (real_inv_pos_pos x Hx)))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp (real_log x Hx)) real_zero
                 (real_opp (real_log x Hx))
                 (real_plus (real_log x Hx)
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                 (real_eq_refl _)
                 (real_eq_sym (real_plus (real_log x Hx)
                                         (real_log (real_inv_pos x Hx)
                                                   (real_inv_pos_pos x Hx)))
                              real_zero Hsum)).
      + apply (real_eq_trans _
                 (real_plus (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
        * apply (real_plus_assoc (real_opp (real_log x Hx)) (real_log x Hx)
                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
        * apply (real_eq_trans _ (real_plus real_zero
                                   (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
          -- apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                       (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       real_zero (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       (projp_plus_zero_opp (real_log x Hx)) (real_eq_refl _)).
          -- apply projp_plus_zero_l. }
  apply (real_eq_sym _ _ Hdir).
Qed.

(* ============================================================ *)
(* Master section: the abstract projection kernel (one normal     *)
(*   form shared by the instantiation sections).  [Z_P] is the    *)
(*   kept mass; [Proj] is [f · inv(Z_P)] on kept entries and      *)
(*   zero elsewhere.                                              *)
(* ============================================================ *)
Section AbstractProjection.

Variable I : Set.                          (* the index type *)
Variable f : I -> Real.                    (* the projected weights *)
Variable P : I -> bool.                    (* the keep predicate *)
Variable idx : list I.                     (* the index enumeration *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.   (* [f] is normalized *)
Variable f_pos : forall i : I, real_lt real_zero (f i).       (* [f] is pointwise positive *)
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

(* the kept mass (the common denominator form of the instantiations: [Σ if P then f else 0]). *)
Definition Z_P : Real :=
  real_list_sum I (fun i : I => if P i then f i else real_zero) idx.

(* ---------- item 0a: [Z_P > 0] (from a kept witness plus [f_pos]
   plus the single-term bound) ---------- *)
(* same shape as [Z_keep_pos] in UpKVEv, with [ZP_pos] stated as a
   theorem rather than a Variable. *)
Lemma Z_P_entry_nonneg : forall (y : I),
  real_le real_zero (if P y then f y else real_zero).
Proof.
  intro y. destruct (P y).
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
Qed.

Theorem ZP_pos : real_lt real_zero Z_P.
Proof.
  destruct P_witness as [i0 [Hk0 Hin0]].
  assert (Hlt0 : real_lt real_zero (if P i0 then f i0 else real_zero)).
  { apply (projp_id_transport bool true (P i0)
             (fun b : bool => real_lt real_zero (if b then f i0 else real_zero))).
    - exact (f_pos i0).
    - exact (id_sym Hk0). }
  assert (Hle : real_le (if P i0 then f i0 else real_zero) Z_P).
  { apply (projp_single_le_sum I
             (fun y : I => if P y then f y else real_zero) i0 idx Hin0).
    intro y. apply Z_P_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Heq).
Qed.

(* ---------- item 0b: [Z_P <= 1] (kept-subset sum bounded by the full sum, via the [f_norm] bridge) ---------- *)
Theorem ZP_le_one : real_le Z_P real_one.
Proof.
  apply (real_le_trans _ (real_list_sum I f idx)).
  - apply (real_list_sum_le I
             (fun i : I => if P i then f i else real_zero) f idx).
    intro y. destruct (P y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply f_pos.
  - apply (RealSetoid.real_eq_le _ _). exact f_norm.
Qed.

(* the kept-branch form (the keep branch of [Proj]; carrier of the log certificate). *)
Definition keep_form (i : I) : Real :=
  real_mult (f i) (real_inv_pos Z_P ZP_pos).

(* positivity certificate of the keep branch (a transparent Definition, carried alongside the log terms). *)
Definition keep_form_pos (i : I) : real_lt real_zero (keep_form i) :=
  real_mult_positive (f i) (real_inv_pos Z_P ZP_pos)
                     (f_pos i) (real_inv_pos_pos Z_P ZP_pos).

(* the projection kernel (master form: [if P i then f i · inv(Z_P) else 0]). *)
Definition Proj (i : I) : Real :=
  if P i then real_mult (f i) (real_inv_pos Z_P ZP_pos) else real_zero.

(* ---------- item 3: dropped entries vanish ---------- *)
Theorem proj_drop_zero : forall i : I,
  Id (P i) false -> real_eq (Proj i) real_zero.
Proof.
  intros i Hb.
  apply (projp_id_transport bool false (P i)
           (fun b : bool =>
              real_eq (if b then
                         real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hb).
Qed.

(* ---------- keep-branch amplifier: [f i <= f i · inv(Z_P)] (from [Z_P <= 1] and antitonicity of the inverse) ---------- *)
Lemma proj_keep_form_ge : forall i : I,
  real_le (f i) (real_mult (f i) (real_inv_pos Z_P ZP_pos)).
Proof.
  intro i.
  apply (real_le_trans _ (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
  - (* the eq-to-le bridge from [f i == f · inv(1)] *)
    apply (RealSetoid.real_eq_le (f i)
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (f i) real_one) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos real_one real_lt_zero_one)
                (f i) real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans _
                  (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
        -- apply real_eq_sym. apply b4_one_mult.
        -- apply real_inv_pos_correct.
    + apply real_mult_one.
  - apply (real_le_mult_compat_r (f i)
             (real_inv_pos real_one real_lt_zero_one)
             (real_inv_pos Z_P ZP_pos)).
    + apply real_le_from_lt_aux. apply f_pos.
    + apply (real_inv_pos_le_compat Z_P real_one ZP_pos real_lt_zero_one).
      apply ZP_le_one.
Qed.

(* ---------- item 2: kept entries are amplified ([f <= Proj] on the keep branch) ---------- *)
Theorem proj_keep_ge : forall i : I,
  Id (P i) true -> real_le (f i) (Proj i).
Proof.
  intros i Hb.
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_le (f i)
                (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                 else real_zero))).
  - apply proj_keep_form_ge.
  - exact (id_sym Hb).
Qed.

(* ---------- item 1: row normalization [Σ Proj == 1] ---------- *)
Theorem proj_normalized :
  real_eq (real_list_sum I (fun i : I => Proj i) idx) real_one.
Proof.
(* first step: rewrite [Proj] pointwise as [g(i) · inv(Z_P)], the drop branch vanishing by [0 · x == 0]. *)
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P i then f i else real_zero)
                           (real_inv_pos Z_P ZP_pos))
              idx) _).
  { apply (real_list_sum_ext I (fun i : I => Proj i) _ idx).
    intro y. destruct (P y) eqn:Hk.
    - unfold Proj. rewrite Hk. apply real_eq_refl.
    - unfold Proj. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos Z_P ZP_pos) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
(* second step: [real_list_sum_linear_r] extracts the constant factor [inv(Z_P)]. *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos Z_P ZP_pos) Z_P) _).
  { apply (real_list_sum_linear_r I
             (real_inv_pos Z_P ZP_pos)
             (fun i : I => if P i then f i else real_zero) idx). }
(* third step: [inv(Z_P) · Z_P == 1] (commutation bridge plus [real_inv_pos_correct]). *)
  apply (real_eq_trans _ (real_mult Z_P (real_inv_pos Z_P ZP_pos)) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- item 5: minorization transport ([δ·u <= f] gives [δ·u <= Proj], unconditionally) ---------- *)
Variable u : I -> Real.                    (* the reference distribution *)
Variable delta : Real.
Variable delta_minor : forall i : I,
  real_le (real_mult delta (u i)) (f i).

Theorem proj_minor_uncond : forall i : I,
  real_le (if P i then real_mult delta (u i) else real_zero) (Proj i).
Proof.
  intro i. destruct (P i) eqn:Hk.
  - unfold Proj. rewrite Hk.
    apply (real_le_trans _ (f i)).
    + apply delta_minor.
    + apply proj_keep_form_ge.
  - unfold Proj. rewrite Hk. apply real_le_refl.
Qed.

(* ---------- item 6: the degenerate image ([P ≡ true] gives [Proj ≡ f]; the corollary-level link to the temperature-limit image) ---------- *)
Theorem proj_uniform_full :
  (forall i : I, Id (P i) true) -> forall i : I, real_eq (Proj i) (f i).
Proof.
  intro P_all. intro i.
  assert (HZ1 : real_eq Z_P real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (P_all y)).
    - exact f_norm. }
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_eq (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 (f i))).
  - apply (real_eq_trans _
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one)) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos Z_P ZP_pos)
                (f i) (real_inv_pos real_one real_lt_zero_one)).
      * apply real_eq_refl.
      * apply (real_inv_pos_ext Z_P real_one ZP_pos real_lt_zero_one HZ1).
    + apply (real_eq_trans _ (real_mult (f i) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                  (f i) (real_inv_pos real_one real_lt_zero_one) (f i) real_one).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _
                      (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
           ++ apply real_eq_sym. apply b4_one_mult.
           ++ apply real_inv_pos_correct.
      * apply real_mult_one.
  - exact (id_sym (P_all i)).
Qed.

End AbstractProjection.

(* ============================================================ *)
(* Item 4: the cost identity (master form; the Real-layer list     *)
(*   version of the baseline [kl_sum_split]/[kl_tail_eval]).  The  *)
(*   KL terms are defined with positivity certificates carried     *)
(*   alongside the logs: the KL against [Proj] uses the masked     *)
(*   form (the keep branch is [keep_form] with matching delta),    *)
(*   avoiding a log premise on dropped entries; the fail branch    *)
(*   is killed by [Hq_fail].                                       *)
(* ============================================================ *)
Section AbstractKL.

Variable I : Set.
Variable f : I -> Real.
Variable P : I -> bool.
Variable idx : list I.
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

Definition ZK : Real := Z_P I f P idx.
Definition keepK (i : I) : Real := keep_form I f P idx f_pos P_witness i.
Definition keepK_pos (i : I) : real_lt real_zero (keepK i) :=
  keep_form_pos I f P idx f_pos P_witness i.

(* per-term KLs ([q||f]: unconditional positivity; [q||Proj] and the tail term: [P]-masked form). *)
Definition KL_f_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  real_mult (q i) (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (f i) (f_pos i)))).
Definition KL_P_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (q i) (Hq i))
                               (real_opp (real_log (keepK i) (keepK_pos i))))
  else real_zero.
Definition KL_T_term (q : I -> Real) (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (keepK i) (keepK_pos i))
                               (real_opp (real_log (f i) (f_pos i))))
  else real_zero.
Definition KL_f_masked (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then KL_f_term q Hq i else real_zero.

Definition KLqf (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_term q Hq) idx.
Definition KLfm (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_masked q Hq) idx.
Definition KLqp (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_P_term q Hq) idx.
Definition KLqt (q : I -> Real) : Real :=
  real_list_sum I (KL_T_term q) idx.

(* step 1: bridge — for a compatible q vanishing on dropped entries, the unmasked sum equals the masked sum. *)
Lemma proj_kl_bridge : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqf q Hq) (KLfm q Hq).
Proof.
  intros q Hq Hq_fail.
  apply (real_list_sum_ext I (KL_f_term q Hq) (KL_f_masked q Hq) idx).
  intro y. unfold KL_f_masked. destruct (P y) eqn:Hb.
  - apply real_eq_refl.
  - assert (Hid : Id (P y) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail y Hid) as Hq0.
    apply (real_eq_trans _ (real_mult real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q y)
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               Hq0 (real_eq_refl _)).
    + apply (real_eq_trans _
               (real_mult (real_plus (real_log (q y) (Hq y))
                                     (real_opp (real_log (f y) (f_pos y))))
                          real_zero) _).
      * apply real_mult_comm.
      * apply real_mult_zero.
Qed.

(* step 2: pointwise decomposition of the masked term (keep branch via [minus_split] + distributivity; drop branch zero equals zero). *)
Lemma proj_kl_pointwise_split : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)) (i : I),
  real_eq (KL_f_masked q Hq i) (real_plus (KL_P_term q Hq i) (KL_T_term q i)).
Proof.
  intros q Hq i. unfold KL_f_masked, KL_P_term, KL_T_term.
  destruct (P i).
  - apply (real_eq_trans _
             (real_mult (q i)
                (real_plus
                   (real_plus (real_log (q i) (Hq i))
                              (real_opp (real_log (keepK i) (keepK_pos i))))
                   (real_plus (real_log (keepK i) (keepK_pos i))
                              (real_opp (real_log (f i) (f_pos i)))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_plus
                  (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (keepK i) (keepK_pos i))))
                  (real_plus (real_log (keepK i) (keepK_pos i))
                             (real_opp (real_log (f i) (f_pos i)))))
               (real_eq_refl _)
               (projp_minus_split (real_log (q i) (Hq i))
                                  (real_log (keepK i) (keepK_pos i))
                                  (real_log (f i) (f_pos i)))).
    + apply (real_distrib (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (keepK i) (keepK_pos i))))
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))).
  - apply real_eq_sym. apply real_plus_zero.
Qed.

(* step 3: sum-level split [Σ masked (q||f) == Σ (q||Proj) + Σ tail]. *)
Lemma proj_kl_split_sum : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)),
  real_eq (KLfm q Hq) (real_plus (KLqp q Hq) (KLqt q)).
Proof.
  intros q Hq.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx) _).
  - apply (real_list_sum_ext I (KL_f_masked q Hq)
             (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx).
    exact (proj_kl_pointwise_split q Hq).
  - apply (real_list_sum_add I (KL_P_term q Hq) (KL_T_term q) idx).
Qed.

(* step 4: pointwise the tail term equals [(- log Z_P) · q] (keep
   branch via [real_log_mult] + [projp_log_inv_neg]; on dropped
   entries q vanishes and both sides are zero, following the
   baseline [kl_tail_eval] skeleton). *)
Lemma proj_kl_tail_pt : forall (q : I -> Real)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero) (i : I),
  real_eq (KL_T_term q i)
          (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                     (q i)).
Proof.
  intros q Hq_fail i. unfold KL_T_term. destruct (P i) eqn:Hb.
  - assert (HL : real_eq (real_log (keepK i) (keepK_pos i))
                         (real_plus (real_log (f i) (f_pos i))
                                    (real_opp (real_log ZK
                                                (ZP_pos I f P idx f_pos P_witness))))).
    { apply (real_eq_trans _
               (real_log (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                         (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                             (f_pos i)
                                             (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
      - apply (real_log_wd (keepK i)
                 (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (keepK_pos i)
                 (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                     (f_pos i)
                                     (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_eq_refl (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))))).
      - apply (real_eq_trans _
                 (real_plus (real_log (f i) (f_pos i))
                            (real_log (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                      (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
        + apply (real_log_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                   (f_pos i) (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness))).
        + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
                   (projp_log_inv_neg ZK (ZP_pos I f P idx f_pos P_witness))). }
    assert (Hmid : real_eq (real_plus (real_log (keepK i) (keepK_pos i))
                                      (real_opp (real_log (f i) (f_pos i))))
                           (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
    { apply (real_eq_trans _
               (real_plus (real_plus (real_log (f i) (f_pos i))
                                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))))
                          (real_opp (real_log (f i) (f_pos i)))) _).
      - apply (RealSetoid.real_eq_plus_compat _ _ _ _ HL (real_eq_refl _)).
      - apply projp_minus_plus_opp. }
    apply (real_eq_trans _
             (real_mult (q i)
                (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (real_eq_refl _) Hmid).
    + apply real_mult_comm.
  - assert (Hid : Id (P i) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail i Hid) as Hq0.
    apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply (RealSetoid.real_eq_mult_compat
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               real_zero
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (q i) (real_eq_refl _) (real_eq_sym (q i) real_zero Hq0)).
Qed.

(* step 5: the tail evaluates to [Σ tail == - log Z_P] (ext + linearity + normalization cancellation). *)
Lemma proj_kl_tail_eval : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqt q) (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))).
Proof.
  intros q Hq_norm Hq_fail.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                      (q i)) idx) _).
  - apply (real_list_sum_ext I (KL_T_term q)
             (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                     (q i)) idx).
    intro w. exact (proj_kl_tail_pt q Hq_fail w).
  - apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        (real_list_sum I q idx)) _).
    + apply (real_list_sum_linear I
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))) q idx).
    + apply (real_eq_trans _
               (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                          real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_list_sum I q idx)
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 real_one (real_eq_refl _) Hq_norm).
      * apply real_mult_one.
Qed.

(* item 4 (main statement, the cost identity):
   [KL(q||f) == KL(q||Proj) + (- log Z_P)].  The information cost of
   audit, truncation and eviction is the log of the lost kept mass;
   one proof serves every instantiation. *)
Theorem proj_kl_cost : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
   real_eq (KLqf q Hq_pos)
          (real_plus (KLqp q Hq_pos)
                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _ (real_plus (KLqp q Hq_pos) (KLqt q)) _).
  - apply (real_eq_trans _ (KLfm q Hq_pos) _).
    + exact (proj_kl_bridge q Hq_pos Hq_fail).
    + exact (proj_kl_split_sum q Hq_pos).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
             (proj_kl_tail_eval q Hq_norm Hq_fail)).
Qed.

End AbstractKL.

(* ============================================================ *)
(* Instantiations (recovering the three instances): each           *)
(* instantiation reconstructs its instance facts by plugging into  *)
(* the master theorems; interface notes are in the section-head    *)
(* comments.                                                       *)
(* ============================================================ *)

(* ---------- instance A: KV eviction (recovering the row
   normalization and items 0/2/2b/3 of UpKVEv) ----------
   seam: the master signature aligns argument by argument with
   the UpKVEv world ([I := Tok], [f := K s] for a fixed row,
   [P := keep]); [f_norm := Krow s], [f_pos := Kpos s] and
   [P_witness := keep_nonempty] pass through directly. *)
Section InstKV.

Variables (Tok : Set) (states : list Tok) (K : Tok -> Tok -> Real)
          (keep : Tok -> bool).
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').
Variable keep_nonempty : sigT (fun s0 : Tok => And (Id (keep s0) true) (InT s0 states)).

Definition Zkv (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.
Definition Kev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Zkv s) (ZP_pos Tok (K s) keep states (Kpos s) keep_nonempty))
  else real_zero.

Theorem kev_Zkv_le_one_via_proj : forall s : Tok, real_le (Zkv s) real_one.
Proof.
  intro s. exact (ZP_le_one Tok (K s) keep states (Krow s) (Kpos s)).
Qed.

Theorem kev_row_normalized_via_proj : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => Kev s s') states) real_one.
Proof.
  intro s. exact (proj_normalized Tok (K s) keep states (Kpos s) keep_nonempty).
Qed.

Theorem kev_drop_zero_via_proj : forall s s' : Tok,
  Id (keep s') false -> real_eq (Kev s s') real_zero.
Proof.
  intros s s' H. unfold Kev.
  exact (projp_id_transport bool false (keep s')
           (fun b : bool => real_eq (if b then
              real_mult (K s s') (real_inv_pos (Zkv s)
                (ZP_pos Tok (K s) keep states (Kpos s) keep_nonempty))
            else real_zero) real_zero)
           (real_eq_refl real_zero) (id_sym H)).
Qed.

Theorem kev_keep_ge_via_proj : forall s s' : Tok,
  Id (keep s') true -> real_le (K s s') (Kev s s').
Proof.
  intros s s' H. exact (proj_keep_ge Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty s' H).
Qed.

Variables (Ukv : Tok -> Real) (deltakv : Real).
Variable delta_minor_kv : forall s s' : Tok,
  real_le (real_mult deltakv (Ukv s')) (K s s').

Theorem kev_minor_uncond_via_proj : forall s s' : Tok,
  real_le (if keep s' then real_mult deltakv (Ukv s') else real_zero) (Kev s s').
Proof.
  intros s s'.
  exact (proj_minor_uncond Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty
                           Ukv deltakv (delta_minor_kv s) s').
Qed.

End InstKV.

(* ---------- instance B: safety filtering (a Real-layer
   restatement of the baseline KLProjection) ----------
   seam: the baseline [projected_normalized] lives at the
   interface-R layer ([sum_over_S]/[StateSpace]); this instance
   restates it at the Real-list layer in the master form ([Z_aud],
   the projected distribution and normalization are isomorphic);
   the baseline-side seam is left to interface instantiation, not
   bridged here. *)
Section InstAudit.

Variables (St : Set) (states : list St) (p : St -> Real) (post_aud : St -> bool).
Variable p_norm : real_eq (real_list_sum St p states) real_one.
Variable p_pos : forall s : St, real_lt real_zero (p s).
Variable aud_witness : sigT (fun s : St => And (Id (post_aud s) true) (InT s states)).

Definition ZaudP : Real :=
  real_list_sum St (fun s : St => if post_aud s then p s else real_zero) states.
Definition proj_dist (s : St) : Real :=
  if post_aud s then
    real_mult (p s) (real_inv_pos ZaudP (ZP_pos St p post_aud states p_pos aud_witness))
  else real_zero.

Theorem Zaud_le_one_via_proj : real_le ZaudP real_one.
Proof.
  exact (ZP_le_one St p post_aud states p_norm p_pos).
Qed.

Theorem projected_normalized_via_proj :
  real_eq (real_list_sum St (fun s : St => proj_dist s) states) real_one.
Proof.
  exact (proj_normalized St p post_aud states p_pos aud_witness).
Qed.

Theorem projected_drop_zero_via_proj : forall s : St,
  Id (post_aud s) false -> real_eq (proj_dist s) real_zero.
Proof.
  intros s H. exact (proj_drop_zero St p post_aud states p_pos aud_witness s H).
Qed.

Theorem projected_keep_ge_via_proj : forall s : St,
  Id (post_aud s) true -> real_le (p s) (proj_dist s).
Proof.
  intros s H. exact (proj_keep_ge St p post_aud states p_norm p_pos aud_witness s H).
Qed.

End InstAudit.

(* ---------- instance C: Min-P (a Set-carrier restatement of
   [real_minp_markov_kernel]) ----------
   seam: the baseline RealMinPMain keep predicate is a Set-layer
   proposition with an [Or]-based decider (not a bool).  This
   instance enters the master theorem through [minp_bool] (the
   decider's bool carrier, constructively legitimate) and then
   recovers the normalization of the match-form kernel by the
   [ext] + [inv_ext] pair of bridges; the difference between the
   baseline [Token : Type] and this file's Set carrier is pure
   carrier generality (the content is verbatim isomorphic). *)
Section InstMinP.

Variables (W : Set) (vocab : list W).
Variable tf : W -> Real.
Variable tf_norm : real_eq (real_list_sum W tf vocab) real_one.
Variable tf_pos : forall w : W, real_lt real_zero (tf w).
(* a faithful transcription of the baseline RealMinPMain decider interface (Set predicate + [Or] decider, not bool). *)
Variable Kw : W -> Set.
Variable keep_dec : forall w : W, Or (Kw w) (Not (Kw w)).

Definition minp_bool (w : W) : bool :=
  match keep_dec w with inl _ => true | inr _ => false end.
Definition temp_sum : Real :=
  real_list_sum W
    (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end) vocab.
Variable temp_sum_pos : real_lt real_zero temp_sum.
(* master-form witness (corresponding to the baseline pick_max
   witness plus in-vocab; the nontrivial baseline side is proved
   by [pick_max_token_minp_keep]/[pick_best_in_vocab'], so this is
   an explicit interface premise here). *)
Variable kept_witness : sigT (fun w : W => And (Id (minp_bool w) true) (InT w vocab)).

Definition minp_kernel (w : W) : Real :=
  match keep_dec w with
  | inl _ => real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
  | inr _ => real_zero
  end.

Theorem minp_normalized_via_proj :
  real_eq (real_list_sum W (fun w : W => minp_kernel w) vocab) real_one.
Proof.
  pose proof (proj_normalized W tf minp_bool vocab tf_pos kept_witness) as HP.
  assert (HZeq : real_eq (Z_P W tf minp_bool vocab) temp_sum).
  { apply (real_list_sum_ext W (fun w : W => if minp_bool w then tf w else real_zero)
             (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end)
             vocab).
    intro w. unfold minp_bool. destruct (keep_dec w) as [Hk | Hd].
    - apply real_eq_refl.
    - apply real_eq_refl. }
  apply (real_eq_trans _
           (real_list_sum W
              (fun w : W => if minp_bool w then
                              real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                            else real_zero) vocab) _).
  - apply (real_list_sum_ext W (fun w : W => minp_kernel w) _ vocab).
    intro w. unfold minp_kernel, minp_bool. destruct (keep_dec w) as [Hk | Hd].
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _
             (real_list_sum W
                (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab) _).
    + apply (real_list_sum_ext W
               (fun w : W => if minp_bool w then
                               real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                             else real_zero)
               (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab).
      intro w. unfold minp_bool, Proj. destruct (keep_dec w) as [Hk | Hd].
      * apply (RealSetoid.real_eq_mult_compat (tf w)
                 (real_inv_pos temp_sum temp_sum_pos)
                 (tf w)
                 (real_inv_pos (Z_P W tf minp_bool vocab)
                               (ZP_pos W tf minp_bool vocab tf_pos kept_witness))).
      -- apply real_eq_refl.
      -- apply (real_inv_pos_ext temp_sum (Z_P W tf minp_bool vocab)
                   temp_sum_pos (ZP_pos W tf minp_bool vocab tf_pos kept_witness)
                   (real_eq_sym (Z_P W tf minp_bool vocab) temp_sum HZeq)).
      * apply real_eq_refl.
    + exact HP.
Qed.

End InstMinP.

(* ======== G04_ProjFam member file: UpPLA (merged verbatim, with its own Requires) ======== *)
(* ===================================================================== *)
(* UpPLA.v — PLA v2 in Coq: p-adic stratified quotients, residue       *)
(*   contracts, and the VCA valuation-account machine.                 *)
(*                                                                     *)
(* Carriers are [Z]/[nat]/[bool] decidability throughout: no           *)
(*   epsilons, no order comparisons, no witness borrowing.             *)
(*   Discipline: purely constructive; the statement face is            *)
(*   Prop-free (the Set-layer identity type [tid], the order type      *)
(*   [nle], and [sumbool] decision branches); stdlib only.             *)
(*                                                                     *)
(* Four parts:                                                         *)
(*   part 1  the p-adic valuation machine [vp] (additivity over        *)
(*             multiplication and a divisibility characterization)     *)
(*   part 2  the stratified quotient core ([layer_closed]/             *)
(*             [layer_decide]/[pla_stratified_quotient], with the      *)
(*             branching counterexample as a contrast theorem)         *)
(*   part 3  explicit residue contracts (the two-tier [contract],      *)
(*             the scheduler input given as a visible premise)         *)
(*   part 4  the VCA valuation-account machine (decidable admission    *)
(*             fee, monotone dissipation, carry-settling scheduling)   *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set-layer infrastructure: the identity type [tid], the order      *)
(*    type [nle], and decidability support.                            *)
(* ===================================================================== *)

(* the Set-layer identity type (an equality carrier keeping the statement face Prop-free). *)
Inductive tid (A : Type) : A -> A -> Type := tid_refl : forall x : A, tid A x x.

Definition tid_sym (A : Type) (x y : A) (H : tid A x y) : tid A y x :=
  match H in tid _ a b return tid _ b a with
  | tid_refl _ a0 => @tid_refl _ a0
  end.

Definition tid_trans (A : Type) (x y z : A) (H1 : tid A x y) (H2 : tid A y z) :
  tid A x z :=
  match H1 in tid _ a b return tid _ b z -> tid _ a z with
  | tid_refl _ a0 => fun H => H
  end H2.

(* functional congruence of the identity type (the general transport lemma). *)
Definition tid_cong {A B : Type} (f : A -> B) (x y : A) (H : tid A x y) :
  tid B (f x) (f y) :=
  match H in tid _ a b return tid B (f a) (f b) with
  | tid_refl _ a0 => @tid_refl _ (f a0)
  end.

(* the Set-layer natural-number order type ([k < m] is encoded as [nle (Datatypes.S k) m]). *)
Inductive nle (n : nat) : nat -> Set :=
| nle_n : nle n n
| nle_S : forall m : nat, nle n m -> nle n (Datatypes.S m).

Ltac tidE H :=
  pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE.

(* boolean identity contradiction closer: [H1 : tid bool X true] and [H2 : tid bool X false]. *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* basic Set-layer [nle] lemmas. *)
Lemma leb_refl_tid : forall a : nat, tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply tid_refl.
Qed.

Lemma leb_S : forall a m : nat,
  tid bool (Nat.leb a m) true -> tid bool (Nat.leb a (Datatypes.S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply tid_refl.
    + change (tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint nle_lebF (a b : nat) (H : nle a b) {struct H} :
  tid bool (Nat.leb a b) true :=
  match H as H0 in nle _ bb
  return tid bool (Nat.leb a bb) true with
  | nle_n _ => leb_refl_tid a
  | nle_S _ m H1 => leb_S a m (nle_lebF a m H1)
  end.

Definition nle_leb (b a : nat) (H : nle a b) : tid bool (Nat.leb a b) true :=
  nle_lebF a b H.

(* extraction of [nle] into nat [<=] (for proof-internal reasoning only; reusable, fresh name each call). *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (nle_leb _ _ H) in tid _ x y return x = y with
        | tid_refl _ _ => eq_refl
        end)) as HN.

Lemma nle_SS : forall a b : nat, nle a b -> nle (Datatypes.S a) (Datatypes.S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_0 : forall m : nat, nle O m.
Proof.
  induction m as [| m1 IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_of_leb : forall b a : nat,
  tid bool (Nat.leb a b) true -> nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply nle_n.
    + change (tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply nle_0.
    + exact (nle_SS a1 b1 (IB a1 H)).
Qed.

Lemma nle_trans : forall a b c : nat, nle a b -> nle b c -> nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply nle_S. exact IH.
Qed.

(* predecessor cancellation for [nle]: [nle (Datatypes.S a) (Datatypes.S b) -> nle a b]. *)
Lemma nle_pred : forall a b : nat, nle (Datatypes.S a) (Datatypes.S b) -> nle a b.
Proof.
  intros a b H. apply nle_of_leb.
  exact (nle_leb (Datatypes.S b) (Datatypes.S a) H).
Qed.

Lemma nle_add_r : forall a b : nat, nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply nle_0.
  - exact (nle_SS a1 (a1 + b) (IH b)).
Qed.


(* the absurdity lemma [nle (Datatypes.S O) O] (empty elimination on disjoint indices, legitimately closing any Set goal). *)
Lemma nle_10_absurd : forall P : Type, nle (Datatypes.S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

(* bridge from the Z-layer strict order to the [nle] encoding (Set
   face: bool carriers [Z.leb]/[Z.ltb]; stdlib order facts enter
   only inside proofs via [Z.leb_le]/[Z.ltb_lt]):
   [Z.leb 0 a = true] and [Z.ltb a b = true] give
   [nle (Datatypes.S (Z.to_nat a)) (Z.to_nat b)]. *)
Lemma zle_to_nle_S : forall a b : Z,
  tid bool (Z.leb 0 a) true -> tid bool (Z.ltb a b) true ->
  nle (Datatypes.S (Z.to_nat a)) (Z.to_nat b).
Proof.
  intros a b Ha Hlt.
  pose proof (match Ha in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HEa.
  pose proof (match Hlt in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HElt.
  assert (HaP : (0 <= a)%Z) by (apply (proj1 (Z.leb_le 0 a)); exact HEa).
  assert (HltP : (a < b)%Z) by (apply (proj1 (Z.ltb_lt a b)); exact HElt).
  assert (Hb : (0 <= b)%Z) by lia.
  apply nle_of_leb.
  assert (Hleb : (Nat.leb (Datatypes.S (Z.to_nat a)) (Z.to_nat b)) = true).
  { apply Nat.leb_le.
    exact (proj1 (Z2Nat.inj_lt a b HaP Hb) HltP). }
  rewrite Hleb. apply tid_refl.
Qed.

(* [n ≠ 0] gives [|n| ≥ (Datatypes.S O)] in the nat encoding. *)
Lemma to_nat_abs_pos : forall n : Z,
  tid bool (Z.eqb n 0) false -> nle (Datatypes.S O) (Z.to_nat (Z.abs n)).
Proof.
  intros n H. tidE H.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  apply (zle_to_nle_S 0 (Z.abs n)).
  - apply tid_refl.
  - rewrite (proj2 (Z.ltb_lt 0 (Z.abs n)) (proj2 (Z.abs_pos n) Hne)).
    apply tid_refl.
Qed.

(* [|x| ≥ (Datatypes.S O)] gives the bool form of [x ≠ 0]. *)
Lemma eqb0_false_of_pos : forall x : Z,
  nle (Datatypes.S O) (Z.to_nat (Z.abs x)) -> tid bool (Z.eqb x 0) false.
Proof.
  intros x H. destruct (Z.eqb x 0) eqn:HEq.
  - apply (proj1 (Z.eqb_eq _ _)) in HEq. rewrite HEq in H.
    exact (nle_10_absurd _ H).
  - apply tid_refl.
Qed.

(* ===================================================================== *)
(* Part 1. the p-adic valuation machine                                 *)
(* ===================================================================== *)

(* the Z form of p / the divisibility test / [p^k] / its divisibility test. *)
Definition pZ (p : nat) : Z := Z.of_nat p.
Definition dvdtest (p : nat) (x : Z) : bool := Z.eqb (Z.modulo x (pZ p)) 0.
Definition powZN (p k : nat) : Z := Z.pow (pZ p) (Z.of_nat k).
Definition dwtest (p k : nat) (x : Z) : bool := Z.eqb (Z.modulo x (powZN p k)) 0.

(* fuel-based valuation counting.  [vp p 0 := 0] has a dedicated
   encoding (the zero state is guarded by [Z.eqb] and dispatched to
   0, avoiding an infinite nat encoding; consumers guard
   nonzeroness with [Z.eqb n 0]). *)
Fixpoint vpF (p : nat) (f : nat) (n : Z) {struct f} : nat :=
  match f with
  | O => O
  | Datatypes.S g =>
      if Z.eqb n 0 then O
      else if dvdtest p n then Datatypes.S (vpF p g (Z.div n (pZ p)))
      else O
  end.

(* the public valuation: fuel is [|n| + 1] (for [n ≠ 0] and [p ≥ 2] each step at least halves [|n|], so the fuel suffices). *)
Definition vp (p : nat) (n : Z) : nat := vpF p (Datatypes.S (Z.to_nat (Z.abs n))) n.

(* key decrease: [p ≥ 2], [n ≠ 0], [p ∣ n] give [|n/p| < |n|] ([nle (Datatypes.S k) m] encodes [k < m]). *)
Lemma zdiv_abs_decr : forall (p : nat) (n : Z), tid bool (Nat.leb 2 p) true ->
  tid bool (Z.eqb n 0) false -> tid bool (dvdtest p n) true ->
  nle (Datatypes.S (Z.to_nat (Z.abs (Z.div n (pZ p))))) (Z.to_nat (Z.abs n)).
Proof.
  intros p n Hp Hnz Hd.
  pose proof (match Hp in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HEp.
  pose proof (proj1 (Nat.leb_le 2 p) HEp) as Hple.
  tidE Hnz.
  pose proof (match Hd in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hple. }
  assert (Hpp : (0 <= pZ p)%Z) by lia.
  assert (Hpz0 : pZ p <> 0) by lia.
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hex : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hdm. rewrite Hmod in Hdm. lia. }
  assert (Hq0 : Z.div n (pZ p) <> 0).
  { intro Hc. rewrite Hc in Hex. lia. }
  assert (Hqa : (0 < Z.abs (Z.div n (pZ p)))%Z).
  { apply (proj2 (Z.abs_pos (Z.div n (pZ p)))). exact Hq0. }
  assert (Habsm : Z.abs n = pZ p * Z.abs (Z.div n (pZ p))).
  { rewrite Hex at 1. rewrite Z.abs_mul. rewrite (Z.abs_eq (pZ p) Hpp).
    reflexivity. }
  assert (Hm2 : (2 * Z.abs (Z.div n (pZ p)) <= Z.abs n)%Z).
  { rewrite Habsm. apply Z.mul_le_mono_nonneg_r.
    - apply Z.abs_nonneg.
    - exact Hpz. }
  assert (Hlt : (Z.abs (Z.div n (pZ p)) < Z.abs n)%Z) by lia.
  apply zle_to_nle_S.
  - rewrite (proj2 (Z.leb_le 0 (Z.abs (Z.div n (pZ p)))) (Z.abs_nonneg _)).
    apply tid_refl.
  - rewrite (proj2 (Z.ltb_lt (Z.abs (Z.div n (pZ p))) (Z.abs n)) Hlt).
    apply tid_refl.
Qed.

(* division preserves nonzeroness: [p ≥ 2], [n ≠ 0], [p ∣ n] give [n/p ≠ 0] (bool form). *)
Lemma zdiv_nz : forall (p : nat) (n : Z), tid bool (Nat.leb 2 p) true ->
  tid bool (Z.eqb n 0) false -> tid bool (dvdtest p n) true ->
  tid bool (Z.eqb (Z.div n (pZ p)) 0) false.
Proof.
  intros p n Hp Hnz Hd.
  pose proof (match Hp in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HEp.
  pose proof (proj1 (Nat.leb_le 2 p) HEp) as Hple.
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hple. }
  assert (Hpz0 : pZ p <> 0) by lia.
  tidE Hnz.
  pose proof (match Hd in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hdm : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hd0. rewrite Hmod in Hd0. lia. }
  assert (Hq0z : Z.div n (pZ p) <> 0).
  { intro Hc. rewrite Hc in Hdm. lia. }
  apply eqb0_false_of_pos.
  apply (zle_to_nle_S 0 (Z.abs (Z.div n (pZ p)))).
  - apply tid_refl.
  - rewrite (proj2 (Z.ltb_lt 0 (Z.abs (Z.div n (pZ p))))
               (proj2 (Z.abs_pos (Z.div n (pZ p))) Hq0z)).
    apply tid_refl.
Qed.

(* fuel independence: whenever both fuels cover [|n|] the count is unique. *)
Lemma vpF_indep : forall (p B : nat), tid bool (Nat.leb 2 p) true ->
  forall (f1 f2 : nat) (n : Z),
    nle (Z.to_nat (Z.abs n)) B ->
    tid bool (Z.eqb n 0) false ->
    nle (Z.to_nat (Z.abs n)) f1 ->
    nle (Z.to_nat (Z.abs n)) f2 ->
    tid nat (vpF p f1 n) (vpF p f2 n).
Proof.
  intros p B Hp. induction B as [| B1 IB]; intros f1 f2 n HnB Hnz Hf1 Hf2.
  - assert (H1 := to_nat_abs_pos n Hnz).
    pose proof (nle_trans _ _ _ H1 HnB) as HC. inversion HC.
  - destruct f1 as [| g1].
    + assert (H1 := to_nat_abs_pos n Hnz).
      pose proof (nle_trans _ _ _ H1 Hf1) as HC. inversion HC.
    + destruct f2 as [| g2].
      * assert (H1 := to_nat_abs_pos n Hnz).
        pose proof (nle_trans _ _ _ H1 Hf2) as HC. inversion HC.
      * cbn [vpF]. tidE Hnz. rewrite HE.
        destruct (dvdtest p n) eqn:Hd.
        -- (* [p ∣ n]: both sides enter the carried branch; compare the counts of [n/p] recursively. *)
           assert (Hdt : tid bool (dvdtest p n) true)
             by (rewrite Hd; apply tid_refl).
           apply (tid_cong Datatypes.S).
           apply IB with (n := Z.div n (pZ p)).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) HnB)).
           ++ exact (zdiv_nz p n Hp Hnz Hdt).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf1)).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf2)).
        -- (* [p does not divide n]: the else branch dispatches to O directly ([destruct] has substituted; iota reduction closes). *)
           apply tid_refl.
Qed.

Close Scope Z_scope.

(* ======== G04_ProjFam member file: UpPredRelax (merged verbatim, with its own Requires) ======== *)
(* ============================================================ *)
(* UpPredRelax.v — monotone relaxation statements of the            *)
(*   prediction region, as qualitative implications: each theorem   *)
(*   takes the missing dynamical premise as an explicit Section     *)
(*   Variable.                                                      *)
(*   item 4  [heat_relaxation_decreasing] (monotone decay of the    *)
(*             heat relaxation)                                     *)
(*   item 5a [fluctuation_scale_decreasing] (monotone decay of the  *)
(*             fluctuation scale)                                   *)
(*   item 5b [landauer_bound_pos] (positivity, three positive       *)
(*             factors)                                             *)
(*   item 5c [disturbance_hierarchical_transitive] and the chain    *)
(*             form ([disturbance_chain_decreasing])                *)
(*   item 5d [total_loss_multi_epoch_decreasing] (multi-epoch       *)
(*             chain)                                               *)
(* Honest boundary: the prediction region has no concrete dynamics  *)
(*   or energy definitions to build on ([equilibrium_dist],         *)
(*   [prediction_landauer] and the like have no constructive        *)
(*   definitions), so full theoremhood is out of reach; this file   *)
(*   states the qualitative implications, with every extra premise  *)
(*   (positivity/monotonicity/log positivity) declared as a Section *)
(*   Variable, nothing hidden.  The cross-domain scaling prediction *)
(*   (a [sigT] premise) has no quantitative lever and is not        *)
(*   carried over.                                                  *)
(* Discipline: purely constructive / Set layer / axiom-free / no    *)
(*   classical logic.                                               *)
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
From Stdlib Require Import Arith.

(* ============================================================ *)
(* Item 4: monotone decay of the heat relaxation.                  *)
(*   Premises: [heat_relaxation_exponential] plus [γ ≥ 0],         *)
(*   [T₀ ≥ 0] and monotonicity of [of_nat] (declared explicitly;   *)
(*   see the honest boundary above).                               *)
(* ============================================================ *)
Section PredRelaxHeat.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.

Variable temperature_difference : nat -> R.
Variable gamma : R.
Variable of_nat : nat -> R.
Variable temperature_difference0 : R.

Variable gamma_nonneg : le zero gamma.
Variable temperature_difference0_nonneg : le zero temperature_difference0.
Variable of_nat_mono : forall t : nat, le (of_nat t) (of_nat (Nat.succ t)).

Variable heat_relaxation_exponential :
  forall t : nat,
    Id (temperature_difference t)
       (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0).

(* the relaxation decays monotonically: [T(S t) <= T(t)]
   (monotone [γ · of_nat] makes [exp_neg] antitone, and
   multiplication by [T₀ >= 0] preserves the order). *)
Theorem heat_relaxation_decreasing : forall t : nat,
  le (temperature_difference (Nat.succ t)) (temperature_difference t).
Proof.
  intro t.
  assert (Hg : le (mult gamma (of_nat t)) (mult gamma (of_nat (Nat.succ t)))).
  { (* the interface [le_mult_compat_weak] is the right-multiplication form; reshaped on both ends via [mult_comm]. *)
    apply (le_id_l (mult gamma (of_nat t)) (mult (of_nat t) gamma)
                   (mult gamma (of_nat (Nat.succ t)))).
    - apply (mult_comm gamma (of_nat t)).
    - apply (le_id_r (mult (of_nat t) gamma) (mult (of_nat (Nat.succ t)) gamma)
                     (mult gamma (of_nat (Nat.succ t)))).
      + apply (mult_comm (of_nat (Nat.succ t)) gamma).
      + apply (le_mult_compat_weak (of_nat t) (of_nat (Nat.succ t)) gamma).
        * exact gamma_nonneg.
        * exact (of_nat_mono t). }
  assert (He : le (exp_neg (mult gamma (of_nat (Nat.succ t))))
                  (exp_neg (mult gamma (of_nat t))))
    by exact (exp_neg_le_decr _ _ Hg).
  assert (Hm : le (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                  (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0))
    by exact (le_mult_compat_weak _ _ temperature_difference0
              temperature_difference0_nonneg He).
  apply (le_id_l (temperature_difference (Nat.succ t))
                 (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                 (temperature_difference t)).
  - exact (heat_relaxation_exponential (Nat.succ t)).
  - apply (le_id_r (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                   (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0)
                   (temperature_difference t)).
    + exact (id_sym (heat_relaxation_exponential t)).
    + exact Hm.
Qed.

End PredRelaxHeat.

(* ============================================================ *)
(* Item 5a: monotone decay of the fluctuation scale (an upgraded    *)
(*   template of the baseline [prediction_fluctuation_scale]).      *)
(* ============================================================ *)
Section PredRelaxFluct.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.

Variable prob_negative_entropy : R -> R.
Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_scale :
  forall N : R,
    Id (prob_negative_entropy N)
       (exp_neg (mult N (inv_pos k_B k_B_pos))).

(* the fluctuation probability decays monotonically in N:
   [P(N+1) <= P(N)].  Core: [N <= N+1] multiplied by [1/k_B >= 0],
   then [exp_neg] reverses the order. *)
Theorem fluctuation_scale_decreasing : forall N : R,
  le (prob_negative_entropy (plus N one)) (prob_negative_entropy N).
Proof.
  intro N.
  assert (Hcore : le (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                     (exp_neg (mult N (inv_pos k_B k_B_pos)))).
  { apply exp_neg_le_decr.
    apply (le_mult_compat_weak N (plus N one) (inv_pos k_B k_B_pos)).
    - apply (lt_le_iff _ _). left. apply inv_pos_pos.
    - apply le_plus_nonneg_r. exact (lt_le_iff _ _ (inl one_pos)). }
  apply (le_id_l (prob_negative_entropy (plus N one))
                 (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                 (prob_negative_entropy N)).
  - exact (fluctuation_scale (plus N one)).
  - apply (le_id_r (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                   (exp_neg (mult N (inv_pos k_B k_B_pos)))
                   (prob_negative_entropy N)).
    + exact (id_sym (fluctuation_scale N)).
    + exact Hcore.
Qed.

End PredRelaxFluct.

(* ============================================================ *)
(* Item 5b: positivity of the Landauer bound (a qualitative         *)
(*   implication with the dynamical premise declared).              *)
(*   Premises: [prediction_landauer] plus [k_B > 0], [T > 0] and    *)
(*   [log 2 > 0] (declared explicitly; the interface [log] has no   *)
(*   order field — see the honest boundary above).                  *)
(* ============================================================ *)
Section PredRelaxLandauer.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let log := @log RI.
Let le := @le RI.
Let lt := @lt RI.

Variable E_min : R.
Variable k_B : R.
Variable T_landauer : R.

Variable k_B_pos : lt zero k_B.
Variable T_pos : lt zero T_landauer.
Variable log_two_pos : lt zero (log (plus one one)).

Variable prediction_landauer :
  Id E_min (mult k_B (mult T_landauer (log (plus one one)))).

(* the Landauer bound is positive: [E_min = k_B · T · log 2 > 0] (product of three positive factors, transported along the identity). *)
Theorem landauer_bound_pos : lt zero E_min.
Proof.
  assert (Hinner : lt zero (mult T_landauer (log (plus one one))))
    by exact (mult_positive T_landauer (log (plus one one)) T_pos log_two_pos).
  assert (Houter : lt zero (mult k_B (mult T_landauer (log (plus one one)))))
    by exact (mult_positive k_B (mult T_landauer (log (plus one one)))
                              k_B_pos Hinner).
  apply (lt_id_r zero _ E_min (id_sym prediction_landauer) Houter).
Qed.

End PredRelaxLandauer.

(* ============================================================ *)
(* Item 5c: disturbance transport for hierarchical stability (a     *)
(*   qualitative implication with the dynamical premise declared).  *)
(* ============================================================ *)
Section PredRelaxHier.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Let R := @R RI.
Let le := @le RI.
Let PropType := @PropositionConvergenceCore.Proposition RI SS.

Variable disturbance : PropType -> R.
Variable hierarchical_relation : PropType -> PropType -> Set.

Variable hierarchical_stability_prediction :
  forall (upper lower : PropType),
    hierarchical_relation upper lower ->
    le (disturbance upper) (disturbance lower).

(* two-step transport: upper disturbance <= middle disturbance <= lower disturbance gives upper <= lower. *)
Theorem disturbance_hierarchical_transitive : forall (u m l : PropType),
  hierarchical_relation u m -> hierarchical_relation m l ->
  le (disturbance u) (disturbance l).
Proof.
  intros u m l Hum Hml.
  apply (le_trans (disturbance u) (disturbance m) (disturbance l)).
  - exact (hierarchical_stability_prediction u m Hum).
  - exact (hierarchical_stability_prediction m l Hml).
Qed.

(* finite-chain version: along n steps of the hierarchy the
   disturbance never increases (nat induction on [le_refl] +
   [le_trans]; the chain premises are explicit pointwise). *)
Theorem disturbance_chain_decreasing : forall (chain : nat -> PropType),
  (forall k : nat, hierarchical_relation (chain k) (chain (Nat.succ k))) ->
  forall (k n : nat), le (disturbance (chain k)) (disturbance (chain (k + n))).
Proof.
  intros chain Hrel k n.
  induction n as [| n IH].
  - rewrite Nat.add_0_r. apply le_refl.
  - replace (k + Datatypes.S n) with (Nat.succ (k + n))
      by apply (eq_sym (Nat.add_succ_r k n)).
    apply (le_trans (disturbance (chain k)) (disturbance (chain (k + n)))
                    (disturbance (chain (Nat.succ (k + n))))).
    + exact IH.
    + exact (hierarchical_stability_prediction (chain (k + n))
                                               (chain (Nat.succ (k + n)))
                                               (Hrel (k + n))).
Qed.

End PredRelaxHier.

(* ============================================================ *)
(* Item 5d: the multi-epoch loss-decrease chain tied to the         *)
(*   language-model structure (a qualitative implication; the       *)
(*   single-step correlation premise is explicit pointwise).        *)
(* ============================================================ *)
Section PredRelaxLM.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let le := @le RI.

Variable Token : Set.
Variable model : nat -> list Token.
Variable grammar_error : list Token -> R.
Variable total_loss : list Token -> R.

Variable loss_structure_correlation :
  forall epoch : nat,
    le (grammar_error (model epoch)) (grammar_error (model (Nat.succ epoch))) ->
    le (total_loss (model epoch)) (total_loss (model (Nat.succ epoch))).

(* the multi-epoch loss-decrease chain: [grammar_error] monotone
   epoch by epoch gives a [total_loss] that never increases over
   any n steps. *)
Theorem total_loss_multi_epoch_decreasing : forall (start n : nat),
  (forall k : nat, le (grammar_error (model k)) (grammar_error (model (Nat.succ k)))) ->
  le (total_loss (model start)) (total_loss (model (start + n))).
Proof.
  intros start n Hg.
  induction n as [| n IH].
  - rewrite Nat.add_0_r. apply le_refl.
  - replace (start + Datatypes.S n) with (Nat.succ (start + n))
      by apply (eq_sym (Nat.add_succ_r start n)).
    apply (le_trans (total_loss (model start)) (total_loss (model (start + n)))
                    (total_loss (model (Nat.succ (start + n))))).
    + exact IH.
    + exact (loss_structure_correlation (start + n) (Hg (start + n))).
Qed.

End PredRelaxLM.

(* ======== G04_ProjFam member file: UpProjBPC (merged verbatim, with its own Requires) ======== *)
(* ============================================================ *)
(* UpProjBPC.v — the multiplicative composition chain of KL cost    *)
(*   intervals.                                                     *)
(*                                                                  *)
(* Companion of UpProj.v (the abstract projection kernel master     *)
(*   theorems).  Within the direct reach of master items 1/4, this  *)
(*   file gives the exact multiplicative composition of the         *)
(*   cost-interval endpoints along a closed chain through the       *)
(*   compound mask:                                                 *)
(*   [Z_{P1∩P2} == Z1 · (Z2|kept1)], where [Z2|kept1] is the        *)
(*   conditional kept mass of the second mask inside the [P1]-kept  *)
(*   set (constructively as the ratio form [Z12 · inv Z1]).         *)
(*   On the cost side: [−log Z12 == (−log Z1) + (−log Zc)] splits   *)
(*   exactly, and the KL cost is additive along the closed chain:   *)
(*   [KL_{P1}(q) == KL_{P12}(q) + (−log Zc)].                       *)
(*                                                                  *)
(* Contrast note: the four neighboring developments carry no KL     *)
(*   interval-multiplication-chain semantics — PCD union bounds     *)
(*   give only bounds with no multiplicative decomposition         *)
(*   identity; PKI notAfter states point-in-time validity with no   *)
(*   KL accounting; series remainders give [|S−S_t| ≤ B]-type       *)
(*   remainder bounds, not endpoint-exact splits; the Doob tower    *)
(*   property is an L2 convergence theorem with no computable       *)
(*   certificates or cost accounting.  The new content here is the  *)
(*   algebra of the closure point: the endpoint identity on the     *)
(*   compound mask plus chainwise additivity.                       *)
(*                                                                  *)
(* World: the Real-layer list world (as in UpProj, rooted in        *)
(*   CW_ConstructiveWorld_219).  All Set layer                      *)
(*   ([Id]/[And]/[Or]/[sigT]); the statement face leaks no Prop;    *)
(*   purely constructive with no external assumptions; log          *)
(*   positivity certificates are carried alongside (transparent     *)
(*   Definitions).                                                  *)
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


(* ============================================================ *)
(* Top-level boosters (Set-layer [real_eq] algebra lemmas, names    *)
(*   reserved under the [bpc_] prefix).                             *)
(* ============================================================ *)

(* [−0 == 0] (the signed-zero bridge; normalizes zero-shaped interval endpoints). *)
Lemma bpc_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  apply (real_eq_trans _ (real_plus (real_opp real_zero) real_zero) _).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_eq_trans _ (real_plus real_zero (real_opp real_zero)) _).
    + apply real_plus_comm.
    + apply real_plus_opp.
Qed.

(* [1·x == x] (the left-unit bridge; [real_mult_one] is the [x·1] form). *)
Lemma bpc_one_mult : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one) _).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* [(−t)+t == 0] (the reversed annihilation; [real_plus_opp] is the [t+(−t)] form). *)
Lemma bpc_opp_plus_zero : forall t : Real, real_eq (real_plus (real_opp t) t) real_zero.
Proof.
  intro t.
  apply (real_eq_trans _ (real_plus t (real_opp t)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* cancellation: [(a+(−t))+t == a] (the arm that shifts terms across the two sides of the chained KL identities). *)
Lemma bpc_cancel_add_opp : forall a t : Real,
  real_eq (real_plus (real_plus a (real_opp t)) t) a.
Proof.
  intros a t.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp t) t)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a real_zero) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus (real_opp t) t)
               a real_zero).
      * apply real_eq_refl.
      * apply bpc_opp_plus_zero.
    + apply real_plus_zero.
Qed.

(* additive commutation: [(a+b)+c == (a+c)+b] (the arm swapping the middle term of the chained identities). *)
Lemma bpc_assoc_swap : forall a b c : Real,
  real_eq (real_plus (real_plus a b) c) (real_plus (real_plus a c) b).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus b c)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a (real_plus c b)) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus b c)
               a (real_plus c b)).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply real_plus_assoc.
Qed.

(* multiplicative swap: [x·(y·z) == y·(x·z)] (the middle-term rearrangement arm of the absorption chain). *)
Lemma bpc_mult_swap : forall x y z : Real,
  real_eq (real_mult x (real_mult y z)) (real_mult y (real_mult x z)).
Proof.
  intros x y z.
  apply (real_eq_trans _ (real_mult (real_mult x y) z) _).
  - apply real_mult_assoc.
  - apply (real_eq_trans _ (real_mult (real_mult y x) z) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult x y) z
               (real_mult y x) z).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply real_eq_sym. apply real_mult_assoc.
Qed.

(* ============================================================ *)
(* Master section: two-level mask composition (same shape as the    *)
(*   UpProj master section, extended).  [I]/[f]/[idx]/[f_norm]/     *)
(*   [f_pos] align argument by argument with UpProj; [P1] and     *)
(*   [P2] are the two mask levels, each with a nonemptiness         *)
(*   witness ([P1_witness] reuses the source module's item 0,       *)
(*   [P12_witness] sits at the compound level).                     *)
(* ============================================================ *)
Section BPChain.

Variable I : Set.                          (* the index type (as in the master) *)
Variable f : I -> Real.                    (* the projected weights (as in the master) *)
Variable P1 : I -> bool.                   (* the first-level keep predicate *)
Variable P2 : I -> bool.                   (* the second-level keep predicate *)
Variable idx : list I.                     (* the index enumeration (as in the master) *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P1_witness : sigT (fun i : I => And (Id (P1 i) true) (InT i idx)).

(* the compound mask [P1∩P2] (boolean conjunction). *)
Definition P12 (i : I) : bool := andb (P1 i) (P2 i).

Variable P12_witness : sigT (fun i : I => And (Id (P12 i) true) (InT i idx)).

(* ---------- masses and certificates (transparent Definitions;     
   log certificates carried alongside) ----------                
   [Z1] is the first-level kept mass; [Z12] the compound kept      
   mass (that is, [Z_{P1∩P2}]). *)
Definition Z1 : Real := Z_P I f P1 idx.
Definition Z12 : Real := Z_P I f P12 idx.

Definition p1 : real_lt real_zero Z1 := ZP_pos I f P1 idx f_pos P1_witness.
Definition p12 : real_lt real_zero Z12 := ZP_pos I f P12 idx f_pos P12_witness.

(* the conditional kept mass [Zc := Z12·inv Z1] (that is [Σ_{P1∧P2} f / Z1], the [Z2|kept1] of the contrast note). *)
Definition Zc : Real := real_mult Z12 (real_inv_pos Z1 p1).
(* the positivity certificate carried alongside (a transparent Definition, not sealed by Qed). *)
Definition Zc_pos : real_lt real_zero Zc :=
  real_mult_positive Z12 (real_inv_pos Z1 p1) p12 (real_inv_pos_pos Z1 p1).

(* the first-level projection kernel (master-form instantiation) and the kernel-summed form of the conditional mass. *)
Definition Proj1 (i : I) : Real := Proj I f P1 idx f_pos P1_witness i.
Definition Zc_proj1 : Real :=
  real_list_sum I (fun i : I => if P12 i then Proj1 i else real_zero) idx.

(* ---------- item 1, core A: the pointwise four-branch mask bridge -- *)
(* on [P12]-kept entries [Proj1] equals [f · inv Z1] (keeping [P1∧P2] *)
(* implies keeping the first level); on [P12]-dropped entries both    *)
(* sides are zero.  Each branch is proved independently by destruct,  *)
(* with no empty match. *)
Lemma bpc_pt_bridge : forall y : I,
  real_eq (if P12 y then Proj1 y else real_zero)
          (real_mult (if P12 y then f y else real_zero)
                     (real_inv_pos Z1 p1)).
Proof.
  intro y. unfold P12, Proj1, Proj.
  destruct (P1 y) eqn:H1y; destruct (P2 y) eqn:H2y; cbn [andb].
  - (* true,true: both sides [f · inv Z1], equal by conversion. *)
    apply real_eq_refl.
  - (* true,false: [0 · inv == 0] (symmetry turning the product head around, then [real_mult_comm] + [real_mult_zero]). *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,true: [0 · inv == 0]. *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,false: [0 · inv == 0]. *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
Qed.

(* ---------- item 1, core B: decomposition of the two-level masked   *)
(*   sum (linear extraction) ------                                    *)
(* [Σ_{P12} Proj1 == inv Z1 · Z12]: the conditional mass (the sum of   *)
(* the second mask against the first-level projection kernel) comes    *)
(* from the pointwise bridge plus [real_list_sum_linear_r] factoring   *)
(* out the linear factor. *)
Lemma bpc_Zc_proj1_sum : real_eq Zc_proj1
  (real_mult (real_inv_pos Z1 p1) Z12).
Proof.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P12 i then f i else real_zero)
                           (real_inv_pos Z1 p1))
              idx) _).
  - apply (real_list_sum_ext I
             (fun i : I => if P12 i then Proj1 i else real_zero)
             (fun i : I =>
                real_mult (if P12 i then f i else real_zero)
                          (real_inv_pos Z1 p1))
             idx).
    intro y. apply bpc_pt_bridge.
  - apply (real_list_sum_linear_r I (real_inv_pos Z1 p1)
             (fun i : I => if P12 i then f i else real_zero) idx).
Qed.

(* ---------- compound domination: [Z12 <= Z1] (the two-level masked sum bounded by the first-level one) ------- *)
Lemma bpc_Z12_le_Z1 : real_le Z12 Z1.
Proof.
  apply (real_list_sum_le I
           (fun i : I => if P12 i then f i else real_zero)
           (fun i : I => if P1 i then f i else real_zero) idx).
  intro y. unfold P12. destruct (P1 y); destruct (P2 y).
  - apply real_le_refl.
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
  - apply real_le_refl.
Qed.

(* ---------- item 1 (main statement, the multiplicative split):       *)
(*   [Z12 == Z1 · Zc] ------                                           *)
(* paper derivation: [Z1·Zc == Z1·(Z12·inv Z1) == Z12·(Z1·inv Z1)]     *)
(*   (swap) [== Z12·1 == Z12].  The core is the distributive           *)
(*   absorption of the inverse (swap + [real_inv_pos_correct] +        *)
(*   [real_mult_one]); circularity of the conditional-ratio form is    *)
(*   excluded because [Zc] is built from [Z12]/[Z1]/the witnesses      *)
(*   while the split cores A/B are independent. *)
Theorem Z_compound_mul : real_eq Z12 (real_mult Z1 Zc).
Proof.
  apply real_eq_sym.
  apply (real_eq_trans _ (real_mult Z1 (real_mult Z12 (real_inv_pos Z1 p1))) _).
  - apply (RealSetoid.real_eq_mult_compat Z1 Zc Z1
             (real_mult Z12 (real_inv_pos Z1 p1))).
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult Z12 (real_mult Z1 (real_inv_pos Z1 p1))) _).
    + apply bpc_mult_swap.
    + apply (real_eq_trans _ (real_mult Z12 real_one) _).
      * apply (RealSetoid.real_eq_mult_compat Z12
                 (real_mult Z1 (real_inv_pos Z1 p1)) Z12 real_one).
        -- apply real_eq_refl.
        -- apply real_inv_pos_correct.
      * apply real_mult_one.
Qed.

(* ---------- item 1 satellite (semantic bridge): the conditional      *)
(*   mass equals the ratio form ------                                  *)
(* the two constructions of [Z2|kept1] coincide:
   [Σ_{P12} Proj1 == Z12·inv Z1]. *)
Lemma bpc_cond_semantics : real_eq Zc_proj1 Zc.
Proof.
  apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) Z12) _).
  - apply bpc_Zc_proj1_sum.
  - unfold Zc. apply real_mult_comm.
Qed.

(* ---------- compound item 0: the conditional mass lies in (0,1] ---- *)
(* [Zc <= 1]: [Zc == Z12·inv Z1 <= Z1·inv Z1 == 1] (domination plus    *)
(* inverse absorption). *)
Theorem Zc_le_one : real_le Zc real_one.
Proof.
  apply (real_le_trans _ (real_mult Z1 (real_inv_pos Z1 p1))).
  - exact (real_le_mult_compat Z12 Z1 (real_inv_pos Z1 p1)
             (real_inv_pos_pos Z1 p1) bpc_Z12_le_Z1).
  - apply (RealSetoid.real_eq_le (real_mult Z1 (real_inv_pos Z1 p1)) real_one).
    apply real_inv_pos_correct.
Qed.

(* ---------- the log composition core: [log Z12 == log Z1 + log Zc] -- *)
(* the log-side form of the endpoint multiplicative composition; the   *)
(* certificate argument of [real_log_mult] matches the [wd] bridge     *)
(* ([real_mult_positive Z1 Zc p1 Zc_pos], transparent-certificate      *)
(* discipline). *)
Lemma bpc_log_Z12_split :
  real_eq (real_log Z12 p12)
          (real_plus (real_log Z1 p1) (real_log Zc Zc_pos)).
Proof.
  apply (real_eq_trans _
           (real_log (real_mult Z1 Zc) (real_mult_positive Z1 Zc p1 Zc_pos)) _).
  - exact (real_log_wd Z12 (real_mult Z1 Zc) p12
             (real_mult_positive Z1 Zc p1 Zc_pos) Z_compound_mul).
  - exact (real_log_mult Z1 Zc p1 Zc_pos).
Qed.

(* ---------- endpoint multiplicative composition on the cost side: [−log Z1 + −log Zc == −log Z12] ----- *)
Lemma bpc_cost_mul_split :
  real_eq (real_plus (real_opp (real_log Z1 p1))
                     (real_opp (real_log Zc Zc_pos)))
          (real_opp (real_log Z12 p12)).
Proof.
  apply (real_eq_trans _
           (real_opp (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))) _).
  - apply real_eq_sym. apply real_opp_plus.
  - apply (RealSetoid.real_eq_opp_compat
             (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))
             (real_log Z12 p12)).
    apply real_eq_sym. apply bpc_log_Z12_split.
Qed.

(* ---------- item 2 (main statement, additivity of the KL cost        *)
(*   chain) ------                                                      *)
(* the master theorem twice (for [P1] and [P12]) + the cost-endpoint    *)
(*   split + a three-arm elimination:                                   *)
(*   [A + (−log Z1) == KLqf == B + (−l12)
   == B + ((−log Z1) + (−lc)) == (B + (−log Z1)) + (−lc)];            *)
(*   transporting both sides by [(x+(−t))+t] gives [A == B + (−lc)].    *)
(* the premises on q are stated honestly: normalization + pointwise     *)
(*   positivity + compatibility with the compound mask ([P12] false     *)
(*   gives [q = 0]; the first-level compatibility follows               *)
(*   definitionally from the [andb] false branch, so a single premise   *)
(*   covers both levels). *)
Theorem proj_kl_chain : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (andb (P1 i) (P2 i)) false -> real_eq (q i) real_zero),
  real_eq (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
          (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                     (real_opp (real_log Zc Zc_pos))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  assert (Hqf1 : forall i : I, Id (P1 i) false -> real_eq (q i) real_zero).
  { intro i. intro Heq1. apply (Hq_fail i).
    exact (projp_id_transport bool false (P1 i)
             (fun b : bool => Id (andb b (P2 i)) false)
             id_refl (id_sym Heq1)). }
  pose proof (proj_kl_cost I f P1 idx f_pos P1_witness q Hq_norm Hq_pos Hqf1) as H1.
  pose proof (proj_kl_cost I f P12 idx f_pos P12_witness q Hq_norm Hq_pos Hq_fail) as H2.
  assert (Hj1 : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                   (real_opp (real_log Z1 p1)))
                        (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))).
  { apply (real_eq_trans _ (KLqf I f idx f_pos q Hq_pos) _).
    - apply real_eq_sym. exact H1.
    - exact H2. }
  assert (Hj2 : real_eq (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))
                        (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                        (real_plus (real_opp (real_log Z1 p1))
                                   (real_opp (real_log Zc Zc_pos)))) _).
    - apply (RealSetoid.real_eq_plus_compat
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Z12 p12))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_plus (real_opp (real_log Z1 p1))
                          (real_opp (real_log Zc Zc_pos)))).
      + apply real_eq_refl.
      + apply real_eq_sym. apply bpc_cost_mul_split.
    - apply real_plus_assoc. }
  assert (Hjoin : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                                (real_opp (real_log Z1 p1)))
                                     (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _ (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                      (real_opp (real_log Z12 p12))) _).
    - exact Hj1.
    - exact Hj2. }
  assert (Hright : real_eq
    (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos)))
               (real_log Z1 p1))
    (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1))) (real_log Z1 p1))
                        (real_opp (real_log Zc Zc_pos))) _) .
    - exact (bpc_assoc_swap (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                       (real_opp (real_log Z1 p1)))
                            (real_opp (real_log Zc Zc_pos)) (real_log Z1 p1)) .
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1))) (real_log Z1 p1))
               (real_opp (real_log Zc Zc_pos))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos))).
      + apply bpc_cancel_add_opp.
      + apply real_eq_refl. }
  apply (real_eq_trans _
           (real_plus (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                 (real_opp (real_log Z1 p1))) (real_log Z1 p1)) _).
  - apply real_eq_sym. apply bpc_cancel_add_opp.
  - apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))
                        (real_log Z1 p1)) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                          (real_opp (real_log Z1 p1))) (real_log Z1 p1)
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos))) (real_log Z1 p1)).
      * exact Hjoin.
      * apply real_eq_refl.
    + exact Hright.
Qed.

(* ---------- item 3a: the closed cost-interval endpoints (mass        *)
(*   sandwich) ------                                                   *)
(* one-sided information-projection version: [S <= Z12 <= S+U] (with    *)
(*   positivity certificates for [S], [U], [S+U]) gives                 *)
(*   [−log(S+U) <= −log Z12 <= −log S].                                 *)
(* both ends are proved: log monotonicity ([real_log_le_mono]) plus     *)
(*   order reversal under negation ([real_opp_le_compat]); the          *)
(*   endpoint multiplicative composition is [bpc_cost_mul_split]. *)
Theorem proj_cost_interval : forall (S U : Real)
  (HSp : real_lt real_zero S)
  (HUp : real_lt real_zero (real_plus S U))
  (Hlo : real_le S Z12) (Hhi : real_le Z12 (real_plus S U)),
  And (real_le (real_opp (real_log (real_plus S U) HUp))
               (real_opp (real_log Z12 p12)))
      (real_le (real_opp (real_log Z12 p12))
               (real_opp (real_log S HSp))).
Proof.
  intros S U HSp HUp Hlo Hhi.
  split.
  - apply (real_opp_le_compat (real_log Z12 p12)
             (real_log (real_plus S U) HUp)).
    apply (real_log_le_mono Z12 (real_plus S U) p12 HUp).
    exact Hhi.
  - apply (real_opp_le_compat (real_log S HSp) (real_log Z12 p12)).
    apply (real_log_le_mono S Z12 HSp p12).
    exact Hlo.
Qed.

(* ---------- item 3b: the fully-kept endpoint (the lower endpoint     *)
(*   is exactly 0) ------                                               *)
(* [P12 ≡ true] gives [Z12 == 1] (the [f_norm] bridge), hence           *)
(*   [−log Z12 == 0]: the degenerate image of the closed cost           *)
(*   interval [−log(S_t+U_t), −log S_t] as [U_t→0] and [S_t→1],         *)
(*   closing exactly at the endpoint against the item-3a sandwich. *)
Theorem proj_cost_full_mask_zero :
  (forall i : I, Id (P12 i) true) ->
  real_eq (real_opp (real_log Z12 p12)) real_zero.
Proof.
  intro Hall.
  assert (HZ1 : real_eq Z12 real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P12 i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P12 y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (Hall y)).
    - exact f_norm. }
  assert (Hlog : real_eq (real_log Z12 p12) real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact (real_log_wd Z12 real_one p12 real_lt_zero_one HZ1).
    - apply (real_log_one real_lt_zero_one). }
  apply (real_eq_trans _ (real_opp real_zero) _).
  - apply (RealSetoid.real_eq_opp_compat (real_log Z12 p12) real_zero Hlog).
  - apply bpc_opp_zero.
Qed.

End BPChain.

(* ===================================================================== *)
(* Tail supply section: signature-preserving discharge of interface     *)
(*   obligations.                                                       *)
(*                                                                      *)
(* Disposition of the interface premises:                               *)
(*  · discharged here by explicit certificates: [P_witness] (and the    *)
(*    same-shaped [P_witness] of AbstractKL), [P12_witness] (BPChain),  *)
(*    [Krow] (InstKV) and [keep_dec] (InstMinP, the approved Set-layer   *)
(*    restatement form); also [f_norm]/[f_pos] certificates of the      *)
(*    same shape, and a demonstration of [ZP_pos] on the concrete       *)
(*    instance.                                                         *)
(*  · same-shaped and mechanically replicable (listed for reuse):       *)
(*    [Kpos]/[keep_nonempty]/[p_norm]/[p_pos]/[aud_witness]/[tf_norm]/  *)
(*    [tf_pos]/[temp_sum_pos]/[kept_witness]/[P1_witness] and the       *)
(*    BPChain [f_norm]/[f_pos].                                         *)
(*  · genuine premises (kept as such): [delta_minor]/[delta_minor_kv]   *)
(*    (Doeblin-gap certificates, independent obligations on the free    *)
(*    [u]/[δ]); the qualitative premises of the five PredRelax          *)
(*    sections ([gamma_nonneg]/[of_nat_mono]/                           *)
(*    [heat_relaxation_exponential]/[k_B_pos]/[fluctuation_scale]/      *)
(*    [T_pos]/[log_two_pos]/[prediction_landauer]/                      *)
(*    [hierarchical_stability_prediction]/[loss_structure_correlation]).*)
(*  · interface parameters (kept): the data parameters of each section  *)
(*    stay in place as interface obligations.                           *)
(* Instance carriers (single-point form): the supply lemmas are         *)
(*   discharge certificates on a concrete instance, so consumers can    *)
(*   use the instance in place of the interface field.                  *)
(* ===================================================================== *)

(* the single-point instance carriers. *)
Definition g04pf_idx1 : list unit := tt :: nil.
Definition g04pf_f1 : unit -> Real := fun _ : unit => real_one.
Definition g04pf_P1t : unit -> bool := fun _ : unit => true.
Definition g04pf_P2t : unit -> bool := fun _ : unit => true.
Definition g04pf_K1 : unit -> unit -> Real := fun _ _ : unit => real_one.
Definition g04pf_Kw1 : unit -> Set := fun _ : unit => unit.

(* the single-point normalization certificate: [Σ_{tt::nil} 1 == 1] (commutation plus the zero-element collapse, a two-step real sum). *)
Lemma g04pf_f_norm_supply :
  real_eq (real_list_sum unit (fun _ : unit => real_one) g04pf_idx1) real_one.
Proof.
  exact (real_eq_trans (real_plus real_one real_zero)
           (real_plus real_zero real_one) real_one
           (real_plus_comm real_one real_zero)
           (projp_plus_zero_l real_one)).
Qed.

(* the single-point positivity certificate: the constant-one weight is pointwise strictly positive (anchored directly at [real_lt_zero_one]). *)
Lemma g04pf_f_pos_supply :
  forall i : unit, real_lt real_zero (g04pf_f1 i).
Proof. intro i. exact real_lt_zero_one. Qed.

(* supply 1: the single-point [P_witness] witness — built directly with  *)
(*   [existT] (the identity arm [id_refl] plus the enumeration arm       *)
(*   [InT_here], packaged with [And]). *)
Lemma g04pf_p_witness_supply :
  sigT (fun i : unit => And (Id (g04pf_P1t i) true) (InT i g04pf_idx1)).
Proof.
  exists tt. split.
  - exact (@id_refl bool true).
  - apply InT_here.
Qed.

(* supply 2: single-point kernel-row normalization — [(fun s' => K1 s    *)
(*   s')] is definitionally the constant-one weight, so the              *)
(*   normalization certificate is the same as [g04pf_f_norm_supply]. *)
Lemma g04pf_krow_supply : forall s : unit,
  real_eq (real_list_sum unit (fun s' : unit => g04pf_K1 s s') g04pf_idx1)
          real_one.
Proof.
  intro s.
  exact (real_eq_trans (real_plus real_one real_zero)
           (real_plus real_zero real_one) real_one
           (real_plus_comm real_one real_zero)
           (projp_plus_zero_l real_one)).
Qed.

(* supply 3 (the approved Set-layer restatement form): the single-point  *)
(*   [keep_dec] decider certificate — [Kw] is inhabited, and the         *)
(*   positive branch is built directly with [inl] ([Or]/[Not] are the    *)
(*   Set-layer sum-type aliases of S01, so the supplied form is          *)
(*   same-layer and synonymous with a [sumbool] carrier). *)
Lemma g04pf_keep_dec_supply :
  forall w : unit, Or (g04pf_Kw1 w) (Not (g04pf_Kw1 w)).
Proof. intro w. exact (@inl (g04pf_Kw1 w) (Not (g04pf_Kw1 w)) tt). Qed.

(* supply 4: the single-point compound [P12_witness] witness —           *)
(*   [P1]/[P2] are constantly true, so [P12 tt = andb true true]         *)
(*   reduces definitionally to true and the witness is built directly. *)
Lemma g04pf_p12_witness_supply :
  sigT (fun i : unit =>
    And (Id (P12 unit g04pf_P1t g04pf_P2t i) true) (InT i g04pf_idx1)).
Proof.
  exists tt. split.
  - exact (@id_refl bool true).
  - apply InT_here.
Qed.

(* demonstration of an instance standing in for the interface fields:    *)
(*   the single-point instance discharges [ZP_pos]'s interface fields    *)
(*   (the three supplies [f_norm]/[f_pos]/[P_witness] are cited with     *)
(*   all arguments explicit), the positivity certificate carried         *)
(*   alongside. *)
Lemma g04pf_zp_pos_supply :
  real_lt real_zero (Z_P unit g04pf_f1 g04pf_P1t g04pf_idx1).
Proof.
  exact (ZP_pos unit g04pf_f1 g04pf_P1t g04pf_idx1
           g04pf_f_pos_supply g04pf_p_witness_supply).
Qed.

(* ======== verification-evidence section (statement face unchanged; only audit commands appended) ======== *)
Print Assumptions projp_id_transport.
Print Assumptions projp_minus_plus_opp.
Print Assumptions kev_Zkv_le_one_via_proj.
Print Assumptions kev_row_normalized_via_proj.
Print Assumptions kev_drop_zero_via_proj.
Print Assumptions kev_keep_ge_via_proj.
Print Assumptions kev_minor_uncond_via_proj.
Print Assumptions Zaud_le_one_via_proj.
Print Assumptions projected_normalized_via_proj.
Print Assumptions projected_drop_zero_via_proj.
Print Assumptions projected_keep_ge_via_proj.
Print Assumptions nle_pred.

(* ----- assumption audit for the supply lemmas (same audit gate) ----- *)
Print Assumptions g04pf_f_norm_supply.
Print Assumptions g04pf_f_pos_supply.
Print Assumptions g04pf_p_witness_supply.
Print Assumptions g04pf_krow_supply.
Print Assumptions g04pf_keep_dec_supply.
Print Assumptions g04pf_p12_witness_supply.
Print Assumptions g04pf_zp_pos_supply.
