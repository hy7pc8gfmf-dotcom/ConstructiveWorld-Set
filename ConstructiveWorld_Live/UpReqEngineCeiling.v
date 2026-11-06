(* ConstructiveWorld-Set -- Q-layer ceiling theorems for the harmonic, truncated-engine and nested-tangent families. *)

(** * UpReqEngineCeiling: exact Q-layer ceilings for the harmonic, truncated-engine and nested-tangent families.

    Mission.  Four Q-layer ceiling statements over the rationals, all carried by [Set]:
      the harmonic lower bound [cec_H_lower] (k >= 5 implies H_k - 1/(k+1) >= 2, via
      the monotone step (k+3)/((k+1)(k+2)) > 0 and the corner value 127/60 at k = 5);
      the piecewise table [cec_trunc_sup] for c*(k) = min(H_k - 1/(k+1), 2) (values
      1/2, 7/6, 19/12, 113/60 at the corners k = 1..4 and 2 on the segment k >= 5,
      five [Qeq] conjuncts); the kernel second-order coefficient [cec_kernel_coef]
      of the R6 nested tangent family, -(k+1)/(2k), carried by the abstract binomial
      inversion engine [cec_inv2] with the fingerprint (k+1)/(2k) > 1/2; and the
      strict ceiling [cec_tangent_ceiling] (2(k-1)/k < 2 for finite k) with the gap
      identity [cec_tangent_gap] (2 - 2m/(m+1) == 2/(m+1)).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring], [QArith.Qabs], [QArith.Qminmax],
      [Lists.List], [Bool.Bool], [Arith.Arith], [Setoid], [Morphisms], [Lia].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp] of this development.

    References.  This development, UpReqEngineCeiling.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqEngineCeiling.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (the 9.3 generational magic). *)
From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qabs
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

(* ---- 0. Elementary Q-layer facts, all under the cec_ prefix ---- *)

(* positivity of [Z.of_nat (n+1) # 1] on the Q-layer; lia settles it through [Nat2Z] *)
Lemma cec_nat_pos : forall n : nat, Qlt 0 (Z.of_nat (n + 1) # 1).
Proof. intro n. unfold Qlt. simpl. lia. Qed.

Lemma cec_nat_pos0 : forall n : nat, (1 <= n)%nat -> Qlt 0 (Z.of_nat n # 1).
Proof. intros n Hn. unfold Qlt. simpl. lia. Qed.

(* Qeq-face nonvanishing, in the shape of [S03_QExp.q_neq_of_lt] (the upstream lemma now lives on the
   QltT/QeqT Set face and its [Not] is the S01 Set-carrier negation [A -> Empty_set], while this
   statement face keeps the Corelib [False]-based [~]; the two layers are bridged through
   [Qlt_to_QltT], [qeq_imp_qeqT] and the canonical empty match of this tree) *)
Lemma cec_neq_of_pos : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof.
  intros x Hx H0.
  exact (match S03_QExp.q_neq_of_lt x (Qlt_to_QltT 0 x Hx)
                         (qeq_imp_qeqT x 0 H0) with end).
Qed.

(* nonvanishing of a product on the Qeq face; [Qmult_integral_l] is itself stated on that face *)
Lemma cec_mult_neq0 : forall x y : Q, ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0).
Proof.
  intros x y Hx Hy H.
  apply Hy.
  exact (Qmult_integral_l x y Hx H).
Qed.

(* uniform closure of the field side conditions, which arrive as conjunctions
   of the form ~ d == 0 /\ ... as in the S03 split pattern; the routine splits
   conjunctions, takes premises directly, splits products, and decides
   positivity by lia (all on the Qeq face) *)
Ltac cec_nz :=
  repeat first
    [ assumption
    | split; cec_nz
    | apply cec_mult_neq0; cec_nz
    | apply cec_neq_of_pos; (assumption || (unfold Qlt; simpl; lia)) ].

(* positivity of the reciprocal, by the three-way case analysis on the numerator integer; the goal is taken on the defining face of Qinv *)
Lemma cec_inv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (/ x).
Proof.
  intros x Hx. destruct x as [a b]. unfold Qlt in Hx. simpl in Hx.
  destruct a.
  - lia.
  - unfold Qlt. simpl. lia.
  - lia.
Qed.

Lemma cec_inv_mult_pos : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qlt 0 (/ (x * y)).
Proof.
  intros x y Hx Hy. rewrite Qinv_mult_distr.
  apply Qmult_lt_0_compat; apply cec_inv_pos; assumption.
Qed.

(* x + y >= x, used in the monotone step of the induction; [Qplus_le_r] has iff shape and is awkward to apply directly, so the fact is proved here *)
Lemma cec_plus_r_le : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy. apply (Qle_trans x (x + 0) (x + y)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat x x 0 y); [apply Qle_refl | exact Hy].
Qed.

(* a local min as the reflection of [Qle_bool], on the same base as [QleT']; this keeps the development independent of the stdlib [Qminmax] spellings *)
Definition cec_min (x y : Q) : Q := if Qle_bool x y then x else y.

Lemma cec_min_ge : forall x y : Q, Qle y x -> cec_min x y == y.
Proof.
  intros x y Hyx. unfold cec_min. destruct (Qle_bool x y) eqn:E.
  - apply Qle_antisym; [| exact Hyx].
    apply (QleT'_to_Qle x y). unfold QleT'. rewrite E. exact id_refl.
  - reflexivity.
Qed.

(* strict order preservation under division by a common denominator, the /e slot of [Qmult_lt_compat_r], bridged by positivity of reciprocals *)
Lemma cec_div_same_denom_lt : forall a c e : Q,
  Qlt 0 e -> Qlt a c -> Qlt (a / e) (c / e).
Proof.
  intros a c e He Hac.
  unfold Qdiv.
  apply (Qmult_lt_compat_r _ _ _ (cec_inv_pos e He) Hac).
Qed.

(* strict comparison across denominators: a*d < c*b with b, d > 0 gives a/b < c/d *)
Lemma cec_lt_div_lt : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qlt (a * d) (c * b) -> Qlt (a / b) (c / d).
Proof.
  intros a b c d Hb Hd H.
  assert (E1 : a / b == (a * d) / (b * d)) by (field; cec_nz).
  assert (E2 : c / d == (c * b) / (b * d)) by (field; cec_nz).
  rewrite E1, E2.
  apply cec_div_same_denom_lt.
  - apply Qmult_lt_0_compat; assumption.
  - exact H.
Qed.

(* ---- 1. Harmonic numbers and corner constants ---- *)

(* H_k := the sum over j = 1..k of 1/j; the inner term is phrased uniformly as m+1 so the Z-image never shifts by one under Datatypes.S *)
Fixpoint cec_H (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => cec_H m + ((1 # 1) / (Z.of_nat (m + 1) # 1))
  end.

(* the corner constant f(k) := H_k - 1/(k+1), the exact Q-layer form of the corner limit of EXP-D1 T1 *)
Definition cec_pt (k : nat) : Q := cec_H k - ((1 # 1) / (Z.of_nat (k + 1) # 1)).

(* the four exact corner values of the EXP-D1 table: 1/2, 7/6, 19/12, 113/60 *)
Lemma cec_pt_1 : cec_pt 1 == (1 # 2).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_2 : cec_pt 2 == (7 # 6).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_3 : cec_pt 3 == (19 # 12).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_4 : cec_pt 4 == (113 # 60).
Proof. vm_compute. reflexivity. Qed.

(* the explicit increment of the monotone step, verified in exact fraction arithmetic: f(k+1) - f(k) = (k+3)/((k+1)(k+2)) *)
Lemma cec_pt_step_eq : forall k : nat,
  cec_pt (Datatypes.S k) ==
  cec_pt k + ((Z.of_nat (k + 3) # 1) / ((Z.of_nat (k + 1) # 1) * (Z.of_nat (k + 2) # 1))).
Proof.
  intro k.
  (* the Z-shapes of S n and n+c are aligned at the atom z#1, a form zify consumes directly, with no dependence on Nat2Z spellings *)
  assert (EA : forall n : nat, (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + (1 # 1)).
  { intro n. unfold Qeq, Qplus. simpl. lia. }
  assert (EB0 : (Z.of_nat (k + 1) # 1) == (Z.of_nat k # 1) + (1 # 1)).
  { unfold Qeq, Qplus. simpl. lia. }
  assert (EB1 : (Z.of_nat (k + 2) # 1) == (Z.of_nat k # 1) + ((1 # 1) + (1 # 1))).
  { unfold Qeq, Qplus. simpl. lia. }
  assert (EB2 : (Z.of_nat (k + 3) # 1) == (Z.of_nat k # 1) + ((1 # 1) + ((1 # 1) + (1 # 1)))).
  { unfold Qeq, Qplus. simpl. lia. }
  unfold cec_pt.
  change ((Datatypes.S k + 1)%nat) with (Datatypes.S (k + 1)).
  rewrite (EA (k + 1)%nat).
  cbn [cec_H].
  rewrite EB0.
  rewrite EB1, EB2.
  field; cec_nz.
Qed.

Lemma cec_pt_step_pos : forall k : nat,
  Qlt 0 ((Z.of_nat (k + 3) # 1) / ((Z.of_nat (k + 1) # 1) * (Z.of_nat (k + 2) # 1))).
Proof.
  intro k. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply (cec_nat_pos0 (k + 3)%nat). lia.
  - apply cec_inv_mult_pos.
    + apply (cec_nat_pos0 (k + 1)%nat). lia.
    + apply (cec_nat_pos0 (k + 2)%nat). lia.
Qed.

(* base case: f(5) = 127/60 in exact fractions, and it exceeds 2 *)
Lemma cec_pt_5 : cec_pt 5 == (127 # 60).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_two_lt_127_60 : Qlt (1 + 1)%Q (127 # 60).
Proof. unfold Qlt. simpl. lia. Qed.

(* strict lower bound by induction: k >= 5 gives 2 < f(k); the strict form is what lets the min tail take the value 2 *)
Lemma cec_pt_gt2 : forall k : nat, (5 <= k)%nat -> Qlt (1 + 1)%Q (cec_pt k).
Proof.
  induction k as [| m IH]; intro Hk.
  - lia.
  - destruct (Nat.eq_dec m 4) as [E4 | Hne].
    + subst m. rewrite cec_pt_5. apply cec_two_lt_127_60.
    + assert (Hm5 : (5 <= m)%nat) by lia.
      specialize (IH Hm5).
      assert (Hstep : Qle (cec_pt m) (cec_pt (Datatypes.S m))).
      { pose proof (cec_pt_step_pos m) as Hp.
        pose proof (cec_pt_step_eq m) as E.
        rewrite E.
        apply (cec_plus_r_le (cec_pt m)
                ((Z.of_nat (m + 3) # 1) /
                 ((Z.of_nat (m + 1) # 1) * (Z.of_nat (m + 2) # 1)))).
        apply Qlt_le_weak. exact Hp. }
      apply (Qlt_le_trans (1 + 1)%Q (cec_pt m) (cec_pt (Datatypes.S m)) IH Hstep).
Qed.

(* the G1 main statement: the harmonic lower bound, carried by QleT' on the Set face as a standalone carrier with no And mixture *)
Theorem cec_H_lower : forall k : nat, (5 <= k)%nat -> QleT' (1 + 1)%Q (cec_pt k).
Proof.
  intros k Hk.
  exact (Qle_to_QleT' (1 + 1)%Q (cec_pt k)
    (Qlt_le_weak (1 + 1)%Q (cec_pt k) (cec_pt_gt2 k Hk))).
Qed.


(* ---- 2. The truncated engine family ceiling c*(k) = min(H_k - 1/(k+1), 2) ---- *)

Definition cec_cstar (k : nat) : Q := cec_min (cec_pt k) (1 + 1)%Q.

(* the segment k >= 5: min(f(k), 2) = 2, selected at the right branch of [cec_min_ge] through the strict lower bound *)
Theorem cec_cstar_tail : forall k : nat, (5 <= k)%nat -> cec_cstar k == (1 + 1)%Q.
Proof.
  intros k Hk. unfold cec_cstar. apply cec_min_ge.
  apply Qlt_le_weak. apply cec_pt_gt2. exact Hk.
Qed.

(* the five-line piecewise statement of the min, its conjuncts Qeq equalities; each conjunct is introduced by apply conj in turn, so no conversion fires through the remaining goals *)
Theorem cec_trunc_sup :
  cec_cstar 1 == (1 # 2) /\
  cec_cstar 2 == (7 # 6) /\
  cec_cstar 3 == (19 # 12) /\
  cec_cstar 4 == (113 # 60) /\
  (forall k : nat, (5 <= k)%nat -> cec_cstar k == (1 + 1)%Q).
Proof.
  repeat apply conj.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact cec_cstar_tail.
Qed.

(* ---- 3. The second-order kernel coefficient -(k+1)/(2k) of the R6 nested tangent family ---- *)

(* an abstract binomial inversion engine: for s = a*v + b*v^2 + v^3*w with
   a > 0, the coefficient of s^2 in a*v is exactly -b/a^2, and the residual
   s^3*rho is displayed; the denominator (a+bv+v^2*w)^3 of rho evaluates to
   a^3 <> 0 at v = 0, so regularity is visible, and the identity was checked
   to vanish on 492 sampled inputs in exact rational arithmetic *)
Definition cec_smap (a b w v : Q) : Q := a * v + b * v * v + v * v * v * w.

Definition cec_rho (a b w v : Q) : Q :=
  (((2 * b * b / a - w) + (b * (b * b + (1 + 1)%Q * a * w) / (a * a)) * v
    + ((1 + 1)%Q * b * b * w / (a * a)) * v * v
    + (b * w * w / (a * a)) * v * v * v)
   / ((a + b * v + v * v * w)
      * ((a + b * v + v * v * w) * (a + b * v + v * v * w)))).

Lemma cec_inv2 : forall (a b w v : Q),
  Qlt 0 a -> ~ (cec_smap a b w v == 0) ->
  Qeq (a * v)
      (cec_smap a b w v - (b / (a * a)) * (cec_smap a b w v * cec_smap a b w v)
       + cec_smap a b w v * cec_smap a b w v * cec_smap a b w v
         * cec_rho a b w v).
Proof.
  intros a b w v Ha Hs.
  assert (Ha0 : ~ (a == 0)) by (apply cec_neq_of_pos; exact Ha).
  assert (Hden : ~ ((a + b * v + v * v * w) == 0)).
  { intro Hd. apply Hs. unfold cec_smap.
    assert (Ef : a * v + b * v * v + v * v * v * w == v * (a + b * v + v * v * w)) by ring.
    rewrite Ef, Hd. ring. }
  unfold cec_smap, cec_rho.
  field; cec_nz.
Qed.

(* the a, b and coefficient of the R6 family: a = k, b = k(k+1)/2, and the coefficient magnitude b/a^2 = (k+1)/(2k) *)
Definition cec_r6_s (k : nat) (v : Q) : Q := (1 # 1) / q_pow (1 - v) k - (1 # 1).
Definition cec_r6_bcoef (k : nat) : Q :=
  ((Z.of_nat k # 1) * ((Z.of_nat k # 1) + 1)) / ((1 + 1)%Q).
Definition cec_r6_coef (k : nat) : Q :=
  ((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)).

Lemma cec_bcoef_div_a2 : forall k : nat, (1 <= k)%nat ->
  cec_r6_bcoef k / ((Z.of_nat k # 1) * (Z.of_nat k # 1)) == cec_r6_coef k.
Proof.
  intros k Hk. unfold cec_r6_bcoef, cec_r6_coef.
  field; cec_nz.
Qed.

(* the R6 fingerprint, unconditional for general k: (k+1)/(2k) > 1/2, the family-wide form of the fact that each branch falls short by 1/(2k) *)
Lemma cec_coef_fingerprint : forall k : nat, (1 <= k)%nat -> Qlt (1 # 2) (cec_r6_coef k).
Proof.
  intros k Hk. unfold cec_r6_coef.
  apply (cec_lt_div_lt (1 # 1) ((1 + 1)%Q) ((Z.of_nat k # 1) + 1)
                       ((1 + 1)%Q * (Z.of_nat k # 1))).
  - unfold Qlt. simpl. lia.
  - apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply (cec_nat_pos0 k Hk)].
  - (* Qmult is locked behind a match on its Qmake arguments, and ring proves
     only polynomial identities because a Qmake over a Z sum is an opaque
     atom; the cross products are therefore reduced to additive polynomial
     forms in the atom z#1 before unfold and lia close the goal *)
    assert (E1 : (1 # 1) * (((1 + 1)%Q) * (Z.of_nat k # 1))
                 == (Z.of_nat k # 1) + (Z.of_nat k # 1)) by ring.
    assert (E2 : ((Z.of_nat k # 1) + 1) * ((1 + 1)%Q)
                 == ((Z.of_nat k # 1) + (Z.of_nat k # 1)) + ((1 + 1)%Q)) by ring.
    rewrite E1, E2.
    unfold Qlt. simpl. lia.
Qed.

(* the upper side of the R6 fingerprint: the coefficient magnitude (k+1)/(2k) <= 1 *)
Lemma cec_coef_le_1 : forall k : nat, (1 <= k)%nat -> Qle (cec_r6_coef k) (1 # 1).
Proof.
  intros k Hk. unfold cec_r6_coef.
  change (Qle (((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)))
              ((1 # 1) / (1 # 1))).
  apply QleT'_to_Qle.
  apply (S03_QExp.q_le_div_le ((Z.of_nat k # 1) + 1)
            ((1 + 1)%Q * (Z.of_nat k # 1)) (1 # 1) (1 # 1)).
  - apply Qlt_to_QltT.
    apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply (cec_nat_pos0 k Hk)].
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - apply Qle_to_QleT'.
    assert (E1 : ((Z.of_nat k # 1) + 1) * (1 # 1)
                 == (Z.of_nat k # 1) + (1 # 1)) by ring.
    assert (E2 : (1 # 1) * (((1 + 1)%Q) * (Z.of_nat k # 1))
                 == (Z.of_nat k # 1) + (Z.of_nat k # 1)) by ring.
    rewrite E1, E2.
    unfold Qle. simpl. lia.
Qed.

(* the G2b main statement, in general-k conditional form: the defining identity is an explicit premise, and the case left open is recorded as such *)
Theorem cec_kernel_coef : forall (k : nat) (v w : Q), (1 <= k)%nat ->
  ~ (cec_r6_s k v == 0) ->
  cec_r6_s k v == (Z.of_nat k # 1) * v + cec_r6_bcoef k * v * v + v * v * v * w ->
  Qeq ((Z.of_nat k # 1) * v)
      (cec_r6_s k v - cec_r6_coef k * (cec_r6_s k v * cec_r6_s k v)
       + cec_r6_s k v * cec_r6_s k v * cec_r6_s k v
         * cec_rho (Z.of_nat k # 1) (cec_r6_bcoef k) w v).
Proof.
  intros k v w Hk Hs Hpar.
  assert (Ha : Qlt 0 (Z.of_nat k # 1)) by (apply (cec_nat_pos0 k Hk)).
  assert (E : cec_r6_s k v == cec_smap (Z.of_nat k # 1) (cec_r6_bcoef k) w v).
  { unfold cec_smap. exact Hpar. }
  assert (Hs2 : ~ (cec_smap (Z.of_nat k # 1) (cec_r6_bcoef k) w v == 0)).
  { intro H0. apply Hs. rewrite E. exact H0. }
  pose proof (cec_inv2 (Z.of_nat k # 1) (cec_r6_bcoef k) w v Ha Hs2) as H.
  rewrite <- E in H.
  rewrite cec_bcoef_div_a2 in H by exact Hk.
  exact H.
Qed.

(* the k = 1 instance of the identity, closed unconditionally by field: 1/(1-v) - 1 == v + v^2 + v^3/(1-v) *)
Lemma cec_r6_param_k1 : forall v : Q, ~ ((1 # 1) - v == 0) ->
  cec_r6_s 1 v == (1 # 1) * v + cec_r6_bcoef 1 * v * v + v * v * v * ((1 # 1) / (1 - v)).
Proof.
  intros v Hv. unfold cec_r6_s, cec_r6_bcoef.
  cbn [q_pow].
  field; cec_nz.
Qed.

(* the k = 1 coefficient instance, unconditional: the s^2 coefficient is -cec_r6_coef 1 = -1 = -(1+1)/(2*1) *)
Theorem cec_kernel_coef_k1 : forall v : Q, ~ ((1 # 1) - v == 0) ->
  ~ (cec_r6_s 1 v == 0) ->
  Qeq ((1 # 1) * v)
      (cec_r6_s 1 v - cec_r6_coef 1 * (cec_r6_s 1 v * cec_r6_s 1 v)
       + cec_r6_s 1 v * cec_r6_s 1 v * cec_r6_s 1 v
         * cec_rho (1 # 1) (cec_r6_bcoef 1) ((1 # 1) / (1 - v)) v).
Proof.
  intros v Hv Hs.
  apply (cec_kernel_coef 1 v ((1 # 1) / (1 - v))).
  - lia.
  - exact Hs.
  - apply cec_r6_param_k1. exact Hv.
Qed.

(* the textbook literal form in the variable s: s/(1+s) = s - s^2 + s^3/(1+s), with coefficient exactly -1 *)
Lemma cec_kernel_coef_literal_s : forall s : Q, ~ ((s + (1 # 1)) == 0) ->
  Qeq (s / (s + (1 # 1)))
      (s - (1 # 1) * (s * s) + s * s * s * ((1 # 1) / (s + (1 # 1)))).
Proof.
  intros s Hs. field; cec_nz.
Qed.

(* ---- 4. The nested tangent family ceiling 2(k-1)/k < 2, strict ---- *)

Definition cec_tg (m : nat) : Q :=
  ((1 + 1)%Q * (Z.of_nat m # 1)) / (Z.of_nat (m + 1) # 1).

(* the strict ceiling on the QltT Set face: 2m/(m+1) < 2 follows from 2m < 2(m+1) *)
Theorem cec_tangent_ceiling : forall m : nat, QltT (cec_tg m) (1 + 1)%Q.
Proof.
  intro m. apply Qlt_to_QltT.
  apply (cec_lt_div_lt ((1 + 1)%Q * (Z.of_nat m # 1)) (Z.of_nat (m + 1) # 1)
                       (1 + 1)%Q (1 # 1)).
  - apply (cec_nat_pos m).
  - unfold Qlt. simpl. lia.
  - assert (E1 : (((1 + 1)%Q * (Z.of_nat m # 1)) * (1 # 1))
                 == (Z.of_nat m # 1) + (Z.of_nat m # 1)) by ring.
    assert (E2 : ((1 + 1)%Q * (Z.of_nat (m + 1) # 1))
                 == (Z.of_nat (m + 1) # 1) + (Z.of_nat (m + 1) # 1)) by ring.
    rewrite E1, E2.
    unfold Qlt. simpl. lia.
Qed.

(* the QleT' companion statement, the <= form on the Set face *)
Theorem cec_tangent_le : forall m : nat, QleT' (cec_tg m) (1 + 1)%Q.
Proof. intro m. exact (qltT_leT' (cec_tg m) (1 + 1)%Q (cec_tangent_ceiling m)). Qed.

(* the gap identity 2 - 2m/(m+1) == 2/(m+1), the exact Q-layer form of the gap being exactly 2/k *)
Theorem cec_tangent_gap : forall m : nat,
  (1 + 1)%Q - cec_tg m == ((1 + 1)%Q) / (Z.of_nat (m + 1) # 1).
Proof.
  intro m. unfold cec_tg.
  (* first align the Z-shapes through z_{m+1} == z_m + 1, a bridge lia accepts; once the expression lives on the single atom z#1, field closes it *)
  assert (EB : (Z.of_nat (m + 1) # 1) == (Z.of_nat m # 1) + (1 # 1)).
  { unfold Qeq, Qplus. simpl. lia. }
  rewrite EB.
  field; cec_nz.
Qed.

(* ---- 5. Global-context audit: Print Assumptions on the main exits ---- *)

Print Assumptions cec_trunc_sup.
Print Assumptions cec_H_lower.
Print Assumptions cec_kernel_coef.
Print Assumptions cec_kernel_coef_k1.
Print Assumptions cec_tangent_ceiling.
Print Assumptions cec_tangent_gap.
