(* ConstructiveWorld-Set — zeta(2) double-integral estimate modules. *)

(** * abl_z2_pointwise: pointwise control for the Beukers zeta(2) integrand family.

    Mission.  Pointwise exponential control for the integrand family of
      the Beukers 1979 zeta(2) irrationality double integral: writing
      N := x(1-x)y(1-y) on the closed square 0 <= x,y <= 1, proves
      10N <= 1-xy ([zb2_ten_le_uv]), the square-identity pair giving
      4N <= (1-xy)^2 ([zb2_N4_le_dsq]), and the composite
      4 * 10^n * N^(n+1) <= (1-xy)^(n+2) ([zb2_pointwise_decay]), i.e.
      the family is pointwise at most (1/4)*(1/10)^n.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [Arith.Arith],
      [Lia]; rational linear estimates go through explicit lemma chains
      ([Qle_trans], [Qplus_le_compat], [Qmult_le_compat_r], squares).

    References.  The baseline module abl_z2_pointwise.v in
      ConstructiveWorld-Main, whose statement names are carried over
      here verbatim (statement-face Set-carrier completion); the
      estimates are the pointwise step of Beukers 1979 (Bull. London
      Math. Soc. 11).

    Constructivity.  Main statements are carried by [Set] via the
      self-contained comparators [zb2_id] and [zb2_qle] (the shape of
      [QleT']); Prop-face [Qle]/[Qeq] serve only as in-body scaffolding;
      nonlinear inequalities go by explicit square decompositions;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_z2_pointwise.v]
      compiles cleanly (exit 0); its artifact begins [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.

Open Scope Q_scope.

(* ================= Section 0. Self-carried Set-layer comparators ================= *)

(* The Set-layer identity type (the shape of the development's [Id]; self-contained). *)
Inductive zb2_id (A : Set) (x : A) : A -> Set :=
  zb2_idrefl : zb2_id A x x.

(* Set-layer witness for the Q order: [Qle_bool] reduced to true (the shape of [QleT']). *)
Definition zb2_qle (x y : Q) : Set := zb2_id bool (Qle_bool x y) true.

(* Constant anchor: [0 <= 1]. *)
Lemma zb2_0_le_1 : zb2_qle 0 1.
Proof. unfold zb2_qle. apply zb2_idrefl. Qed.

(* Bridge: lift the Prop-face [Qle] to the Set face. *)
Lemma zb2_qle_of_Qle : forall x y : Q, x <= y -> zb2_qle x y.
Proof.
  intros x y H.
  assert (Hb : Qle_bool x y = true) by exact (proj2 (Qle_bool_iff x y) H).
  unfold zb2_qle. rewrite Hb. apply zb2_idrefl.
Qed.

(* Bridge: drop the Set face back to the Prop-face [Qle] (reasoning scaffold). *)
Lemma zb2_qle_to_Qle : forall x y : Q, zb2_qle x y -> x <= y.
Proof.
  intros x y H. apply (proj1 (Qle_bool_iff x y)).
  destruct H. reflexivity.
Qed.

(* From [Qeq] into the order (expansion of [Qeq] and [Qle] over [Qnum]/[QDen]). *)
Lemma zb2_qeq_imp_le : forall x y : Q, x == y -> zb2_qle y x.
Proof.
  intros x y Hxy. apply zb2_qle_of_Qle. unfold Qle. unfold Qeq in Hxy.
  rewrite Hxy. apply Z.le_refl.
Qed.

(* Exchange along equality: [a == b] and [0 <= a] give [a <= b]. *)
Lemma zb2_le_eq_swap : forall a b : Q, a == b -> 0 <= a -> zb2_qle a b.
Proof.
  intros a b Hab Ha.
  exact (zb2_qeq_imp_le b a (Qeq_sym a b Hab)).
Qed.

(* Exchange along equality with no premises: [a == b] gives [a <= b]. *)
Lemma zb2_le_eq : forall a b : Q, a == b -> zb2_qle a b.
Proof.
  intros a b Hab.
  exact (zb2_qeq_imp_le b a (Qeq_sym a b Hab)).
Qed.

(* Nonnegativity transports along [Qeq]: [a == b] and [0 <= a] give [0 <= b]. *)
Lemma zb2_ge0_wd : forall a b : Q, a == b -> 0 <= a -> zb2_qle 0 b.
Proof.
  intros a b Hab Ha.
  apply zb2_qle_of_Qle.
  apply (Qle_trans 0 a b).
  - exact Ha.
  - exact (zb2_qle_to_Qle a b (zb2_le_eq_swap a b Hab Ha)).
Qed.

(* Same-side rewrite of the left argument along [Qeq]. *)
Lemma zb2_qle_wd_l : forall x y z : Q, x == y -> zb2_qle x z -> zb2_qle y z.
Proof.
  intros x y z Hxy Hxz. apply zb2_qle_of_Qle.
  apply (Qle_trans y x z)
  ; [ exact (zb2_qle_to_Qle _ _ (zb2_qeq_imp_le x y Hxy))
    | apply zb2_qle_to_Qle; exact Hxz ].
Qed.

(* Same-side rewrite of the right argument along [Qeq]. *)
Lemma zb2_qle_wd_r : forall x y z : Q, y == z -> zb2_qle x y -> zb2_qle x z.
Proof.
  intros x y z Hyz Hxy. apply zb2_qle_of_Qle.
  apply (Qle_trans x y z)
  ; [ apply zb2_qle_to_Qle; exact Hxy
    | exact (zb2_qle_to_Qle _ _ (zb2_qeq_imp_le z y (Qeq_sym y z Hyz))) ].
Qed.

(* ================= Section A. Linear estimate atoms (explicit chains) ================= *)

(* Adding on the right: [0 <= b] gives [a <= a + b]. *)
Lemma zb2_add_ge0_le : forall a b : Q, 0 <= b -> zb2_qle a (a + b).
Proof.
  intros a b H.
  apply zb2_qle_of_Qle.
  apply (Qle_trans a (a + 0) (a + b)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat a a 0 b); [ apply Qle_refl | exact H ].
Qed.

(* Shifting by a nonnegative difference: [0 <= b - a] gives [a <= b]. *)
Lemma zb2_sub_ge0 : forall a b : Q, 0 <= b - a -> zb2_qle a b.
Proof.
  intros a b H.
  apply (zb2_qle_wd_r a (a + (b - a)) b).
  - assert (Heq : a + (b - a) == b) by ring. exact Heq.
  - apply zb2_add_ge0_le. exact H.
Qed.

(* Subtracting an upper bound: [a <= b] gives [0 <= b - a]. *)
Lemma zb2_le_sub : forall a b : Q, a <= b -> zb2_qle 0 (b - a).
Proof.
  intros a b H.
  apply zb2_qle_of_Qle.
  assert (H1 : a + (- a) <= b + (- a))
    by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
  assert (Heq1 : a + (- a) == 0) by ring.
  assert (Heq2 : b + (- a) == b - a) by ring.
  rewrite Heq1, Heq2 in H1. exact H1.
Qed.

(* Moving a bound across negation: [s <= 0] gives [0 <= -s]. *)
Lemma zb2_le0_opp : forall s : Q, s <= 0 -> zb2_qle 0 (- s).
Proof.
  intros s H.
  apply zb2_qle_of_Qle.
  assert (H1 : s + (- s) <= 0 + (- s))
    by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
  assert (Heq1 : s + (- s) == 0) by ring.
  assert (Heq2 : 0 + (- s) == - s) by ring.
  rewrite Heq1, Heq2 in H1. exact H1.
Qed.

(* Negating a nonnegative: [0 <= t] gives [-t <= 0]. *)
Lemma zb2_ge0_opp_le : forall t : Q, 0 <= t -> zb2_qle (- t) 0.
Proof.
  intros t H.
  apply zb2_qle_of_Qle.
  assert (H1 : (- t) + 0 <= (- t) + t)
    by (apply (Qplus_le_compat (- t) (- t) 0 t); [ apply Qle_refl | exact H ]).
  assert (Heq1 : (- t) + t == 0) by ring.
  rewrite Heq1 in H1. rewrite Qplus_0_r in H1. exact H1.
Qed.

(* Subtracting from a common left side: [q <= r] gives [p - r <= p - q]. *)
Lemma zb2_minus_le : forall p q r : Q, q <= r -> zb2_qle (p - r) (p - q).
Proof.
  intros p q r H. apply (zb2_sub_ge0 (p - r) (p - q)).
  assert (Heq : (p - q) - (p - r) == r - q) by ring.
  rewrite Heq. exact (zb2_qle_to_Qle _ _ (zb2_le_sub q r H)).
Qed.

(* Shifting by a nonnegative: [0 <= t] gives [c - t <= c]. *)
Lemma zb2_minus_ge0 : forall t c : Q, 0 <= t -> zb2_qle (c - t) c.
Proof.
  intros t c H. apply (zb2_sub_ge0 (c - t) c).
  assert (Heq : c - (c - t) == t) by ring.
  rewrite Heq. exact H.
Qed.

(* Squares are nonnegative ([s*s >= 0]), by the cases 0 < s and s <= 0
   (substituting -s in the negative case). *)
Lemma zb2_sq_ge0 : forall s : Q, zb2_qle 0 (s * s).
Proof.
  intro s. apply zb2_qle_of_Qle.
  destruct (Qlt_le_dec 0 s) as [Hlt | Hle].
  - apply Qmult_le_0_compat
    ; [ apply Qlt_le_weak; exact Hlt | apply Qlt_le_weak; exact Hlt ].
  - assert (Hn : 0 <= - s) by exact (zb2_qle_to_Qle _ _ (zb2_le0_opp s Hle)).
    assert (Heq : s * s == (- s) * (- s)) by ring.
    rewrite Heq. apply Qmult_le_0_compat; exact Hn.
Qed.

(* Products of two nonnegative factors are nonnegative. *)
Lemma zb2_mult2_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> zb2_qle 0 (a * b).
Proof. intros a b Ha Hb. apply zb2_qle_of_Qle. apply Qmult_le_0_compat; assumption. Qed.

(* Products of four nonnegative factors are nonnegative. *)
Lemma zb2_mult4_ge0 : forall a b c d : Q,
  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> zb2_qle 0 (((a * b) * c) * d).
Proof.
  intros a b c d Ha Hb Hc Hd.
  apply zb2_qle_of_Qle.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply Qmult_le_0_compat; assumption.
    + exact Hc.
  - exact Hd.
Qed.

(* Dividing by a positive factor: [a*c >= 0] and [c > 0] give [a >= 0]
   (for a < 0 the product a*c would be negative, a contradiction). *)
Lemma zb2_div_pos : forall a c : Q, 0 <= a * c -> 0 < c -> zb2_qle 0 a.
Proof.
  intros a c Hac Hc.
  apply zb2_qle_of_Qle.
  destruct (Qlt_le_dec 0 a) as [Hlt | Hle].
  - apply Qlt_le_weak; exact Hlt.
  - destruct (Qlt_le_dec a 0) as [Hneg | Hzero].
    + exfalso.
      pose proof (Qmult_lt_compat_r a 0 c Hc Hneg) as Hbad.
      assert (Heq : 0 * c == 0) by ring.
      rewrite Heq in Hbad.
      exact (Qlt_not_le (a * c) 0 Hbad Hac).
    + assert (Ha0 : a == 0) by (apply Qle_antisym; assumption).
      rewrite Ha0. apply Qle_refl.
Qed.

(* Rational powers (locally defined, isomorphic to the standard one). *)
Fixpoint zb2_pow (t : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | S k' => t * zb2_pow t k'
  end.

Lemma zb2_pow_ge0 : forall (t : Q) (k : nat), 0 <= t -> zb2_qle 0 (zb2_pow t k).
Proof.
  intros t k Ht. apply zb2_qle_of_Qle.
  induction k as [| k' IH].
  - simpl. exact (zb2_qle_to_Qle 0 1 zb2_0_le_1).
  - simpl. apply Qmult_le_0_compat; [ exact Ht | exact IH ].
Qed.

(* Products stay under one: [0 <= x <= 1] and [0 <= y <= 1] give [x*y <= 1]. *)
Lemma zb2_xy_le_1 : forall x y : Q,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> zb2_qle (x * y) 1.
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2.
  apply zb2_qle_of_Qle.
  apply (Qle_trans (x * y) (1 * 1) 1).
  - apply (Qmult_le_compat_nonneg x 1 y 1)
    ; [ split; assumption | split; assumption ].
  - assert (Heq : 1 * 1 == 1) by ring.
    rewrite Heq. apply Qle_refl.
Qed.


(* Positivity of the constants involved (Z-domain literals). *)
Lemma zb2_qmake_pos : forall (a : Z) (b : positive),
  (0 <= a)%Z -> zb2_qle 0 (a # b)%Q.
Proof.
  intros a b Ha.
  apply zb2_qle_of_Qle. unfold Qle. simpl. lia.
Qed.

Lemma zb2_nat_pos : forall n : nat, zb2_qle 0 (Z.of_nat n # 1)%Q.
Proof.
  intro n. apply zb2_qle_of_Qle.
  apply (proj1 (Qle_bool_iff 0 (Z.of_nat n # 1))).
  destruct n as [| n']; reflexivity.
Qed.

(* Paired monotonicity: [a <= b], [c <= d] with all factors nonnegative give
   [c*a <= d*b]. *)
Lemma zb2_mono_pair : forall a b c d : Q,
  a <= b -> c <= d -> 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
  zb2_qle (c * a) (d * b).
Proof.
  intros a b c d Hab Hcd Ha Hb Hc Hd.
  apply zb2_qle_of_Qle.
  apply (Qle_trans (c * a) (d * a) (d * b)).
  - apply (Qmult_le_compat_r c d a); [ exact Hcd | exact Ha ].
  - apply (Qmult_le_compat_nonneg d d a b)
    ; [ split; [ exact Hd | apply Qle_refl ] | split; [ exact Ha | exact Hab ] ].
Qed.

(* ================= Section B. The main inequality 10N <= 1 - xy ================= *)

(* The main inequality (substituted form): 0 <= u,v <= 1 gives
   10 * u(1-u)v(1-v) <= u+v-uv.
   Certificate chain (write m = u+v, k = uv; F := u+v-uv-10u(1-u)v(1-v)):
   F = m-k(11-10m+10k) >= m-k((5/2)(2-m)^2+1) >= m-(m^2/4)((5/2)(2-m)^2+1)
     = (m/8)(8-2m-5m(2-m)^2) >= 0. *)
Lemma zb2_ten_le_uv : forall u v : Q,
  0 <= u <= 1 -> 0 <= v <= 1 ->
  zb2_qle (10 * u * (1 - u) * v * (1 - v)) (u + v - u * v).
Proof.
  intros u v [Hu1 Hu2] [Hv1 Hv2].
  apply zb2_qle_of_Qle.
  assert (Hzb2_0_le_1 : (0 <= 1)%Q) by exact (zb2_qle_to_Qle 0 1 zb2_0_le_1).
  assert (Hzb2_qeq_imp_le : forall p q : Q, p == q -> q <= p)
    by (intros p q H; exact (zb2_qle_to_Qle _ _ (zb2_qeq_imp_le p q H))).
  assert (Hzb2_le_eq_swap : forall a b : Q, a == b -> 0 <= a -> a <= b)
    by (intros a b Hab Ha; exact (zb2_qle_to_Qle _ _ (zb2_le_eq_swap a b Hab Ha))).
  assert (Hzb2_le_eq : forall a b : Q, a == b -> a <= b)
    by (intros a b Hab; exact (zb2_qle_to_Qle _ _ (zb2_le_eq a b Hab))).
  assert (Hzb2_ge0_wd : forall a b : Q, a == b -> 0 <= a -> 0 <= b)
    by (intros a b Hab Ha; exact (zb2_qle_to_Qle _ _ (zb2_ge0_wd a b Hab Ha))).
  assert (Hzb2_add_ge0_le : forall a b : Q, 0 <= b -> a <= a + b)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_add_ge0_le a b H))).
  assert (Hzb2_sub_ge0 : forall a b : Q, 0 <= b - a -> a <= b)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_sub_ge0 a b H))).
  assert (Hzb2_le_sub : forall a b : Q, a <= b -> 0 <= b - a)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_le_sub a b H))).
  assert (Hzb2_le0_opp : forall s : Q, s <= 0 -> 0 <= - s)
    by (intros s H; exact (zb2_qle_to_Qle _ _ (zb2_le0_opp s H))).
  assert (Hzb2_ge0_opp_le : forall t : Q, 0 <= t -> - t <= 0)
    by (intros t H; exact (zb2_qle_to_Qle _ _ (zb2_ge0_opp_le t H))).
  assert (Hzb2_minus_le : forall p q r : Q, q <= r -> p - r <= p - q)
    by (intros p q r H; exact (zb2_qle_to_Qle _ _ (zb2_minus_le p q r H))).
  assert (Hzb2_minus_ge0 : forall t c : Q, 0 <= t -> c - t <= c)
    by (intros t c H; exact (zb2_qle_to_Qle _ _ (zb2_minus_ge0 t c H))).
  assert (Hzb2_sq_ge0 : forall s : Q, 0 <= s * s)
    by (intro s; exact (zb2_qle_to_Qle _ _ (zb2_sq_ge0 s))).
  assert (Hzb2_mult2_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b)
    by (intros a b Ha Hb; exact (zb2_qle_to_Qle _ _ (zb2_mult2_ge0 a b Ha Hb))).
  assert (Hzb2_mult4_ge0 : forall a b c d : Q,
      0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> 0 <= ((a * b) * c) * d)
    by (intros a b c d Ha Hb Hc Hd;
        exact (zb2_qle_to_Qle _ _ (zb2_mult4_ge0 a b c d Ha Hb Hc Hd))).
  assert (Hzb2_div_pos : forall a c : Q, 0 <= a * c -> 0 < c -> 0 <= a)
    by (intros a c Hac Hc; exact (zb2_qle_to_Qle _ _ (zb2_div_pos a c Hac Hc))).
  assert (Hzb2_pow_ge0 : forall (t : Q) (k : nat), 0 <= t -> 0 <= zb2_pow t k)
    by (intros t k Ht; exact (zb2_qle_to_Qle _ _ (zb2_pow_ge0 t k Ht))).
  assert (Hzb2_xy_le_1 : forall p q : Q,
      0 <= p -> p <= 1 -> 0 <= q -> q <= 1 -> p * q <= 1)
    by (intros p q Ha Hb Hc Hd; exact (zb2_qle_to_Qle _ _ (zb2_xy_le_1 p q Ha Hb Hc Hd))).
  assert (Hzb2_qmake_pos : forall (a : Z) (b : positive), (0 <= a)%Z -> 0 <= (a # b)%Q)
    by (intros a b Ha; exact (zb2_qle_to_Qle _ _ (zb2_qmake_pos a b Ha))).
  assert (Hzb2_nat_pos : forall k0 : nat, 0 <= (Z.of_nat k0 # 1)%Q)
    by (intro k0; exact (zb2_qle_to_Qle _ _ (zb2_nat_pos k0))).
  assert (Hzb2_mono_pair : forall a b c d : Q,
      a <= b -> c <= d -> 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> c * a <= d * b)
    by (intros a b c d Hab Hcd Ha Hb Hc Hd;
        exact (zb2_qle_to_Qle _ _ (zb2_mono_pair a b c d Hab Hcd Ha Hb Hc Hd))).
  assert (Hk0 : 0 <= u * v) by (apply Hzb2_mult2_ge0; assumption).
  assert (Hm0 : 0 <= u + v).
  { apply (Qle_trans 0 (0 + 0) (u + v)).
    - rewrite Qplus_0_l. apply Qle_refl.
    - apply (Qplus_le_compat 0 u 0 v); assumption. }
  assert (Hm2 : (u + v) <= 2).
  { apply (Qle_trans (u + v) (1 + 1) 2).
    - apply (Qplus_le_compat u 1 v 1); assumption.
    - assert (Heq : 1 + 1 == 2) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (H4k : 0 <= (u+v)*(u+v) - 4*(u*v)).
  { assert (Heq : (u+v)*(u+v) - 4*(u*v) == (u-v)*(u-v)) by ring.
    rewrite Heq. apply Hzb2_sq_ge0. }
(* Linear consequences of H4k: 10k <= (5/2)m^2 and k <= m^2/4. *)
  assert (HBB : 10 * (u*v) <= (5#2)*(u+v)*(u+v)).
  { apply (Qle_trans (10 * (u*v))
      (10 * (u*v) + (5#2) * ((u+v)*(u+v) - 4*(u*v)))
      ((5#2)*(u+v)*(u+v))).
    - apply Hzb2_add_ge0_le.
      apply (Hzb2_mult2_ge0 (5#2) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (Hzb2_qmake_pos (5%Z) 2%positive); lia | exact H4k ].
    - assert (Heq : 10 * (u*v) + (5#2) * ((u+v)*(u+v) - 4*(u*v))
                 == (5#2)*(u+v)*(u+v)) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk_le : u * v <= ((u+v)*(u+v)) * (1#4)).
  { apply (Qle_trans (u * v)
      (u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4))
      (((u+v)*(u+v)) * (1#4))).
    - apply Hzb2_add_ge0_le.
      assert (Heqc : ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                  == (1#4) * ((u+v)*(u+v) - 4*(u*v))) by ring.
      rewrite Heqc.
      apply (Hzb2_mult2_ge0 (1#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (Hzb2_qmake_pos (1%Z) 4%positive); lia | exact H4k ].
    - assert (Heq : u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                 == ((u+v)*(u+v)) * (1#4)) by ring.
      rewrite Heq. apply Qle_refl. }
(* Factor bounds: B <= Bstar, and Bstar = (5/2)(2-m)^2+1 >= 0. *)
  assert (HBp : 0 <= 11 - 10*(u+v) + (5#2)*(u+v)*(u+v)).
  { assert (Hid0 : 11 - 10*(u+v) + (5#2)*(u+v)*(u+v)
                 == (5#2)*(2-(u+v))*(2-(u+v)) + 1) by ring.
    rewrite Hid0.
    assert (Hs : 0 <= (2-(u+v))*(2-(u+v))) by apply Hzb2_sq_ge0.
    assert (HX : 0 <= (5#2)*(2-(u+v))*(2-(u+v))).
    { assert (Hasso : (5#2)*(2-(u+v))*(2-(u+v))
                    == (5#2)*((2-(u+v))*(2-(u+v)))) by ring.
      rewrite Hasso.
      apply (Hzb2_mult2_ge0 (5#2) ((2-(u+v))*(2-(u+v)))).
      - apply (Hzb2_qmake_pos (5%Z) 2%positive). lia.
      - exact Hs. }
    apply (Qle_trans 0 ((5#2)*(2-(u+v))*(2-(u+v)))
                      (((5#2)*(2-(u+v))*(2-(u+v))) + 1)).
    - exact HX.
    - apply Hzb2_add_ge0_le. exact Hzb2_0_le_1. }
  assert (HBs : 11 - 10*(u+v) + 10*(u*v)
             <= 11 - 10*(u+v) + (5#2)*(u+v)*(u+v)).
  { apply (Qplus_le_compat (11 - 10*(u+v)) (11 - 10*(u+v))
             (10*(u*v)) ((5#2)*(u+v)*(u+v)))
    ; [ apply Qle_refl | exact HBB ]. }
(* Step one: k*B <= k*Bstar. *)
  assert (HkBB : (u*v) * (11 - 10*(u+v) + 10*(u*v))
              <= (u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (11 - 10*(u+v) + 10*(u*v))
                  (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)) (u*v) HBs Hk0) as H.
    assert (Heq1 : (u*v) * (11 - 10*(u+v) + 10*(u*v))
                 == (11 - 10*(u+v) + 10*(u*v)) * (u*v)) by ring.
    assert (Heq2 : (u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))
                 == (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)) * (u*v)) by ring.
    rewrite <- Heq1, <- Heq2 in H. exact H. }
(* Step two: k*Bstar <= (m^2/4)*Bstar. *)
  assert (HkB2 : (u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))
              <= (((u+v)*(u+v)) * (1#4)) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (u*v) (((u+v)*(u+v)) * (1#4))
                  (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)) Hk_le HBp) as H.
    exact H. }
(* The single-variable final expression is nonnegative (two ranges). *)
  assert (Hlow : 0 <= ((u+v) * (1#8))
                   * (8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v)))).
  { destruct (Qlt_le_dec (u+v) 1) as [Hm1 | Hm3].
    - (* Range m <= 1: m(2-m)^2 <= 32/27. *)
      assert (Hsq : 0 <= (3*(u+v)-2)*(3*(u+v)-2)) by apply Hzb2_sq_ge0.
      assert (Hfac : 32 - 27*(u+v)*(2-(u+v))*(2-(u+v))
                  == (3*(u+v)-2)*(3*(u+v)-2)*(8-3*(u+v))) by ring.
      assert (Hprod : 0 <= 32 - 27*(u+v)*(2-(u+v))*(2-(u+v))).
      { rewrite Hfac.
        apply (Hzb2_mult2_ge0 ((3*(u+v)-2)*(3*(u+v)-2)) (8-3*(u+v)))
        ; [ exact Hsq | ].
        assert (H1m : 0 <= 1 - (u+v)) by (apply (Hzb2_le_sub (u+v) 1); exact (Qlt_le_weak (u+v) 1 Hm1)).
        assert (Hide : 8 - 3*(u+v) == 5 + 3*(1-(u+v))) by ring.
        rewrite Hide.
        apply (Qle_trans 0 5 (5 + 3*(1-(u+v)))).
        + apply (Hzb2_nat_pos 5%nat).
        + apply Hzb2_add_ge0_le.
          apply (Hzb2_mult2_ge0 3); [ apply (Hzb2_nat_pos 3%nat) | exact H1m ]. }
      assert (Hd : (u+v)*(2-(u+v))*(2-(u+v)) <= (32#27)).
      { apply (Hzb2_sub_ge0 ((u+v)*(2-(u+v))*(2-(u+v))) (32#27)).
        assert (H0b : 0 <= (32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27)).
        { apply (Hzb2_mult2_ge0 (32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) (1#27))
          ; [ exact Hprod | apply (Hzb2_qmake_pos (1%Z) 27%positive); lia ]. }
        assert (Heq2 : (32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27)
                    == (32#27) - (u+v)*(2-(u+v))*(2-(u+v))) by ring.
        apply (Qle_trans 0
                 ((32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27))
                 ((32#27) - (u+v)*(2-(u+v))*(2-(u+v)))).
        - exact H0b.
        - apply (Hzb2_le_eq_swap
                   ((32 - 27*(u+v)*(2-(u+v))*(2-(u+v))) * (1#27))
                   ((32#27) - (u+v)*(2-(u+v))*(2-(u+v)))).
          + exact Heq2.
          + exact H0b. }
      apply Qmult_le_0_compat.
      + apply (Hzb2_mult2_ge0 (u+v) (1#8))
        ; [ exact Hm0 | apply (Hzb2_qmake_pos (1%Z) 8%positive); lia ].
      + assert (H1m : 0 <= 1 - (u+v)) by (apply (Hzb2_le_sub (u+v) 1); exact (Qlt_le_weak (u+v) 1 Hm1)).
        assert (Hp2 : 0 <= 2*(1-(u+v)))
          by (apply (Hzb2_mult2_ge0 2); [ apply (Hzb2_nat_pos 2%nat) | exact H1m ]).
        assert (Hp3 : 0 <= 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v))))
          by (apply (Hzb2_mult2_ge0 5)
            ; [ apply (Hzb2_nat_pos 5%nat)
              | apply (Hzb2_le_sub ((u+v)*(2-(u+v))*(2-(u+v))) (32#27))
              ; exact Hd ]).
        assert (Hide : 8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))
                    == (2#27) + 2*(1-(u+v))
                         + 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v)))) by ring.
        rewrite Hide.
        apply (Qle_trans 0 (2#27)
                         ((2#27) + 2*(1-(u+v))
                                + 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v))))).
        { apply (Hzb2_qmake_pos (2%Z) 27%positive); lia. }
        { apply (Qle_trans (2#27) ((2#27) + 2*(1-(u+v)))
                           ((2#27) + 2*(1-(u+v))
                                  + 5*((32#27) - (u+v)*(2-(u+v))*(2-(u+v))))).
          { apply (Qplus_le_compat (2#27) (2#27) 0 (2*(1-(u+v))))
            ; [ apply Qle_refl | exact Hp2 ]. }
          { apply Hzb2_add_ge0_le; exact Hp3. } }
    - (* Range m >= 1: w = 2-m in [0,1], and 5w(w-1)^2+(4-3w) >= 1. *)
      assert (Hwge : 0 <= 2-(u+v)) by (apply (Hzb2_le_sub (u+v) 2); exact Hm2).
      assert (Hwle : (2-(u+v)) <= 1).
      { assert (Hm4 : 0 <= (u+v) - 1)
          by (apply (Hzb2_le_sub 1 (u+v)); exact Hm3).
        apply (Hzb2_sub_ge0 (2-(u+v)) 1).
        assert (Heq : 1 - (2-(u+v)) == (u+v) - 1) by ring.
        rewrite Heq. apply (Hzb2_le_sub 1 (u+v)). exact Hm3. }
      assert (Hid3 : 8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))
                  == 5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1)
                   + (4 - 3*(2-(u+v)))) by ring.
      assert (Hs0 : 0 <= (2-(u+v)-1)*(2-(u+v)-1)) by apply Hzb2_sq_ge0.
      assert (Hasso2 : (5*(2-(u+v))*((2-(u+v)-1)*(2-(u+v)-1)))
                     == 5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1)) by ring.
      assert (Hp1g : 0 <= 5*(2-(u+v))*((2-(u+v)-1)*(2-(u+v)-1))).
      { apply (Hzb2_mult2_ge0 (5*(2-(u+v))) ((2-(u+v)-1)*(2-(u+v)-1))).
        + apply (Hzb2_mult2_ge0 5); [ apply (Hzb2_nat_pos 5%nat) | exact Hwge ].
        + exact Hs0. }
      assert (Hp1 : 0 <= 5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1))
        by (apply (Hzb2_ge0_wd _ _ Hasso2 Hp1g)).
      assert (H4m : 0 <= 4 - 3*(2-(u+v))).
      { assert (Hide : 4 - 3*(2-(u+v)) == 3*(1-(2-(u+v))) + 1) by ring.
        rewrite Hide.
        assert (H1w : 0 <= 1 - (2-(u+v)))
          by (apply (Hzb2_le_sub (2-(u+v)) 1); exact Hwle).
        apply (Qle_trans 0 (3*(1-(2-(u+v)))))
        ; [ apply (Hzb2_mult2_ge0 3); [ apply (Hzb2_nat_pos 3%nat) | exact H1w ]
          | apply Hzb2_add_ge0_le; exact Hzb2_0_le_1 ]. }
      rewrite Hid3.
      apply Qmult_le_0_compat.
      + apply (Hzb2_mult2_ge0 (u+v) (1#8))
        ; [ exact Hm0 | apply (Hzb2_qmake_pos (1%Z) 8%positive); lia ].
      + apply (Qle_trans 0 (5*(2-(u+v))*(2-(u+v)-1)*(2-(u+v)-1)) _).
        * exact Hp1.
        * apply Hzb2_add_ge0_le. exact H4m. }
(* Chained composition: 0 <= (m/8)(...) = m-(m^2/4)Bstar <= m-k*Bstar
   <= m-k*B = F. *)
  assert (Hid2 : (u+v) - (((u+v)*(u+v)) * (1#4))
                       * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))
              == ((u+v) * (1#8))
                   * (8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))))
    by ring.
  assert (HF : 0 <= u + v - u*v - 10*u*(1-u)*v*(1-v)).
  { assert (HeqF : u + v - u*v - 10*u*(1-u)*v*(1-v)
                 == (u+v) - (u*v)*(11 - 10*(u+v) + 10*(u*v))) by ring.
    rewrite HeqF.
    apply (Qle_trans _ (((u+v) * (1#8))
              * (8 - 2*(u+v) - 5*(u+v)*(2-(u+v))*(2-(u+v))))).
    - exact Hlow.
    - rewrite <- Hid2.
      apply (Qle_trans _ ((u+v) - (u*v)*(11 - 10*(u+v) + (5#2)*(u+v)*(u+v)))).
      + apply (Hzb2_minus_le (u+v)
          ((u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v)))
          ((((u+v)*(u+v)) * (1#4)) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))))
        ; exact HkB2.
      + apply (Hzb2_minus_le (u+v)
          ((u*v) * (11 - 10*(u+v) + 10*(u*v)))
          ((u*v) * (11 - 10*(u+v) + (5#2)*(u+v)*(u+v))))
        ; exact HkBB. }
(* Concluding step: u+v-uv = 10N + F >= 10N. *)
  apply (Qle_trans (10*u*(1-u)*v*(1-v))
    (10*u*(1-u)*v*(1-v) + (u + v - u*v - 10*u*(1-u)*v*(1-v)))
    (u + v - u*v)).
  - apply Hzb2_add_ge0_le. exact HF.
  - assert (HeqG : 10*u*(1-u)*v*(1-v)
                 + (u + v - u*v - 10*u*(1-u)*v*(1-v))
                == u + v - u*v) by ring.
    rewrite HeqG. apply Qle_refl.
Qed.

(* The main inequality in the original variables: [0 <= x,y <= 1] gives
   [10N <= 1 - xy]. *)
Theorem zb2_ten_le : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  zb2_qle (10 * x * (1 - x) * y * (1 - y)) (1 - x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hu1 : 0 <= 1 - x) by exact (zb2_qle_to_Qle _ _ (zb2_le_sub x 1 Hx2)).
  assert (Hu2 : (1 - x) <= 1) by exact (zb2_qle_to_Qle _ _ (zb2_minus_ge0 x 1 Hx1)).
  assert (Hv1 : 0 <= 1 - y) by exact (zb2_qle_to_Qle _ _ (zb2_le_sub y 1 Hy2)).
  assert (Hv2 : (1 - y) <= 1) by exact (zb2_qle_to_Qle _ _ (zb2_minus_ge0 y 1 Hy1)).
  pose proof (zb2_ten_le_uv (1 - x) (1 - y) (conj Hu1 Hu2) (conj Hv1 Hv2)) as H.
  assert (Hl : 10 * x * (1 - x) * y * (1 - y)
            == 10 * (1 - x) * x * (1 - y) * y) by ring.
  assert (Hr : (1 - x) + (1 - y) - (1 - x) * (1 - y) == 1 - x * y) by ring.
  assert (Hn : 10 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y))
            == 10 * x * (1 - x) * y * (1 - y)) by ring.
  apply (zb2_qle_wd_r (10 * x * (1 - x) * y * (1 - y))
            ((1 - x) + (1 - y) - (1 - x) * (1 - y)) (1 - x * y)).
  - exact Hr.
  - apply (zb2_qle_wd_l (10 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
                        (10 * x * (1 - x) * y * (1 - y))
                        ((1 - x) + (1 - y) - (1 - x) * (1 - y))).
    + exact Hn.
    + exact H.
Qed.

(* ================= Section C. The square identity pair and 4N <= (1-xy)^2 ================= *)

(* The identities (1-xy)^2 - 4x(1-x)(1-y) = (1-2x+xy)^2 and its symmetric
   form in y. *)
Lemma zb2_amgm_eq_l : forall x y : Q,
  zb2_id bool (Qeq_bool ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y))
                         ((1 - 2*x + x*y)*(1 - 2*x + x*y))) true.
Proof. intros x y.
  assert (H : ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y)) == ((1 - 2*x + x*y)*(1 - 2*x + x*y))) by ring.
  assert (Hb : Qeq_bool ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y))
                         ((1 - 2*x + x*y)*(1 - 2*x + x*y)) = true)
    by exact (proj2 (Qeq_bool_iff ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y)) ((1 - 2*x + x*y)*(1 - 2*x + x*y))) H).
  rewrite Hb. apply zb2_idrefl. Qed.

Lemma zb2_amgm_eq_r : forall x y : Q,
  zb2_id bool (Qeq_bool ((1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y))
                         ((1 - 2*y + x*y)*(1 - 2*y + x*y))) true.
Proof. intros x y.
  assert (H : ((1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y)) == ((1 - 2*y + x*y)*(1 - 2*y + x*y))) by ring.
  assert (Hb : Qeq_bool ((1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y))
                         ((1 - 2*y + x*y)*(1 - 2*y + x*y)) = true)
    by exact (proj2 (Qeq_bool_iff ((1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y)) ((1 - 2*y + x*y)*(1 - 2*y + x*y))) H).
  rewrite Hb. apply zb2_idrefl. Qed.

(* The composite step: 0 <= x,y <= 1 gives 4N <= (1-xy)^2.
   The two identities give P >= A and P >= B (P = (1-xy)^2,
   A = 4x(1-x)(1-y), B = 4(1-x)y(1-y)); multiplying, P^2 >= A*B; and
   A*B - Q^2 = 16xy(1-x)^2(1-y)^2(1-xy) >= 0 (Q = 4N), so P^2 >= Q^2;
   from P,Q >= 0 and P+Q > 0 (or the degenerate case P+Q <= 0), P >= Q. *)
Lemma zb2_N4_le_dsq : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  zb2_qle (4 * x * (1 - x) * y * (1 - y)) ((1 - x*y)*(1 - x*y)).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hzb2_0_le_1 : (0 <= 1)%Q) by exact (zb2_qle_to_Qle 0 1 zb2_0_le_1).
  assert (Hzb2_qeq_imp_le : forall p q : Q, p == q -> q <= p)
    by (intros p q H; exact (zb2_qle_to_Qle _ _ (zb2_qeq_imp_le p q H))).
  assert (Hzb2_le_eq_swap : forall a b : Q, a == b -> 0 <= a -> a <= b)
    by (intros a b Hab Ha; exact (zb2_qle_to_Qle _ _ (zb2_le_eq_swap a b Hab Ha))).
  assert (Hzb2_le_eq : forall a b : Q, a == b -> a <= b)
    by (intros a b Hab; exact (zb2_qle_to_Qle _ _ (zb2_le_eq a b Hab))).
  assert (Hzb2_ge0_wd : forall a b : Q, a == b -> 0 <= a -> 0 <= b)
    by (intros a b Hab Ha; exact (zb2_qle_to_Qle _ _ (zb2_ge0_wd a b Hab Ha))).
  assert (Hzb2_add_ge0_le : forall a b : Q, 0 <= b -> a <= a + b)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_add_ge0_le a b H))).
  assert (Hzb2_sub_ge0 : forall a b : Q, 0 <= b - a -> a <= b)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_sub_ge0 a b H))).
  assert (Hzb2_le_sub : forall a b : Q, a <= b -> 0 <= b - a)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_le_sub a b H))).
  assert (Hzb2_le0_opp : forall s : Q, s <= 0 -> 0 <= - s)
    by (intros s H; exact (zb2_qle_to_Qle _ _ (zb2_le0_opp s H))).
  assert (Hzb2_ge0_opp_le : forall t : Q, 0 <= t -> - t <= 0)
    by (intros t H; exact (zb2_qle_to_Qle _ _ (zb2_ge0_opp_le t H))).
  assert (Hzb2_minus_le : forall p q r : Q, q <= r -> p - r <= p - q)
    by (intros p q r H; exact (zb2_qle_to_Qle _ _ (zb2_minus_le p q r H))).
  assert (Hzb2_minus_ge0 : forall t c : Q, 0 <= t -> c - t <= c)
    by (intros t c H; exact (zb2_qle_to_Qle _ _ (zb2_minus_ge0 t c H))).
  assert (Hzb2_sq_ge0 : forall s : Q, 0 <= s * s)
    by (intro s; exact (zb2_qle_to_Qle _ _ (zb2_sq_ge0 s))).
  assert (Hzb2_mult2_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b)
    by (intros a b Ha Hb; exact (zb2_qle_to_Qle _ _ (zb2_mult2_ge0 a b Ha Hb))).
  assert (Hzb2_mult4_ge0 : forall a b c d : Q,
      0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> 0 <= ((a * b) * c) * d)
    by (intros a b c d Ha Hb Hc Hd;
        exact (zb2_qle_to_Qle _ _ (zb2_mult4_ge0 a b c d Ha Hb Hc Hd))).
  assert (Hzb2_div_pos : forall a c : Q, 0 <= a * c -> 0 < c -> 0 <= a)
    by (intros a c Hac Hc; exact (zb2_qle_to_Qle _ _ (zb2_div_pos a c Hac Hc))).
  assert (Hzb2_pow_ge0 : forall (t : Q) (k : nat), 0 <= t -> 0 <= zb2_pow t k)
    by (intros t k Ht; exact (zb2_qle_to_Qle _ _ (zb2_pow_ge0 t k Ht))).
  assert (Hzb2_xy_le_1 : forall p q : Q,
      0 <= p -> p <= 1 -> 0 <= q -> q <= 1 -> p * q <= 1)
    by (intros p q Ha Hb Hc Hd; exact (zb2_qle_to_Qle _ _ (zb2_xy_le_1 p q Ha Hb Hc Hd))).
  assert (Hzb2_qmake_pos : forall (a : Z) (b : positive), (0 <= a)%Z -> 0 <= (a # b)%Q)
    by (intros a b Ha; exact (zb2_qle_to_Qle _ _ (zb2_qmake_pos a b Ha))).
  assert (Hzb2_nat_pos : forall k0 : nat, 0 <= (Z.of_nat k0 # 1)%Q)
    by (intro k0; exact (zb2_qle_to_Qle _ _ (zb2_nat_pos k0))).
  assert (Hzb2_mono_pair : forall a b c d : Q,
      a <= b -> c <= d -> 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> c * a <= d * b)
    by (intros a b c d Hab Hcd Ha Hb Hc Hd;
        exact (zb2_qle_to_Qle _ _ (zb2_mono_pair a b c d Hab Hcd Ha Hb Hc Hd))).
  assert (Hxb : 0 <= 1 - x) by exact (Hzb2_le_sub x 1 Hx2).
  assert (Hyb : 0 <= 1 - y) by exact (Hzb2_le_sub y 1 Hy2).
  assert (HN0 : 0 <= 4 * x * (1 - x) * y * (1 - y)).
  { apply (Hzb2_mult2_ge0 ((4 * x * (1 - x)) * y) (1 - y)).
    - apply (Hzb2_mult2_ge0 (4 * x * (1 - x)) y).
      + apply (Hzb2_mult2_ge0 (4 * x) (1 - x)).
        * apply (Hzb2_mult2_ge0 4 x); [ apply (Hzb2_nat_pos 4%nat) | exact Hx1 ].
        * exact Hxb.
      + exact Hy1.
    - exact Hyb. }
  assert (HP : 0 <= (1 - x*y)*(1 - x*y)) by exact (Hzb2_sq_ge0 (1 - x*y)).
  assert (HAlX : (1 - 2*x + x*y)*(1 - 2*x + x*y)
              == (1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y)) by ring.
  assert (HAl : 0 <= (1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y)).
  { apply (zb2_qle_to_Qle _ _ (zb2_qle_wd_r 0 _ _ HAlX (zb2_sq_ge0 (1 - 2*x + x*y)))). }
  assert (HArX : (1 - 2*y + x*y)*(1 - 2*y + x*y)
              == (1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y)) by ring.
  assert (HAr : 0 <= (1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y)).
  { apply (zb2_qle_to_Qle _ _ (zb2_qle_wd_r 0 _ _ HArX (zb2_sq_ge0 (1 - 2*y + x*y)))). }
  assert (Hm1 : 4*x*(1-x)*(1-y) <= (1 - x*y)*(1 - x*y))
    by exact (Hzb2_sub_ge0 (4*x*(1-x)*(1-y)) _ HAl).
  assert (Hm2 : 4*(1-x)*y*(1-y) <= (1 - x*y)*(1 - x*y))
    by exact (Hzb2_sub_ge0 (4*(1-x)*y*(1-y)) _ HAr).
  assert (HPP : (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))
             <= ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))).
  { apply Qmult_le_compat_r; [ exact Hm1 | exact HP ]. }
  assert (HNA : 0 <= 4*x*(1-x)*(1-y)).
  { apply (Hzb2_mult2_ge0 (4*x*(1-x)) (1-y)).
    - apply (Hzb2_mult2_ge0 (4*x) (1-x)).
      + apply (Hzb2_mult2_ge0 4 x); [ apply (Hzb2_nat_pos 4%nat) | exact Hx1 ].
      + exact Hxb.
    - exact Hyb. }
  assert (HAA : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             <= (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))).
  { apply (Qle_trans _ ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
    - apply (Hzb2_le_eq ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))
                       ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
      assert (Hcmm : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                  == (4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y))) by ring.
      exact Hcmm.
    - apply (Qle_trans _ (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))).
      + apply (Qmult_le_compat_r (4*(1-x)*y*(1-y)) ((1 - x*y)*(1 - x*y))
               (4*x*(1-x)*(1-y)))
        ; [ exact Hm2 | exact HNA ].
      + apply (Hzb2_le_eq (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))
                         ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))).
        assert (Hcmm2 : ((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y))
                     == (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))) by ring.
        exact Hcmm2. }
  assert (Hqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             >= (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))).
  { apply (Hzb2_sub_ge0 ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))).
    assert (Heqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                 - (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))
              == (4*x*(1-x)*(1-y)) * (4*y*(1-x)*(1-y)*(1-x*y))) by ring.
    rewrite Heqq.
    apply Qmult_le_0_compat.
    - apply (Hzb2_mult4_ge0 4 x (1-x) (1-y))
      ; [ apply (Hzb2_nat_pos 4%nat) | exact Hx1 | exact Hxb | exact Hyb ].
    - apply Qmult_le_0_compat.
      + apply (Hzb2_mult4_ge0 4 y (1-x) (1-y))
        ; [ apply (Hzb2_nat_pos 4%nat) | exact Hy1 | exact Hxb | exact Hyb ].
      + apply (Hzb2_le_sub (x*y) 1).
        apply (Hzb2_xy_le_1 x y); assumption. }
  assert (HPPQ : ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))
              >= (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))).
  { apply (Qle_trans ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                     ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))
                     (((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y)))).
    - apply (Qle_trans ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))).
      + exact Hqq.
      + exact HAA.
    - exact HPP. }
  destruct (Qlt_le_dec 0
    ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))) as [Hpos | Hzero].
  - assert (Hdiff : 0 <= ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y))
                       * ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))).
    { assert (Heqd : ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y))
                   * ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))
                == ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))
                 - (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))) by ring.
      rewrite Heqd. exact (Hzb2_le_sub _ _ HPPQ). }
    assert (Hres : 0 <= (1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y)).
    { apply (Hzb2_div_pos _ ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y)))
      ; assumption. }
    exact (zb2_sub_ge0 _ _ Hres).
  - assert (HQle : (4*x*(1-x)*y*(1-y)) <= 0).
    { assert (Hcq : (4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)
                 == (1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y))) by ring.
      apply (Qle_trans (4*x*(1-x)*y*(1-y))
               ((4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)) 0).
      - apply Hzb2_add_ge0_le. exact HP.
      - apply (Qle_trans _ ((1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y)))).
        + apply (Hzb2_le_eq _ _). exact Hcq.
        + exact Hzero. }
    assert (Heq : (4*x*(1-x)*y*(1-y)) == 0) by (apply Qle_antisym; assumption).
    apply zb2_qle_of_Qle. rewrite Heq. exact HP.
Qed.

(* ================= Section D. The composite decay bound ================= *)

(* Inductive composition: the base case is Section C; the step multiplies
   by N <= (1-xy)/10 (the Section B main inequality) and then by (1-xy):
   the division-free form of the family being pointwise at most
   (1/4)*(1/10)^n. *)
Theorem zb2_pointwise_decay : forall (n : nat) (x y : Q),
  0 <= x <= 1 -> 0 <= y <= 1 ->
  zb2_qle (4 * zb2_pow 10 n * zb2_pow (x*(1-x)*y*(1-y)) (S n))
          (zb2_pow (1 - x*y) (S (S n))).
Proof.
  assert (Hzb2_0_le_1 : (0 <= 1)%Q) by exact (zb2_qle_to_Qle 0 1 zb2_0_le_1).
  assert (Hzb2_qeq_imp_le : forall p q : Q, p == q -> q <= p)
    by (intros p q H; exact (zb2_qle_to_Qle _ _ (zb2_qeq_imp_le p q H))).
  assert (Hzb2_le_eq_swap : forall a b : Q, a == b -> 0 <= a -> a <= b)
    by (intros a b Hab Ha; exact (zb2_qle_to_Qle _ _ (zb2_le_eq_swap a b Hab Ha))).
  assert (Hzb2_le_eq : forall a b : Q, a == b -> a <= b)
    by (intros a b Hab; exact (zb2_qle_to_Qle _ _ (zb2_le_eq a b Hab))).
  assert (Hzb2_ge0_wd : forall a b : Q, a == b -> 0 <= a -> 0 <= b)
    by (intros a b Hab Ha; exact (zb2_qle_to_Qle _ _ (zb2_ge0_wd a b Hab Ha))).
  assert (Hzb2_add_ge0_le : forall a b : Q, 0 <= b -> a <= a + b)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_add_ge0_le a b H))).
  assert (Hzb2_sub_ge0 : forall a b : Q, 0 <= b - a -> a <= b)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_sub_ge0 a b H))).
  assert (Hzb2_le_sub : forall a b : Q, a <= b -> 0 <= b - a)
    by (intros a b H; exact (zb2_qle_to_Qle _ _ (zb2_le_sub a b H))).
  assert (Hzb2_le0_opp : forall s : Q, s <= 0 -> 0 <= - s)
    by (intros s H; exact (zb2_qle_to_Qle _ _ (zb2_le0_opp s H))).
  assert (Hzb2_ge0_opp_le : forall t : Q, 0 <= t -> - t <= 0)
    by (intros t H; exact (zb2_qle_to_Qle _ _ (zb2_ge0_opp_le t H))).
  assert (Hzb2_minus_le : forall p q r : Q, q <= r -> p - r <= p - q)
    by (intros p q r H; exact (zb2_qle_to_Qle _ _ (zb2_minus_le p q r H))).
  assert (Hzb2_minus_ge0 : forall t c : Q, 0 <= t -> c - t <= c)
    by (intros t c H; exact (zb2_qle_to_Qle _ _ (zb2_minus_ge0 t c H))).
  assert (Hzb2_sq_ge0 : forall s : Q, 0 <= s * s)
    by (intro s; exact (zb2_qle_to_Qle _ _ (zb2_sq_ge0 s))).
  assert (Hzb2_mult2_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b)
    by (intros a b Ha Hb; exact (zb2_qle_to_Qle _ _ (zb2_mult2_ge0 a b Ha Hb))).
  assert (Hzb2_mult4_ge0 : forall a b c d : Q,
      0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> 0 <= ((a * b) * c) * d)
    by (intros a b c d Ha Hb Hc Hd;
        exact (zb2_qle_to_Qle _ _ (zb2_mult4_ge0 a b c d Ha Hb Hc Hd))).
  assert (Hzb2_div_pos : forall a c : Q, 0 <= a * c -> 0 < c -> 0 <= a)
    by (intros a c Hac Hc; exact (zb2_qle_to_Qle _ _ (zb2_div_pos a c Hac Hc))).
  assert (Hzb2_pow_ge0 : forall (t : Q) (k : nat), 0 <= t -> 0 <= zb2_pow t k)
    by (intros t k Ht; exact (zb2_qle_to_Qle _ _ (zb2_pow_ge0 t k Ht))).
  assert (Hzb2_xy_le_1 : forall p q : Q,
      0 <= p -> p <= 1 -> 0 <= q -> q <= 1 -> p * q <= 1)
    by (intros p q Ha Hb Hc Hd; exact (zb2_qle_to_Qle _ _ (zb2_xy_le_1 p q Ha Hb Hc Hd))).
  assert (Hzb2_qmake_pos : forall (a : Z) (b : positive), (0 <= a)%Z -> 0 <= (a # b)%Q)
    by (intros a b Ha; exact (zb2_qle_to_Qle _ _ (zb2_qmake_pos a b Ha))).
  assert (Hzb2_nat_pos : forall k0 : nat, 0 <= (Z.of_nat k0 # 1)%Q)
    by (intro k0; exact (zb2_qle_to_Qle _ _ (zb2_nat_pos k0))).
  assert (Hzb2_mono_pair : forall a b c d : Q,
      a <= b -> c <= d -> 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> c * a <= d * b)
    by (intros a b c d Hab Hcd Ha Hb Hc Hd;
        exact (zb2_qle_to_Qle _ _ (zb2_mono_pair a b c d Hab Hcd Ha Hb Hc Hd))).
  induction n as [| n IH]; intros x y [Hx1 Hx2] [Hy1 Hy2].
  - apply zb2_qle_of_Qle.
    assert (Heq1 : 4 * zb2_pow 10 0 * zb2_pow (x*(1-x)*y*(1-y)) 1
                == 4 * x * (1-x) * y * (1-y)) by (simpl; ring).
    assert (Heq2 : zb2_pow (1 - x*y) 2 == ((1 - x*y)*(1 - x*y)))
      by (simpl; ring).
    rewrite Heq1, Heq2.
    exact (zb2_qle_to_Qle _ _
      (zb2_N4_le_dsq x y (conj Hx1 Hx2) (conj Hy1 Hy2))).
  - apply zb2_qle_of_Qle.
    assert (HIH := IH x y (conj Hx1 Hx2) (conj Hy1 Hy2)).
    apply zb2_qle_to_Qle in HIH.
    pose proof (zb2_ten_le x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as Hten.
    apply zb2_qle_to_Qle in Hten.
    assert (Hxy1 : 0 <= x*y) by (apply (Hzb2_mult2_ge0 x y); assumption).
    assert (HP0 : 0 <= zb2_pow (1 - x*y) (S (S n)))
      by (apply Hzb2_pow_ge0; apply (Hzb2_le_sub (x*y) 1);
        apply (Hzb2_xy_le_1 x y); assumption).
    assert (Hxb : 0 <= 1 - x) by (apply (Hzb2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y) by (apply (Hzb2_le_sub y 1); exact Hy2).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y))
      by (apply (Hzb2_mult4_ge0 x (1-x) y (1-y))
        ; [ exact Hx1 | exact Hxb | exact Hy1 | exact Hyb ]).
    assert (H4N : 0 <= (4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)).
    { apply (Hzb2_mult2_ge0 (4 * zb2_pow 10 n) (zb2_pow (x*(1-x)*y*(1-y)) (S n))).
      - apply (Hzb2_mult2_ge0 4 (zb2_pow 10 n))
        ; [ apply (Hzb2_nat_pos 4%nat) | apply Hzb2_pow_ge0; exact (Hzb2_nat_pos 10%nat) ].
      - apply Hzb2_pow_ge0. exact HN0. }
    assert (HPn : 0 <= 1 - x*y)
      by (apply (Hzb2_le_sub (x*y) 1); apply (Hzb2_xy_le_1 x y); assumption).
    assert (HN10 : 0 <= ((10 * x * (1 - x)) * y) * (1 - y)).
    { apply (Hzb2_mult2_ge0 ((10 * x * (1 - x)) * y) (1 - y)).
      - apply (Hzb2_mult2_ge0 ((10 * x) * (1 - x)) y).
        + apply (Hzb2_mult2_ge0 (10 * x) (1 - x)).
          * apply (Hzb2_mult2_ge0 10 x); [ apply (Hzb2_nat_pos 10%nat) | exact Hx1 ].
          * exact Hxb.
        + exact Hy1.
      - exact Hyb. }
    apply (Qle_trans (4 * zb2_pow 10 (S n) * zb2_pow (x*(1-x)*y*(1-y)) (S (S n)))
                     (10 * x * (1 - x) * y * (1 - y) * ((4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)))
                     ((1 - x*y) * zb2_pow (1 - x*y) (S (S n)))).
    + apply (Hzb2_le_eq (4 * zb2_pow 10 (S n) * zb2_pow (x*(1-x)*y*(1-y)) (S (S n)))
                       (10 * x * (1 - x) * y * (1 - y) * ((4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)))).
      assert (Hrw : 4 * zb2_pow 10 (S n) * zb2_pow (x*(1-x)*y*(1-y)) (S (S n))
                 == 10 * x * (1 - x) * y * (1 - y) * ((4 * zb2_pow 10 n) * zb2_pow (x*(1-x)*y*(1-y)) (S n)))
        by (simpl; ring).
      exact Hrw.
    + apply (Hzb2_mono_pair (4 * zb2_pow 10 n * zb2_pow (x*(1-x)*y*(1-y)) (S n))
                           (zb2_pow (1 - x*y) (S (S n)))
                           _ (1 - x*y))
      ; [ exact HIH | exact Hten | exact H4N | exact HP0 | exact HN10 | exact HPn ].
Qed.

(* Assumption closure of every statement ([Print Assumptions]). *)
Print Assumptions zb2_0_le_1.
Print Assumptions zb2_qle_of_Qle.
Print Assumptions zb2_qle_to_Qle.
Print Assumptions zb2_qeq_imp_le.
Print Assumptions zb2_le_eq_swap.
Print Assumptions zb2_le_eq.
Print Assumptions zb2_ge0_wd.
Print Assumptions zb2_qle_wd_l.
Print Assumptions zb2_qle_wd_r.
Print Assumptions zb2_add_ge0_le.
Print Assumptions zb2_sub_ge0.
Print Assumptions zb2_le_sub.
Print Assumptions zb2_le0_opp.
Print Assumptions zb2_ge0_opp_le.
Print Assumptions zb2_minus_le.
Print Assumptions zb2_minus_ge0.
Print Assumptions zb2_sq_ge0.
Print Assumptions zb2_mult2_ge0.
Print Assumptions zb2_mult4_ge0.
Print Assumptions zb2_div_pos.
Print Assumptions zb2_pow_ge0.
Print Assumptions zb2_xy_le_1.
Print Assumptions zb2_qmake_pos.
Print Assumptions zb2_nat_pos.
Print Assumptions zb2_mono_pair.
Print Assumptions zb2_ten_le_uv.
Print Assumptions zb2_ten_le.
Print Assumptions zb2_amgm_eq_l.
Print Assumptions zb2_amgm_eq_r.
Print Assumptions zb2_N4_le_dsq.
Print Assumptions zb2_pointwise_decay.
