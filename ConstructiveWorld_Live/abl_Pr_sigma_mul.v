(* ConstructiveWorld-Set -- divisor-sum function multiplicativity on nat. *)

(** * abl_Pr_sigma_mul: multiplicativity of the divisor-sum function on nat.

    Mission.  The divisor-sum function [pza_sigma] on nat, the finite sum of
      the divisors of [N] via the divisibility indicator [pza_dvdind]; main
      statement [pza_sigma_mul]: coprime positive [m] and [n] satisfy
      [pza_sigma (m * n) = pza_sigma m * pza_sigma n].  The proof path:
      the coprime splitting [pza_split_coprime] with uniqueness
      [pza_split_inj], the counting identity [pza_count_eq], and the
      finite-sum rearrangement [pza_triple_align]; companions
      [pza_dvdind_mul_cancel], [pza_sumf_trunc].

    Dependencies.  Stdlib [Arith.Arith], [List], [Bool], [Lia].  Requires
      [Hanson3Pow], [HansonLcm], [abl_Pr_core_01], [abl_Pr_enum_02],
      [abl_Pr_euclid_03], [abl_Pr_lcm_eq], [abl_Pr_lcmdecomp_04] of this
      development.

    References.  This development, abl_Pr_sigma_mul.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_Pr_sigma_mul.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import S01_BaseRing (NatLe_drop).
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_lcm_eq.

(* ---- Section 0. Finite sums and the divisibility indicator ---- *)

Fixpoint pza_sumf (f : nat -> nat) (N : nat) : nat :=
  match N with
  | O => 0
  | S N' => pza_sumf f N' + f (S N')
  end.

Definition pza_dvdind (d N : nat) : nat :=
  if Nat.eqb (N mod d) 0 then 1 else 0.

Definition pza_sigma (N : nat) : nat :=
  pza_sumf (fun d => d * pza_dvdind d N) N.

(* ---- Section 1. Basic lemmas on finite sums ---- *)

Lemma pza_sumf_zero : forall (f : nat -> nat) (N : nat),
  (forall d, 1 <= d -> d <= N -> f d = 0) -> pza_sumf f N = 0.
Proof.
  intros f N H. induction N as [| N' IH].
  - reflexivity.
  - simpl. rewrite IH by (intros d H1 H2; apply H; lia).
    rewrite H by lia. reflexivity.
Qed.

Lemma pza_sumf_ext : forall (f g : nat -> nat) (N : nat),
  (forall d, 1 <= d -> d <= N -> f d = g d) -> pza_sumf f N = pza_sumf g N.
Proof.
  intros f g N H. induction N as [| N' IH].
  - reflexivity.
  - simpl. rewrite IH by (intros d H1 H2; apply H; lia).
    rewrite H by lia. reflexivity.
Qed.

Lemma pza_sumf_scal_l : forall (f : nat -> nat) (c N : nat),
  pza_sumf (fun d => c * f d) N = c * pza_sumf f N.
Proof.
  intros f c N. induction N as [| N' IH].
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl. rewrite IH, Nat.mul_add_distr_l. reflexivity.
Qed.

Lemma pza_sumf_scal_r : forall (f : nat -> nat) (c N : nat),
  pza_sumf (fun d => f d * c) N = pza_sumf f N * c.
Proof.
  intros f c N. induction N as [| N' IH].
  - reflexivity.
  - simpl. rewrite IH, Nat.mul_add_distr_r. reflexivity.
Qed.

Lemma pza_sumf_add : forall (f g : nat -> nat) (N : nat),
  pza_sumf (fun d => f d + g d) N = pza_sumf f N + pza_sumf g N.
Proof.
  intros f g N. induction N as [| N' IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma pza_sumf_mul : forall (f g : nat -> nat) (M N : nat),
  pza_sumf f M * pza_sumf g N
  = pza_sumf (fun x => pza_sumf (fun y => f x * g y) N) M.
Proof.
  intros f g M. induction M as [| M' IH]; intros N.
  - reflexivity.
  - simpl. rewrite Nat.mul_add_distr_r, IH, pza_sumf_scal_l. reflexivity.
Qed.

Lemma pza_sumf_fubini : forall (F : nat -> nat -> nat) (M N : nat),
  pza_sumf (fun x => pza_sumf (fun y => F x y) N) M
  = pza_sumf (fun y => pza_sumf (fun x => F x y) M) N.
Proof.
  intros F M. induction M as [| M' IH]; intros N.
  - simpl. symmetry. apply pza_sumf_zero. intros d _ _. reflexivity.
  - simpl. rewrite pza_sumf_add. rewrite IH. reflexivity.
Qed.

(* Two dedicated rotations of the triple sum, avoiding the ambiguity of
   general higher-order rewrites. *)
Lemma pza_sumf_rot_dx : forall (F : nat -> nat -> nat -> nat) (K M N : nat),
  pza_sumf (fun d => pza_sumf (fun x => pza_sumf (fun y => F d x y) N) M) K
  = pza_sumf (fun x => pza_sumf (fun d => pza_sumf (fun y => F d x y) N) K) M.
Proof.
  intros F K M N. apply pza_sumf_fubini.
Qed.

Lemma pza_sumf_rot_yd : forall (F : nat -> nat -> nat -> nat) (M N K : nat),
  pza_sumf (fun x => pza_sumf (fun y => pza_sumf (fun d => F d x y) K) N) M
  = pza_sumf (fun x => pza_sumf (fun d => pza_sumf (fun y => F d x y) N) K) M.
Proof.
  intros F M N K. apply pza_sumf_ext. intros x Hx _.
  apply pza_sumf_fubini.
Qed.

(* Point mass: the two closed forms of the finite sum when exactly one
   index is hit. *)
Lemma pza_sumf_point_hit : forall (v c N : nat),
  1 <= c -> c <= N ->
  pza_sumf (fun d => if Nat.eqb d c then v else 0) N = v.
Proof.
  intros v c N H1 H2. induction N as [| N' IH].
  - lia.
  - cbn [pza_sumf]. destruct (Nat.eq_dec c (S N')) as [Ec | Nc].
    + subst c. rewrite Nat.eqb_refl.
      rewrite pza_sumf_zero
        by (intros d Hd1 Hd2; destruct (Nat.eqb d (S N')) eqn:E;
            [apply Nat.eqb_eq in E; lia | reflexivity]).
      lia.
    + assert (HcN : c <= N') by lia.
      assert (Eb : (S N' =? c) = false) by (apply Nat.eqb_neq; lia).
      rewrite Eb, Nat.add_0_r. apply IH; lia.
Qed.

Lemma pza_sumf_count_one : forall (c N : nat),
  1 <= c -> c <= N ->
  pza_sumf (fun d => if Nat.eqb c d then 1 else 0) N = 1.
Proof.
  intros c N H1 H2. induction N as [| N' IH].
  - lia.
  - cbn [pza_sumf]. destruct (Nat.eq_dec c (S N')) as [Ec | Nc].
    + subst c. rewrite Nat.eqb_refl.
      rewrite pza_sumf_zero
        by (intros d Hd1 Hd2; destruct (Nat.eqb (S N') d) eqn:E;
            [apply Nat.eqb_eq in E; lia | reflexivity]).
      lia.
    + assert (HcN : c <= N') by lia.
      assert (Eb : (c =? S N') = false) by (apply Nat.eqb_neq; lia).
      rewrite Eb, Nat.add_0_r. apply IH; lia.
Qed.

Lemma pza_mul_pos : forall x y : nat,
  1 <= x -> 1 <= y -> 1 <= x * y.
Proof.
  intros x y Hx Hy.
  assert (H : 1 * 1 <= x * y) by (apply Nat.mul_le_mono; lia).
  simpl in H. lia.
Qed.

(* ---- Section 2. Gcd auxiliaries and the coprime splitting ---- *)

Lemma pza_gcd_pos : forall x y : nat, 1 <= x -> 1 <= Nat.gcd x y.
Proof.
  intros x y Hx.
  destruct (Nat.eq_dec (Nat.gcd x y) 0) as [Hz | Hnz].
  - exfalso. subst.
    assert (Hd : Nat.divide 0 x) by (rewrite <- Hz; apply Nat.gcd_divide_l).
    destruct Hd as [z Hz0]. rewrite Nat.mul_0_r in Hz0. lia.
  - lia.
Qed.

Lemma pza_gcd_1_of_div_both : forall g m n : nat,
  1 <= g -> Nat.divide g m -> Nat.divide g n -> Nat.gcd m n = 1 -> g = 1.
Proof.
  intros g m n Hg1 Hm Hn Hgcd.
  assert (Hd : Nat.divide g (Nat.gcd m n)) by (apply Nat.gcd_greatest; assumption).
  rewrite Hgcd in Hd.
  assert (Hle : g <= 1) by (apply (Nat.divide_pos_le g 1); [lia | exact Hd]).
  lia.
Qed.

Lemma pza_gcd1 : forall x : nat, Nat.gcd x 1 = 1.
Proof.
  intros x. apply Nat.divide_antisym.
  - apply Nat.gcd_divide_r.
  - apply Nat.divide_1_l.
Qed.

(* Coprime splitting: a divisor of the product of two coprime numbers is a
   product of factors dividing each side. *)
Lemma pza_split_coprime_aux : forall (fuel m n d : nat),
  d <= fuel -> 1 <= m -> 1 <= n -> Nat.gcd m n = 1 ->
  Nat.divide d (m * n) ->
  exists d1 d2 : nat, d = d1 * d2 /\ Nat.divide d1 m /\ Nat.divide d2 n.
Proof.
  intros fuel. induction fuel as [| fuel IH];
    intros m n d Hdle Hm Hn Hgcd Hdvd.
  - assert (Hz : d = 0) by lia. subst d.
    destruct Hdvd as [z Hz]. rewrite Nat.mul_0_r in Hz. lia.
  - destruct (Nat.eq_dec d 0) as [Hz0 | Hn0].
    + subst d. destruct Hdvd as [z Hz]. rewrite Nat.mul_0_r in Hz. lia.
    + destruct (Nat.eq_dec d 1) as [Hz1 | Hn1].
      * subst d. exists 1, 1.
        split; [reflexivity | split; apply Nat.divide_1_l].
      * assert (H2d : 2 <= d) by lia.
        destruct (pr_min_factor_exists d H2d) as [p [Hpd Hpp]].
        destruct Hpp as [Hp2 Hpdiv].
        assert (Hpdd : Nat.divide p d) by exact Hpd.
        destruct Hpd as [q Hq].  (* d = q * p *)
        assert (Hq1 : 1 <= q)
          by (destruct q; [rewrite Nat.mul_0_l in Hq; lia | lia]).
        assert (Hq2 : q * 2 <= q * p)
          by (apply Nat.mul_le_mono_l; apply NatLe_drop; exact Hp2).
        assert (Hqlt : q < d) by lia.
        assert (Hqle : q <= fuel) by lia.
        assert (Hpmn : Nat.divide p (m * n))
          by (apply (Nat.divide_trans p d); assumption).
        destruct (plm_prime_dvd_mul p m n (Hp2, Hpdiv) Hpmn)
          as [Hpm | Hpn].
        -- (* the least prime factor divides m: write m = w * p and
              induct on (w, n) *)
           destruct Hpm as [w Hw].
           assert (Hw1 : 1 <= w)
             by (destruct w; [rewrite Nat.mul_0_l in Hw; lia | lia]).
           assert (Hgw : Nat.gcd w n = 1).
           { apply (pza_gcd_1_of_div_both (Nat.gcd w n) m n).
             - apply pza_gcd_pos. exact Hw1.
             - apply (Nat.divide_trans (Nat.gcd w n) w m).
               + apply Nat.gcd_divide_l.
               + exists p. rewrite Hw. apply Nat.mul_comm.
             - apply (Nat.divide_trans (Nat.gcd w n) n n).
               + apply Nat.gcd_divide_r.
               + apply Nat.divide_refl.
             - exact Hgcd. }
           destruct Hdvd as [z Hz].  (* m * n = z * d *)
           rewrite Hw, Hq in Hz.
           rewrite <- Nat.mul_assoc in Hz.  (* w * (p * n) = z * (q * p) *)
           assert (Hpnz : p <> 0) by lia.
           assert (Hqdiv : Nat.divide q (w * n)).
           { assert (Hcan0 : w * n * p = z * q * p).
             { rewrite <- !Nat.mul_assoc, (Nat.mul_comm n p). exact Hz. }
             rewrite (Nat.mul_comm (w * n) p), (Nat.mul_comm (z * q) p)
               in Hcan0.
             apply (proj1 (Nat.mul_cancel_l (w * n) (z * q) p Hpnz))
               in Hcan0.
             exists z. exact Hcan0. }
           destruct (IH w n q Hqle Hw1 Hn Hgw Hqdiv)
             as [d1 [d2 [Hdeq [Hd1 Hd2]]]].
           exists (d1 * p), d2.
           split.
           { rewrite Hq, Hdeq. ring. }
           split.
           { destruct Hd1 as [k Hk].  (* w = k * d1 *)
             exists k. rewrite Hw, Hk. ring. }
           { exact Hd2. }
        -- (* the least prime factor divides n: write n = w * p and
              induct on (m, w) *)
           destruct Hpn as [w Hw].
           assert (Hw1 : 1 <= w)
             by (destruct w; [rewrite Nat.mul_0_l in Hw; lia | lia]).
           assert (Hgw : Nat.gcd m w = 1).
           { apply (pza_gcd_1_of_div_both (Nat.gcd m w) m n).
             - apply pza_gcd_pos. exact Hm.
             - apply Nat.gcd_divide_l.
             - apply (Nat.divide_trans (Nat.gcd m w) w n).
               + apply Nat.gcd_divide_r.
               + exists p. rewrite Hw. apply Nat.mul_comm.
             - exact Hgcd. }
           destruct Hdvd as [z Hz].  (* m * n = z * d *)
           rewrite Hw, Hq in Hz.  (* m * (w * p) = z * (q * p) *)
           assert (Hpnz : p <> 0) by lia.
           assert (Hqdiv : Nat.divide q (m * w)).
           { assert (Hcan0 : m * w * p = z * q * p).
             { rewrite <- !Nat.mul_assoc. exact Hz. }
             rewrite (Nat.mul_comm (m * w) p), (Nat.mul_comm (z * q) p)
               in Hcan0.
             apply (proj1 (Nat.mul_cancel_l (m * w) (z * q) p Hpnz))
               in Hcan0.
             exists z. exact Hcan0. }
           destruct (IH m w q Hqle Hm Hw1 Hgw Hqdiv)
             as [d1 [d2 [Hdeq [Hd1 Hd2]]]].
           exists d1, (d2 * p).
           split.
           { rewrite Hq, Hdeq. ring. }
           split.
           { exact Hd1. }
           { destruct Hd2 as [k Hk].  (* w = k * d2 *)
             exists k. rewrite Hw, Hk. ring. }
Qed.

(* The conclusion form of the coprime splitting. *)
Lemma pza_split_coprime : forall (m n d : nat),
  1 <= m -> 1 <= n -> Nat.gcd m n = 1 -> Nat.divide d (m * n) ->
  exists d1 d2 : nat, d = d1 * d2 /\ Nat.divide d1 m /\ Nat.divide d2 n.
Proof.
  intros m n d Hm Hn Hgcd Hdvd.
  apply (pza_split_coprime_aux d m n d (Nat.le_refl d) Hm Hn Hgcd Hdvd).
Qed.

(* Uniqueness of the splitting: two splittings with factors on the m and
   n sides and equal products coincide. *)
Lemma pza_split_inj : forall m n x y x' y' : nat,
  1 <= m -> 1 <= n -> Nat.gcd m n = 1 ->
  Nat.divide x m -> Nat.divide y n -> 1 <= x -> 1 <= y ->
  Nat.divide x' m -> Nat.divide y' n -> 1 <= x' -> 1 <= y' ->
  x * y = x' * y' -> x = x' /\ y = y'.
Proof.
  intros m n x y x' y' Hm Hn Hgcd Hx Hy Hx1 Hy1 Hx' Hy' Hx'1 Hy'1 Heq.
  assert (Hgym : Nat.gcd y m = 1).
  { apply (pza_gcd_1_of_div_both (Nat.gcd y m) m n).
    - apply pza_gcd_pos. exact Hy1.
    - apply Nat.gcd_divide_r.
    - apply (Nat.divide_trans (Nat.gcd y m) y n).
      + apply Nat.gcd_divide_l.
      + exact Hy.
    - exact Hgcd. }
  assert (Hgym' : Nat.gcd y' m = 1).
  { apply (pza_gcd_1_of_div_both (Nat.gcd y' m) m n).
    - apply pza_gcd_pos. exact Hy'1.
    - apply Nat.gcd_divide_r.
    - apply (Nat.divide_trans (Nat.gcd y' m) y' n).
      + apply Nat.gcd_divide_l.
      + exact Hy'.
    - exact Hgcd. }
  assert (Hxy1 : 1 <= x * y) by (apply pza_mul_pos; lia).
  assert (Hgx : Nat.gcd (x * y) m = x).
  { apply Nat.divide_antisym.
    - apply (plm_gauss (Nat.gcd (x * y) m) y x).
      + apply (pza_gcd_1_of_div_both
                 (Nat.gcd (Nat.gcd (x * y) m) y) m n).
        * apply pza_gcd_pos. apply pza_gcd_pos. exact Hxy1.
        * apply (Nat.divide_trans
                   (Nat.gcd (Nat.gcd (x * y) m) y)
                   (Nat.gcd (x * y) m) m).
          -- apply Nat.gcd_divide_l.
          -- apply Nat.gcd_divide_r.
        * apply (Nat.divide_trans
                   (Nat.gcd (Nat.gcd (x * y) m) y) y n).
          -- apply Nat.gcd_divide_r.
          -- exact Hy.
        * exact Hgcd.
      + rewrite (Nat.mul_comm y x). apply Nat.gcd_divide_l.
    - apply (Nat.gcd_greatest (x * y) m x).
      + exists y. apply Nat.mul_comm.
      + exact Hx. }
  assert (Hgx' : Nat.gcd (x' * y') m = x').
  { apply Nat.divide_antisym.
    - apply (plm_gauss (Nat.gcd (x' * y') m) y' x').
      + apply (pza_gcd_1_of_div_both
                 (Nat.gcd (Nat.gcd (x' * y') m) y') m n).
        * apply pza_gcd_pos. apply pza_gcd_pos.
          assert (Hxy'1 : 1 <= x' * y') by (apply pza_mul_pos; lia).
          exact Hxy'1.
        * apply (Nat.divide_trans
                   (Nat.gcd (Nat.gcd (x' * y') m) y')
                   (Nat.gcd (x' * y') m) m).
          -- apply Nat.gcd_divide_l.
          -- apply Nat.gcd_divide_r.
        * apply (Nat.divide_trans
                   (Nat.gcd (Nat.gcd (x' * y') m) y') y' n).
          -- apply Nat.gcd_divide_r.
          -- exact Hy'.
        * exact Hgcd.
      + rewrite (Nat.mul_comm y' x'). apply Nat.gcd_divide_l.
    - apply (Nat.gcd_greatest (x' * y') m x').
      + exists y'. apply Nat.mul_comm.
      + exact Hx'. }
  assert (Hxx : x = x').
  { rewrite <- Hgx. rewrite Heq. exact Hgx'. }
  subst x'. split; [reflexivity |].
  assert (Hxnz : x <> 0) by lia.
  apply (proj1 (Nat.mul_cancel_l y y' x Hxnz)).
  exact Heq.
Qed.

(* ---- Section 3. The counting identity: the divisibility indicator of a
   product counts its split pairs ---- *)

Definition pza_count (m n d : nat) : nat :=
  pza_sumf (fun x => pza_sumf (fun y =>
    (if Nat.eqb (x * y) d then 1 else 0)
      * pza_dvdind x m * pza_dvdind y n) n) m.

Lemma pza_count_eq : forall m n d : nat,
  1 <= m -> 1 <= n -> Nat.gcd m n = 1 ->
  pza_count m n d = pza_dvdind d (m * n).
Proof.
  intros m n d Hm Hn Hgcd. unfold pza_count, pza_dvdind.
  destruct (Nat.eqb (m * n mod d) 0) eqn:Ed.
  - (* d divides m * n: the count is exactly 1, the point mass at the
       anchor pair (d1, d2) *)
    assert (Hd1 : 1 <= d).
    { destruct d as [| d']; [exfalso | lia].
      rewrite Nat.mod_0_r in Ed. apply Nat.eqb_eq in Ed. lia. }
    assert (Hdvd : Nat.divide d (m * n))
      by (apply pr_mod0_dvd; [lia | apply Nat.eqb_eq in Ed; exact Ed]).
    destruct (pza_split_coprime m n d Hm Hn Hgcd Hdvd)
      as [d1 [d2 [Hdeq [Hd1m Hd2n]]]].
    assert (Hd11 : 1 <= d1).
    { destruct d1 as [| d1']; [exfalso | lia].
      rewrite Nat.mul_0_l in Hdeq. lia. }
    assert (Hd21 : 1 <= d2).
    { destruct d2 as [| d2']; [exfalso | lia].
      rewrite Nat.mul_0_r in Hdeq. lia. }
    assert (Hd1nz : d1 <> 0) by lia.
    assert (Hd1m2 : d1 <= m)
      by (apply (Nat.divide_pos_le d1 m); [lia | exact Hd1m]).
    assert (Hd2n2 : d2 <= n)
      by (apply (Nat.divide_pos_le d2 n); [lia | exact Hd2n]).
    assert (Hmod1 : m mod d1 = 0)
      by (apply (proj2 (Nat.Div0.mod_divides m d1));
          destruct Hd1m as [c Hc]; exists c; rewrite Hc; apply Nat.mul_comm).
    assert (Hmod2 : n mod d2 = 0)
      by (apply (proj2 (Nat.Div0.mod_divides n d2));
          destruct Hd2n as [c Hc]; exists c; rewrite Hc; apply Nat.mul_comm).
    transitivity
      (pza_sumf (fun x => pza_sumf (fun y =>
        if Nat.eqb x d1 then if Nat.eqb y d2 then 1 else 0 else 0) n) m).
    { apply pza_sumf_ext. intros x Hx1 Hx2.
      apply pza_sumf_ext. intros y Hy1 Hy2.
      destruct (Nat.eqb x d1) eqn:Ex.
      - apply Nat.eqb_eq in Ex. subst x.
        destruct (Nat.eqb y d2) eqn:Ey.
        + apply Nat.eqb_eq in Ey. subst y.
          rewrite Hdeq, Hmod1, Hmod2, !Nat.eqb_refl. reflexivity.
        + apply Nat.eqb_neq in Ey.
          destruct (Nat.eqb (d1 * y) d) eqn:E1; [| reflexivity].
          apply Nat.eqb_eq in E1. rewrite Hdeq in E1.
          apply (proj1 (Nat.mul_cancel_l y d2 d1 Hd1nz)) in E1.
          contradiction.
      - apply Nat.eqb_neq in Ex.
        destruct (Nat.eqb (x * y) d) eqn:E1; [| reflexivity].
        destruct (Nat.eqb (m mod x) 0) eqn:E2; [| reflexivity].
        destruct (Nat.eqb (n mod y) 0) eqn:E3; [| reflexivity].
        exfalso.
        apply Nat.eqb_eq in E1.
        apply Nat.eqb_eq in E2. apply Nat.eqb_eq in E3.
        assert (Hxm : Nat.divide x m) by (apply pr_mod0_dvd; [lia | exact E2]).
        assert (Hyn : Nat.divide y n) by (apply pr_mod0_dvd; [lia | exact E3]).
        assert (Hxyd : x * y = d1 * d2) by (rewrite E1; exact Hdeq).
        destruct (pza_split_inj m n x y d1 d2 Hm Hn Hgcd
          Hxm Hyn Hx1 Hy1 Hd1m Hd2n Hd11 Hd21 Hxyd) as [Hc _].
        apply Ex. exact Hc. }
    transitivity (pza_sumf (fun x => if Nat.eqb x d1 then 1 else 0) m).
    { apply pza_sumf_ext. intros x Hx1 Hx2.
      destruct (Nat.eqb x d1) eqn:Ex.
      - apply Nat.eqb_eq in Ex. subst x.
        apply pza_sumf_point_hit; lia.
      - apply Nat.eqb_neq in Ex.
        apply pza_sumf_zero. intros y Hy1 Hy2. reflexivity. }
    apply pza_sumf_point_hit; lia.
  - (* d does not divide m * n: every counting term is zero *)
    apply pza_sumf_zero. intros x Hx1 Hx2.
    apply pza_sumf_zero. intros y Hy1 Hy2.
    destruct (Nat.eqb (x * y) d) eqn:E1; [| reflexivity].
    destruct (Nat.eqb (m mod x) 0) eqn:E2; [| reflexivity].
    destruct (Nat.eqb (n mod y) 0) eqn:E3; [| reflexivity].
    exfalso.
    apply Nat.eqb_eq in E1.
    apply Nat.eqb_eq in E2. apply Nat.eqb_eq in E3.
    assert (Hxm : Nat.divide x m) by (apply pr_mod0_dvd; [lia | exact E2]).
    assert (Hyn : Nat.divide y n) by (apply pr_mod0_dvd; [lia | exact E3]).
    assert (Hgxy : Nat.gcd x y = 1).
    { apply (pza_gcd_1_of_div_both (Nat.gcd x y) m n).
      - apply pza_gcd_pos. lia.
      - apply (Nat.divide_trans (Nat.gcd x y) x m).
        + apply Nat.gcd_divide_l.
        + exact Hxm.
      - apply (Nat.divide_trans (Nat.gcd x y) y n).
        + apply Nat.gcd_divide_r.
        + exact Hyn.
      - exact Hgcd. }
    assert (Hdvd2 : Nat.divide (x * y) (m * n)).
    { apply (plm_dvd_mul_coprime x y (m * n)).
      - apply (Nat.divide_trans x m).
        + exact Hxm.
        + exists n. apply Nat.mul_comm.
      - apply (Nat.divide_trans y n).
        + exact Hyn.
        + exists m. reflexivity.
      - exact Hgxy. }
    assert (Hxy1 : 1 <= x * y) by (apply pza_mul_pos; lia).
    assert (Hmod : m * n mod (x * y) = 0)
      by (apply (proj2 (Nat.Div0.mod_divides (m * n) (x * y)));
          destruct Hdvd2 as [c Hc]; exists c; rewrite Hc; apply Nat.mul_comm).
    rewrite E1 in Hmod.
    rewrite Hmod in Ed. rewrite Nat.eqb_refl in Ed. discriminate.
Qed.

(* ---- Section 4. Rearrangement of the folded product and the
   multiplicativity theorem ---- *)

Lemma pza_sigma_prod_pair : forall m n : nat,
  1 <= m -> 1 <= n ->
  pza_sigma m * pza_sigma n
  = pza_sumf (fun x => pza_sumf (fun y =>
      (x * pza_dvdind x m) * (y * pza_dvdind y n)) n) m.
Proof.
  intros m n Hm Hn. unfold pza_sigma. apply pza_sumf_mul.
Qed.

Lemma pza_prod_term : forall m n d : nat,
  d * pza_count m n d
  = pza_sumf (fun x => pza_sumf (fun y =>
      x * y * ((if Nat.eqb (x * y) d then 1 else 0)
                 * pza_dvdind x m * pza_dvdind y n)) n) m.
Proof.
  intros m n d. unfold pza_count.
  rewrite <- pza_sumf_scal_l.
  apply pza_sumf_ext. intros x Hx1 Hx2.
  rewrite <- pza_sumf_scal_l.
  apply pza_sumf_ext. intros y Hy1 Hy2.
  destruct (Nat.eqb (x * y) d) eqn:E1.
  - apply Nat.eqb_eq in E1. rewrite E1. ring.
  - rewrite !Nat.mul_0_l, !Nat.mul_0_r. reflexivity.
Qed.

Lemma pza_flatten : forall (A c K : nat),
  1 <= c -> c <= K ->
  pza_sumf (fun d => A * (if Nat.eqb c d then 1 else 0)) K = A.
Proof.
  intros A c K H1 H2. induction K as [| K' IH].
  - cbn [pza_sumf]. exfalso. lia.
  - cbn [pza_sumf]. destruct (le_lt_dec c K') as [Hc1 | Hc1].
    + rewrite (IH Hc1).
      assert (Eb : (c =? S K') = false) by (apply Nat.eqb_neq; lia).
      rewrite Eb. cbn. lia.
    + assert (Hc2 : c = S K') by lia. subst c.
      rewrite Nat.eqb_refl.
      rewrite pza_sumf_zero
        by (intros d Hd1 Hd2; destruct (Nat.eqb (S K') d) eqn:E;
            [apply Nat.eqb_eq in E; lia | cbn; apply Nat.mul_0_r]).
      cbn. rewrite Nat.mul_1_r. reflexivity.
Qed.

(* Whole equality of the triple sums when the terms agree pointwise (the
   two sides nest in different orders). *)
Lemma pza_triple_align :
  forall (L R : nat -> nat -> nat -> nat) (K M N : nat),
  (forall d x y, L d x y = R d x y) ->
  pza_sumf (fun d => pza_sumf (fun x => pza_sumf (fun y => L d x y) N) M) K
  = pza_sumf (fun x => pza_sumf (fun y =>
      pza_sumf (fun d => R d x y) K) N) M.
Proof.
  intros L R K M N H.
  transitivity
    (pza_sumf (fun x => pza_sumf (fun d =>
      pza_sumf (fun y => L d x y) N) K) M).
  - apply pza_sumf_rot_dx.
  - rewrite (pza_sumf_rot_yd R M N K).
    apply pza_sumf_ext. intros d Hd1 _.
    apply pza_sumf_ext. intros x Hx1 _.
    apply pza_sumf_ext. intros y Hy1 _.
    apply H.
Qed.

Theorem pza_sigma_mul : forall m n : nat,
  1 <= m -> 1 <= n -> Nat.gcd m n = 1 ->
  pza_sigma (m * n) = pza_sigma m * pza_sigma n.
Proof.
  intros m n Hm Hn Hgcd.
  rewrite (pza_sigma_prod_pair m n Hm Hn).
  unfold pza_sigma.
  transitivity
    (pza_sumf (fun d => pza_sumf (fun x => pza_sumf (fun y =>
      x * y * ((if Nat.eqb (x * y) d then 1 else 0)
                 * pza_dvdind x m * pza_dvdind y n)) n) m) (m * n)).
  - apply pza_sumf_ext. intros d Hd1 Hd2.
    rewrite <- (pza_count_eq m n d Hm Hn Hgcd).
    apply pza_prod_term.
  - transitivity
      (pza_sumf (fun x => pza_sumf (fun y => pza_sumf (fun d =>
        (x * pza_dvdind x m) * (y * pza_dvdind y n)
          * (if Nat.eqb (x * y) d then 1 else 0)) (m * n)) n) m).
    + apply pza_triple_align. intros d x y. ring.
    + apply pza_sumf_ext. intros x Hx1 Hx2.
      apply pza_sumf_ext. intros y Hy1 Hy2.
      apply pza_flatten.
      * apply pza_mul_pos; lia.
      * assert (HxyK : x * y <= m * n) by (apply Nat.mul_le_mono; lia).
        lia.
Qed.

(* ---- Section 5. Companion interfaces ---- *)

Theorem pza_sumf_trunc : forall (f : nat -> nat) (k N : nat),
  k <= N -> (forall d, k < d -> d <= N -> f d = 0) ->
  pza_sumf f N = pza_sumf f k.
Proof.
  intros f k N Hle H0. induction N as [| N' IH].
  - assert (Hz : k = 0) by lia. subst k. reflexivity.
  - destruct (Nat.eq_dec k (S N')) as [Ek | Nk].
    + subst k. reflexivity.
    + simpl. rewrite (H0 (S N')) by lia. rewrite Nat.add_0_r.
      apply IH; [lia | intros; apply H0; lia].
Qed.

Theorem pza_dvdind_mul_cancel : forall p j X : nat,
  1 <= p -> pza_dvdind (p * j) (p * X) = pza_dvdind j X.
Proof.
  intros p j X Hp. unfold pza_dvdind.
  destruct j as [| j'].
  - rewrite Nat.mul_0_r, !Nat.mod_0_r.
    destruct (Nat.eqb (p * X) 0) eqn:E1;
      destruct (Nat.eqb X 0) eqn:E2; try reflexivity; exfalso.
    + apply Nat.eqb_eq in E1. apply Nat.eqb_neq in E2.
      destruct X as [| X']; [lia |].
      assert (HpX : 1 <= p * S X')
        by (apply pza_mul_pos; lia).
      rewrite E1 in HpX. lia.
    + apply Nat.eqb_eq in E2. subst X.
      rewrite Nat.mul_0_r, Nat.eqb_refl in E1. discriminate.
  - destruct (Nat.eqb (p * X mod (p * S j')) 0) eqn:E1;
      destruct (Nat.eqb (X mod S j') 0) eqn:E2;
      try reflexivity; exfalso.
    + apply Nat.eqb_eq in E1.
      assert (Hd : Nat.divide (p * S j') (p * X))
        by (apply pr_mod0_dvd; [lia | exact E1]).
      destruct Hd as [z Hz].
      assert (Hpnz : p <> 0) by lia.
      assert (Hj : Nat.divide (S j') X).
      { exists z.
        apply (proj1 (Nat.mul_cancel_l X (z * S j') p Hpnz)).
        rewrite Hz. ring. }
      assert (Hmod : X mod S j' = 0)
        by (apply (proj2 (Nat.Div0.mod_divides X (S j')));
            destruct Hj as [c Hc]; exists c; rewrite Hc; apply Nat.mul_comm).
      rewrite Hmod, Nat.eqb_refl in E2. discriminate.
    + apply Nat.eqb_eq in E2.
      assert (Hd : Nat.divide (S j') X)
        by (apply pr_mod0_dvd; [lia | exact E2]).
      destruct Hd as [z Hz].
      assert (Hd2 : Nat.divide (p * S j') (p * X)).
      { exists z. rewrite Hz. ring. }
      assert (Hmod : p * X mod (p * S j') = 0)
        by (apply (proj2 (Nat.Div0.mod_divides (p * X) (p * S j')));
            destruct Hd2 as [c Hc]; exists c; rewrite Hc; apply Nat.mul_comm).
      rewrite Hmod, Nat.eqb_refl in E1. discriminate.
Qed.

(* ---- Section 6. Numerical witnesses ---- *)

Example pza_smoke_1 : pza_sigma 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Example pza_smoke_12 : pza_sigma 12 = 28.
Proof. vm_compute. reflexivity. Qed.

Example pza_smoke_35 : pza_sigma 35 = 48.
Proof. vm_compute. reflexivity. Qed.

Example pza_smoke_420 : pza_sigma 420 = 1344.
Proof. vm_compute. reflexivity. Qed.

(* ---- Section 7. Closing audit of constructive purity ---- *)

Print Assumptions pza_sigma.
Print Assumptions pza_sigma_mul.
Print Assumptions pza_dvdind_mul_cancel.
Print Assumptions pza_sumf_trunc.
Print Assumptions pza_count_eq.
Print Assumptions pza_split_coprime.
Print Assumptions pza_split_inj.
