(* ========================================================================= *)
(* LW2NivenInt - Niven 源头件第三供件面: Niven 型多项式的整系数性自动获证.    *)
(* 模块名：LW2NivenInt.  数学使命：给出 M3 e-超越装配实际衔接形的 Niven 源头多项式 f = t^n (a - b*t)^n 的纯 ℤ 版直接构造（a b : Z, 系数全为 ℤ 闭式： *)
(* 二项系数 lw2_binom × ℤ 幂 × 符号因子 (−1)^k），并自动获证其整系数性 lw2_niven_f_intpoly : forall a b n, lw2i_intpoly (lw2_niven_int_f a b n) *)
(* —— 每个系数自带 sigT 整数证人（Type 层见证形，复用 LW2Hermite 的 lw2i_intpoly 谓词），另附首项系数闭式面供 M3 非零性判定取用。 *)
(* π 承载裁决（M2 源头件既有裁决沿用）：M3 预留接口为 eval(p,e) 型，f∈ℤ[X] 直接构造，π 不入 f——故本件取纯 ℤ 版：f 中 π 不以有理 q=a/b 形 *)
(* 出现，亦不触碰 real_pi_geom（Real 层零接触）。与 Niven f（LW0Integrality2 之 lw0_niven_f_z q b n = (b^n/n!)·t^n(q−t)^n，q:Q b:Z）的关系：当 q=a/b *)
(* 时 lw0_niven_f_z (a/b) b n = (1/n!)·lw2_niven_int_f a b n（有理恒等，本件不 Require LW0Integrality2——其上游链 S03_QExp/UpReqBanachAdd 未入沙箱， *)
(* 依 LW2Hermite 同款窄依赖裁决，关系作头注声明）；1/n! 标度不属系数层——Niven 论证中 j!/n! 的整数性在 k≥n 的导数值层成立（j!/n! 为 nat 阶乘比）， *)
(* 系数层取未标度的 t^n(a−bt)^n 使整系数性免证成立。诚实面注记：对 lw0_niven_f_z 本身作无条件整系数谓词为假（q=1,b=1,n=2 时 t^2 系数=1/2）， *)
(* 故施工指引主件的非零前提形在此由免证的无前提强化形取代。                   *)
(* 依赖清单：LW0QPoly (QPoly, lw0_coef 经 LW2Hermite); LW2Binom (lw2_binom, lw2_binom_diag); LW2Hermite (lw2i_intpoly, lw0_coef); Stdlib QArith, *)
(* ZArith, Arith, Lia, List.                                                  *)
(* 语句面 Exact 形态声明：lw2_niven_int_f 由闭式系数函数 lw2_niven_zcoef 经 map/seq 直接列装，三条取用方程刻画： *)
(*   lw2_niven_int_f a b n = map (fun k => (lw2_niven_zcoef a b n k # 1)%Q) (seq 0 (Datatypes.S (n + n))) *)
(*   lw2_niven_zcoef a b n k = if n <=? k then (−1)^(k−n)·binom n (k−n)·a^(n−(k−n))·b^(k−n) *)
(*   else 0  （nat 截断减法；k>2n 支由 lw2_binom 越界零支自消）               *)
(*   lw2_niven_f_intpoly a b n : lw2i_intpoly (lw2_niven_int_f a b n)，三区域构造（i<n 证人 0 / n≤i≤2n 证人闭式 / i>2n 证人 0） *)
(* 构造性注记：every operation is a closed-form map with computing content (Defined); statements carry Qeq between rational data with explicit Z *)
(* witnesses in sigT form; nat orderings appear only inside proofs (erased on extraction); every proof ends in Qed, purely constructive throughout. *)
(* 编译配方：env COQLIB/ROCQLIB set to the Rocq 9.1 library, then "coqc.exe -q -Q . "" LW2NivenInt.v" in a sandbox holding byte-identical *)
(* LW0QPoly.v (md5 6f836288), LW2Binom.v (md5 c3489226), LW2Hermite.v (md5 7b6d5d71), each compiled green in the same sandbox first. *)
(* ========================================================================= *)

From Stdlib Require Import QArith ZArith Arith Lia List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW0QPoly.
Require Import LW2Binom.
Require Import LW2Hermite.

(* ------------------------------------------------------------------ *)
(* Section 1.  Leibniz-form coefficient lookup on mapped index lists.  *)
(* (map g (seq s m)) is [g s; g (s+1); ...; g (s+m-1)]: its j-th       *)
(* coefficient is g (s+j) when j < m, and structurally 0 beyond.       *)
(* Everything in this section is plain Leibniz equality on Q, so the   *)
(* downstream rewrites need no setoid machinery.                       *)
(* ------------------------------------------------------------------ *)

Lemma lw2_len_map_seq : forall (g : nat -> Q) (m s : nat),
  Id m (length (map g (seq s m))).
Proof.
  intros g.
  assert (Hc : forall m s, length (map g (seq s m)) = m).
  { induction m as [|m IH]; intros s.
    - reflexivity.
    - cbn [seq map length].
      rewrite (IH (Datatypes.S s)).
      reflexivity. }
  intros m s.
  rewrite (Hc m s).
  apply id_refl.
Qed.

Lemma lw2_coef_beyond_eq : forall (j : nat) (p : QPoly),
  (length p <= j)%nat -> Id (lw0_coef j p) 0%Q.
Proof.
  assert (Hc : forall (j : nat) (p : QPoly),
    (length p <= j)%nat -> lw0_coef j p = 0%Q).
  { intros j p.
    revert j.
    induction p as [|a p IH]; intros j Hj.
    - reflexivity.
    - destruct j as [|j'].
      + simpl in Hj. lia.
      + cbn [lw0_coef].
        apply (IH j').
        simpl in Hj. lia. }
  intros j p Hj.
  rewrite (Hc j p Hj).
  apply id_refl.
Qed.

Lemma lw2_coef_seq_gen_eq : forall (g : nat -> Q) (m s i : nat),
  (i < m)%nat -> Id (lw0_coef i (map g (seq s m))) (g (s + i)%nat).
Proof.
  assert (Hc : forall (g : nat -> Q) (m s i : nat),
    (i < m)%nat -> lw0_coef i (map g (seq s m)) = g (s + i)%nat).
  { intros g.
    induction m as [|m IH]; intros s i Hi.
    - exfalso. lia.
    - cbn [seq map].
      destruct i as [|i'].
      + cbn [lw0_coef].
        rewrite Nat.add_0_r.
        reflexivity.
      + cbn [lw0_coef].
        replace (s + Datatypes.S i')%nat with (Datatypes.S s + i')%nat by lia.
        apply IH.
        lia. }
  intros g m s i Hi.
  rewrite (Hc g m s i Hi).
  apply id_refl.
Qed.

Lemma lw2_coef_seq0_eq : forall (g : nat -> Q) (m i : nat),
  (i < m)%nat -> Id (lw0_coef i (map g (seq 0 m))) (g i).
Proof.
  assert (Hc : forall (g : nat -> Q) (m i : nat),
    (i < m)%nat -> lw0_coef i (map g (seq 0 m)) = g i).
  { intros g m i Hi.
    rewrite <- (Nat.add_0_l i).
    destruct (lw2_coef_seq_gen_eq g m 0 i Hi).
    reflexivity. }
  intros g m i Hi.
  rewrite (Hc g m i Hi).
  apply id_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  The Niven source polynomial, pure-Z face.               *)
(* f = t^n (a - b*t)^n with a b : Z.  Closed-form coefficients: the    *)
(* coefficient of t^(n+k) is (-1)^k * binom(n,k) * a^(n-k) * b^k, zero *)
(* outside [n, 2n].  Indexing by the absolute degree i with d = i - n  *)
(* (truncated nat subtraction), the gate n <=? i zeroes the low band;  *)
(* the high band (d > n) dies through lw2_binom's zero branch.         *)
(* ------------------------------------------------------------------ *)

Definition lw2_niven_zcoef (a b : Z) (n i : nat) : Z :=
  match Nat.leb n i with
  | true =>
      (Z.pow (-1)%Z (Z.of_nat (i - n)) *
       Z.of_nat (lw2_binom n (i - n)) *
       Z.pow a (Z.of_nat (n - (i - n))) *
       Z.pow b (Z.of_nat (i - n)))%Z
  | false => 0%Z
  end.

Definition lw2_niven_int_f (a b : Z) (n : nat) : QPoly :=
  map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
      (seq 0 (Datatypes.S (n + n))).

(* ------------------------------------------------------------------ *)
(* Section 3.  Automatic integrality (the seat's main deliverable).    *)
(* Each coefficient carries an explicit Z witness: the same closed     *)
(* form that defines it -- integrality holds by construction.          *)
(* ------------------------------------------------------------------ *)

Theorem lw2_niven_f_intpoly : forall (a b : Z) (n : nat),
  lw2i_intpoly (lw2_niven_int_f a b n).
Proof.
  intros a b n i.
  destruct (Nat.leb n i) eqn:Hb1.
  - destruct (Nat.leb i (n + n)) eqn:Hb2.
    + (* main band: witness is the closed form itself. *)
      apply Nat.leb_le in Hb1.
      apply Nat.leb_le in Hb2.
      assert (Hin : (i < Datatypes.S (n + n))%nat) by lia.
      exists (lw2_niven_zcoef a b n i).
      unfold lw2_niven_int_f.
      assert (Hc0 : lw0_coef i
                 (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                      (seq 0 (Datatypes.S (n + n))))
                 = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) i).
      { destruct (lw2_coef_seq0_eq
               (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
               (Datatypes.S (n + n)) i Hin).
        reflexivity. }
      rewrite Hc0. cbv beta.
      apply qeq_imp_qeqT. apply Qeq_refl.
    + (* beyond the list: coefficient is structurally zero. *)
      apply Nat.leb_gt in Hb2.
      assert (Hout : (Datatypes.S (n + n) <= i)%nat) by lia.
      exists 0%Z.
      unfold lw2_niven_int_f.
      assert (Hlen : length (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                      (seq 0 (Datatypes.S (n + n)))) = Datatypes.S (n + n)).
      { destruct (lw2_len_map_seq
               (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
               (Datatypes.S (n + n)) 0).
        reflexivity. }
      assert (Hbeyond : lw0_coef i
                 (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                      (seq 0 (Datatypes.S (n + n)))) = 0%Q).
      { destruct (lw2_coef_beyond_eq i
               (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                    (seq 0 (Datatypes.S (n + n))))
               ltac:(rewrite Hlen; exact Hout)).
        reflexivity. }
      rewrite Hbeyond.
      reflexivity.
  - (* low band: coefficient is the gated zero. *)
    assert (Hlt : (i < n)%nat) by (apply Nat.leb_gt; exact Hb1).
    assert (Hin : (i < Datatypes.S (n + n))%nat) by lia.
    exists 0%Z.
    unfold lw2_niven_int_f.
    assert (Hc0 : lw0_coef i
               (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                    (seq 0 (Datatypes.S (n + n))))
               = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) i).
    { destruct (lw2_coef_seq0_eq
             (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
             (Datatypes.S (n + n)) i Hin).
      reflexivity. }
    rewrite Hc0.
    cbv beta.
    unfold lw2_niven_zcoef.
    rewrite Hb1.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4.  Leading-coefficient faces for M3's nonzero consumption. *)
(* The top coefficient (degree 2n) is the closed form at i = n + n;    *)
(* it further collapses to (-1)^n * b^n (binom n n = 1, a^0 = 1), so   *)
(* b <> 0 in Z certifies f <> 0 by pure Z arithmetic downstream.       *)
(* ------------------------------------------------------------------ *)

Lemma lw2_niven_f_lc : forall (a b : Z) (n : nat),
  QeqT (lw0_coef (n + n) (lw2_niven_int_f a b n))
       ((lw2_niven_zcoef a b n (n + n)) # 1)%Q.
Proof.
  intros a b n.
  unfold lw2_niven_int_f.
  assert (Hc0 : lw0_coef (n + n)
             (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                  (seq 0 (Datatypes.S (n + n))))
             = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) (n + n)%nat).
  { destruct (lw2_coef_seq0_eq
           (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
           (Datatypes.S (n + n)) (n + n) (Nat.lt_succ_diag_r (n + n))).
    reflexivity. }
  rewrite Hc0. cbv beta.
  apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

Lemma lw2_niven_f_lc_closed : forall (a b : Z) (n : nat),
  QeqT (lw0_coef (n + n) (lw2_niven_int_f a b n))
       ((Z.pow (-1)%Z (Z.of_nat n) * Z.pow b (Z.of_nat n)) # 1)%Q.
Proof.
  intros a b n.
  unfold lw2_niven_int_f.
  assert (Hc0 : lw0_coef (n + n)
             (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                  (seq 0 (Datatypes.S (n + n))))
             = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) (n + n)%nat).
  { destruct (lw2_coef_seq0_eq
           (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
           (Datatypes.S (n + n)) (n + n) (Nat.lt_succ_diag_r (n + n))).
    reflexivity. }
  rewrite Hc0.
  cbv beta.
  apply qeq_imp_qeqT.
  unfold lw2_niven_zcoef.
  assert (Hg : Nat.leb n (n + n) = true) by (apply Nat.leb_le; lia).
  rewrite Hg.
  replace (n + n - n)%nat with n by lia.
  rewrite lw2_binom_diag.
  change (Z.of_nat 1) with 1%Z.
  replace (n - n)%nat with 0%nat by lia.
  change (Z.of_nat 0) with 0%Z.
  rewrite Z.pow_0_r.
  unfold Qeq.
  cbn [Qnum Qden].
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 5.  Extraction probe and assumption checks.                 *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Extraction.
Separate Extraction lw2_niven_int_f lw2_niven_f_intpoly lw2_niven_f_lc.

Print Assumptions lw2_niven_int_f.
Print Assumptions lw2_niven_f_intpoly.
Print Assumptions lw2_niven_f_lc.
Print Assumptions lw2_niven_f_lc_closed.
