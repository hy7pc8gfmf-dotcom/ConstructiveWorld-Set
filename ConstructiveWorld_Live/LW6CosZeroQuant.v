(* ============================================================ *)
(* LW6CosZeroQuant.v                                            *)
(*                                                              *)
(* Mission. Quantitative simplicity of the cos zero in (3/2,2): *)
(*   the constructive shape of a nondegenerate zero. The        *)
(*   "forall-eps distance control" uniqueness reading becomes   *)
(*   an explicit inverse-bound statement: a zero w with window  *)
(*   [lo,hi] and constant K such that any u <= v in the window  *)
(*   with cos values (term j) below du and dv satisfy           *)
(*   |u - v| <= K*(du + dv). Main theorem: cos_pi_half is a     *)
(*   nondegenerate zero (K = 2); corollary: separation modulus. *)
(* Dependencies. S01_BaseRing (And, NatLe family); S02_Cauchy-  *)
(*   Complete (Real, real_eq, real_lt, QltT/QleT' conversions,  *)
(*   qeq_le); S07_RealSetoidExpLog; S10_KVQuantTrig (cos_inv_   *)
(*   dist_le2, cauchy_real_cos, cos_pi_half, real_cos_proj and  *)
(*   the window/endpoint lemmas); Stdlib QArith/Setoid/         *)
(*   Morphisms/Lia.                                             *)
(* References. cos_pi_half_unique_widened of S10_KVQuantTrig.v: *)
(*   rewritten from its forall-eps reading to an exists-K       *)
(*   inverse-bound reading; the constant 2 is the native value  *)
(*   of cos_inv_dist_le2 (core estimate of cos_inv_pt).         *)
(* Constructivity. Whole piece Set/Type leveled; purely         *)
(*   constructive with zero classical steps; Q-level comparison *)
(*   and existence take QltT/QleT'/sigT, real level real_lt and *)
(*   real_eq; the corollary trichotomy is carried by the        *)
(*   Type-level three-way certificate lw6q_sep_cert (no         *)
(*   sumbool injection); proofs erasable, all Qed-closed.       *)
(* Build. coqc -q -Q <main vo lib root> "" LW6CosZeroQuant.v    *)
(*   with COQLIB and ROCQLIB verbatim at the 9.1 lib root.      *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ---- Nondegenerate zero (Set-level definition) ----
   Triple shape: a zero w together with a window [lo, hi] and an
   inverse-bound constant K: w is a zero of cos, lies in the
   window, and the inverse bound holds -- any two points
   u <= v of the window whose cos values (term j, j >= 2) fall
   below du and dv respectively satisfy |u - v| <= K*(du + dv).
   K finite is the quantitative form of "small cos values force
   two points close inside the window", i.e. the quantified
   content of zero simplicity. *)
Definition lw6q_nondegenerate_zero (w : Real) (lo hi : Q) : Set :=
  And (real_lt (real_const lo) w)
    (And (real_lt w (real_const hi))
      (And (real_eq (cauchy_real_cos w) real_zero)
        (sigT (fun K : Q =>
          And (QltT 0 K)
            (forall (u v du dv : Q) (j : nat), (2 <= j)%nat ->
              QleT' lo u -> QleT' u v -> QleT' v hi ->
              QltT (Qabs (projT1 (cauchy_real_cos (real_const u)) j
                            - projT1 real_zero j)) du ->
              QltT (Qabs (projT1 (cauchy_real_cos (real_const v)) j
                            - projT1 real_zero j)) dv ->
              QleT' (Qabs (u - v)) (K * (du + dv))%Q))))).

(* ---- Inverse-bound lemma (constant 2) ----
   Transcribed from cos_inv_dist_le2: the Qlt/Qle premise faces
   are exchanged for QltT/QleT' faces, the conclusion v - u is
   exchanged for |u - v| (u <= v gives Qabs (u-v) == v-u), and
   2*(du+dv) is split into two steps via qleT'_trans. *)
Lemma lw6q_cos_inv_bound : forall (u v du dv : Q) (j : nat),
  (2 <= j)%nat ->
  QleT' (3 / 2) u -> QleT' u v -> QleT' v 2 ->
  QltT (Qabs (projT1 (cauchy_real_cos (real_const u)) j
                - projT1 real_zero j)) du ->
  QltT (Qabs (projT1 (cauchy_real_cos (real_const v)) j
                - projT1 real_zero j)) dv ->
  QleT' (Qabs (u - v)) (2 * (du + dv))%Q.
Proof.
  intros u v du dv j Hj Hu0 Huv Hv2 Hdu Hdv.
  assert (Habs : Qabs (u - v) == v - u).
  { rewrite (Qabs_Qminus u v). apply Qabs_pos.
    apply (proj1 (Qle_minus_iff u v)). apply QleT'_to_Qle. exact Huv. }
  apply (qleT'_trans _ (v - u) _).
  - apply qeq_le. apply qeq_imp_qeqT. exact Habs.
  - apply qltT_leT'.
    apply (cos_inv_dist_le2 u v du dv j Hj).
    + apply QleT'_to_Qle. exact Hu0.
    + apply QleT'_to_Qle. exact Huv.
    + apply QleT'_to_Qle. exact Hv2.
    + apply QltT_to_Qlt. exact Hdu.
    + apply QltT_to_Qlt. exact Hdv.
Qed.

(* ---- Endpoint lemma: cos_pi_half < 2 ----
   Via order transition through 5/3: real_lt_cos_pi_half_five_thirds
   and real_const_lt (5/3 < 2) composed with real_lt_trans. *)
Lemma lw6q_cos_pi_half_lt_two : real_lt cos_pi_half (real_const 2).
Proof.
  apply (real_lt_trans cos_pi_half (real_const (5 / 3)) (real_const 2)).
  - exact real_lt_cos_pi_half_five_thirds.
  - apply real_const_lt. apply Qlt_to_QltT. change (Qlt (5 / 3) 2). compute. reflexivity.
Qed.

(* ---- Main theorem: cos_pi_half is a nondegenerate zero (K = 2) ----
   Window endpoints: left real_lt_three_halves_cos_pi_half, right
   lw6q_cos_pi_half_lt_two; zero-ness real_cos_pi_half_zero;
   the inverse-bound component is lw6q_cos_inv_bound. *)
Theorem lw6q_cos_pi_half_nondegenerate :
  lw6q_nondegenerate_zero cos_pi_half (3 / 2) 2.
Proof.
  unfold lw6q_nondegenerate_zero.
  split.
  - exact real_lt_three_halves_cos_pi_half.
  - split.
    + exact lw6q_cos_pi_half_lt_two.
    + split.
      * exact real_cos_pi_half_zero.
      * exists 2.
        split.
        -- apply Qlt_to_QltT. change (Qlt 0 2). compute. reflexivity.
        -- exact lw6q_cos_inv_bound.
Qed.

(* ---- Separation certificate (Type-level three-way inductive) ----
   Certificate type for the corollary conclusion face: the near
   branch carries a QleT' certificate of the distance, the two far
   wings each carry the QleT' certificate that the corresponding
   point's cos value is not below its explicit bound. Semantically
   equivalent to the old shape (bool-indexed match family plus an
   inner sumbool inside the far branches), entirely Type level. *)
Inductive lw6q_sep_cert (u v : Real) (du dv : Q) (k : nat) : Set :=
| lw6q_cert_near :
    QleT' (Qabs (projT1 u k - projT1 v k)) (2 * (du + dv))%Q ->
    lw6q_sep_cert u v du dv k
| lw6q_cert_far_u :
    QleT' du (Qabs (projT1 (cauchy_real_cos u) k - projT1 real_zero k)) ->
    lw6q_sep_cert u v du dv k
| lw6q_cert_far_v :
    QleT' dv (Qabs (projT1 (cauchy_real_cos v) k - projT1 real_zero k)) ->
    lw6q_sep_cert u v du dv k.

(* ---- Corollary: separation modulus shape ----
   Any two points u, v of the window: either they are already
   mutually close within modulus 2*(du+dv), or at least one of
   them has cos value not below its explicit bound (du or dv) --
   the quantitative form of "two points cannot both hug the zero
   while staying far apart". The three branches are decidable at
   Q level; the certificate is expressed by the Type-level
   three-way inductive lw6q_sep_cert (far branches not recast as
   dependent, sumbool injection positions removed). *)
Corollary lw6q_zero_separation_modulus : forall (u v : Real),
  real_lt (real_const (3 / 2)) u -> real_lt u (real_const 2) ->
  real_lt (real_const (3 / 2)) v -> real_lt v (real_const 2) ->
  forall du dv : Q, QltT 0 du -> QltT 0 dv ->
  sigT (fun N : nat => forall k : nat, (N <= k)%nat ->
    lw6q_sep_cert u v du dv k).
Proof.
  intros u v Hul Huu Hvl Hvu du dv Hdu Hdv.
  destruct (real_lt_lower_pt (3 / 2) u Hul) as [Nul HNul].
  destruct (real_lt_upper_pt 2 u Huu) as [Nuu HNuu].
  destruct (real_lt_lower_pt (3 / 2) v Hvl) as [Nvl HNvl].
  destruct (real_lt_upper_pt 2 v Hvu) as [Nvu HNvu].
  exists (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))).
  intros k Hk.
  assert (Hk2 : (2 <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
      [apply Nat.le_max_l | exact Hk]. }
  assert (Hkul : (Nul <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
      [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
        [apply Nat.le_max_r | exact Hk]]. }
  assert (Hkuu : (Nuu <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nuu (Nat.max Nvl Nvu)) _);
      [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
        [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
          [apply Nat.le_max_r | exact Hk]]]. }
  assert (Hkvl : (Nvl <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nvl Nvu) _);
      [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max Nuu (Nat.max Nvl Nvu)) _);
        [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
          [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
            [apply Nat.le_max_r | exact Hk]]]]. }
  assert (Hkvu : (Nvu <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nvl Nvu) _);
      [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max Nuu (Nat.max Nvl Nvu)) _);
        [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
          [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
            [apply Nat.le_max_r | exact Hk]]]]. }
  assert (Hul' : Qle (3 / 2) (projT1 u k)) by (apply Qlt_le_weak; apply (HNul k Hkul)).
  assert (Huu' : Qle (projT1 u k) 2) by (apply Qlt_le_weak; apply (HNuu k Hkuu)).
  assert (Hvl' : Qle (3 / 2) (projT1 v k)) by (apply Qlt_le_weak; apply (HNvl k Hkvl)).
  assert (Hvu' : Qle (projT1 v k) 2) by (apply Qlt_le_weak; apply (HNvu k Hkvu)).
  destruct (Qlt_le_dec (Qabs (projT1 (cauchy_real_cos u) k
                                - projT1 real_zero k)) du) as [Hcu | Hcu].
  - (* cos value u_k below du: inspect cos value v_k *)
    destruct (Qlt_le_dec (Qabs (projT1 (cauchy_real_cos v) k
                                - projT1 real_zero k)) dv) as [Hcv | Hcv].
    + (* both cos values below their bounds: distance within modulus 2*(du+dv) *)
      apply lw6q_cert_near. apply Qle_to_QleT'. apply Qlt_le_weak.
      assert (Hcu' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 u k))) k
                                - projT1 real_zero k)) du).
      { apply (Qle_lt_trans _ (Qabs (projT1 (cauchy_real_cos u) k
                                      - projT1 real_zero k)) _).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 u k))) k ==
                       projT1 (cauchy_real_cos u) k).
          { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 u k)) k)).
            rewrite (qeqT_imp_qeq _ _ (real_cos_proj u k)). reflexivity. }
          rewrite Hq. reflexivity.
        - exact Hcu. }
      assert (Hcv' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 v k))) k
                                - projT1 real_zero k)) dv).
      { apply (Qle_lt_trans _ (Qabs (projT1 (cauchy_real_cos v) k
                                      - projT1 real_zero k)) _).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 v k))) k ==
                       projT1 (cauchy_real_cos v) k).
          { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 v k)) k)).
            rewrite (qeqT_imp_qeq _ _ (real_cos_proj v k)). reflexivity. }
          rewrite Hq. reflexivity.
        - exact Hcv. }
      destruct (Qlt_le_dec (projT1 v k) (projT1 u k)) as [Hvlu | Huvl].
      * (* v_k < u_k: u is the upper point; bounds swap with the points (du<->dv) *)
        assert (Habs : Qabs (projT1 u k - projT1 v k) == projT1 u k - projT1 v k).
        { apply Qabs_pos. apply (proj1 (Qle_minus_iff (projT1 v k) (projT1 u k))).
          apply Qlt_le_weak. exact Hvlu. }
        rewrite Habs.
        assert (Hd : Qlt (projT1 u k - projT1 v k) (2 * (dv + du))).
        { apply QltT_to_Qlt.
          apply (cos_inv_dist_le2 (projT1 v k) (projT1 u k) dv du k Hk2 Hvl'
                                  (Qlt_le_weak (projT1 v k) (projT1 u k) Hvlu)
                                  Huu' Hcv' Hcu'). }
        rewrite (Qplus_comm du dv). exact Hd.
      * (* u_k <= v_k: v is the upper point *)
        assert (Habs : Qabs (projT1 u k - projT1 v k) == projT1 v k - projT1 u k).
        { rewrite (Qabs_Qminus (projT1 u k) (projT1 v k)). apply Qabs_pos.
          exact (proj1 (Qle_minus_iff (projT1 u k) (projT1 v k)) Huvl). }
        rewrite Habs.
        apply QltT_to_Qlt.
        apply (cos_inv_dist_le2 (projT1 u k) (projT1 v k) du dv k Hk2 Hul'
                                Huvl Hvu' Hcu' Hcv').
    + (* cos value v_k not below dv: far branch takes the v wing *)
      apply lw6q_cert_far_v. apply Qle_to_QleT'. exact Hcv.
  - (* cos value u_k not below du: far branch takes the u wing *)
    apply lw6q_cert_far_u. apply Qle_to_QleT'. exact Hcu.
Qed.

(* ---- closure check ---- *)
Print Assumptions lw6q_cos_inv_bound.
Print Assumptions lw6q_cos_pi_half_lt_two.
Print Assumptions lw6q_cos_pi_half_nondegenerate.
Print Assumptions lw6q_zero_separation_modulus.
