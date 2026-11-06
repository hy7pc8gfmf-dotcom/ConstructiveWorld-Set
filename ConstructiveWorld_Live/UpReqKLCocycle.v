(* ConstructiveWorld-Set -- exact real-arithmetic identity family. *)
(** * UpReqKLCocycle: symmetric KL cocycle identities along chains of positive temperatures.

    Mission.  The lift of the two-temperature firewall identity
      [retm_energy_temp_kl_pair_ident] to chains of three and four positive
      temperatures: the vanishing self-divergence [cyc_kl_sym_self_zero],
      the symmetric cocycle [cyc_kl_temp_cocycle] with its bracket form
      [cyc_kl_temp_cocycle_dev] over the deviation [cyc_dev], the forward
      decomposition [cyc_kl_forward_cocycle], and the 2-cocycle closure
      [cyc_kl_temp_cocycle_2up]; all exact, division free [real_eq] forms.

    Dependencies.  Stdlib [QArith.Qring].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], and [RealEnergyTempMono] of this development.

    References.  This development, UpReqKLCocycle.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqKLCocycle.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.Qring.
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
Require Import RealEnergyTempMono.

(* algebraic closure for [real_eq] goals, playing the role of the tactic
   [retm_alg] of [RealEnergyTempMono] and carried by this file itself so
   that no Ltac export is required: reduce the equality to a zero
   difference, move from the [QeqT] carrier face to the [Qeq] ring face
   (the equality [ring] reifies over), project pointwise in [n], and close
   by the rational ring. *)
Ltac cyc_alg :=
  apply real_eq_of_zero_diff; intro n; apply qeq_imp_qeqT;
  repeat first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) ];
  ring.

(* specialization for goals whose right side is [real_zero]: the projection
   [projT1 real_zero n] is not reached by the rewrite surface and must be
   computed away first; after that reduction the goal moves from the
   [QeqT] carrier face to the [Qeq] ring face and closes by the rational
   ring over the projected atoms. *)
Ltac cyc_alg0 :=
  apply real_eq_of_zero_diff; intro n;
  cbn [real_zero projT1];
  apply qeq_imp_qeqT;
  repeat first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) ];
  ring.

(* ============================================================ *)
(* Section 0.  the algebraic closure regime of this file.        *)
(*                                                              *)
(*   on [real_eq] goals, [ring] reification digests any number  *)
(*   of application-projection atoms of the form                *)
(*   [projT1 (real_inv_pos t Ht) n] or                          *)
(*   [projT1 (retm_Eexp ...) n].  bare variable projections     *)
(*   [projT1 b n], with [b] a universally quantified variable,  *)
(*   stay ring atoms only up to three occurrences; beyond that  *)
(*   [ring] rejects the goal as not a valid ring equation,      *)
(*   which is why every ring statement of [S02_CauchyComplete]  *)
(*   carries at most three of them.  the algebraic core is      *)
(*   therefore never isolated as a standalone statement: the    *)
(*   compatibility chain substitutes the concrete applications  *)
(*   first, and the resulting goal, whose atoms are all         *)
(*   application forms, closes inline.                          *)
(* ============================================================ *)

(* ============================================================ *)
(* Section 1.  the degenerate branch: no division is used anywhere, so *)
(*   the identities take a cross-product form, and the vanishing    *)
(*   of the self-divergence is their base case.                     *)
(* ============================================================ *)

(* the self-divergence [KL(p_t||p_t)] is exactly zero: the base edge of a
   degenerate triangle.  this specializes [retm_KL_decomp] at the pair
   [(t,t)] and closes the degenerate core algebraically. *)
Theorem cyc_kl_sym_self_zero : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t : Real) (Ht : real_lt real_zero t),
  real_eq (retm_KL X u s0 l t Ht t Ht) real_zero.
Proof.
  intros X u s0 l t Ht.
  apply (real_eq_trans (retm_KL X u s0 l t Ht t Ht)
           (real_plus
              (real_mult (real_plus (real_inv_pos t Ht) (real_opp (real_inv_pos t Ht)))
                         (retm_Eexp X u s0 l t Ht))
              (real_plus (retm_LZ X u s0 l t Ht) (real_opp (retm_LZ X u s0 l t Ht))))
           real_zero).
  - exact (retm_KL_decomp X u s0 l t Ht t Ht).
  - cyc_alg0.
Qed.

(* ============================================================ *)
(* Section 2.  main statement: the three-temperature symmetric KL  *)
(*   cocycle identity.                                          *)
(* ============================================================ *)

(* with P(i,j) := KL(p_j||p_i) + KL(p_i||p_j), the KL(p_j||p_i) summand
   kept first as in the pair identity, the three instances below align
   with it verbatim and need no reordering.  the claim is
   P(1,2) + (P(2,3) - P(1,3)) == (beta2 - beta1)(E3 - E2)
     + (beta3 - beta2)(E2 - E1):
   the right side is a sum of cross products with no division, so equal or
   coinciding temperatures are covered without any distinctness side
   condition. *)
Theorem cyc_kl_temp_cocycle : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1)
  (t2 : Real) (Ht2 : real_lt real_zero t2)
  (t3 : Real) (Ht3 : real_lt real_zero t3),
  real_eq
    (real_plus (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                          (retm_KL X u s0 l t1 Ht1 t2 Ht2))
               (real_plus (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2)
                                     (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                          (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1)
                                               (retm_KL X u s0 l t1 Ht1 t3 Ht3)))))
    (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
                          (real_plus (retm_Eexp X u s0 l t3 Ht3)
                                     (real_opp (retm_Eexp X u s0 l t2 Ht2))))
               (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
                          (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                     (real_opp (retm_Eexp X u s0 l t1 Ht1))))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 t3 Ht3.
  assert (H12 := retm_energy_temp_kl_pair_ident X u s0 l t1 Ht1 t2 Ht2).
  assert (H23 := retm_energy_temp_kl_pair_ident X u s0 l t2 Ht2 t3 Ht3).
  assert (H13 := retm_energy_temp_kl_pair_ident X u s0 l t1 Ht1 t3 Ht3).
  apply (real_eq_trans
           (real_plus (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                                 (retm_KL X u s0 l t1 Ht1 t2 Ht2))
                      (real_plus (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2)
                                            (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                                 (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1)
                                                      (retm_KL X u s0 l t1 Ht1 t3 Ht3)))))
           (real_plus
              (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                         (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))
              (real_plus
                 (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t3 Ht3)))
                            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                 (real_opp (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                                      (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1)))))))).
  - exact (RealSetoid.real_eq_plus_compat
             (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t2 Ht2))
             (real_plus (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2) (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                        (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t3 Ht3))))
             (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                        (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))
             (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t3 Ht3)))
                                   (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                        (real_opp (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                                             (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1))))))
             H12
             (RealSetoid.real_eq_plus_compat
                (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2) (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t3 Ht3)))
                (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t3 Ht3)))
                           (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                (real_opp (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                                     (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1)))))
                H23
                (RealSetoid.real_eq_opp_compat
                   (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t3 Ht3))
                   (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                              (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1))))
                   H13))).
  - cyc_alg.
Qed.

(* the deviation bracket, a transparent definition with every argument
   explicit: D(i,j,k) := P(i,j) + (P(j,k) - P(i,k)). *)
Definition cyc_dev (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (ta : Real) (Ha : real_lt real_zero ta)
  (tb : Real) (Hb : real_lt real_zero tb)
  (tc : Real) (Hc : real_lt real_zero tc) : Real :=
  real_plus (real_plus (retm_KL X u s0 l tb Hb ta Ha)
                       (retm_KL X u s0 l ta Ha tb Hb))
            (real_plus (real_plus (retm_KL X u s0 l tc Hc tb Hb)
                                  (retm_KL X u s0 l tb Hb tc Hc))
                       (real_opp (real_plus (retm_KL X u s0 l tc Hc ta Ha)
                                            (retm_KL X u s0 l ta Ha tc Hc)))).

(* bracket-form restatement of the main statement: [cyc_dev] unfolds to
   exactly the combination displayed there, so [exact] closes the goal. *)
Theorem cyc_kl_temp_cocycle_dev : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (ta : Real) (Ha : real_lt real_zero ta)
  (tb : Real) (Hb : real_lt real_zero tb)
  (tc : Real) (Hc : real_lt real_zero tc),
  real_eq (cyc_dev X u s0 l ta Ha tb Hb tc Hc)
          (real_plus (real_mult (real_plus (real_inv_pos tb Hb) (real_opp (real_inv_pos ta Ha)))
                                (real_plus (retm_Eexp X u s0 l tc Hc)
                                           (real_opp (retm_Eexp X u s0 l tb Hb))))
                     (real_mult (real_plus (real_inv_pos tc Hc) (real_opp (real_inv_pos tb Hb)))
                                (real_plus (retm_Eexp X u s0 l tb Hb)
                                           (real_opp (retm_Eexp X u s0 l ta Ha))))).
Proof.
  exact (cyc_kl_temp_cocycle).
Qed.

(* ============================================================ *)
(* Section 3.  forward companion: the forward KL decomposition law  *)
(*   along the temperature chain.                                *)
(* ============================================================ *)

(* with F(i,j) := KL(p_i||p_j), the forward combination satisfies
   F(1,2) + (F(2,3) - F(1,3)) == (beta3 - beta2)(E2 - E1): the logarithmic
   terms cancel along the chain and only the middle energy gap survives.
   this instantiates [retm_KL_decomp] at the three pairs. *)
Theorem cyc_kl_forward_cocycle : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1)
  (t2 : Real) (Ht2 : real_lt real_zero t2)
  (t3 : Real) (Ht3 : real_lt real_zero t3),
  real_eq
    (real_plus (retm_KL X u s0 l t1 Ht1 t2 Ht2)
               (real_plus (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                          (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3))))
    (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
               (real_plus (retm_Eexp X u s0 l t2 Ht2)
                          (real_opp (retm_Eexp X u s0 l t1 Ht1)))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 t3 Ht3.
  assert (d12 := retm_KL_decomp X u s0 l t1 Ht1 t2 Ht2).
  assert (d23 := retm_KL_decomp X u s0 l t2 Ht2 t3 Ht3).
  assert (d13 := retm_KL_decomp X u s0 l t1 Ht1 t3 Ht3).
  apply (real_eq_trans
           (real_plus (retm_KL X u s0 l t1 Ht1 t2 Ht2)
                      (real_plus (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                                 (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3))))
           (real_plus
              (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2)
                                                (real_opp (real_inv_pos t1 Ht1)))
                                    (retm_Eexp X u s0 l t1 Ht1))
                         (real_plus (retm_LZ X u s0 l t2 Ht2)
                                    (real_opp (retm_LZ X u s0 l t1 Ht1))))
              (real_plus
                 (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3)
                                                   (real_opp (real_inv_pos t2 Ht2)))
                                       (retm_Eexp X u s0 l t2 Ht2))
                            (real_plus (retm_LZ X u s0 l t3 Ht3)
                                       (real_opp (retm_LZ X u s0 l t2 Ht2))))
                 (real_opp (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3)
                                                             (real_opp (real_inv_pos t1 Ht1)))
                                                 (retm_Eexp X u s0 l t1 Ht1))
                                      (real_plus (retm_LZ X u s0 l t3 Ht3)
                                                 (real_opp (retm_LZ X u s0 l t1 Ht1)))))))).
  - exact (RealSetoid.real_eq_plus_compat
             (retm_KL X u s0 l t1 Ht1 t2 Ht2)
             (real_plus (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                        (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3)))
             (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
                                   (retm_Eexp X u s0 l t1 Ht1))
                        (real_plus (retm_LZ X u s0 l t2 Ht2) (real_opp (retm_LZ X u s0 l t1 Ht1))))
             (real_plus (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
                                   (retm_Eexp X u s0 l t2 Ht2))
                        (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t2 Ht2))))
             (real_opp (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
                                                  (retm_Eexp X u s0 l t1 Ht1))
                                       (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t1 Ht1))))))
             d12
             (RealSetoid.real_eq_plus_compat
                (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3))
                (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
                                      (retm_Eexp X u s0 l t2 Ht2))
                           (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t2 Ht2))))
                (real_opp (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
                                                (retm_Eexp X u s0 l t1 Ht1))
                                     (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t1 Ht1)))))
                d23
                (RealSetoid.real_eq_opp_compat
                   (retm_KL X u s0 l t1 Ht1 t3 Ht3)
                   (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
                                         (retm_Eexp X u s0 l t1 Ht1))
                              (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t1 Ht1))))
                   d13))).
  - cyc_alg.
Qed.

(* ============================================================ *)
(* Section 4.  the four-temperature 2-cocycle closedness.        *)
(* ============================================================ *)

(* expansion of the deviation bracket: D(a,b,c) equals the explicit
   combination appearing in the goal of the main statement. *)
Lemma cyc_kl_dev_expand : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (ta : Real) (Ha : real_lt real_zero ta)
  (tb : Real) (Hb : real_lt real_zero tb)
  (tc : Real) (Hc : real_lt real_zero tc),
  real_eq (cyc_dev X u s0 l ta Ha tb Hb tc Hc)
          (real_plus (real_mult (real_plus (real_inv_pos tb Hb) (real_opp (real_inv_pos ta Ha)))
                                (real_plus (retm_Eexp X u s0 l tc Hc)
                                           (real_opp (retm_Eexp X u s0 l tb Hb))))
                     (real_mult (real_plus (real_inv_pos tc Hc) (real_opp (real_inv_pos tb Hb)))
                                (real_plus (retm_Eexp X u s0 l tb Hb)
                                           (real_opp (retm_Eexp X u s0 l ta Ha))))).
Proof.
  exact (fun X u s0 l ta Ha tb Hb tc Hc =>           cyc_kl_temp_cocycle X u s0 l ta Ha tb Hb tc Hc).
Qed.

(* the 2-cocycle closure: D(2,3,4) + D(1,2,4) == D(1,3,4) + D(1,2,3).  the
   deviation bracket itself has vanishing coboundary along the
   four-temperature chain, so the symmetrized KL deviation is a pure
   2-cocycle on the temperature line. *)
Theorem cyc_kl_temp_cocycle_2up : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1)
  (t2 : Real) (Ht2 : real_lt real_zero t2)
  (t3 : Real) (Ht3 : real_lt real_zero t3)
  (t4 : Real) (Ht4 : real_lt real_zero t4),
  real_eq
    (real_plus (cyc_dev X u s0 l t2 Ht2 t3 Ht3 t4 Ht4)
               (cyc_dev X u s0 l t1 Ht1 t2 Ht2 t4 Ht4))
    (real_plus (cyc_dev X u s0 l t1 Ht1 t3 Ht3 t4 Ht4)
               (cyc_dev X u s0 l t1 Ht1 t2 Ht2 t3 Ht3)).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 t3 Ht3 t4 Ht4.
  assert (E234 := cyc_kl_dev_expand X u s0 l t2 Ht2 t3 Ht3 t4 Ht4).
  assert (E124 := cyc_kl_dev_expand X u s0 l t1 Ht1 t2 Ht2 t4 Ht4).
  assert (E134 := cyc_kl_dev_expand X u s0 l t1 Ht1 t3 Ht3 t4 Ht4).
  assert (E123 := cyc_kl_dev_expand X u s0 l t1 Ht1 t2 Ht2 t3 Ht3).
  apply (real_eq_trans
           (real_plus (cyc_dev X u s0 l t2 Ht2 t3 Ht3 t4 Ht4)
                      (cyc_dev X u s0 l t1 Ht1 t2 Ht2 t4 Ht4))
           (real_plus
              (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3)
                                                (real_opp (real_inv_pos t2 Ht2)))
                                    (real_plus (retm_Eexp X u s0 l t4 Ht4)
                                               (real_opp (retm_Eexp X u s0 l t3 Ht3))))
                         (real_mult (real_plus (real_inv_pos t4 Ht4)
                                               (real_opp (real_inv_pos t3 Ht3)))
                                    (real_plus (retm_Eexp X u s0 l t3 Ht3)
                                               (real_opp (retm_Eexp X u s0 l t2 Ht2)))))
              (real_plus
                 (real_mult (real_plus (real_inv_pos t2 Ht2)
                                       (real_opp (real_inv_pos t1 Ht1)))
                            (real_plus (retm_Eexp X u s0 l t4 Ht4)
                                       (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                 (real_mult (real_plus (real_inv_pos t4 Ht4)
                                       (real_opp (real_inv_pos t2 Ht2)))
                            (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                       (real_opp (retm_Eexp X u s0 l t1 Ht1))))))).
  - exact (RealSetoid.real_eq_plus_compat _ _ _ _ E234 E124).
  - apply (real_eq_trans
             (real_plus (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
            (real_plus (retm_Eexp X u s0 l t4 Ht4) (real_opp (retm_Eexp X u s0 l t3 Ht3)))) (real_mult (real_plus (real_inv_pos t4 Ht4) (real_opp (real_inv_pos t3 Ht3)))
            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))) (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
            (real_plus (retm_Eexp X u s0 l t4 Ht4) (real_opp (retm_Eexp X u s0 l t2 Ht2)))) (real_mult (real_plus (real_inv_pos t4 Ht4) (real_opp (real_inv_pos t2 Ht2)))
            (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))))
             (real_plus (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
            (real_plus (retm_Eexp X u s0 l t4 Ht4) (real_opp (retm_Eexp X u s0 l t3 Ht3)))) (real_mult (real_plus (real_inv_pos t4 Ht4) (real_opp (real_inv_pos t3 Ht3)))
            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1))))) (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2)))) (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
            (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))))).
    + cyc_alg.
    + exact (RealSetoid.real_eq_plus_compat _ _ _ _
               (real_eq_sym _ _ E134) (real_eq_sym _ _ E123)).
Qed.

(* ============================================================ *)
(* assumption-surface evidence: the five main statements print as closed
   under the global context. *)
(* ============================================================ *)
Print Assumptions cyc_kl_sym_self_zero.
Print Assumptions cyc_kl_temp_cocycle.
Print Assumptions cyc_kl_temp_cocycle_dev.
Print Assumptions cyc_kl_forward_cocycle.
Print Assumptions cyc_kl_temp_cocycle_2up.
