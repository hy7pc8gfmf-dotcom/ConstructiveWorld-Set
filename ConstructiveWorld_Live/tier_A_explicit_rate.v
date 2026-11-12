(* ConstructiveWorld-Set -- Tier A: the explicit approximation-rate theorem
   for the Machin vertex real (route 2, W-E certification).
    Mission.  Work order R2-WD-WE section 4 (W-E seat): the synthesized budget
      N_total_of_eps at the scaled eps/6 dominates every source modulus, and
      past it any two vertex partial sums agree within eps.  Statements:
      tier_A_eps6_pos, tier_A_scale_lt (Prop premise-position bridges, Qed per
      the erasure-face exemption); tier_A_explicit_rate, tier_A_vertex_instance
      (Set sigT conclusions, Defined).
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S10_KVQuantTrig,
      S11_TP3B5, mach_fold_q, N_total_assembly, window_cos_assembly; Stdlib
      QArith.QArith, QArith.Qabs, Arith.Arith, Lqa.  Source routing: the
      vertex face collapses projT1 (mach_pi_quarter) onto the Machin
      combination via the transparent-Real change step; the w-side
      certificates enter in premise form per the work order's W-C
      weak-caliber provision (R2-WC section 8 fallback), the vertex
      cos-diagonal certificate staying an explicit premise;
      tier_A_vertex_instance discharges the two window premises with the W-A
      certificates vertex_window_lower / vertex_window_upper.
    References.  N_total_of_eps / N_total_sound (W-D); vertex_window_lower /
      vertex_window_upper (W-A); mach_pi_quarter (mach_fold_q);
      arctan_partial (S11_TP3B5); QltT bridges (S02_CauchyComplete); Stdlib
      Qabs_Qlt_condition / Qopp_lt_compat / Qmult_lt_compat_r / Qmult_1_l.
    Constructivity.  Zero axioms, zero admitted goals; the main theorem ends
      in Defined (pure existT assembly over the W-D synthesis bundle).
      Measured band-part growth (4d): N = 8, 64, 512 at eps = 1/8, 1/64,
      1/512 unscaled, i.e. 48, 384, 3072 at the eps/6 budget scale (linear in
      1/eps; witness evaluation milliseconds; tables in the receipt).
    Build.  coqc -native-compiler no -q -Q <sandbox> "" -Q <base_local> ""
      tier_A_explicit_rate.v -- Rocq 9.3.0, under the cpu-guard wrapper. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import mach_fold_q.
Require Import N_total_assembly.
Require Import window_cos_assembly.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lqa.

(* ============================================================ *)
(* Section 1  Premise-position bookkeeping bridges               *)
(*                                                              *)
(*   Strictness bookkeeping for the scaled budget eps/6 and the *)
(*   5/6 * eps < eps closure of the vertex triangle chain.      *)
(*   Both are consumed at premise/proof positions only.         *)
(* ============================================================ *)

Lemma tier_A_eps6_pos : forall eps : Q, Qlt 0 eps -> Qlt 0 (eps / 6).
Proof.
  intros eps Heps.
  apply (Qlt_shift_div_l 0 eps 6).
  - change (Qlt 0 6). compute. reflexivity.
  - simpl. exact Heps.
Qed.

Lemma tier_A_scale_lt : forall eps : Q, Qlt 0 eps -> Qlt (5 * (eps / 6)) eps.
Proof.
  intros eps Heps.
  assert (Hr : 5 * (eps / 6) == (5#6) * eps).
  { assert (H1 : eps / 6 == eps * (1#6)) by reflexivity.
    rewrite H1. ring. }
  rewrite Hr.
  apply (Qlt_le_trans _ (1 * eps)).
  - apply (Qmult_lt_compat_r (5#6) 1 eps Heps).
    compute. reflexivity.
  - rewrite Qmult_1_l. apply Qle_refl.
Qed.

(* ============================================================ *)
(* Section 2  Tier A: vertex-side explicit approximation rate    *)
(*                                                              *)
(*   The synthesized budget N_total_of_eps at the scaled eps/6  *)
(*   dominates every source modulus; past it, any two vertex    *)
(*   partial sums 4*S_n(1/5) - S_n(1/239), S_m(1/5) - S_m(1/239)*)
(*   agree within eps.  The witness N is the W-D synthesis      *)
(*   value; the vertex face is the Cauchy rate of the vertex    *)
(*   real mach_pi_quarter, written on its projT1 face.          *)
(* ============================================================ *)

Theorem tier_A_explicit_rate :
  forall (w : Real)
    (Hw0 : real_eq (cauchy_real_cos w) real_zero)
    (Hlow : real_lt (real_const (3#2)) w)
    (Hup : real_lt w (real_const (5#3)))
    (eps : Q), Qlt 0 eps ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (m <= n)%nat ->
    QltT (Qabs (projT1 (mach_pi_quarter) n - projT1 (mach_pi_quarter) m)) eps).
Proof.
  intros w Hw0 Hlow Hup eps Heps.
  assert (Heps6 : Qlt 0 (eps / 6))
    by exact (tier_A_eps6_pos eps Heps).
  exists (N_total_of_eps w Hw0 Hlow Hup (eps / 6) Heps6).
  intros m n Hm Hn.
  destruct (N_total_sound w Hw0 Hlow Hup (eps / 6) Heps6 m n Hm Hn)
    as [c1 [c2 [c3 [c4 [c5 c6]]]]].
  pose proof (QltT_to_Qlt _ _ c1) as H1.
  pose proof (QltT_to_Qlt _ _ c2) as H2.
  pose proof (tier_A_scale_lt eps Heps) as Hsc.
  (* Two-sided band bounds: each |difference| < eps/6 face expands through
     Qle_Qabs, with the mirrored side via Qabs_opp (R3 prescription). *)
  assert (Hd5u : Qlt (arctan_partial n (1#5) - arctan_partial m (1#5)) (eps / 6)).
  { apply (Qle_lt_trans _ (Qabs (arctan_partial n (1#5) - arctan_partial m (1#5)))).
    - apply Qle_Qabs.
    - exact H1. }
  assert (Hd5l : Qlt (- (arctan_partial n (1#5) - arctan_partial m (1#5))) (eps / 6)).
  { apply (Qle_lt_trans _ (Qabs (- (arctan_partial n (1#5) - arctan_partial m (1#5))))).
    - apply Qle_Qabs.
    - rewrite Qabs_opp. exact H1. }
  assert (Hd2u : Qlt (arctan_partial n (1#239) - arctan_partial m (1#239)) (eps / 6)).
  { apply (Qle_lt_trans _ (Qabs (arctan_partial n (1#239) - arctan_partial m (1#239)))).
    - apply Qle_Qabs.
    - exact H2. }
  assert (Hd2l : Qlt (- (arctan_partial n (1#239) - arctan_partial m (1#239))) (eps / 6)).
  { apply (Qle_lt_trans _ (Qabs (- (arctan_partial n (1#239) - arctan_partial m (1#239))))).
    - apply Qle_Qabs.
    - rewrite Qabs_opp. exact H2. }
  (* Projection collapse: the vertex real's pointwise face is the Machin
     combination itself (transparent constructors, probe-2 collapse). *)
  apply Qlt_to_QltT.
  change (Qlt (Qabs ((4 * arctan_partial n (1#5) - arctan_partial n (1#239))
                     - (4 * arctan_partial m (1#5) - arctan_partial m (1#239)))) eps).
  (* Linear triangle at the eps/6 atoms, closed by the 5/6 * eps scale. *)
  assert (HXlt : Qlt ((4 * arctan_partial n (1#5) - arctan_partial n (1#239))
                      - (4 * arctan_partial m (1#5) - arctan_partial m (1#239)))
                     (5 * (eps / 6)))
    by lra.
  assert (HXge : Qle (- (5 * (eps / 6)))
                     ((4 * arctan_partial n (1#5) - arctan_partial n (1#239))
                      - (4 * arctan_partial m (1#5) - arctan_partial m (1#239))))
    by lra.
  apply (proj2 (Qabs_Qlt_condition _ _)).
  split.
  - apply (Qlt_le_trans _ (- (5 * (eps / 6)))).
    + apply (Qopp_lt_compat (5 * (eps / 6)) eps). exact Hsc.
    + exact HXge.
  - apply (Qlt_le_trans _ (5 * (eps / 6))).
    + exact HXlt.
    + apply (Qlt_le_weak _ _). exact Hsc.
Defined.

(* ============================================================ *)
(* Section 3  Vertex-occupant instance                           *)
(*                                                              *)
(*   The vertex occupant doubled, real_mult (real_const 2)      *)
(*   mach_pi_quarter, supplies its two window premises from the *)
(*   W-A real-layer certificates; the cos-diagonal certificate  *)
(*   stays explicit (honest-interface disclosure).              *)
(* ============================================================ *)

Theorem tier_A_vertex_instance : forall eps : Q, Qlt 0 eps ->
  real_eq (cauchy_real_cos (real_mult (real_const 2) mach_pi_quarter)) real_zero ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (m <= n)%nat ->
    QltT (Qabs (projT1 (mach_pi_quarter) n - projT1 (mach_pi_quarter) m)) eps).
Proof.
  intros eps Heps Hw0v.
  exact (tier_A_explicit_rate (real_mult (real_const 2) mach_pi_quarter)
           Hw0v vertex_window_lower vertex_window_upper eps Heps).
Defined.

(* Assumption-face print anchors: every statement must report
   "Closed under the global context". *)
Print Assumptions tier_A_eps6_pos.
Print Assumptions tier_A_scale_lt.
Print Assumptions tier_A_explicit_rate.
Print Assumptions tier_A_vertex_instance.
