(* ConstructiveWorld-Set -- pointwise Q-level window bounds for the Machin
   vertex value V n := 4*arctan_partial n (1/5) - arctan_partial n (1/239).
    Mission.  Pointwise Q-level window bounds for the Machin vertex value
      V n := 4*arctan_partial n (1/5) - arctan_partial n (1/239):
      vertex_pt_lower and vertex_pt_upper over their absolute-value premises.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp, S11_TP3B5;
      Stdlib QArith (QArith/Qabs/Qround/Qminmax), ZArith, Lia, Lqa, Setoid,
      Morphisms.
    Constructivity.  Zero admitting statements; the pointwise bounds are
      QleT'-faced with strict QltT closed-term anchors discharged by direct
      computation; the linear chains close with lra over Q inside proofs
      only.

    Order no.  Route 2, work order R2-WA (Mach premise layer), step P3.

    Statement faces.  vertex_abs_le_1_5, vertex_abs_le_1_239,
      vertex_pt_lower, vertex_pt_upper -- carried by Set through the
      QleT' / QltT faces; zero Prop statement faces.

    Source routing.  Proof skeleton carried over from the route-2
      prerun probe probe2_mach_window.v with the atan_tail_bound
      consumption moved to the Set face: the Set-form
      lemma concludes in QleT', and each numeric band descends through the
      bridge QleT'_to_Qle (cross-tree signature map, group 9).  Closed-term
      anchors are strict QltT faces discharged by direct computation; the
      final linear chains close with lra over Q (Lqa imported), per the
      work-order pitfall table.

    Build.  coqc -native-compiler no -q -Q <sandbox> "" -Q <base> ""
      vertex_window.v  -- Rocq 9.3.0; the sandbox world carries the
      Set-form S01..S14 chain.

    Related registrations.  arctan_partial / atan_mag / atan_tail_bound
      from S11_TP3B5 (direct import; S11 names are not re-exported
      elsewhere); the bridges QleT'_to_Qle / QltT_to_Qlt / Qlt_to_QltT from
      S02_CauchyComplete; closed by tail bounds on the 1/5 band from index
      7 with modulus atan_mag 8 and on the 1/239 band from index 0 with
      modulus atan_mag 1 (lower), respectively from indices 6/1 with
      moduli atan_mag 7 / atan_mag 2 (upper). *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S11_TP3B5.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax ZArith.
From Stdlib Require Import Lqa.
Import PropositionConvergenceCore.
Opaque Qred.

(* ============================================================ *)
(* Section 1  Closed premise faces                                  *)
(*                                                                *)
(*   Both series arguments sit in the unit disc; the QleT' faces    *)
(*   are boolean-identity statements on closed fractions and are   *)
(*   discharged by direct computation.                              *)
(* ============================================================ *)

Lemma vertex_abs_le_1_5 : QleT' (Qabs (1#5)) 1.
Proof. reflexivity. Defined.

Lemma vertex_abs_le_1_239 : QleT' (Qabs (1#239)) 1.
Proof. reflexivity. Defined.

(* ============================================================ *)
(* Section 2  Pointwise vertex bounds                               *)
(*                                                                *)
(*   The arctan tail lemma gives two bands: the 1/5 partial sums    *)
(*   stay within atan_mag 8 of their index-7 value once n >= 7, and *)
(*   the 1/239 partial sums stay within atan_mag 1 of their index-0 *)
(*   value.  Strictness of the window comes entirely from the       *)
(*   closed-term anchors, computed exactly at the Q level; the      *)
(*   band inequalities then feed a linear chain.                    *)
(* ============================================================ *)

(* Lower bound: n >= 7 implies 49/64 < 4*S_n(1/5) - S_n(1/239). *)
Lemma vertex_pt_lower : forall n : nat, (7 <= n)%nat ->
  QltT (49#64) (4 * arctan_partial n (1#5) - arctan_partial n (1#239)).
Proof.
  intros n Hn.
  (* Set-face tail bounds: atan_tail_bound concludes in QleT'; each band
     descends to the Qle face for the numeric chain. *)
  assert (H1T : QleT' (Qabs (arctan_partial n (1#5) - arctan_partial 7 (1#5)))
                (atan_mag 8 (1#5)))
    by (apply (atan_tail_bound (1#5) 7 n vertex_abs_le_1_5 Hn)).
  pose proof (QleT'_to_Qle _ _ H1T) as H1.
  assert (Hn0 : (0 <= n)%nat) by lia.
  assert (H2T : QleT' (Qabs (arctan_partial n (1#239) - arctan_partial 0 (1#239)))
                (atan_mag 1 (1#239)))
    by (apply (atan_tail_bound (1#239) 0 n vertex_abs_le_1_239 Hn0)).
  pose proof (QleT'_to_Qle _ _ H2T) as H2.
  (* The anchor is strict on purpose: a non-strict anchor cannot imply a
     strict goal; this closed QltT face is discharged by direct
     computation of the closed fractions. *)
  assert (Hanchor : QltT (49#64) (4 * (arctan_partial 7 (1#5) - atan_mag 8 (1#5))
                              - (arctan_partial 0 (1#239) + atan_mag 1 (1#239))))
    by reflexivity.
  apply QltT_to_Qlt in Hanchor.
  (* Band one expanded on both sides: S_n(1/5) in [S_7 - mag8, S_7 + mag8]. *)
  pose proof (Qle_Qabs (arctan_partial n (1#5) - arctan_partial 7 (1#5))) as Ha1.
  pose proof (Qle_trans (arctan_partial n (1#5) - arctan_partial 7 (1#5))
              (Qabs (arctan_partial n (1#5) - arctan_partial 7 (1#5))) (atan_mag 8 (1#5)) Ha1 H1) as Ha2.
  pose proof (Qle_Qabs (- (arctan_partial n (1#5) - arctan_partial 7 (1#5)))) as Ha3.
  rewrite Qabs_opp in Ha3.
  pose proof (Qle_trans (- (arctan_partial n (1#5) - arctan_partial 7 (1#5)))
              (Qabs (arctan_partial n (1#5) - arctan_partial 7 (1#5))) (atan_mag 8 (1#5)) Ha3 H1) as Ha4.
  (* Band two expanded on both sides: S_n(1/239) in [S_0 - mag1, S_0 + mag1]. *)
  pose proof (Qle_Qabs (arctan_partial n (1#239) - arctan_partial 0 (1#239))) as Hb1.
  pose proof (Qle_trans (arctan_partial n (1#239) - arctan_partial 0 (1#239))
              (Qabs (arctan_partial n (1#239) - arctan_partial 0 (1#239))) (atan_mag 1 (1#239)) Hb1 H2) as Hb2.
  pose proof (Qle_Qabs (- (arctan_partial n (1#239) - arctan_partial 0 (1#239)))) as Hb3.
  rewrite Qabs_opp in Hb3.
  pose proof (Qle_trans (- (arctan_partial n (1#239) - arctan_partial 0 (1#239)))
              (Qabs (arctan_partial n (1#239) - arctan_partial 0 (1#239))) (atan_mag 1 (1#239)) Hb3 H2) as Hb4.
  apply Qlt_to_QltT.
  lra.
Defined.

(* Upper bound: n >= 6 implies 4*S_n(1/5) - S_n(1/239) < 157/192
   (equal to 5/6 - 1/64). *)
Lemma vertex_pt_upper : forall n : nat, (6 <= n)%nat ->
  QltT (4 * arctan_partial n (1#5) - arctan_partial n (1#239)) (157#192).
Proof.
  intros n Hn.
  assert (H1T : QleT' (Qabs (arctan_partial n (1#5) - arctan_partial 6 (1#5)))
                (atan_mag 7 (1#5)))
    by (apply (atan_tail_bound (1#5) 6 n vertex_abs_le_1_5 Hn)).
  pose proof (QleT'_to_Qle _ _ H1T) as H1.
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (H2T : QleT' (Qabs (arctan_partial n (1#239) - arctan_partial 1 (1#239)))
                (atan_mag 2 (1#239)))
    by (apply (atan_tail_bound (1#239) 1 n vertex_abs_le_1_239 Hn1)).
  pose proof (QleT'_to_Qle _ _ H2T) as H2.
  assert (Hanchor : Qlt (4 * (arctan_partial 6 (1#5) + atan_mag 7 (1#5))
                          - (arctan_partial 1 (1#239) - atan_mag 2 (1#239))) (157#192))
    by (apply QltT_to_Qlt; reflexivity).
  pose proof (Qle_Qabs (arctan_partial n (1#5) - arctan_partial 6 (1#5))) as Ha1.
  pose proof (Qle_trans (arctan_partial n (1#5) - arctan_partial 6 (1#5))
              (Qabs (arctan_partial n (1#5) - arctan_partial 6 (1#5))) (atan_mag 7 (1#5)) Ha1 H1) as Ha2.
  pose proof (Qle_Qabs (- (arctan_partial n (1#5) - arctan_partial 6 (1#5)))) as Ha3.
  rewrite Qabs_opp in Ha3.
  pose proof (Qle_trans (- (arctan_partial n (1#5) - arctan_partial 6 (1#5)))
              (Qabs (arctan_partial n (1#5) - arctan_partial 6 (1#5))) (atan_mag 7 (1#5)) Ha3 H1) as Ha4.
  pose proof (Qle_Qabs (arctan_partial n (1#239) - arctan_partial 1 (1#239))) as Hb1.
  pose proof (Qle_trans (arctan_partial n (1#239) - arctan_partial 1 (1#239))
              (Qabs (arctan_partial n (1#239) - arctan_partial 1 (1#239))) (atan_mag 2 (1#239)) Hb1 H2) as Hb2.
  pose proof (Qle_Qabs (- (arctan_partial n (1#239) - arctan_partial 1 (1#239)))) as Hb3.
  rewrite Qabs_opp in Hb3.
  pose proof (Qle_trans (- (arctan_partial n (1#239) - arctan_partial 1 (1#239)))
              (Qabs (arctan_partial n (1#239) - arctan_partial 1 (1#239))) (atan_mag 2 (1#239)) Hb3 H2) as Hb4.
  apply Qlt_to_QltT.
  lra.
Defined.
