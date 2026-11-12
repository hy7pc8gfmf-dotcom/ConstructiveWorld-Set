(* ConstructiveWorld-Set -- real-level assembly of the Machin vertex window
   2*theta' in (3/2, 5/3) and its same-window face against the cos anchors.
    Mission.  Assemble the real-level window face of the Machin vertex:
      2*theta' in (3/2, 5/3) via vertex_window_lower / vertex_window_upper,
      the sigT pair vertex_window_pair, and the same-window link
      cos_window_face / vertex_cos_same_window(_holds) to the cos anchors.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp,
      S10_KVQuantTrig, S11_TP3B5, mach_fold_q, vertex_window; Stdlib QArith
      (QArith/Qabs/Qround/Qminmax), ZArith, Lia, Lqa, Setoid, Morphisms.
    Constructivity.  Zero admitting statements; every named statement is
      carried by Set through the real_lt / sigT / QltT faces; all Real
      constructors and cauchy_real_arctan are transparent (Defined) so the
      assemblies collapse definitionally; Prop occurs at premise and
      proof-body positions only.

    Order no.  Route 2, work order R2-WA (Mach premise layer), step P4.

    Statement faces.  vertex_window_lower, vertex_window_upper,
      vertex_window_pair, cos_window_face, vertex_cos_same_window,
      vertex_cos_same_window_holds -- carried by Set through the real_lt /
      sigT / QltT faces; zero Prop statement faces.

    Source routing.  Real-level corollaries carried over from the route-2
      prerun probe probe2_mach_window.v and renamed for landing; the
      cos-window link shares the window of cos_zero_lower / cos_zero_upper
      (S10, QltT faces on cos_zero_seq n).  All Real constructors and
      cauchy_real_arctan are transparent (Defined), so each assembly proof
      collapses into a single change step onto the Q-level window face.
      The conjunction of two real_lt facts is carried by a sigT pair (the
      Set-sorted real_lt value cannot be hosted by the Prop And); the
      real_eq diagonal comparison belongs to the assembly stage, out of
      scope here.

    Build.  coqc -native-compiler no -q -Q <sandbox> "" -Q <base> ""
      window_cos_assembly.v  -- Rocq 9.3.0; requires the vertex_window.v
      pointwise bounds and the mach_fold_q transplant in the same world.

    Related registrations.  mach_pi_quarter from mach_fold_q; arctan_partial
      from S11_TP3B5; cos_zero_seq / cos_zero_lower / cos_zero_upper from
      S10_KVQuantTrig (direct import); NatLe_drop from S01_BaseRing; the
      eps = 1/32 witnesses realize the margins 49/32 - 3/2 = 1/32 and
      5/3 - 157/96 = 1/32. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import mach_fold_q.
Require Import vertex_window.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax ZArith.
From Stdlib Require Import Lqa.
Import PropositionConvergenceCore.
(* No Opaque Qred here: the cos-anchor linkage faces carry the Qdiv
   literals (3 / 2) and (5 / 3) (verbatim faces of cos_zero_lower /
   cos_zero_upper in S10); with Qred transparent these normalize to the
   canonical Qmake forms and the linear chains close with lra. *)

(* ============================================================ *)
(* Section 1  The real-level window faces                           *)
(*                                                                *)
(*   real_lt x y is a Set-sorted existential: a positive eps together *)
(*   with an index N beyond which every pointwise gap exceeds eps.   *)
(*   The witness eps = 1/32 realizes the exact margins of the Q      *)
(*   level bounds doubled: 2*49/64 - 3/2 = 1/32 and                  *)
(*   5/3 - 2*157/192 = 1/32.                                         *)
(* ============================================================ *)

(* Lower face: 3/2 < 2*theta', fed by vertex_pt_lower. *)
Lemma vertex_window_lower :
  real_lt (real_const (3#2)) (real_mult (real_const 2) mach_pi_quarter).
Proof.
  unfold real_lt.
  exists (1#32). split.
  - reflexivity.
  - exists 7%nat. intros n Hn.
    (* Projection transport is definitional (transparent constructors), so
       the pointwise goal collapses onto the Q-level window face. *)
    change (QltT (1#32)
      (2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239)) - (3#2))).
    apply Qlt_to_QltT.
    pose proof (QltT_to_Qlt _ _ (vertex_pt_lower n (NatLe_drop 7 n Hn))) as HX.
    lra.
Defined.

(* Upper face: 2*theta' < 5/3, fed by vertex_pt_upper. *)
Lemma vertex_window_upper :
  real_lt (real_mult (real_const 2) mach_pi_quarter) (real_const (5#3)).
Proof.
  unfold real_lt.
  exists (1#32). split.
  - reflexivity.
  - exists 6%nat. intros n Hn.
    change (QltT (1#32)
      ((5#3) - 2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239)))).
    apply Qlt_to_QltT.
    pose proof (QltT_to_Qlt _ _ (vertex_pt_upper n (NatLe_drop 6 n Hn))) as HX.
    lra.
Defined.

(* ============================================================ *)
(* Section 2  The window pair carrier                               *)
(*                                                                *)
(*   Both faces are Set-sorted values, so their conjunction is       *)
(*   carried by a dependent pair rather than the Prop And.           *)
(* ============================================================ *)

Definition vertex_window_pair :
  sigT (fun _ : real_lt (real_const (3#2)) (real_mult (real_const 2) mach_pi_quarter) =>
        real_lt (real_mult (real_const 2) mach_pi_quarter) (real_const (5#3))) :=
  existT _ vertex_window_lower vertex_window_upper.

(* ============================================================ *)
(* Section 3  Same-window statement face against the cos anchors    *)
(*                                                                *)
(*   The cos-zero anchors live on the same interval (S10):           *)
(*   cos_zero_lower n : QltT (3/2) (cos_zero_seq n) and              *)
(*   cos_zero_upper n : QltT (cos_zero_seq n) (5/3).  The record     *)
(*   below states that the doubled vertex value and the cos-zero     *)
(*   sequence share the window for a common index; the real_eq       *)
(*   diagonal comparison between the occupants is assembly-stage      *)
(*   scope and is not claimed here.                                  *)
(* ============================================================ *)

Definition cos_window_face (n : nat) : Set :=
  sigT (fun _ : QltT (3 / 2) (cos_zero_seq n) => QltT (cos_zero_seq n) (5 / 3)).

Definition vertex_cos_same_window (n : nat) : Set :=
  sigT (fun _ : QltT (3 / 2) (2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239))) =>
        sigT (fun _ : QltT (2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239))) (5 / 3) =>
              cos_window_face n)).

Lemma vertex_cos_same_window_holds : forall n : nat, (7 <= n)%nat ->
  vertex_cos_same_window n.
Proof.
  intros n Hn.
  assert (H6 : (6 <= n)%nat) by lia.
  assert (Hlow2 : QltT (3 / 2)
            (2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239)))).
  { apply Qlt_to_QltT.
    (* lra's reifier treats the Qdiv literal (3 / 2) as an opaque atom;
       kernel conversion (Qred transparent) closes the move to the Qmake
       face that the linear chain needs. *)
    change (Qlt (3#2) (2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239)))).
    pose proof (QltT_to_Qlt _ _ (vertex_pt_lower n Hn)) as Hlow.
    lra. }
  assert (Hup2 : QltT (2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239)))
            (5 / 3)).
  { apply Qlt_to_QltT.
    change (Qlt (2 * (4 * arctan_partial n (1#5) - arctan_partial n (1#239))) (5#3)).
    pose proof (QltT_to_Qlt _ _ (vertex_pt_upper n H6)) as Hup.
    lra. }
  exists Hlow2.
  exact (existT _ Hup2 (existT _ (cos_zero_lower n) (cos_zero_upper n))).
Defined.
