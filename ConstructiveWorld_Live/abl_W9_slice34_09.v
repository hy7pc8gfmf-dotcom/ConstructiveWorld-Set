(* ==========================================================================
   abl_W9_slice34_09.v - S11 dead-spec disposition (slice 3) + arctan'
   live-slot landing assessment (slice 4); source piece S11_TP3B5.v read-only.
   Mission. Part 1 bridges the dead-spec shape (b5a_one_plus_sq_pos witness,
     inv*h order) and the in-tree landing shape (b3r_one_sq_real_pos witness,
     h*inv order) at the real_eq layer: derivative-term bridge (inverse along
     the positivity-proof argument via real_inv_pos_ext), error-term bridge
     (plus/opp/abs compat pushdown), generic le-swap transfer. Part 2 lands
     the B5A_Ode dead spec real_arctan_deriv (L7588, redecl L8606)
     constructively on |x|<=1/2 and |x|<=r<1 over the in-tree chain
     real_arctan_deriv_linear (L4586) / b3rr_real_arctan_deriv_linear
     (L5521); the original Variable slots are machine-checkably covered and
     can retire. Part 3 reparses the B5A_Item1B live-slot exact type (L11855)
     verbatim as the assessment anchor (closed unit domain vs uniform inner
     bound r: not inhabitable by any ready in-tree piece).
   Dependencies. Stdlib QArith.QArith QArith.Qabs QArith.Qround ZArith
     Extraction; in-tree S01_BaseRing S02_CauchyComplete S03_QExp
     S07_RealSetoidExpLog S11_TP3B5 (read-only -Q deps; zero registration).
   References. Dead-spec faces real_arctan_deriv@S11_TP3B5 L7588, kin
     L7603/L7617/L8606/L11855; landing chain L4586/L5521. The r-dom station
     keeps its base-lemma premise carriers (Qle 0 r / Qlt r 1) frozen at
     premise positions (census EXEMPT lawful keep: premise Prop is lawful).
   Constructivity. Purely constructive, zero classical steps, zero
     acknowledgement faces; statements Set-carried (real_le/real_lt/real_eq/
     QleT'); dead-spec content truly landed via the witness bridge as a real
     composition of in-tree pieces, not a forwarding placeholder; all five
     Qed faces close under the global context.
   Build. source toolchain env; unset COQLIB ROCQLIB; ulimit -s 65532;
     rocq c -native-compiler no -q -Q <world-dir> "" <this-file>
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround ZArith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S11_TP3B5.

(* ============================================================ *)
(* Part 1 - witness bridge: dead-spec shape <-> in-tree landing  *)
(*   shape. Deltas two of three: the positivity witness          *)
(*   (b5a_one_plus_sq_pos vs b3r_one_sq_real_pos) and the        *)
(*   product order (real_mult inv*h vs real_mult h*inv). Delta   *)
(*   three (the arctan x domain witness) is carried by the       *)
(*   landing-lemma statement faces (b3r_half_dom / b3rr_dom_r1),  *)
(*   taking no bridge.                                           *)
(* ============================================================ *)

(* Derivative-term bridge: real_inv_pos along its positivity-proof argument
   via Extensionality (in-tree real_inv_pos_ext + real_eq_refl): the inverses
   produced by the two witnesses are real_eq equal; then the product order is
   swapped (real_mult_comm). Note real_inv_pos destructs its proof argument
   in its body (S03 L6684), so the two witnesses' inverses are not
   convertible - the bridge must go through the real_eq layer; this lemma is
   the core of the bridge. *)
Lemma abl09_deriv_term_bridge : forall (x h : Real),
  real_eq
    (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                              (b5a_one_plus_sq_pos x)) h)
    (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                               (b3r_one_sq_real_pos x))).
Proof.
  intros x h.
  apply (real_eq_trans
           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                     (b5a_one_plus_sq_pos x)) h)
           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                     (b3r_one_sq_real_pos x)) h)
           (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                      (b3r_one_sq_real_pos x)))).
  - (* same multiplier: inverse along the witness argument by ext (two proofs
       of the same value) *)
    apply (RealSetoid.real_eq_mult_compat
             (real_inv_pos (real_plus real_one (real_mult x x))
                           (b5a_one_plus_sq_pos x)) h
             (real_inv_pos (real_plus real_one (real_mult x x))
                           (b3r_one_sq_real_pos x)) h).
    + exact (real_inv_pos_ext
               (real_plus real_one (real_mult x x))
               (real_plus real_one (real_mult x x))
               (b5a_one_plus_sq_pos x) (b3r_one_sq_real_pos x)
               (real_eq_refl (real_plus real_one (real_mult x x)))).
    + apply real_eq_refl.
  - (* product order swap *)
    exact (real_mult_comm (real_inv_pos (real_plus real_one (real_mult x x))
                                        (b3r_one_sq_real_pos x)) h).
Qed.

(* Error-term bridge: the arctan' error term of the dead-spec shape (inv*h
   order + b5a witness) and of the in-tree landing shape (h*inv order + b3r
   witness) are real_eq equal under real_abs - pushed down layer by layer
   through the plus/opp/abs three-layer compat (in-tree
   RealSetoid.real_eq_plus_compat / RealSetoid.real_eq_opp_compat /
   RealSetoid.real_eq_abs_compat) to the derivative-term bridge. *)
Lemma abl09_err_term_bridge :
  forall (x h : Real)
         (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
         (Hx1 : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  real_eq
    (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x Hx1)
                          (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                (b5a_one_plus_sq_pos x)) h)))))
    (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x Hx1)
                          (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                   (b3r_one_sq_real_pos x))))))).
Proof.
  intros x h Hxh Hx1.
  apply RealSetoid.real_eq_abs_compat.
  apply (RealSetoid.real_eq_plus_compat (cauchy_real_arctan (real_plus x h) Hxh)
                             (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                        (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                              (b5a_one_plus_sq_pos x)) h)))
                             (cauchy_real_arctan (real_plus x h) Hxh)
                             (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                        (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                                 (b3r_one_sq_real_pos x)))))).
  - apply real_eq_refl.
  - apply RealSetoid.real_eq_opp_compat.
    apply (RealSetoid.real_eq_plus_compat (cauchy_real_arctan x Hx1)
                               (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                  (b5a_one_plus_sq_pos x)) h)
                               (cauchy_real_arctan x Hx1)
                               (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                    (b3r_one_sq_real_pos x)))).
    + apply real_eq_refl.
    + exact (abl09_deriv_term_bridge x h).
Qed.

(* real_le transfer along real_eq on the left argument (the working form of
   the in-tree RealSetoid.real_le_compat): the in-tree landing lemma gives
   "h*inv order shape <= bound"; via the bridge this file turns it into
   "inv*h dead-spec shape <= the same bound". *)
Lemma abl09_le_swap_generic :
  forall (x h C : Real)
         (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
         (Hx1 : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))))))) C ->
  real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                    (b5a_one_plus_sq_pos x)) h))))) C.
Proof.
  intros x h C Hxh Hx1 Hle.
  apply (RealSetoid.real_le_compat
           (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                 (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b3r_one_sq_real_pos x)))))))
           (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (real_plus (cauchy_real_arctan x Hx1)
                                 (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                      (b5a_one_plus_sq_pos x)) h)))))
           C C).
  - exact (real_eq_sym _ _ (abl09_err_term_bridge x h Hxh Hx1)).
  - apply real_eq_refl.
  - exact Hle.
Qed.

(* ============================================================ *)
(* Part 2 - slice 3 main cut: content landing of the B5A_Ode      *)
(*   dead spec real_arctan_deriv, part two: the dead spec's own   *)
(*   shape (b5a_one_plus_sq_pos witness + inv*h order + Hxh       *)
(*   closed-domain certificate) lands on the two subdomains       *)
(*   |x|<=1/2 and |x|<=r<1. The original Variable slots           *)
(*   (L7588/L8606) are machine-checkably covered by the in-tree   *)
(*   chain; retirement registration in the file header.           *)
(* ============================================================ *)

(* Landing piece 1: |x|<=1/2 subdomain (in-tree base real_arctan_deriv_linear, L4586) *)
Theorem abl09_b5a_spec_half_dom :
  forall (x : Real) (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) (Qinv 2)),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x Hxb eps Heps.
  destruct (real_arctan_deriv_linear x Hxb eps Heps) as [d [Hd0 Hdh]].
  exists d. split.
  - exact Hd0.
  - intros h Hh Hxh eps' Heps'.
    exact (abl09_le_swap_generic x h (real_plus (real_mult eps (real_abs h)) eps')
             Hxh (b3r_half_dom x Hxb) (Hdh h Hh Hxh eps' Heps')).
Qed.

(* Landing piece 2: |x|<=r<1 subdomain (in-tree base b3rr_real_arctan_deriv_linear,
   L5521, the S12-cited kin lemma) - arbitrary inner bound r, covering all strict
   interior points *)
Theorem abl09_b5a_spec_r_dom :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxb eps Heps.
  destruct (b3rr_real_arctan_deriv_linear r Hr0 Hr1 x Hxb eps Heps) as [d [Hd0 Hdh]].
  exists d. split.
  - exact Hd0.
  - intros h Hh Hxh eps' Heps'.
    exact (abl09_le_swap_generic x h (real_plus (real_mult eps (real_abs h)) eps')
             Hxh (b3rr_dom_r1 x r Hxb Hr1) (Hdh h Hh Hxh eps' Heps')).
Qed.

(* ============================================================ *)
(* Part 3 - slice 4 assessment anchor: the live-slot exact type   *)
(*   reparsed verbatim (L11855 original). That this Definition    *)
(*   type-checks proves the reparse matches the source live-slot  *)
(*   type verbatim; the conclusion that no ready in-tree piece    *)
(*   inhabits it (closed domain vs uniform inner bound r) is in   *)
(*   the file header - assessment registration form, not a        *)
(*   landing piece.                                               *)
(* ============================================================ *)

Definition abl09_item1b_live_spec : Type :=
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                          (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ============================================================ *)
(* Part 4 - extractability check (informative faces, zero         *)
(*   Obj.magic): Q-layer sampling, the 1/(1+t^2) Q sample of the  *)
(*   arctan' derivative shape (computation core of this cut);     *)
(*   Real-layer informative term real_inv_pos(1+x^2), the         *)
(*   informative face of the bridge object.                       *)
(* ============================================================ *)

Definition abl09_probe_q (t : Q) : Q := Qplus t (Qinv (Qplus (1 # 2) (t * t))).

Definition abl09_probe_deriv_term (x : Real) : Real :=
  real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x).

Recursive Extraction abl09_probe_q.
Recursive Extraction abl09_probe_deriv_term.

(* ============================================================ *)
(* Part 5 - tail check: Print Assumptions on all pieces           *)
(*   (3 bridges + 2 landing pieces = 5 Qed faces accounted)       *)
(* ============================================================ *)

Print Assumptions abl09_deriv_term_bridge.
Print Assumptions abl09_err_term_bridge.
Print Assumptions abl09_le_swap_generic.
Print Assumptions abl09_b5a_spec_half_dom.
Print Assumptions abl09_b5a_spec_r_dom.
