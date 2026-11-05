(* ConstructiveWorld-Set -- Real-face instance family for the abstract differentiability layer. *)

(** * abl_diffreal_family: Real-face differentiability instances for opp, plus, affine, and power_nat.

    Mission.  Closure of the differentiability record [RealDifferentiable]
      (slope [rdf], per-epsilon Bishop-form correctness [rdf_correct]) under
      four shapes on the positive reals: negation [real_differentiable_opp],
      pointwise sum [real_differentiable_plus], affine maps
      [real_differentiable_affine], and nat powers [real_differentiable_power_nat]
      by induction on [real_r_pow]; the increment identities [drf_opp_incr_eq]
      and [drf_plus_incr_eq] carry the per-shape slope algebra.

    Dependencies.  Stdlib [QArith.QArith], [Lists.List], [Arith.Arith],
      [Setoid], [Morphisms].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal] of this development.

    References.  This development, abl_diffreal_family.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_diffreal_family.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
Import PropositionConvergenceCore.

(* ============================================================ *)
(* Helper 1 (drf_ prefix): the opp-shape increment identity.                                        *)
(*   −Fh − (−Fx + (−df)·h) == −(Fh − (Fx + df·h))                              *)
(*   both sides normalize to the canonical form -Fh + (Fx + df·h); opp_plus/opp_opp/opp_mult_r rewiring *)
(* ============================================================ *)
Lemma drf_opp_incr_eq : forall (Fh Fx df h : Real),
  real_eq (real_plus (real_opp Fh)
                     (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h))))
          (real_opp (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))).
Proof.
  intros Fh Fx df h.
  apply (real_eq_trans
           (real_plus (real_opp Fh)
                      (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h))))
           (real_plus (real_opp Fh) (real_plus Fx (real_mult df h)))
           (real_opp (real_plus Fh (real_opp (real_plus Fx (real_mult df h)))))).
  - (* LHS == canonical form: opp(-Fx + -df·h) == Fx + df·h *)
    apply (RealSetoid.real_eq_plus_compat (real_opp Fh)
             (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h)))
             (real_opp Fh) (real_plus Fx (real_mult df h))).
    + apply real_eq_refl.
    + apply (real_eq_trans
               (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h)))
               (real_plus (real_opp (real_opp Fx)) (real_opp (real_mult (real_opp df) h)))
               (real_plus Fx (real_mult df h))).
      * apply (real_opp_plus (real_opp Fx) (real_mult (real_opp df) h)).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_opp (real_opp Fx)) (real_opp (real_mult (real_opp df) h))
                 Fx (real_mult df h)).
        -- apply (real_opp_opp Fx).
        -- apply (real_eq_trans
                    (real_opp (real_mult (real_opp df) h))
                    (real_opp (real_opp (real_mult df h)))
                    (real_mult df h)).
           ++ apply (RealSetoid.real_eq_opp_compat
                       (real_mult (real_opp df) h) (real_opp (real_mult df h))).
              ** apply real_eq_sym.
                 apply (real_opp_mult_r df h).
           ++ apply (real_opp_opp (real_mult df h)).
  - (* canonical form == RHS: split the outer opp by opp_plus, then recombine by opp_opp *)
    apply (real_eq_trans
             (real_plus (real_opp Fh) (real_plus Fx (real_mult df h)))
             (real_plus (real_opp Fh) (real_opp (real_opp (real_plus Fx (real_mult df h)))))
             (real_opp (real_plus Fh (real_opp (real_plus Fx (real_mult df h)))))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_opp Fh) (real_plus Fx (real_mult df h))
               (real_opp Fh) (real_opp (real_opp (real_plus Fx (real_mult df h))))).
      * apply real_eq_refl.
      * apply real_eq_sym.
        apply (real_opp_opp (real_plus Fx (real_mult df h))).
    + (* M == RHS: real_opp_plus read backwards, since RHS == opp Fh + opp(opp X) is exactly M *)
      apply real_eq_sym.
      apply (real_opp_plus Fh (real_opp (real_plus Fx (real_mult df h)))).
Qed.

(* ============================================================ *)
(* Helper 2 (drf_ prefix): the plus-shape increment identity.                                       *)
(*   (Fh+Gh) − ((Fx+Gx) + (df+dg)·h) == (Fh−(Fx+df·h)) + (Gh−(Gx+dg·h))        *)
(*   distrib_r rewiring, real_plus_swap rearrangement, opp_plus splitting, swap recombination       *)
(* ============================================================ *)
Lemma drf_plus_incr_eq : forall (Fh Gh Fx Gx df dg h : Real),
  real_eq (real_plus (real_plus Fh Gh)
                     (real_opp (real_plus (real_plus Fx Gx)
                                          (real_mult (real_plus df dg) h))))
          (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))
                     (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))).
Proof.
  intros Fh Gh Fx Gx df dg h.
  (* chain: D0 -(distrib_r)-> M0 -(swap)-> M0' -(opp_plus)-> M1 -(swap)-> T *)
  apply (real_eq_trans
           (real_plus (real_plus Fh Gh)
                      (real_opp (real_plus (real_plus Fx Gx)
                                           (real_mult (real_plus df dg) h))))
           (real_plus (real_plus Fh Gh)
                      (real_plus (real_opp (real_plus Fx (real_mult df h)))
                                 (real_opp (real_plus Gx (real_mult dg h)))))
           (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))
                      (real_plus Gh (real_opp (real_plus Gx (real_mult dg h)))))).
  - (* D0 == M1: through the two intermediate forms M0 and M0' *)
    apply (real_eq_trans
             (real_plus (real_plus Fh Gh)
                        (real_opp (real_plus (real_plus Fx Gx)
                                             (real_mult (real_plus df dg) h))))
             (real_plus (real_plus Fh Gh)
                        (real_opp (real_plus (real_plus Fx Gx)
                                             (real_plus (real_mult df h) (real_mult dg h)))))
             (real_plus (real_plus Fh Gh)
                        (real_plus (real_opp (real_plus Fx (real_mult df h)))
                                   (real_opp (real_plus Gx (real_mult dg h)))))).
    + (* D0 == M0: (df+dg)·h == df·h + dg·h, distrib_r read backwards, inside the opp *)
      apply (RealSetoid.real_eq_plus_compat (real_plus Fh Gh)
               (real_opp (real_plus (real_plus Fx Gx)
                                    (real_mult (real_plus df dg) h)))
               (real_plus Fh Gh)
               (real_opp (real_plus (real_plus Fx Gx)
                                    (real_plus (real_mult df h) (real_mult dg h))))).
      * apply real_eq_refl.
      * apply (RealSetoid.real_eq_opp_compat
                 (real_plus (real_plus Fx Gx) (real_mult (real_plus df dg) h))
                 (real_plus (real_plus Fx Gx)
                            (real_plus (real_mult df h) (real_mult dg h)))).
        apply (RealSetoid.real_eq_plus_compat (real_plus Fx Gx)
                 (real_mult (real_plus df dg) h)
                 (real_plus Fx Gx)
                 (real_plus (real_mult df h) (real_mult dg h))).
        -- apply real_eq_refl.
        -- apply real_eq_sym.
           apply (real_distrib_r df dg h).
    + (* M0 == M1: swap rearrangement inside the opp, then opp_plus splitting *)
      apply (real_eq_trans
               (real_plus (real_plus Fh Gh)
                          (real_opp (real_plus (real_plus Fx Gx)
                                               (real_plus (real_mult df h) (real_mult dg h)))))
               (real_plus (real_plus Fh Gh)
                          (real_opp (real_plus (real_plus Fx (real_mult df h))
                                               (real_plus Gx (real_mult dg h)))))
               (real_plus (real_plus Fh Gh)
                          (real_plus (real_opp (real_plus Fx (real_mult df h)))
                                     (real_opp (real_plus Gx (real_mult dg h)))))).
      * apply (RealSetoid.real_eq_plus_compat (real_plus Fh Gh)
                 (real_opp (real_plus (real_plus Fx Gx)
                                      (real_plus (real_mult df h) (real_mult dg h))))
                 (real_plus Fh Gh)
                 (real_opp (real_plus (real_plus Fx (real_mult df h))
                                      (real_plus Gx (real_mult dg h))))).
        -- apply real_eq_refl.
        -- apply (RealSetoid.real_eq_opp_compat
                    (real_plus (real_plus Fx Gx)
                               (real_plus (real_mult df h) (real_mult dg h)))
                    (real_plus (real_plus Fx (real_mult df h))
                               (real_plus Gx (real_mult dg h)))).
           apply (real_plus_swap Fx Gx (real_mult df h) (real_mult dg h)).
      * apply (RealSetoid.real_eq_plus_compat (real_plus Fh Gh)
                 (real_opp (real_plus (real_plus Fx (real_mult df h))
                                      (real_plus Gx (real_mult dg h))))
                 (real_plus Fh Gh)
                 (real_plus (real_opp (real_plus Fx (real_mult df h)))
                            (real_opp (real_plus Gx (real_mult dg h))))).
        -- apply real_eq_refl.
        -- apply (real_opp_plus (real_plus Fx (real_mult df h))
                                (real_plus Gx (real_mult dg h))).
  - (* M1 == T: the outer real_plus_swap recombination *)
    apply (real_plus_swap Fh Gh (real_opp (real_plus Fx (real_mult df h)))
                             (real_opp (real_plus Gx (real_mult dg h)))).
Qed.

(* ============================================================ *)
(* Main lemma 1: the opp shape. The slope is df := −rdf f, and the eps budget passes through unchanged      *)
(* ============================================================ *)
Lemma real_differentiable_opp : forall (f : forall x : Real, real_lt real_zero x -> Real)
  (Hf : RealDifferentiable f),
  RealDifferentiable (fun x Hx => real_opp (f x Hx)).
Proof.
  intros f Hf.
  exists (fun x Hx => real_opp (rdf f Hf x Hx)).
  intros x Hx eps Heps.
  destruct (rdf_correct f Hf x Hx eps Heps) as [delta_f [Hdf Hf_corr]].
  exists delta_f.
  split.
  - exact Hdf.
  - intros h Hh Hxh eps' Heps'.
    apply (real_le_trans
             (real_abs (real_plus (real_opp (f (real_plus x h) Hxh))
                                  (real_opp (real_plus (real_opp (f x Hx))
                                                       (real_mult (real_opp (rdf f Hf x Hx)) h)))))
             (real_abs (real_plus (f (real_plus x h) Hxh)
                                  (real_opp (real_plus (f x Hx)
                                                       (real_mult (rdf f Hf x Hx) h)))))
             (real_plus (real_mult eps (real_abs h)) eps')).
    + (* |E| ≤ |A|: E == −A by drf_opp_incr_eq, and |−A| == |A| by real_abs_opp *)
      apply RealSetoid.real_eq_le.
      apply (real_eq_trans
               (real_abs (real_plus (real_opp (f (real_plus x h) Hxh))
                                    (real_opp (real_plus (real_opp (f x Hx))
                                                         (real_mult (real_opp (rdf f Hf x Hx)) h)))))
               (real_abs (real_opp (real_plus (f (real_plus x h) Hxh)
                                              (real_opp (real_plus (f x Hx)
                                                                   (real_mult (rdf f Hf x Hx) h))))))
               (real_abs (real_plus (f (real_plus x h) Hxh)
                                    (real_opp (real_plus (f x Hx)
                                                         (real_mult (rdf f Hf x Hx) h)))))).
      * apply (real_abs_eq_compat
                 (real_plus (real_opp (f (real_plus x h) Hxh))
                            (real_opp (real_plus (real_opp (f x Hx))
                                                 (real_mult (real_opp (rdf f Hf x Hx)) h))))
                 (real_opp (real_plus (f (real_plus x h) Hxh)
                                      (real_opp (real_plus (f x Hx)
                                                           (real_mult (rdf f Hf x Hx) h)))))).
        apply drf_opp_incr_eq.
      * apply (real_abs_opp (real_plus (f (real_plus x h) Hxh)
                                       (real_opp (real_plus (f x Hx)
                                                            (real_mult (rdf f Hf x Hx) h))))).
    + (* |A| ≤ eps|h| + eps': rdf_correct applies directly, the eps budget passes without splitting *)
      exact (Hf_corr h Hh Hxh eps' Heps').
Qed.

(* ============================================================ *)
(* Main lemma 2: the plus shape. The slope is df+dg and delta := min δf δg; the eps budget *)
(*          splits into halves and quarters, the same plan as the S09 minus lemma; the identity D == A+B is simpler:    *)
(*          the minus shape threads an opp recombination, the plus shape is a pure swap rearrangement)                       *)
(* ============================================================ *)
Lemma real_differentiable_plus : forall (f g : forall x : Real, real_lt real_zero x -> Real)
  (Hf : RealDifferentiable f) (Hg : RealDifferentiable g),
  RealDifferentiable (fun x Hx => real_plus (f x Hx) (g x Hx)).
Proof.
  intros f g Hf Hg.
  exists (fun (x : Real) (Hx : real_lt real_zero x) =>
            real_plus (rdf f Hf x Hx) (rdf g Hg x Hx)).
  intros x Hx eps Heps.
  set (half := real_inv_pos (real_plus real_one real_one) real_two_pos_local).
  set (quarter := real_mult half half).
  set (eps_half := real_mult half eps).
  assert (Hhalf : real_lt real_zero half).
  { unfold half.
    apply (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local). }
  assert (Hquarter : real_lt real_zero quarter).
  { unfold quarter.
    apply real_mult_positive; [exact Hhalf | exact Hhalf]. }
  assert (Heps_half : real_lt real_zero eps_half).
  { unfold eps_half.
    apply real_mult_positive; [exact Hhalf | exact Heps]. }
  destruct (rdf_correct f Hf x Hx eps_half Heps_half) as [delta_f [Hdf Hf_corr]].
  destruct (rdf_correct g Hg x Hx eps_half Heps_half) as [delta_g [Hdg Hg_corr]].
  exists (real_min delta_f delta_g).
  split.
  - apply real_min_pos; [exact Hdf | exact Hdg].
  - intros h Hh Hxh eps' Heps'.
    set (epsq := real_mult quarter eps').
    set (eps_tri := real_mult half eps').
    assert (Hepsq : real_lt real_zero epsq).
    { unfold epsq.
      apply real_mult_positive; [exact Hquarter | exact Heps']. }
    assert (Heptr : real_lt real_zero eps_tri).
    { unfold eps_tri.
      apply real_mult_positive; [exact Hhalf | exact Heps']. }
    assert (Hhdf : real_lt (real_abs h) delta_f).
    { apply (real_min_lt_l h delta_f delta_g).
      exact Hh. }
    assert (Hhdg : real_lt (real_abs h) delta_g).
    { apply (real_min_lt_r h delta_f delta_g).
      exact Hh. }
    set (A := real_plus (f (real_plus x h) Hxh)
                        (real_opp (real_plus (f x Hx) (real_mult (rdf f Hf x Hx) h)))).
    set (B := real_plus (g (real_plus x h) Hxh)
                        (real_opp (real_plus (g x Hx) (real_mult (rdf g Hg x Hx) h)))).
    assert (HA : real_le (real_abs A) (real_plus (real_mult eps_half (real_abs h)) epsq)).
    { exact (Hf_corr h Hhdf Hxh epsq Hepsq). }
    assert (HB : real_le (real_abs B) (real_plus (real_mult eps_half (real_abs h)) epsq)).
    { exact (Hg_corr h Hhdg Hxh epsq Hepsq). }
    apply (real_le_trans
             (real_abs (real_plus (real_plus (f (real_plus x h) Hxh) (g (real_plus x h) Hxh))
                                  (real_opp (real_plus (real_plus (f x Hx) (g x Hx))
                                                       (real_mult (real_plus (rdf f Hf x Hx)
                                                                             (rdf g Hg x Hx)) h)))))
             (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)
             (real_plus (real_mult eps (real_abs h)) eps')).
    + (* |D| ≤ |A|+|B|+eps_tri: |D| == |A+B| by drf_plus_incr_eq, then the eps triangle bound real_abs_triangle_le_eps *)
      apply (real_le_trans
               (real_abs (real_plus (real_plus (f (real_plus x h) Hxh) (g (real_plus x h) Hxh))
                                    (real_opp (real_plus (real_plus (f x Hx) (g x Hx))
                                                         (real_mult (real_plus (rdf f Hf x Hx)
                                                                               (rdf g Hg x Hx)) h)))))
               (real_abs (real_plus A B))
               (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)).
      * apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
                 (real_plus (real_plus (f (real_plus x h) Hxh) (g (real_plus x h) Hxh))
                            (real_opp (real_plus (real_plus (f x Hx) (g x Hx))
                                                 (real_mult (real_plus (rdf f Hf x Hx)
                                                                       (rdf g Hg x Hx)) h))))
                 (real_plus A B)).
        unfold A, B.
        apply drf_plus_incr_eq.
      * apply (real_abs_triangle_le_eps A B eps_tri).
        exact Heptr.
    + (* |A|+|B|+eps_tri ≤ eps|h| + eps': through the intermediate term M2, the same chain as the minus lemma *)
      apply (real_le_trans
               (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)
               (real_plus (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                     (real_plus (real_mult eps_half (real_abs h)) epsq)) eps_tri)
               (real_plus (real_mult eps (real_abs h)) eps')).
      * (* |A|+|B|+eps_tri ≤ M2: real_le_plus_compat on HA and HB, with eps_tri equal on both sides *)
        apply (real_le_plus_compat (real_plus (real_abs A) (real_abs B))
                                     (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                                (real_plus (real_mult eps_half (real_abs h)) epsq))
                                     eps_tri eps_tri).
        -- apply (real_le_plus_compat (real_abs A)
                                        (real_plus (real_mult eps_half (real_abs h)) epsq)
                                        (real_abs B)
                                        (real_plus (real_mult eps_half (real_abs h)) epsq)).
           ++ exact HA.
           ++ exact HB.
        -- apply real_le_refl.
      * (* M2 == eps|h| + eps': an algebraic chain of rearrangement and half merges, as in the minus lemma *)
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans
                 (real_plus (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                       (real_plus (real_mult eps_half (real_abs h)) epsq)) eps_tri)
                 (real_plus (real_mult eps (real_abs h)) (real_plus (real_plus epsq epsq) eps_tri))
                 (real_plus (real_mult eps (real_abs h)) eps')).
        -- (* rearrangement with the A+C merge: ((A+B)+(C+D))+E == eps|h| + ((B+D)+E) *)
          apply (real_eq_trans _
                   (real_plus (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq)) eps_tri)
                   _).
          ++ (* ((A+B)+(C+D))+E == (eps|h|+(B+D))+E: real_plus_swap, then the A+C merge *)
            apply (RealSetoid.real_eq_plus_compat
                     (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                (real_plus (real_mult eps_half (real_abs h)) epsq))
                     eps_tri
                     (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq))
                     eps_tri).
            ** (* (A+B)+(C+D) == eps|h|+(B+D): real_plus_swap first, then A+C == eps|h| *)
              apply (real_eq_trans
                       (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                  (real_plus (real_mult eps_half (real_abs h)) epsq))
                       (real_plus (real_plus (real_mult eps_half (real_abs h))
                                             (real_mult eps_half (real_abs h)))
                                  (real_plus epsq epsq))
                       (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq))).
              --- apply (real_plus_swap (real_mult eps_half (real_abs h)) epsq
                                          (real_mult eps_half (real_abs h)) epsq).
              --- apply (RealSetoid.real_eq_plus_compat
                           (real_plus (real_mult eps_half (real_abs h))
                                      (real_mult eps_half (real_abs h)))
                           (real_plus epsq epsq)
                           (real_mult eps (real_abs h))
                           (real_plus epsq epsq)).
              *** (* eps_half|h| + eps_half|h| == eps|h|: a real_mult_assoc rewiring, then real_half_plus_half *)
                apply (real_eq_trans
                         (real_plus (real_mult eps_half (real_abs h))
                                    (real_mult eps_half (real_abs h)))
                         (real_plus (real_mult half (real_mult eps (real_abs h)))
                                    (real_mult half (real_mult eps (real_abs h))))
                         (real_mult eps (real_abs h))).
                +++ apply (RealSetoid.real_eq_plus_compat
                             (real_mult eps_half (real_abs h)) (real_mult eps_half (real_abs h))
                             (real_mult half (real_mult eps (real_abs h)))
                             (real_mult half (real_mult eps (real_abs h)))).
                **** unfold eps_half.
                apply real_eq_sym.
                apply (real_mult_assoc half eps (real_abs h)).
                **** unfold eps_half.
                apply real_eq_sym.
                apply (real_mult_assoc half eps (real_abs h)).
                +++ apply (real_half_plus_half (real_mult eps (real_abs h))).
              *** apply real_eq_refl.
            ** apply real_eq_refl.
          ++ apply real_eq_sym.
            apply (real_plus_assoc (real_mult eps (real_abs h)) (real_plus epsq epsq) eps_tri).
        -- (* eps|h| + ((epsq+epsq)+eps_tri) == eps|h| + eps': the remaining sum B+D+E == eps' *)
          apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))
                   (real_plus (real_plus epsq epsq) eps_tri)
                   (real_mult eps (real_abs h))
                   eps').
          ++ apply real_eq_refl.
          ++ (* (epsq+epsq)+eps_tri == eps': quarter+quarter == half and half+half == 1 *)
            apply (real_eq_trans (real_plus (real_plus epsq epsq) eps_tri)
                                   (real_plus (real_mult half eps') (real_mult half eps'))
                                   eps').
            ** (* (epsq+epsq)+eps_tri == half·eps' + half·eps': the quarter merge *)
              apply (real_eq_trans (real_plus (real_plus epsq epsq) eps_tri)
                                     (real_plus (real_mult (real_plus quarter quarter) eps')
                                                (real_mult half eps'))
                                     (real_plus (real_mult half eps') (real_mult half eps'))).
              --- unfold epsq, eps_tri.
                apply (RealSetoid.real_eq_plus_compat
                         (real_plus (real_mult quarter eps') (real_mult quarter eps'))
                         (real_mult half eps')
                         (real_mult (real_plus quarter quarter) eps')
                         (real_mult half eps')).
                +++ apply (real_distrib_r quarter quarter eps').
                +++ apply real_eq_refl.
              --- apply (RealSetoid.real_eq_plus_compat
                           (real_mult (real_plus quarter quarter) eps') (real_mult half eps')
                           (real_mult half eps') (real_mult half eps')).
                +++ apply (RealSetoid.real_eq_mult_compat (real_plus quarter quarter) eps' half eps'
                             (real_half_plus_half half) (real_eq_refl _)).
                +++ apply real_eq_refl.
            ** apply (real_half_plus_half eps').
Qed.

(* ============================================================ *)
(* Main lemma 3: the affine shape, assembled: affine x = a·x + b builds on the const/mult/id/plus   *)
(*          instances; the closing exact rides the beta definitional conversion,     *)
(*          and the plus leg is the real_differentiable_plus instance of main lemma 2)              *)
(* ============================================================ *)
Lemma real_differentiable_affine : forall (a b : Real),
  RealDifferentiable (fun (x : Real) (Hx : real_lt real_zero x) =>
                        real_plus (real_mult a x) b).
Proof.
  intros a b.
  exact (real_differentiable_plus
           (fun (x : Real) (_ : real_lt real_zero x) => real_mult a x)
           (fun (x : Real) (_ : real_lt real_zero x) => b)
           (real_differentiable_mult
              (fun (x : Real) (_ : real_lt real_zero x) => a)
              (fun (x : Real) (_ : real_lt real_zero x) => x)
              (real_differentiable_const a) real_differentiable_id)
           (real_differentiable_const b)).
Qed.

(* ============================================================ *)
(* Main lemma 4: the power_nat shape, by assembly induction: real_r_pow 0 ≡ 1 (const instance),                *)
(*          real_r_pow (S m) ≡ x·real_r_pow m (mult of the identity instance with IH); the slope comes from the mult  *)
(*          instance itself; no explicit Z.of_nat→Q coefficient conversion is needed)          *)
(* ============================================================ *)
Lemma real_differentiable_power_nat : forall (n : nat),
  RealDifferentiable (fun (x : Real) (Hx : real_lt real_zero x) => real_r_pow x n).
Proof.
  intros n.
  induction n as [| m IHm].
  - (* n = 0: real_r_pow x 0 ≡ real_one by the iota reduction of its S09 definition; the const instance gives it *)
    exact (real_differentiable_const real_one).
  - (* n = S m: real_r_pow x (S m) ≡ real_mult x (real_r_pow x m) by iota, *)
    (* so mult(identity, IHm) assembles the step, closed by beta and fix iota *)
    exact (real_differentiable_mult
             (fun (x : Real) (_ : real_lt real_zero x) => x)
             (fun (x : Real) (_ : real_lt real_zero x) => real_r_pow x m)
             real_differentiable_id IHm).
Qed.

(* ============ assumption audit ============ *)
Print Assumptions real_differentiable_opp.
Print Assumptions real_differentiable_plus.
Print Assumptions real_differentiable_affine.
Print Assumptions real_differentiable_power_nat.
