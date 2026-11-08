(* ConstructiveWorld-Set — constructive Real-layer entropy and Boltzmann distributions (constructive Set layer). *)

(** * S09_EntropyReal: Real-layer entropy and Boltzmann distributions.

    Mission.  Formalizes the Real-layer construction of entropy and the
      Boltzmann distribution: KL decomposition, the Gibbs equality,
      maximum-entropy duality, and order-preserving structure.  Main
      statement: [exp_order_embedding] (exp is order-preserving in both
      directions) — the Set-layer construction of an order-preserving
      group isomorphism (homomorphism, injection, surjection, range).

    Dependencies.  Stdlib [QArith.QArith], [List], [Bool], [Arith],
      [Setoid], [Morphisms], [Lia].  Requires [S01_BaseRing] through
      [S08_RealMainlineDPO] of this development.

    References.  This development, [CW_ConstructiveWorld_219.v], the
      baseline module in ConstructiveWorld-Main whose statement names
      are carried over here verbatim (statement-face Set-carrier
      completion); this module splits its region L46821-L53931, and the
      statement body matches that region.

    Constructivity.  All named statements live in the constructive
      [Set] layer with zero admitted statements (mechanically checked).

    Build.  [coqc -native-compiler no -q -Q . "" S09_EntropyReal.v]
      compiles cleanly (exit 0). *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
Opaque Qred.

Section EntropyDiffReal. (* ============ 0. Constant: f := fun x Hx => c, rdf := 0 ============   Error: |c − (c + 0·h)| == |opp(0·h)| == 0 ≤ eps|h| + eps'   0 ≤ eps|h| + eps': |eps·h| + eps' ≥ 0 (real_abs_nonneg_le_eps) + |eps·h| == eps|h| *)
Lemma real_differentiable_const : forall (c : Real),  RealDifferentiable (fun (x : Real) (Hx : real_lt real_zero x) => c).
Proof.
intros c.
exists (fun x Hx => real_zero).
intros x Hx eps Heps.
exists real_one.
split.
- apply real_lt_zero_one.
- intros h Hh Hxh eps' Heps'.
apply (real_le_trans      (real_abs (real_plus c (real_opp (real_plus c (real_mult real_zero h)))))      real_zero      (real_plus (real_mult eps (real_abs h)) eps')).
+ (* |c − (c + 0·h)| == 0: eq_le (opp_plus + plus_opp + comm/mult_zero + abs_zero). *)      apply RealSetoid.real_eq_le.
apply (real_eq_trans        (real_abs (real_plus c (real_opp (real_plus c (real_mult real_zero h)))))        (real_abs (real_mult real_zero h))        real_zero).
* (* |c + opp(c + z)| == |z|: the eq_le chain (z := 0·h, c + opp(c+z) == z). *)        apply (real_abs_eq_compat          (real_plus c (real_opp (real_plus c (real_mult real_zero h))))          (real_mult real_zero h)).
set (z := real_mult real_zero h).
assert (Hz0 : real_eq z real_zero).
{ unfold z.
apply (real_eq_trans (real_mult real_zero h) (real_mult h real_zero) real_zero).
- apply (real_mult_comm real_zero h).
- apply (real_mult_zero h).
}        apply (real_eq_trans (real_plus c (real_opp (real_plus c z)))                             (real_plus (real_plus c (real_opp c)) (real_opp z))                             z).
-- (* c + opp(c+z) == (c + opp c) + opp z: opp_plus + assoc. *)           apply (real_eq_trans (real_plus c (real_opp (real_plus c z)))                                (real_plus c (real_plus (real_opp c) (real_opp z)))                                (real_plus (real_plus c (real_opp c)) (real_opp z))).
++ apply (RealSetoid.real_eq_plus_compat c (real_opp (real_plus c z))                                                      c (real_plus (real_opp c) (real_opp z))).
** apply real_eq_refl.
** apply (real_opp_plus c z).
++ apply (real_plus_assoc c (real_opp c) (real_opp z)).
-- (* (c + opp c) + opp z == z: plus_opp + comm + z == 0 (Hz0). *)            apply (real_eq_trans (real_plus (real_plus c (real_opp c)) (real_opp z))                                 (real_plus real_zero (real_opp z))                                 z).
++ apply (RealSetoid.real_eq_plus_compat (real_plus c (real_opp c)) (real_opp z)                                                     real_zero (real_opp z)).
** apply (real_plus_opp c).
** apply real_eq_refl.
++ apply (real_eq_trans (real_plus real_zero (real_opp z))                                    (real_opp z)                                    z).
{ apply (real_eq_trans (real_plus real_zero (real_opp z))                                      (real_plus (real_opp z) real_zero)                                      (real_opp z)).
{ apply (real_plus_comm real_zero (real_opp z)).
}                 { apply (real_plus_zero (real_opp z)).
} }               { apply (real_eq_trans (real_opp z) (real_opp real_zero) z).
{ apply (RealSetoid.real_eq_opp_compat z real_zero).
exact Hz0.
}                 { apply (real_eq_trans (real_opp real_zero) real_zero z).
{ apply (real_opp_zero).
}                   { apply real_eq_sym.
exact Hz0.
} } }      * (* |0·h| == 0: abs_zero + mult_zero. *)        apply (real_eq_trans (real_abs (real_mult real_zero h)) (real_abs real_zero) real_zero).
-- apply (real_abs_eq_compat (real_mult real_zero h) real_zero).
apply (real_eq_trans (real_mult real_zero h) (real_mult h real_zero) real_zero).
++ apply (real_mult_comm real_zero h).
++ apply (real_mult_zero h).
-- apply (real_abs_zero_req).
+ (* 0 ≤ eps|h| + eps': |eps·h| + eps' ≥ 0 (real_abs_nonneg_le_eps). *)      apply (real_le_trans real_zero (real_plus (real_abs (real_mult eps h)) eps')                           (real_plus (real_mult eps (real_abs h)) eps')).
* apply (real_abs_nonneg_le_eps (real_mult eps h) eps').
exact Heps'.
* apply RealSetoid.real_eq_le.
apply (RealSetoid.real_eq_plus_compat (real_abs (real_mult eps h))                                              eps'                                              (real_mult eps (real_abs h))                                              eps').
-- apply (real_eq_trans (real_abs (real_mult eps h)) (real_mult (real_abs eps) (real_abs h)) (real_mult eps (real_abs h))).
++ apply (real_abs_mult_req eps h).
++ apply (RealSetoid.real_eq_mult_compat (real_abs eps) (real_abs h) eps (real_abs h)                                                      (real_abs_pos_req eps Heps) (real_eq_refl _)).
-- apply real_eq_refl.
Qed. (* ============ 1. Identity: f := fun x Hx => x, rdf := 1 ============   Error: |x+h − (x + 1·h)| == |0| == 0 (1·h == h, so opp cancels) *)
Lemma real_differentiable_id : RealDifferentiable  (fun (x : Real) (Hx : real_lt real_zero x) => x).
Proof.
exists (fun x Hx => real_one).
intros x Hx eps Heps.
exists real_one.
split.
- apply real_lt_zero_one.
- intros h Hh Hxh eps' Heps'.
apply (real_le_trans      (real_abs (real_plus (real_plus x h) (real_opp (real_plus x (real_mult real_one h)))))      real_zero      (real_plus (real_mult eps (real_abs h)) eps')).
+ (* |x+h − (x + 1·h)| == |(x+h) + opp(x+h)| == |0| == 0 *)      apply RealSetoid.real_eq_le.
apply (real_eq_trans        (real_abs (real_plus (real_plus x h) (real_opp (real_plus x (real_mult real_one h)))))        (real_abs (real_plus (real_plus x h) (real_opp (real_plus x h))))        real_zero).
* (* 1·h == h restated (abs_eq_compat + opp/plus compat). *)        apply (real_abs_eq_compat          (real_plus (real_plus x h) (real_opp (real_plus x (real_mult real_one h))))          (real_plus (real_plus x h) (real_opp (real_plus x h)))).
apply (RealSetoid.real_eq_plus_compat (real_plus x h) (real_opp (real_plus x (real_mult real_one h)))                                              (real_plus x h) (real_opp (real_plus x h))).
-- apply real_eq_refl.
-- apply (RealSetoid.real_eq_opp_compat (real_plus x (real_mult real_one h)) (real_plus x h)).
apply (RealSetoid.real_eq_plus_compat x (real_mult real_one h) x h).
++ apply real_eq_refl.
++ apply (real_eq_trans (real_mult real_one h) (real_mult h real_one) h).
** apply (real_mult_comm real_one h).
** apply (real_mult_one h).
* (* |(x+h) + opp(x+h)| == |0| == 0: plus_opp + abs_zero. *)        apply (real_eq_trans          (real_abs (real_plus (real_plus x h) (real_opp (real_plus x h))))          (real_abs real_zero)          real_zero).
-- apply (real_abs_eq_compat (real_plus (real_plus x h) (real_opp (real_plus x h))) real_zero).
apply (real_plus_opp (real_plus x h)).
-- apply (real_abs_zero_req).
+ (* 0 ≤ eps|h| + eps': as in the constant case. *)      apply (real_le_trans real_zero (real_plus (real_abs (real_mult eps h)) eps')                           (real_plus (real_mult eps (real_abs h)) eps')).
* apply (real_abs_nonneg_le_eps (real_mult eps h) eps').
exact Heps'.
* apply RealSetoid.real_eq_le.
apply (RealSetoid.real_eq_plus_compat (real_abs (real_mult eps h))                                              eps'                                              (real_mult eps (real_abs h))                                              eps').
-- apply (real_eq_trans (real_abs (real_mult eps h)) (real_mult (real_abs eps) (real_abs h)) (real_mult eps (real_abs h))).
++ apply (real_abs_mult_req eps h).
++ apply (RealSetoid.real_eq_mult_compat (real_abs eps) (real_abs h) eps (real_abs h)                                                    (real_abs_pos_req eps Heps) (real_eq_refl _)).
-- apply real_eq_refl.
Qed. (* ============ 2. Difference: f − g, rdf := rdf_f − rdf_g ============   D == A − B; |D| ≤ |A| + |B| + eps_tri (triangle, with eps_tri := eps'/2)   A and B use Hf/Hg at eps_half := half·eps and epsq := quarter·eps'   (delta does not depend on eps'; epsq/eps_tri are defined after intros eps'). *)(* Auxiliary: right distributivity (x·z + y·z == (x+y)·z, via the comm bridge + real_distrib). *)
Lemma real_distrib_r : forall x y z : Real,  real_eq (real_plus (real_mult x z) (real_mult y z)) (real_mult (real_plus x y) z).
Proof.
intros x y z.
apply real_eq_sym.
apply (real_eq_trans (real_mult (real_plus x y) z)                       (real_plus (real_mult z x) (real_mult z y))                       (real_plus (real_mult x z) (real_mult y z))).
- apply (real_eq_trans (real_mult (real_plus x y) z)                         (real_mult z (real_plus x y))                         (real_plus (real_mult z x) (real_mult z y))).
+ apply (real_mult_comm (real_plus x y) z).
+ apply (real_distrib z x y).
- apply (RealSetoid.real_eq_plus_compat (real_mult z x) (real_mult z y)                                          (real_mult x z) (real_mult y z)).
+ apply (real_mult_comm z x).
+ apply (real_mult_comm z y).
Qed. (* Auxiliary: four-term addition exchange (a+b)+(c+d) == (a+c)+(b+d)   Chain: assoc backwards + comm + assoc backwards + comm + assoc backwards *)
Lemma real_plus_swap : forall a b c d : Real,  real_eq (real_plus (real_plus a b) (real_plus c d))          (real_plus (real_plus a c) (real_plus b d)).
Proof.
intros a b c d.
apply (real_eq_trans (real_plus (real_plus a b) (real_plus c d))                       (real_plus a (real_plus (real_plus c d) b))                       (real_plus (real_plus a c) (real_plus b d))).
- apply (real_eq_trans (real_plus (real_plus a b) (real_plus c d))                         (real_plus a (real_plus b (real_plus c d)))                         (real_plus a (real_plus (real_plus c d) b))).
+ apply real_eq_sym.
apply (real_plus_assoc a b (real_plus c d)).
+ apply (RealSetoid.real_eq_plus_compat a (real_plus b (real_plus c d))                                            a (real_plus (real_plus c d) b)).
* apply real_eq_refl.
* apply (real_plus_comm b (real_plus c d)).
- apply (real_eq_trans (real_plus a (real_plus (real_plus c d) b))                         (real_plus a (real_plus c (real_plus d b)))                         (real_plus (real_plus a c) (real_plus b d))).
+ apply (RealSetoid.real_eq_plus_compat a (real_plus (real_plus c d) b)                                            a (real_plus c (real_plus d b))).
* apply real_eq_refl.
* apply real_eq_sym.
apply (real_plus_assoc c d b).
+ apply (real_eq_trans (real_plus a (real_plus c (real_plus d b)))                           (real_plus a (real_plus c (real_plus b d)))                           (real_plus (real_plus a c) (real_plus b d))).
* apply (RealSetoid.real_eq_plus_compat a (real_plus c (real_plus d b))                                              a (real_plus c (real_plus b d))).
-- apply real_eq_refl.
-- apply (RealSetoid.real_eq_plus_compat c (real_plus d b) c (real_plus b d)).
++ apply real_eq_refl.
++ apply (real_plus_comm d b).
* apply (real_plus_assoc a c (real_plus b d)).
Qed.

Lemma real_differentiable_minus : forall (f g : forall x : Real, real_lt real_zero x -> Real)  (Hf : RealDifferentiable f) (Hg : RealDifferentiable g),  RealDifferentiable (fun x Hx => real_plus (f x Hx) (real_opp (g x Hx))).
Proof.
intros f g Hf Hg.
exists (fun (x : Real) (Hx : real_lt real_zero x) =>            real_plus (rdf f Hf x Hx) (real_opp (rdf g Hg x Hx))).
intros x Hx eps Heps.
set (half := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
set (quarter := real_mult half half).
set (eps_half := real_mult half eps).
assert (Hhalf : real_lt real_zero half).
{ unfold half.
apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
}  assert (Heps_half : real_lt real_zero eps_half).
{ unfold eps_half.
apply real_mult_positive; [exact Hhalf | exact Heps].
}  destruct (rdf_correct f Hf x Hx eps_half Heps_half) as [delta_f [Hdf Hf_corr]].
destruct (rdf_correct g Hg x Hx eps_half Heps_half) as [delta_g [Hdg Hg_corr]].
exists (real_min delta_f delta_g).
split.
- apply real_min_pos; [exact Hdf | exact Hdg].
- intros h Hh Hxh eps' Heps'.
set (epsq := real_mult quarter eps').
set (eps_tri := real_mult half eps').
assert (Hepsq : real_lt real_zero epsq).
{ unfold epsq.
apply real_mult_positive.
- unfold quarter.
apply real_mult_positive; [exact Hhalf | exact Hhalf].
- exact Heps'.
}    assert (Heptr : real_lt real_zero eps_tri).
{ unfold eps_tri.
apply real_mult_positive; [exact Hhalf | exact Heps'].
}    assert (Hhdf : real_lt (real_abs h) delta_f).
{ apply (real_min_lt_l h delta_f delta_g).
exact Hh.
}    assert (Hhdg : real_lt (real_abs h) delta_g).
{ apply (real_min_lt_r h delta_f delta_g).
exact Hh.
}    set (A := real_plus (f (real_plus x h) Hxh)                        (real_opp (real_plus (f x Hx) (real_mult (rdf f Hf x Hx) h)))).
set (B := real_plus (g (real_plus x h) Hxh)                        (real_opp (real_plus (g x Hx) (real_mult (rdf g Hg x Hx) h)))).
assert (HA : real_le (real_abs A) (real_plus (real_mult eps_half (real_abs h)) epsq)).
{ unfold A.
exact (Hf_corr h Hhdf Hxh epsq Hepsq).
}    assert (HB : real_le (real_abs B) (real_plus (real_mult eps_half (real_abs h)) epsq)).
{ unfold B.
exact (Hg_corr h Hhdg Hxh epsq Hepsq).
}    (* Goal: |D| ≤ eps|h| + eps', with D := (f−g)(x+h) − ((f−g)(x) + (rdf_f−rdf_g)·h) *)    set (D := real_plus (real_plus (f (real_plus x h) Hxh) (real_opp (g (real_plus x h) Hxh)))                        (real_opp (real_plus (real_plus (f x Hx) (real_opp (g x Hx)))                                             (real_mult (real_plus (rdf f Hf x Hx) (real_opp (rdf g Hg x Hx))) h)))).
apply (real_le_trans      (real_abs D)      (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)      (real_plus (real_mult eps (real_abs h)) eps')).
{ (* |D| ≤ |A| + |B| + eps_tri: triangle (with D == A + opp B restated). *)      apply (real_le_trans (real_abs D)                           (real_abs (real_plus A (real_opp B)))                           (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)).
{ (* |D| == |A + opp B|: eq_le, restating D. *)        apply RealSetoid.real_eq_le.
apply (real_abs_eq_compat D (real_plus A (real_opp B))).
(* D == A + opp B: via the normal form (Fh − Gh) + ((−Fx + Gx) + (−df·h + dg·h)). *)        unfold D, A, B.
set (Fh := f (real_plus x h) Hxh).
set (Fx := f x Hx).
set (Gh := g (real_plus x h) Hxh).
set (Gx := g x Hx).
set (df := rdf f Hf x Hx).
set (dg := rdf g Hg x Hx).
apply (real_eq_trans          (real_plus (real_plus Fh (real_opp Gh))                     (real_opp (real_plus (real_plus Fx (real_opp Gx))                                          (real_mult (real_plus df (real_opp dg)) h))))          (real_plus (real_plus Fh (real_opp Gh))                     (real_plus (real_plus (real_opp Fx) Gx)                                (real_plus (real_opp (real_mult df h)) (real_mult dg h))))          (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                     (real_opp (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))))).
- (* D' == normal form: split opp (opp_plus + opp_opp) + distrib_r + opp_mult_r. *)          apply (RealSetoid.real_eq_plus_compat                   (real_plus Fh (real_opp Gh))                   (real_opp (real_plus (real_plus Fx (real_opp Gx)) (real_mult (real_plus df (real_opp dg)) h)))                   (real_plus Fh (real_opp Gh))                   (real_plus (real_plus (real_opp Fx) Gx)                              (real_plus (real_opp (real_mult df h)) (real_mult dg h)))).
+ apply real_eq_refl.
+ (* opp((Fx−Gx) + (df−dg)·h) == (−Fx+Gx) + (−df·h + dg·h). *)            apply (real_eq_trans              (real_opp (real_plus (real_plus Fx (real_opp Gx)) (real_mult (real_plus df (real_opp dg)) h)))              (real_plus (real_opp (real_plus Fx (real_opp Gx))) (real_opp (real_mult (real_plus df (real_opp dg)) h)))              (real_plus (real_plus (real_opp Fx) Gx) (real_plus (real_opp (real_mult df h)) (real_mult dg h)))).
* apply (real_opp_plus (real_plus Fx (real_opp Gx)) (real_mult (real_plus df (real_opp dg)) h)).
* apply (RealSetoid.real_eq_plus_compat                       (real_opp (real_plus Fx (real_opp Gx)))                       (real_opp (real_mult (real_plus df (real_opp dg)) h))                       (real_plus (real_opp Fx) Gx)                       (real_plus (real_opp (real_mult df h)) (real_mult dg h))).
-- (* opp(Fx − Gx) == −Fx + Gx: opp_plus + opp_opp. *)                 apply (real_eq_trans (real_opp (real_plus Fx (real_opp Gx)))                                      (real_plus (real_opp Fx) (real_opp (real_opp Gx)))                                      (real_plus (real_opp Fx) Gx)).
++ apply (real_opp_plus Fx (real_opp Gx)).
++ apply (RealSetoid.real_eq_plus_compat (real_opp Fx) (real_opp (real_opp Gx))                                                          (real_opp Fx) Gx).
** apply real_eq_refl.
** apply (real_opp_opp Gx).
-- (* opp((df−dg)·h) == −df·h + dg·h: distrib_r + opp_plus + opp_opp. *)                 apply (real_eq_trans                   (real_opp (real_mult (real_plus df (real_opp dg)) h))                   (real_opp (real_plus (real_mult df h) (real_mult (real_opp dg) h)))                   (real_plus (real_opp (real_mult df h)) (real_mult dg h))).
++ apply (RealSetoid.real_eq_opp_compat                            (real_mult (real_plus df (real_opp dg)) h)                            (real_plus (real_mult df h) (real_mult (real_opp dg) h))).
apply real_eq_sym.
apply (real_distrib_r df (real_opp dg) h).
++ apply (real_eq_trans                            (real_opp (real_plus (real_mult df h) (real_mult (real_opp dg) h)))                            (real_plus (real_opp (real_mult df h)) (real_opp (real_mult (real_opp dg) h)))                            (real_plus (real_opp (real_mult df h)) (real_mult dg h))).
** apply (real_opp_plus (real_mult df h) (real_mult (real_opp dg) h)).
** apply (RealSetoid.real_eq_plus_compat                               (real_opp (real_mult df h))                               (real_opp (real_mult (real_opp dg) h))                               (real_opp (real_mult df h))                               (real_mult dg h)).
{ apply real_eq_refl.
}                       { (* opp(opp dg·h) == dg·h: opp_mult_r backwards + opp_opp. *)                         apply (real_eq_trans (real_opp (real_mult (real_opp dg) h))                                              (real_opp (real_opp (real_mult dg h)))                                              (real_mult dg h)).
{ apply (RealSetoid.real_eq_opp_compat (real_mult (real_opp dg) h) (real_opp (real_mult dg h))).
apply real_eq_sym.
apply (real_opp_mult_r dg h).
}                         { apply (real_opp_opp (real_mult dg h)).
} }        - (* normal form == A' + opp B': assembled backwards. *)          apply (real_eq_trans            (real_plus (real_plus Fh (real_opp Gh))                       (real_plus (real_plus (real_opp Fx) Gx)                                  (real_plus (real_opp (real_mult df h)) (real_mult dg h))))            (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                       (real_opp (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))))            (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                       (real_opp (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))))).
+ (* normal form == A'+opp B': via the M1/M2' intermediate shapes (rearrangement + opp folding). *)            apply (real_eq_trans              (real_plus (real_plus Fh (real_opp Gh))                         (real_plus (real_plus (real_opp Fx) Gx)                                    (real_plus (real_opp (real_mult df h)) (real_mult dg h))))              (real_plus (real_plus Fh (real_opp Gh))                         (real_plus (real_plus (real_opp Fx) (real_opp (real_mult df h)))                                    (real_plus Gx (real_mult dg h))))              (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                         (real_opp (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))))).
* (* NF == M1: inner rearrangement ((−Fx+Gx)+(−df·h+dg·h)) == ((−Fx+−df·h)+(Gx+dg·h)). *)              apply (RealSetoid.real_eq_plus_compat                       (real_plus Fh (real_opp Gh))                       (real_plus (real_plus (real_opp Fx) Gx)                                  (real_plus (real_opp (real_mult df h)) (real_mult dg h)))                       (real_plus Fh (real_opp Gh))                       (real_plus (real_plus (real_opp Fx) (real_opp (real_mult df h)))                                  (real_plus Gx (real_mult dg h)))).
-- apply real_eq_refl.
-- (* ((−Fx+Gx)+(−df·h+dg·h)) == ((−Fx+−df·h)+(Gx+dg·h)). *)                 apply (real_eq_trans                   (real_plus (real_plus (real_opp Fx) Gx) (real_plus (real_opp (real_mult df h)) (real_mult dg h)))                   (real_plus (real_opp Fx) (real_plus (real_opp (real_mult df h)) (real_plus Gx (real_mult dg h))))                   (real_plus (real_plus (real_opp Fx) (real_opp (real_mult df h))) (real_plus Gx (real_mult dg h)))).
++ apply (real_eq_trans                            (real_plus (real_plus (real_opp Fx) Gx) (real_plus (real_opp (real_mult df h)) (real_mult dg h)))                            (real_plus (real_opp Fx) (real_plus Gx (real_plus (real_opp (real_mult df h)) (real_mult dg h))))                            (real_plus (real_opp Fx) (real_plus (real_opp (real_mult df h)) (real_plus Gx (real_mult dg h))))).
** apply real_eq_sym.
apply (real_plus_assoc (real_opp Fx) Gx (real_plus (real_opp (real_mult df h)) (real_mult dg h))).
** apply (RealSetoid.real_eq_plus_compat                                (real_opp Fx)                                (real_plus Gx (real_plus (real_opp (real_mult df h)) (real_mult dg h)))                                (real_opp Fx)                                (real_plus (real_opp (real_mult df h)) (real_plus Gx (real_mult dg h)))).
{ apply real_eq_refl.
}                        { (* Gx + (−df·h + dg·h) == −df·h + (Gx + dg·h): comm + assoc + comm *)                          apply (real_eq_trans                            (real_plus Gx (real_plus (real_opp (real_mult df h)) (real_mult dg h)))                            (real_plus (real_plus (real_opp (real_mult df h)) (real_mult dg h)) Gx)                            (real_plus (real_opp (real_mult df h)) (real_plus Gx (real_mult dg h)))).
{ apply (real_plus_comm Gx (real_plus (real_opp (real_mult df h)) (real_mult dg h))).
}                          { apply (real_eq_trans                                     (real_plus (real_plus (real_opp (real_mult df h)) (real_mult dg h)) Gx)                                     (real_plus (real_opp (real_mult df h)) (real_plus (real_mult dg h) Gx))                                     (real_plus (real_opp (real_mult df h)) (real_plus Gx (real_mult dg h)))).
{ apply real_eq_sym.
apply (real_plus_assoc (real_opp (real_mult df h)) (real_mult dg h) Gx).
}                            { apply (RealSetoid.real_eq_plus_compat (real_opp (real_mult df h))                                                                     (real_plus (real_mult dg h) Gx)                                                                     (real_opp (real_mult df h))                                                                     (real_plus Gx (real_mult dg h))).
{ apply real_eq_refl.
}                              { apply (real_plus_comm (real_mult dg h) Gx).
} } } }                     
++ apply (real_plus_assoc (real_opp Fx) (real_opp (real_mult df h)) (real_plus Gx (real_mult dg h))).
* (* M1 == A''+opp B'': opp folding (opp_plus backwards + opp_opp backwards) + outer rearrangement. *)                      apply (real_eq_trans                        (real_plus (real_plus Fh (real_opp Gh))                                   (real_plus (real_plus (real_opp Fx) (real_opp (real_mult df h)))                                              (real_plus Gx (real_mult dg h))))                        (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                                   (real_plus (real_opp Gh) (real_plus Gx (real_mult dg h))))                        (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                                   (real_opp (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))))).
{ (* Outer rearrangement: (Fh+oppGh) + ((oppFx+oppdfh)+(Gx+dgfh)) == (Fh+opp(Fx+dfh)) + (oppGh+(Gx+dgfh)). *)                        apply (real_eq_trans                          (real_plus (real_plus Fh (real_opp Gh))                                     (real_plus (real_plus (real_opp Fx) (real_opp (real_mult df h)))                                                (real_plus Gx (real_mult dg h))))                          (real_plus (real_plus Fh (real_plus (real_opp Fx) (real_opp (real_mult df h))))                                     (real_plus (real_opp Gh) (real_plus Gx (real_mult dg h))))                          (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                                     (real_plus (real_opp Gh) (real_plus Gx (real_mult dg h))))).
{ (* Rearrangement: (Fh+oppGh) + (X+Y) == (Fh+X) + (oppGh+Y): real_plus_swap. *)                          apply (real_plus_swap Fh (real_opp Gh)                                                (real_plus (real_opp Fx) (real_opp (real_mult df h)))                                                (real_plus Gx (real_mult dg h))).
}                        { (* oppFx+oppdfh == opp(Fx+dfh): opp_plus backwards. *)                          apply (RealSetoid.real_eq_plus_compat                                   (real_plus Fh (real_plus (real_opp Fx) (real_opp (real_mult df h))))                                   (real_plus (real_opp Gh) (real_plus Gx (real_mult dg h)))                                   (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                                   (real_plus (real_opp Gh) (real_plus Gx (real_mult dg h)))).
{ apply (RealSetoid.real_eq_plus_compat Fh (real_plus (real_opp Fx) (real_opp (real_mult df h)))                                                                   Fh (real_opp (real_plus Fx (real_mult df h)))).
{ apply real_eq_refl.
}                            { apply real_eq_sym.
apply (real_opp_plus Fx (real_mult df h)).
} }                          { apply real_eq_refl.
} } }                      { (* (Fh+opp(Fx+dfh)) + (oppGh+(Gx+dgfh)) == A''+oppB'': opp folding. *)                        apply (RealSetoid.real_eq_plus_compat                                 (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                                 (real_plus (real_opp Gh) (real_plus Gx (real_mult dg h)))                                 (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                                 (real_opp (real_plus Gh (real_opp (real_plus Gx (real_mult dg h)))))).
{ apply real_eq_refl.
}                        { (* oppGh + (Gx+dgfh) == opp(Gh + opp(Gx+dgfh)) *)                          apply (real_eq_trans                            (real_plus (real_opp Gh) (real_plus Gx (real_mult dg h)))                            (real_plus (real_opp Gh) (real_opp (real_opp (real_plus Gx (real_mult dg h)))))                            (real_opp (real_plus Gh (real_opp (real_plus Gx (real_mult dg h)))))).
{ apply (RealSetoid.real_eq_plus_compat (real_opp Gh) (real_plus Gx (real_mult dg h))                                                                  (real_opp Gh) (real_opp (real_opp (real_plus Gx (real_mult dg h))))).
{ apply real_eq_refl.
}                            { apply real_eq_sym.
apply (real_opp_opp (real_plus Gx (real_mult dg h))).
} }                          { apply real_eq_sym.
apply (real_opp_plus Gh (real_opp (real_plus Gx (real_mult dg h)))).
} } }          + apply real_eq_refl.
}      { (* |A + opp B| ≤ |A| + |B| + eps_tri: triangle + |opp B| == |B|. *)        apply (real_le_trans (real_abs (real_plus A (real_opp B)))                             (real_plus (real_plus (real_abs A) (real_abs (real_opp B))) eps_tri)                             (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)).
- apply (real_abs_triangle_le_eps A (real_opp B) eps_tri).
exact Heptr.
- apply RealSetoid.real_eq_le.
apply (RealSetoid.real_eq_plus_compat (real_plus (real_abs A) (real_abs (real_opp B)))                                                eps_tri                                                (real_plus (real_abs A) (real_abs B))                                                eps_tri).
+ apply (RealSetoid.real_eq_plus_compat (real_abs A) (real_abs (real_opp B))                                                  (real_abs A) (real_abs B)).
* apply real_eq_refl.
* apply (real_abs_opp B).
+ apply real_eq_refl.
} }      { (* |A|+|B|+eps_tri ≤ eps|h| + eps': first through the M2 intermediate term. *)        apply (real_le_trans          (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)          (real_plus (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)                                (real_plus (real_mult eps_half (real_abs h)) epsq)) eps_tri)          (real_plus (real_mult eps (real_abs h)) eps')).
- (* |A|+|B|+eps_tri ≤ M2: plus_compat (HA + HB) *)          apply (real_le_plus_compat (real_plus (real_abs A) (real_abs B))                                     (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)                                                (real_plus (real_mult eps_half (real_abs h)) epsq))                                     eps_tri eps_tri).
+ apply (real_le_plus_compat (real_abs A) (real_plus (real_mult eps_half (real_abs h)) epsq)                                       (real_abs B) (real_plus (real_mult eps_half (real_abs h)) epsq)).
* exact HA.
* exact HB.
+ apply real_le_refl.
- (* M2 == eps|h| + eps': algebraic chain (rearrangement + merging halves). *)          apply RealSetoid.real_eq_le.
apply (real_eq_trans            (real_plus (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)                                  (real_plus (real_mult eps_half (real_abs h)) epsq)) eps_tri)            (real_plus (real_mult eps (real_abs h)) (real_plus (real_plus epsq epsq) eps_tri))            (real_plus (real_mult eps (real_abs h)) eps')).
+ (* Rearrangement + merging A+C: ((A+B)+(C+D))+E == eps|h| + ((B+D)+E). *)            apply (real_eq_trans _              (real_plus (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq)) eps_tri)              _).
{ (* ((A+B)+(C+D))+E == (eps|h|+(B+D))+E: swap + merging A+C. *)              apply (RealSetoid.real_eq_plus_compat                       (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)                                  (real_plus (real_mult eps_half (real_abs h)) epsq))                       eps_tri                       (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq))                       eps_tri).
- (* (A+B)+(C+D) == eps|h|+(B+D): swap + A+C == eps|h| *)                apply (real_eq_trans                  (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)                             (real_plus (real_mult eps_half (real_abs h)) epsq))                  (real_plus (real_plus (real_mult eps_half (real_abs h)) (real_mult eps_half (real_abs h)))                             (real_plus epsq epsq))                  (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq))).
+ apply (real_plus_swap (real_mult eps_half (real_abs h)) epsq                                        (real_mult eps_half (real_abs h)) epsq).
+ apply (RealSetoid.real_eq_plus_compat                           (real_plus (real_mult eps_half (real_abs h)) (real_mult eps_half (real_abs h)))                           (real_plus epsq epsq)                           (real_mult eps (real_abs h))                           (real_plus epsq epsq)).
* (* eps_half|h| + eps_half|h| == eps|h|: mult_assoc restatement + real_half_plus_half. *)                    apply (real_eq_trans                      (real_plus (real_mult eps_half (real_abs h)) (real_mult eps_half (real_abs h)))                      (real_plus (real_mult half (real_mult eps (real_abs h))) (real_mult half (real_mult eps (real_abs h))))                      (real_mult eps (real_abs h))).
-- apply (RealSetoid.real_eq_plus_compat                               (real_mult eps_half (real_abs h)) (real_mult eps_half (real_abs h))                               (real_mult half (real_mult eps (real_abs h))) (real_mult half (real_mult eps (real_abs h)))).
++ unfold eps_half.
apply real_eq_sym.
apply (real_mult_assoc half eps (real_abs h)).
++ unfold eps_half.
apply real_eq_sym.
apply (real_mult_assoc half eps (real_abs h)).
-- apply (real_half_plus_half (real_mult eps (real_abs h))).
* apply real_eq_refl.
- apply real_eq_refl.
}            { apply real_eq_sym.
apply (real_plus_assoc (real_mult eps (real_abs h)) (real_plus epsq epsq) eps_tri).
}          + (* eps|h| + ((epsq+epsq)+eps_tri) == eps|h| + eps': B+D+E == eps' *)            apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))                                                  (real_plus (real_plus epsq epsq) eps_tri)                                                  (real_mult eps (real_abs h))                                                  eps').
* apply real_eq_refl.
* (* (epsq+epsq)+eps_tri == eps': quarter+quarter == half, half+half == 1 *)              apply (real_eq_trans (real_plus (real_plus epsq epsq) eps_tri)                                   (real_plus (real_mult half eps') (real_mult half eps'))                                   eps').
-- (* (epsq+epsq)+eps_tri == half·eps' + half·eps': merging quarters. *)                 apply (real_eq_trans (real_plus (real_plus epsq epsq) eps_tri)                                      (real_plus (real_mult (real_plus quarter quarter) eps') (real_mult half eps'))                                      (real_plus (real_mult half eps') (real_mult half eps'))).
++ unfold epsq, eps_tri.
apply (RealSetoid.real_eq_plus_compat                             (real_plus (real_mult quarter eps') (real_mult quarter eps'))                             (real_mult half eps')                             (real_mult (real_plus quarter quarter) eps')                             (real_mult half eps')).
** apply (real_distrib_r quarter quarter eps').
** apply real_eq_refl.
++ apply (RealSetoid.real_eq_plus_compat                             (real_mult (real_plus quarter quarter) eps')                             (real_mult half eps')                             (real_mult half eps') (real_mult half eps')).
** apply (RealSetoid.real_eq_mult_compat (real_plus quarter quarter) eps' half eps'                                                             (real_half_plus_half half) (real_eq_refl _)).
** apply real_eq_refl.
-- apply (real_half_plus_half eps').
}
Qed. (* ============ 3. mult auxiliary lemma family (in the Real layer there is no 0 ≤ |a|, so product bounds go pointwise) ============   The Real-layer real_le = Or lt eq cannot express 0 ≤ |a|, so real_le_mult_compat(_weak)   is unusable at product bounds of the shape |f|·|A_g| ≤ Mf·(eps_g|h|+β_g).  The detour: pointwise at the Q layer (Qabs_nonneg is decidable).   Three new lemmas: real_abs_plus_one_pos (0 < 1+|a|, positivity of Mf/Mg), real_abs_le_plus_one   (|a| ≤ 1+|a|, |f| ≤ Mf), real_abs_prod_le_eps (|a| ≤ M → |b| ≤ B →   |a|·|b| ≤ M·B + eps, with the margin absorbing the eq-branch Cauchy surplus). *)(* 3a: 0 < 1 + |a| (pointwise 1 + Qabs(a_n) ≥ 1 > 1/2). *)
Lemma real_abs_plus_one_pos : forall a : Real,  real_lt real_zero (real_plus real_one (real_abs a)).
Proof.
intro a.
unfold real_lt.
exists (1 / 2)%Q.
split.
- apply Qlt_to_QltT.
compute.
reflexivity.
- exists 0%nat.
intros n Hn.
apply Qlt_to_QltT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
assert (Hnz : projT1 (real_plus real_one (real_abs a)) n == 1 + Qabs (projT1 a n)).
{ setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs a) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
cbn [projT1].
reflexivity.
}    setoid_rewrite Hz.
setoid_rewrite Hnz.
apply (Qlt_le_trans _ 1 _).
{ compute.
reflexivity.
}    { (* Qle 1 ((1+Qabs(a_n)) − 0): via 1+Qabs(a_n) (Qabs ≥ 0; X−0 == X). *)      apply (Qle_trans _ (1 + Qabs (projT1 a n)) _).
{ apply (Qplus_le_compat 1 1 0 (Qabs (projT1 a n))).
{ apply Qle_refl.
}        { apply Qabs_nonneg.
} }      { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
} }
Qed. (* 3b: 0 < b gives 0 < |a| + b (Lf := |df|+eps_f, positivity of the Den factor; pointwise |a|_n ≥ 0 and b_n > eps0). *)
Lemma real_abs_plus_pos : forall (a b : Real),  real_lt real_zero b -> real_lt real_zero (real_plus (real_abs a) b).
Proof.
intros a b Hb.
destruct Hb as [eps0 [Heps0 [N0 HN0]]].
unfold real_lt.
exists (eps0 / 2)%Q.
split.
- apply Qlt_to_QltT.
apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
- exists N0.
intros n Hn.
apply Qlt_to_QltT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
assert (Hbn : Qlt eps0 (projT1 b n)).
{ apply (Qlt_le_trans _ (projT1 b n - projT1 real_zero n) _).
- apply QltT_to_Qlt.
exact (HN0 n Hn).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Habsn : Qle 0 (projT1 (real_abs a) n)).
{ rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
apply Qabs_nonneg.
}    assert (Hsum : Qlt eps0 (projT1 (real_abs a) n + projT1 b n)).
{ apply (Qlt_le_trans _ (0 + projT1 b n) _).
- apply (Qlt_le_trans _ (projT1 b n) _).
+ exact Hbn.
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
- apply (Qplus_le_compat 0 (projT1 (real_abs a) n) (projT1 b n) (projT1 b n)).
+ exact Habsn.
+ apply Qle_refl.
}    apply (Qlt_le_trans _ (projT1 (real_abs a) n + projT1 b n) _).
+ apply (Qlt_trans _ eps0 _).
* apply QltT_to_Qlt.
apply (q_half_lt_self eps0).
exact Heps0.
* exact Hsum.
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
unfold Qminus.
rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_abs a) b n)).
assert (Hn0 : - 0 == 0) by (compute; reflexivity).
setoid_rewrite Hn0.
apply Qeq_sym.
apply Qplus_0_r.
Qed. (* 3c: |a| ≤ 1 + |a| (the lt branch, pointwise difference == 1). *)
Lemma real_abs_le_plus_one : forall a : Real,  real_le (real_abs a) (real_plus real_one (real_abs a)).
Proof.
intro a.
apply (RealSetoid.real_lt_le_iff_req (real_abs a) (real_plus real_one (real_abs a))).
left.
unfold real_lt.
exists (1 / 2)%Q.
split.
- apply Qlt_to_QltT.
compute.
reflexivity.
- exists 0%nat.
intros n Hn.
apply Qlt_to_QltT.
assert (Hnz : projT1 (real_plus real_one (real_abs a)) n == 1 + Qabs (projT1 a n)).
{ setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs a) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
cbn [projT1].
reflexivity.
}    assert (Habs : projT1 (real_abs a) n == Qabs (projT1 a n)) by (apply qeqT_imp_qeq; apply real_abs_proj).
setoid_rewrite Hnz.
setoid_rewrite Habs.
apply (Qlt_le_trans _ 1 _).
{ compute.
reflexivity.
}    { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}
Qed. (* 3d: 0 < b gives 0 < 1 + b (positivity of inv(1+eps'); pointwise 1 + b_n ≥ 1). *)
Lemma real_one_plus_pos : forall b : Real,  real_lt real_zero b -> real_lt real_zero (real_plus real_one b).
Proof.
intros b Hb.
destruct Hb as [eps0 [Heps0 [N0 HN0]]].
unfold real_lt.
exists (1 / 2)%Q.
split.
- apply Qlt_to_QltT.
compute.
reflexivity.
- exists N0.
intros n Hn.
apply Qlt_to_QltT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
assert (Hbn : Qle 0 (projT1 b n)).
{ apply (Qle_trans _ (projT1 b n - projT1 real_zero n) _).
- (* 0 ≤ b_n − 0: 0 < eps0 < b_n − 0 ⟹ Qlt_le_weak *)        apply Qlt_le_weak.
apply (Qlt_trans _ eps0 _).
+ apply QltT_to_Qlt.
exact Heps0.
+ apply QltT_to_Qlt.
exact (HN0 n Hn).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hnz : projT1 (real_plus real_one b) n == 1 + projT1 b n).
{ setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one b n)).
cbn [projT1].
reflexivity.
}    setoid_rewrite Hz.
setoid_rewrite Hnz.
apply (Qlt_le_trans _ 1 _).
{ compute.
reflexivity.
}    { (* Qle 1 ((1+b_n) − 0): via 1+b_n (Qle_plus_nonneg_r; X−0 == X). *)      apply (Qle_trans _ (1 + projT1 b n) _).
{ apply (Qle_plus_nonneg_r 1 (projT1 b n)).
exact Hbn.
}      { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
} }
Qed. (* 3e: 0 < b gives 1 ≤ 1 + b (the premise of K ≤ K(1+eps'), via real_le_mult_compat + real_inv_pos_le_compat). *)
Lemma real_le_one_plus : forall b : Real,  real_lt real_zero b -> real_le real_one (real_plus real_one b).
Proof.
intros b Hb.
destruct Hb as [eps0 [Heps0 [N0 HN0]]].
apply (RealSetoid.real_lt_le_iff_req real_one (real_plus real_one b)).
left.
unfold real_lt.
exists (eps0 / 2)%Q.
split.
- apply Qlt_to_QltT.
apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
- exists N0.
intros n Hn.
apply Qlt_to_QltT.
assert (Hbn : Qlt eps0 (projT1 b n)).
{ assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
apply (Qlt_le_trans _ (projT1 b n - projT1 real_zero n) _).
- apply QltT_to_Qlt.
exact (HN0 n Hn).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hnz : projT1 (real_plus real_one b) n == 1 + projT1 b n).
{ setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one b n)).
cbn [projT1].
reflexivity.
}    setoid_rewrite Hnz.
assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
setoid_rewrite Ho.
apply (Qlt_le_trans _ (projT1 b n) _).
{ apply (Qlt_trans _ eps0 _).
{ apply QltT_to_Qlt.
apply (q_half_lt_self eps0).
exact Heps0.
}      { exact Hbn.
} }    { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}
Qed. (* 3f: pointwise tail-bound extraction of |a| ≤ M (the lt branch gives exactly ≤ M_n; the eq branch gives ≤ M_n + c, with c a given Q margin). *)
Lemma real_abs_le_extract : forall (a M : Real) (c : Q),  QltT 0 c -> real_le (real_abs a) M ->  sigT (fun N : nat => forall n : nat, NatLe N n ->    QleT' (Qabs (projT1 a n)) (projT1 M n + c)).
Proof.
intros a M c Hc Hle.
unfold real_le in Hle.
destruct Hle as [Hlt | Heq].
- destruct Hlt as [c1 [Hc1 [N1 HN1]]].
exists N1.
intros n Hn.
apply Qle_to_QleT'.
apply (Qle_trans _ (projT1 M n) _).
+ apply QleT'_to_Qle. apply (q_lt_diff_le c1 (Qabs (projT1 a n)) (projT1 M n)).
* exact Hc1.
* assert (Hq : Qlt c1 (projT1 M n - Qabs (projT1 a n))).
{ assert (Hq0 : Qlt c1 (projT1 M n - projT1 (real_abs a) n)).
{ apply QltT_to_Qlt.
exact (HN1 n Hn).
}          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)) in Hq0.
exact Hq0.
}        exact (Qlt_to_QltT _ _ Hq).
+ apply (Qle_plus_nonneg_r (projT1 M n) c).
apply Qlt_le_weak.
apply QltT_to_Qlt.
exact Hc.
- destruct (Heq c Hc) as [N1 HN1].
exists N1.
intros n Hn.
apply Qle_to_QleT'.
assert (HN1n : Qlt (Qabs (Qabs (projT1 a n) - projT1 M n)) c).
{ assert (Hq0 : Qlt (Qabs (projT1 (real_abs a) n - projT1 M n)) c).
{ apply QltT_to_Qlt.
exact (HN1 n Hn).
}      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)) in Hq0.
exact Hq0.
}    apply (Qle_trans _ (projT1 M n + Qabs (Qabs (projT1 a n) - projT1 M n)) _).
+ apply (Qle_trans _ (projT1 M n + (Qabs (projT1 a n) - projT1 M n)) _).
* apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
* apply (Qplus_le_compat (projT1 M n) (projT1 M n)                               (Qabs (projT1 a n) - projT1 M n)                               (Qabs (Qabs (projT1 a n) - projT1 M n))).
-- apply Qle_refl.
-- apply Qle_Qabs.
+ apply (Qplus_le_compat (projT1 M n) (projT1 M n)                             (Qabs (Qabs (projT1 a n) - projT1 M n)) c).
* apply Qle_refl.
* apply Qlt_le_weak.
exact HN1n.
Qed. (* 3g: the main product-bound lemma (pointwise; the margin eps absorbs the eq-branch Cauchy surplus)   |a| ≤ M → |b| ≤ B → |a|·|b| ≤ M·B + eps   Pointwise: Qabs(a_n) ≤ M_n + c0 and Qabs(b_n) ≤ B_n + c0 (c0 := min(eps0/(16(1+Ma+Mb)), 1))   gives Qabs(a)·Qabs(b) ≤ (M+c0)(B+c0) ≤ M·B + eps0/2, witnessed by eps0/2. *)
Lemma real_abs_prod_le_eps : forall (a b M B eps : Real),  real_lt real_zero eps ->  real_le (real_abs a) M ->  real_le (real_abs b) B ->  real_le (real_mult (real_abs a) (real_abs b))          (real_plus (real_mult M B) eps).
Proof.
intros a b M B eps Heps HMa HMB.
destruct Heps as [eps0 [Heps0 [N0 HN0]]].
destruct (real_norm_bounded M) as [Ma [HMa_pos HMa_b]].
destruct (real_norm_bounded B) as [Mb [HMb_pos HMb_b]].
assert (Hamb : Qlt 0 (1 + Ma + Mb)).
{ apply (Qlt_le_trans _ 1 _).
- reflexivity.
- apply (Qle_trans _ (1 + (Ma + Mb)) _).
+ apply (Qle_plus_nonneg_r 1 (Ma + Mb)).
apply (Qle_trans _ (0 + 0) _).
* apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
* apply (Qplus_le_compat 0 Ma 0 Mb).
-- apply Qlt_le_weak.
exact (QltT_to_Qlt _ _ HMa_pos).
-- apply Qlt_le_weak.
exact (QltT_to_Qlt _ _ HMb_pos).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}  set (c0 := Qmin (eps0 / (16 * (1 + Ma + Mb))) 1).
assert (Hc0 : QltT 0 c0).
{ unfold c0.
apply Qlt_to_QltT.
apply Q.min_glb_lt.
- apply (Qlt_shift_div_l 0 eps0 (16 * (1 + Ma + Mb))).
+ apply (Qmult_lt_0_compat 16 (1 + Ma + Mb)).
* vm_compute.
reflexivity.
* exact Hamb.
+ rewrite Qmult_0_l.
apply QltT_to_Qlt.
exact Heps0.
- reflexivity.
}  assert (Hc0_le1 : Qle c0 1).
{ unfold c0.
apply Q.le_min_r.
}  assert (Hc0_le_div : Qle c0 (eps0 / (16 * (1 + Ma + Mb)))).
{ unfold c0.
apply Q.le_min_l.
}  destruct (real_abs_le_extract a M c0 Hc0 HMa) as [Na HNa].
destruct (real_abs_le_extract b B c0 Hc0 HMB) as [Nb HNb].
apply (RealSetoid.real_lt_le_iff_req    (real_mult (real_abs a) (real_abs b))    (real_plus (real_mult M B) eps)).
left.
unfold real_lt.
exists (eps0 / 2)%Q.
split.
- apply Qlt_to_QltT.
apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
- exists (Nat.max N0 (Nat.max Na Nb)).
intros n Hn.
apply NatLe_drop in Hn.
assert (Hn0 : (N0 <= n)%nat) by lia.
assert (Hna : (Na <= n)%nat) by lia.
assert (Hnb : (Nb <= n)%nat) by lia.
set (an := projT1 (real_abs a) n).
set (bn := projT1 (real_abs b) n).
set (Mn := projT1 M n).
set (Bn := projT1 B n).
set (en := projT1 eps n).
set (qn := projT1 (real_mult (real_abs a) (real_abs b)) n).
set (pn := projT1 (real_plus (real_mult M B) eps) n).
assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
assert (Hepsn : Qlt eps0 en).
{ unfold en.
apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
- apply QltT_to_Qlt.
exact (HN0 n (NatLe_lift _ _ Hn0)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hzero.
ring.
}    assert (Hqn_eq : qn == an * bn).
{ unfold qn, an, bn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_abs a) (real_abs b) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj b n)).
reflexivity.
}    assert (Hpn_eq : pn == Mn * Bn + en).
{ unfold pn, Mn, Bn, en.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult M B) eps n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj M B n)).
reflexivity.
}    assert (Han : Qle an (Mn + c0)).
{ unfold an, Mn.
rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
exact (QleT'_to_Qle _ _ (HNa n (NatLe_lift _ _ Hna))).
}    assert (Hbn : Qle bn (Bn + c0)).
{ unfold bn, Bn.
rewrite (qeqT_imp_qeq _ _ (real_abs_proj b n)).
exact (QleT'_to_Qle _ _ (HNb n (NatLe_lift _ _ Hnb))).
}    assert (Han0 : Qle 0 an).
{ unfold an.
rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
apply Qabs_nonneg.
}    assert (Hbn0 : Qle 0 bn).
{ unfold bn.
rewrite (qeqT_imp_qeq _ _ (real_abs_proj b n)).
apply Qabs_nonneg.
}    (* an·bn ≤ (Mn+c0)(Bn+c0) *)    assert (Hprod : Qle (an * bn) ((Mn + c0) * (Bn + c0))).
{ apply (Qmult_le_compat_nonneg an (Mn + c0) bn (Bn + c0)).
- split; [exact Han0 | exact Han].
- split; [exact Hbn0 | exact Hbn].
}    (* Main chain: pn − qn ≥ en − c0(1+Ma+Mb) ≥ eps0 − eps0/16 > eps0/2. *)    assert (Hmain : Qle (en - c0 * (1 + Ma + Mb)) (pn - qn)).
{ rewrite Hpn_eq.
rewrite Hqn_eq.
apply (Qle_trans _ (Mn * Bn + en - (Mn + c0) * (Bn + c0)) _).
- (* en − c0(1+Ma+Mb) ≤ MnBn + en − (Mn+c0)(Bn+c0) *)        assert (Hmn : Qle Mn Ma).
{ apply (Qle_trans _ (Qabs Mn) _); [apply Qle_Qabs | apply (QleT'_to_Qle _ _ (HMa_b n))].
}        assert (Hbn_l : Qle Bn Mb).
{ apply (Qle_trans _ (Qabs Bn) _); [apply Qle_Qabs | apply (QleT'_to_Qle _ _ (HMb_b n))].
}        assert (Hdelta : Qle 0 (c0 * (1 + Ma + Mb - Mn - Bn) - c0 * c0)).
{ (* = c0·[(1+Ma+Mb−Mn−Bn) − c0]; both factors are ≥ 0. *)          assert (Hdm : Qle 0 (Ma - Mn)) by (apply (proj1 (Qle_minus_iff Mn Ma)); exact Hmn).
assert (Hdb : Qle 0 (Mb - Bn)) by (apply (proj1 (Qle_minus_iff Bn Mb)); exact Hbn_l).
assert (Hnonneg : Qle 0 (Ma + Mb - Mn - Bn)).
{ apply (Qle_trans _ ((Ma - Mn) + (Mb - Bn)) _).
- apply (Qplus_le_compat 0 (Ma - Mn) 0 (Mb - Bn)).
+ exact Hdm.
+ exact Hdb.
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}          assert (H1le : Qle 1 (1 + Ma + Mb - Mn - Bn)).
{ apply (Qle_trans _ (1 + (Ma + Mb - Mn - Bn)) _).
- apply (Qplus_le_compat 1 1 0 (Ma + Mb - Mn - Bn)).
+ apply Qle_refl.
+ exact Hnonneg.
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}          assert (Hc1le : Qle (c0 * 1) (c0 * (1 + Ma + Mb - Mn - Bn))).
{ apply (Qle_trans _ (1 * c0) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
- apply (Qle_trans _ ((1 + Ma + Mb - Mn - Bn) * c0) _).
+ apply (Qmult_le_compat_r 1 (1 + Ma + Mb - Mn - Bn) c0).
* exact H1le.
* apply Qlt_le_weak.
apply QltT_to_Qlt.
exact Hc0.
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}          assert (Hc0le1 : Qle 0 (1 - c0)).
{ apply (proj1 (Qle_minus_iff c0 1)).
exact Hc0_le1.
}          apply (Qle_trans _ (c0 * 1 - c0 * c0) _).
- (* c0·1 − c0² ≥ 0: c0(1−c0) ≥ 0 *)            assert (Heq : c0 * 1 - c0 * c0 == c0 * (1 - c0)) by ring.
rewrite Heq.
apply (Qmult_le_0_compat c0 (1 - c0)).
+ apply Qlt_le_weak.
apply QltT_to_Qlt.
exact Hc0.
+ exact Hc0le1.
- apply (Qplus_le_compat (c0 * 1) (c0 * (1 + Ma + Mb - Mn - Bn))                                   (Qopp (c0 * c0)) (Qopp (c0 * c0))).
+ exact Hc1le.
+ apply Qle_refl.
}        (* en − c0(1+Ma+Mb) ≤ (MnBn + en) − (Mn+c0)(Bn+c0): the difference == Hdelta. *)        apply (Qle_trans _ (en - c0 * (1 + Ma + Mb) + (c0 * (1 + Ma + Mb - Mn - Bn) - c0 * c0)) _).
{ apply (Qle_plus_nonneg_r (en - c0 * (1 + Ma + Mb))                                   (c0 * (1 + Ma + Mb - Mn - Bn) - c0 * c0)).
exact Hdelta.
}        { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}      - (* MnBn + en − (Mn+c0)(Bn+c0) ≤ pn − qn: qn = an·bn ≤ (Mn+c0)(Bn+c0) *)        apply (Qle_trans _ (Mn * Bn + (en - (Mn + c0) * (Bn + c0))) _).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
+ apply (Qle_trans _ (Mn * Bn + (en - an * bn)) _).
* apply (Qplus_le_compat (Mn * Bn) (Mn * Bn)                                   (en - (Mn + c0) * (Bn + c0)) (en - an * bn)).
-- apply Qle_refl.
-- apply (Qplus_le_compat en en (Qopp ((Mn + c0) * (Bn + c0))) (Qopp (an * bn))).
++ apply Qle_refl.
++ apply (Qopp_le_compat (an * bn) ((Mn + c0) * (Bn + c0))).
exact Hprod.
* apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}    (* Main chain: eps0/2 < en − c0(1+Ma+Mb) ≤ pn − qn. *)    apply Qlt_to_QltT.
apply (Qlt_le_trans _ (en - c0 * (1 + Ma + Mb)) _).
{ (* eps0/2 < en − c0(1+Ma+Mb) *)      apply (Qlt_le_trans _ (eps0 - eps0 / 16) _).
+ (* eps0/2 < eps0 − eps0/16 *)        apply (proj2 (Qlt_minus_iff (eps0 / 2) (eps0 - eps0 / 16))).
assert (Halg : (eps0 - eps0 / 16) - eps0 / 2 == eps0 * (7 / 16)) by (unfold Qdiv; field).
rewrite Halg.
apply (Qmult_lt_0_compat eps0 (7 / 16)); [apply QltT_to_Qlt; exact Heps0 | compute; reflexivity].
+ (* eps0 − eps0/16 ≤ en − c0(1+Ma+Mb) *)        apply (Qle_trans _ (en - eps0 / 16) _).
* apply (Qplus_le_compat eps0 en (Qopp (eps0 / 16)) (Qopp (eps0 / 16))).
-- apply Qlt_le_weak.
exact Hepsn.
-- apply Qle_refl.
* apply (Qplus_le_compat en en (Qopp (eps0 / 16)) (Qopp (c0 * (1 + Ma + Mb)))).
-- apply Qle_refl.
-- apply (Qopp_le_compat (c0 * (1 + Ma + Mb)) (eps0 / 16)).
apply (Qle_trans _ (eps0 / (16 * (1 + Ma + Mb)) * (1 + Ma + Mb)) _).
++ apply (Qmult_le_compat_r c0 (eps0 / (16 * (1 + Ma + Mb))) (1 + Ma + Mb)).
** exact Hc0_le_div.
** apply Qlt_le_weak.
exact Hamb.
++ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
unfold Qdiv.
field.
intro Hnz.
apply (Qlt_irrefl 0).
rewrite Hnz in Hamb.
exact Hamb.
}    { exact Hmain.
}
Qed. (* ============ 4. Multiplicative error decomposition identity (real_mult_diff_decomp) ============   D := (f·g)(x+h) − ((f·g)(x) + (f'·g + f·g')·h)      == f(x)·A_g + g(x)·A_f + Δf·Δg   (T1 + T2 + T3)   A_f := f(x+h) − (f(x) + f'·h); A_g := g(x+h) − (g(x) + g'·h)   Δf := f(x+h) − f(x); Δg := g(x+h) − g(x)   Route: D == (Fh·Gh + opp(Fx·Gx)) + opp(Y)            [opp_plus + assoc, Y := (df·Gx+Fx·dg)·h]        == (Δf·Gx + Fx·Δg + Δf·Δg) + opp(Y)            [expanding Fh·Gh == (Fx+Δf)(Gx+Δg) + cancelling Fx·Gx]        == ((Δf·Gx + Fx·Δg) + Δf·Δg) + (opp(df·Gx·h) + opp(Fx·dg·h))   [expanding Y + opp_plus]        == ((Δf·Gx + opp(df·Gx·h)) + (Fx·Δg + opp(Fx·dg·h))) + Δf·Δg    [real_plus_swap rearrangement]        == (Gx·A_f + Fx·A_g) + Δf·Δg                    [distrib + opp_mult_r/opp_mult folding]        == (Fx·A_g + Gx·A_f) + Δf·Δg                    [comm]. *)(* Auxiliary: x + (y − x) == y (the Fh == Fx + Δf bridge). *)
Lemma real_plus_minus_cancel : forall x y : Real,  real_eq (real_plus x (real_plus y (real_opp x))) y.
Proof.
intros x y.
apply (real_eq_trans (real_plus x (real_plus y (real_opp x)))                       (real_plus (real_plus x y) (real_opp x))                       y).
- apply (real_plus_assoc x y (real_opp x)).
- apply (real_eq_trans (real_plus (real_plus x y) (real_opp x))                         (real_plus (real_plus y x) (real_opp x))                         y).
+ apply (RealSetoid.real_eq_plus_compat (real_plus x y) (real_opp x)                                            (real_plus y x) (real_opp x)).
* apply (real_plus_comm x y).
* apply real_eq_refl.
+ apply (real_eq_trans (real_plus (real_plus y x) (real_opp x))                           (real_plus y (real_plus x (real_opp x)))                           y).
* apply real_eq_sym.
apply (real_plus_assoc y x (real_opp x)).
* apply (real_eq_trans (real_plus y (real_plus x (real_opp x)))                             (real_plus y real_zero)                             y).
-- apply (RealSetoid.real_eq_plus_compat y (real_plus x (real_opp x))                                                  y real_zero).
++ apply real_eq_refl.
++ apply (real_plus_opp x).
-- apply (real_plus_zero y).
Qed.

Lemma real_mult_diff_decomp : forall (Fh Fx Gh Gx df dg h : Real),  real_eq    (real_plus (real_mult Fh Gh)       (real_opp (real_plus (real_mult Fx Gx)          (real_mult (real_plus (real_mult df Gx) (real_mult Fx dg)) h))))    (real_plus       (real_plus (real_mult Fx           (real_plus Gh (real_opp (real_plus Gx (real_mult dg h)))))         (real_mult Gx           (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))))       (real_mult (real_plus Fh (real_opp Fx)) (real_plus Gh (real_opp Gx)))).
Proof.
intros Fh Fx Gh Gx df dg h.
set (D := real_plus (real_mult Fh Gh)         (real_opp (real_plus (real_mult Fx Gx)            (real_mult (real_plus (real_mult df Gx) (real_mult Fx dg)) h)))).
set (Y := real_mult (real_plus (real_mult df Gx) (real_mult Fx dg)) h).
set (Df := real_plus Fh (real_opp Fx)).
set (Dg := real_plus Gh (real_opp Gx)).
set (Af := real_plus Fh (real_opp (real_plus Fx (real_mult df h)))).
set (Ag := real_plus Gh (real_opp (real_plus Gx (real_mult dg h)))).
set (T1 := real_mult Fx Ag).
set (T2 := real_mult Gx Af).
set (T3 := real_mult Df Dg).
set (E1 := real_plus (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)                       (real_plus (real_opp (real_mult (real_mult df Gx) h))                                  (real_opp (real_mult (real_mult Fx dg) h)))).
set (E2 := real_plus (real_plus (real_plus (real_mult Df Gx)                                             (real_opp (real_mult (real_mult df Gx) h)))                                  (real_plus (real_mult Fx Dg)                                             (real_opp (real_mult (real_mult Fx dg) h))))                       T3).
set (E3 := real_plus (real_plus (real_mult Gx Af) (real_mult Fx Ag)) T3).
(* D == E1: split opp + expand Fh·Gh + cancel Fx·Gx + expand Y. *)  assert (HDE1 : real_eq D E1).
{    (* D == (Fh·Gh + opp(Fx·Gx)) + opp(Y) *)    assert (HD1 : real_eq D (real_plus (real_plus (real_mult Fh Gh) (real_opp (real_mult Fx Gx)))                                       (real_opp Y))).
{ unfold D.
apply (real_eq_trans        (real_plus (real_mult Fh Gh)           (real_opp (real_plus (real_mult Fx Gx) Y)))        (real_plus (real_mult Fh Gh)           (real_plus (real_opp (real_mult Fx Gx)) (real_opp Y)))        (real_plus (real_plus (real_mult Fh Gh) (real_opp (real_mult Fx Gx)))                   (real_opp Y))).
- apply (RealSetoid.real_eq_plus_compat (real_mult Fh Gh)               (real_opp (real_plus (real_mult Fx Gx) Y))               (real_mult Fh Gh)               (real_plus (real_opp (real_mult Fx Gx)) (real_opp Y))).
+ apply real_eq_refl.
+ apply (real_opp_plus (real_mult Fx Gx) Y).
- apply (real_plus_assoc (real_mult Fh Gh)                               (real_opp (real_mult Fx Gx))                               (real_opp Y)).
}    (* Fh == Fx + Df, Gh == Gx + Dg *)    assert (HFh : real_eq Fh (real_plus Fx Df)).
{ unfold Df.
apply real_eq_sym.
apply (real_plus_minus_cancel Fx Fh).
}    assert (HGh : real_eq Gh (real_plus Gx Dg)).
{ unfold Dg.
apply real_eq_sym.
apply (real_plus_minus_cancel Gx Gh).
}    (* Fh·Gh == ((Fx·Gx + Df·Gx) + Fx·Dg) + Df·Dg *)    assert (HFhGh : real_eq (real_mult Fh Gh)        (real_plus (real_plus (real_plus (real_mult Fx Gx) (real_mult Df Gx))                              (real_mult Fx Dg))                   (real_mult Df Dg))).
{ apply (real_eq_trans (real_mult Fh Gh)                           (real_mult (real_plus Fx Df) (real_plus Gx Dg))                           (real_plus (real_plus (real_plus (real_mult Fx Gx) (real_mult Df Gx))                                                 (real_mult Fx Dg))                                      (real_mult Df Dg))).
- apply (RealSetoid.real_eq_mult_compat Fh Gh                                              (real_plus Fx Df) (real_plus Gx Dg)).
+ exact HFh.
+ exact HGh.
- apply (real_eq_trans          (real_mult (real_plus Fx Df) (real_plus Gx Dg))          (real_plus (real_mult (real_plus Fx Df) Gx) (real_mult (real_plus Fx Df) Dg))          (real_plus (real_plus (real_plus (real_mult Fx Gx) (real_mult Df Gx))                                (real_mult Fx Dg))                     (real_mult Df Dg))).
+ apply (real_distrib (real_plus Fx Df) Gx Dg).
+ apply (real_eq_trans            (real_plus (real_mult (real_plus Fx Df) Gx) (real_mult (real_plus Fx Df) Dg))            (real_plus (real_plus (real_mult Fx Gx) (real_mult Df Gx))                       (real_plus (real_mult Fx Dg) (real_mult Df Dg)))            (real_plus (real_plus (real_plus (real_mult Fx Gx) (real_mult Df Gx))                                  (real_mult Fx Dg))                       (real_mult Df Dg))).
* apply (RealSetoid.real_eq_plus_compat                     (real_mult (real_plus Fx Df) Gx)                     (real_mult (real_plus Fx Df) Dg)                     (real_plus (real_mult Fx Gx) (real_mult Df Gx))                     (real_plus (real_mult Fx Dg) (real_mult Df Dg))).
-- apply real_eq_sym.
apply (real_distrib_r Fx Df Gx).
-- apply real_eq_sym.
apply (real_distrib_r Fx Df Dg).
* apply (real_plus_assoc              (real_plus (real_mult Fx Gx) (real_mult Df Gx))              (real_mult Fx Dg) (real_mult Df Dg)).
}    (* (Fh·Gh + opp(Fx·Gx)) == (Df·Gx + Fx·Dg) + T3: cancelling A := Fx·Gx. *)    assert (HC : real_eq (real_plus (real_mult Fh Gh) (real_opp (real_mult Fx Gx)))                         (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)).
{ apply (real_eq_trans        (real_plus (real_mult Fh Gh) (real_opp (real_mult Fx Gx)))        (real_plus (real_plus (real_plus (real_plus (real_mult Fx Gx) (real_mult Df Gx))                                         (real_mult Fx Dg))                              (real_mult Df Dg))                   (real_opp (real_mult Fx Gx)))        (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)).
- apply (RealSetoid.real_eq_plus_compat (real_mult Fh Gh)               (real_opp (real_mult Fx Gx))               (real_plus (real_plus (real_plus (real_mult Fx Gx) (real_mult Df Gx))                                     (real_mult Fx Dg))                          (real_mult Df Dg))               (real_opp (real_mult Fx Gx))).
+ exact HFhGh.
+ apply real_eq_refl.
- (* Cancellation: ((((A+B)+C)+D) + E) == (B+C)+D, with A := Fx·Gx and E := opp A. *)        set (A := real_mult Fx Gx).
set (B := real_mult Df Gx).
set (C := real_mult Fx Dg).
set (Dv := real_mult Df Dg).
set (E := real_opp A).
apply (real_eq_trans          (real_plus (real_plus (real_plus (real_plus A B) C) Dv) E)          (real_plus (real_plus (real_plus A B) (real_plus C Dv)) E)          (real_plus (real_plus B C) T3)).
{ apply (RealSetoid.real_eq_plus_compat                   (real_plus (real_plus (real_plus A B) C) Dv)                   E                   (real_plus (real_plus A B) (real_plus C Dv))                   E).
- apply real_eq_sym.
apply (real_plus_assoc (real_plus A B) C Dv).
- apply real_eq_refl.
}        { apply (real_eq_trans            (real_plus (real_plus (real_plus A B) (real_plus C Dv)) E)            (real_plus (real_plus (real_plus A B) (real_plus C E)) Dv)            (real_plus (real_plus B C) T3)).
- apply (real_eq_trans              (real_plus (real_plus (real_plus A B) (real_plus C Dv)) E)              (real_plus (real_plus A B) (real_plus (real_plus C Dv) E))              (real_plus (real_plus (real_plus A B) (real_plus C E)) Dv)).
+ apply real_eq_sym.
apply (real_plus_assoc (real_plus A B) (real_plus C Dv) E).
+ apply (real_eq_trans                (real_plus (real_plus A B) (real_plus (real_plus C Dv) E))                (real_plus (real_plus A B) (real_plus (real_plus C E) Dv))                (real_plus (real_plus (real_plus A B) (real_plus C E)) Dv)).
* apply (RealSetoid.real_eq_plus_compat                         (real_plus A B) (real_plus (real_plus C Dv) E)                         (real_plus A B) (real_plus (real_plus C E) Dv)).
-- apply real_eq_refl.
-- apply (real_eq_trans (real_plus (real_plus C Dv) E)                                        (real_plus C (real_plus Dv E))                                        (real_plus (real_plus C E) Dv)).
++ apply real_eq_sym.
apply (real_plus_assoc C Dv E).
++ apply (real_eq_trans (real_plus C (real_plus Dv E))                                           (real_plus C (real_plus E Dv))                                           (real_plus (real_plus C E) Dv)).
** apply (RealSetoid.real_eq_plus_compat C (real_plus Dv E)                                                               C (real_plus E Dv)).
{ apply real_eq_refl.
}                         { apply (real_plus_comm Dv E).
}                      
** apply (real_plus_assoc C E Dv).
* apply (real_plus_assoc (real_plus A B) (real_plus C E) Dv).
- apply (real_eq_trans              (real_plus (real_plus (real_plus A B) (real_plus C E)) Dv)              (real_plus (real_plus (real_plus A B) (real_plus E C)) Dv)              (real_plus (real_plus B C) T3)).
+ apply (RealSetoid.real_eq_plus_compat                       (real_plus (real_plus A B) (real_plus C E))                       Dv                       (real_plus (real_plus A B) (real_plus E C))                       Dv).
* apply (RealSetoid.real_eq_plus_compat                         (real_plus A B) (real_plus C E)                         (real_plus A B) (real_plus E C)).
-- apply real_eq_refl.
-- apply (real_plus_comm C E).
* apply real_eq_refl.
+ apply (real_eq_trans                (real_plus (real_plus (real_plus A B) (real_plus E C)) Dv)                (real_plus (real_plus (real_plus A E) (real_plus B C)) Dv)                (real_plus (real_plus B C) T3)).
* apply (RealSetoid.real_eq_plus_compat                         (real_plus (real_plus A B) (real_plus E C))                         Dv                         (real_plus (real_plus A E) (real_plus B C))                         Dv).
-- apply (real_plus_swap A B E C).
-- apply real_eq_refl.
* (* M3 == TARGET: A+E == 0, 0+(B+C) == B+C, Dv == T3 *)                apply (real_eq_trans                  (real_plus (real_plus (real_plus A E) (real_plus B C)) Dv)                  (real_plus (real_plus real_zero (real_plus B C)) Dv)                  (real_plus (real_plus B C) T3)).
-- apply (RealSetoid.real_eq_plus_compat                           (real_plus (real_plus A E) (real_plus B C))                           Dv                           (real_plus real_zero (real_plus B C))                           Dv).
++ apply (RealSetoid.real_eq_plus_compat (real_plus A E) (real_plus B C)                                                            real_zero (real_plus B C)).
** unfold E.
apply (real_plus_opp A).
** apply real_eq_refl.
++ apply real_eq_refl.
-- apply (RealSetoid.real_eq_plus_compat                           (real_plus real_zero (real_plus B C))                           Dv                           (real_plus B C)                           T3).
++ apply (real_eq_trans (real_plus real_zero (real_plus B C))                                           (real_plus (real_plus B C) real_zero)                                           (real_plus B C)).
** apply (real_plus_comm real_zero (real_plus B C)).
** apply (real_plus_zero (real_plus B C)).
++ unfold T3, Dv, Df, Dg.
apply real_eq_refl.
} }    (* D == ((B+C)+D) + opp(Y); opp(Y) == u+v ⟹ D == E1 *)    apply (real_eq_trans D        (real_plus (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)                   (real_opp Y))        E1).
{ apply (real_eq_trans D        (real_plus (real_plus (real_mult Fh Gh) (real_opp (real_mult Fx Gx)))                   (real_opp Y))        (real_plus (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)                   (real_opp Y))).
- exact HD1.
- apply (RealSetoid.real_eq_plus_compat                 (real_plus (real_mult Fh Gh) (real_opp (real_mult Fx Gx)))                 (real_opp Y)                 (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)                 (real_opp Y)).
+ exact HC.
+ apply real_eq_refl.
}    { apply (RealSetoid.real_eq_plus_compat               (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)               (real_opp Y)               (real_plus (real_plus (real_mult Df Gx) (real_mult Fx Dg)) T3)               (real_plus (real_opp (real_mult (real_mult df Gx) h))                          (real_opp (real_mult (real_mult Fx dg) h)))).
- apply real_eq_refl.
- (* opp(Y) == opp(df·Gx·h) + opp(Fx·dg·h) *)        apply (real_eq_trans (real_opp Y)               (real_opp (real_plus (real_mult (real_mult df Gx) h)                                    (real_mult (real_mult Fx dg) h)))               (real_plus (real_opp (real_mult (real_mult df Gx) h))                          (real_opp (real_mult (real_mult Fx dg) h)))).
+ apply (RealSetoid.real_eq_opp_compat Y                 (real_plus (real_mult (real_mult df Gx) h)                            (real_mult (real_mult Fx dg) h))).
unfold Y.
apply real_eq_sym.
apply (real_distrib_r (real_mult df Gx) (real_mult Fx dg) h).
+ apply (real_opp_plus (real_mult (real_mult df Gx) h)                               (real_mult (real_mult Fx dg) h)).
}  }  (* E1 == E2: real_plus_swap rearrangement. *)  assert (HE1E2 : real_eq E1 E2).
{    set (a := real_mult Df Gx).
set (b := real_mult Fx Dg).
set (c := T3).
set (u := real_opp (real_mult (real_mult df Gx) h)).
set (v := real_opp (real_mult (real_mult Fx dg) h)).
(* Lemma 1: ((a+b)+c)+(u+v) == (a+b)+((c+u)+v). *)    assert (H1 : real_eq      (real_plus (real_plus (real_plus a b) c) (real_plus u v))      (real_plus (real_plus a b) (real_plus (real_plus c u) v))).
{ apply (real_eq_trans        (real_plus (real_plus (real_plus a b) c) (real_plus u v))        (real_plus (real_plus a b) (real_plus c (real_plus u v)))        (real_plus (real_plus a b) (real_plus (real_plus c u) v))).
- apply real_eq_sym.
apply (real_plus_assoc (real_plus a b) c (real_plus u v)).
- apply (RealSetoid.real_eq_plus_compat (real_plus a b)               (real_plus c (real_plus u v))               (real_plus a b)               (real_plus (real_plus c u) v)).
+ apply real_eq_refl.
+ apply (real_plus_assoc c u v).
}    (* Lemma 2: (a+b)+((c+u)+v) == ((a+u)+(b+v))+c. *)    assert (H2 : real_eq      (real_plus (real_plus a b) (real_plus (real_plus c u) v))      (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
{ apply (real_eq_trans        (real_plus (real_plus a b) (real_plus (real_plus c u) v))        (real_plus (real_plus (real_plus a b) (real_plus c u)) v)        (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
- apply (real_plus_assoc (real_plus a b) (real_plus c u) v).
- (* (((a+b)+(c+u))+v == ((a+u)+(b+v))+c *)        apply (real_eq_trans          (real_plus (real_plus (real_plus a b) (real_plus c u)) v)          (real_plus (real_plus (real_plus a b) (real_plus u c)) v)          (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
+ apply (RealSetoid.real_eq_plus_compat                   (real_plus (real_plus a b) (real_plus c u))                   v                   (real_plus (real_plus a b) (real_plus u c))                   v).
* apply (RealSetoid.real_eq_plus_compat (real_plus a b) (real_plus c u)                                                  (real_plus a b) (real_plus u c)).
-- apply real_eq_refl.
-- apply (real_plus_comm c u).
* apply real_eq_refl.
+ (* (X+Y)+v == ((a+u)+(b+v))+c: swap, then split out c. *)          apply (real_eq_trans            (real_plus (real_plus (real_plus a b) (real_plus u c)) v)            (real_plus (real_plus (real_plus a u) (real_plus b c)) v)            (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
* apply (RealSetoid.real_eq_plus_compat                     (real_plus (real_plus a b) (real_plus u c))                     v                     (real_plus (real_plus a u) (real_plus b c))                     v).
-- apply (real_plus_swap a b u c).
-- apply real_eq_refl.
* (* ((a+u)+(b+c))+v == ((a+u)+(b+v))+c *)            apply (real_eq_trans              (real_plus (real_plus (real_plus a u) (real_plus b c)) v)              (real_plus (real_plus a u) (real_plus (real_plus b c) v))              (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
-- apply real_eq_sym.
apply (real_plus_assoc (real_plus a u) (real_plus b c) v).
-- apply (real_eq_trans                (real_plus (real_plus a u) (real_plus (real_plus b c) v))                (real_plus (real_plus a u) (real_plus b (real_plus c v)))                (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
++ apply (RealSetoid.real_eq_plus_compat (real_plus a u)                        (real_plus (real_plus b c) v)                        (real_plus a u)                        (real_plus b (real_plus c v))).
** apply real_eq_refl.
** apply real_eq_sym.
apply (real_plus_assoc b c v).
++ apply (real_eq_trans                   (real_plus (real_plus a u) (real_plus b (real_plus c v)))                   (real_plus (real_plus a u) (real_plus b (real_plus v c)))                   (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
** apply (RealSetoid.real_eq_plus_compat (real_plus a u)                           (real_plus b (real_plus c v))                           (real_plus a u)                           (real_plus b (real_plus v c))).
{ apply real_eq_refl.
}                     { apply (RealSetoid.real_eq_plus_compat b (real_plus c v)                                                              b (real_plus v c)).
{ apply real_eq_refl.
}                        { apply (real_plus_comm c v).
} }                  
** apply (real_eq_trans                      (real_plus (real_plus a u) (real_plus b (real_plus v c)))                      (real_plus (real_plus a u) (real_plus (real_plus b v) c))                      (real_plus (real_plus (real_plus a u) (real_plus b v)) c)).
{ apply (RealSetoid.real_eq_plus_compat (real_plus a u)                              (real_plus b (real_plus v c))                              (real_plus a u)                              (real_plus (real_plus b v) c)).
{ apply real_eq_refl.
}                       { apply (real_plus_assoc b v c).
} }                      { apply (real_plus_assoc (real_plus a u) (real_plus b v) c).
} }    (* Assembly: E1 == the H1 start == the H2 end == E2. *)    apply (real_eq_trans      (real_plus (real_plus (real_plus a b) c) (real_plus u v))      (real_plus (real_plus a b) (real_plus (real_plus c u) v))      E2).
- exact H1.
- apply (real_eq_trans        (real_plus (real_plus a b) (real_plus (real_plus c u) v))        (real_plus (real_plus (real_plus a u) (real_plus b v)) c)        E2).
+ exact H2.
+ unfold E1, E2.
apply real_eq_refl.
}  (* E2 == E3: a+u == Gx·Af, b+v == Fx·Ag *)  assert (HE2E3 : real_eq E2 E3).
{    assert (Hau : real_eq (real_plus (real_mult Df Gx)                                     (real_opp (real_mult (real_mult df Gx) h)))                          (real_mult Gx Af)).
{ (* Df·Gx + opp(df·Gx·h) == Gx·(Df + opp(df·h)) == Gx·Af *)      apply (real_eq_trans        (real_plus (real_mult Df Gx)                   (real_opp (real_mult (real_mult df Gx) h)))        (real_plus (real_mult Df Gx) (real_mult (real_opp (real_mult df h)) Gx))        (real_mult Gx Af)).
- apply (RealSetoid.real_eq_plus_compat                 (real_mult Df Gx)                 (real_opp (real_mult (real_mult df Gx) h))                 (real_mult Df Gx)                 (real_mult (real_opp (real_mult df h)) Gx)).
+ apply real_eq_refl.
+ (* opp(df·Gx·h) == opp(df·h)·Gx: opp_mult_r + assoc/comm chain. *)          apply (real_eq_trans            (real_opp (real_mult (real_mult df Gx) h))            (real_opp (real_mult (real_mult df h) Gx))            (real_mult (real_opp (real_mult df h)) Gx)).
* apply (RealSetoid.real_eq_opp_compat                     (real_mult (real_mult df Gx) h)                     (real_mult (real_mult df h) Gx)).
apply (real_eq_trans (real_mult (real_mult df Gx) h)                                 (real_mult df (real_mult Gx h))                                 (real_mult (real_mult df h) Gx)).
-- apply real_eq_sym.
apply (real_mult_assoc df Gx h).
-- apply (real_eq_trans (real_mult df (real_mult Gx h))                                    (real_mult df (real_mult h Gx))                                    (real_mult (real_mult df h) Gx)).
++ apply (RealSetoid.real_eq_mult_compat df (real_mult Gx h)                                                        df (real_mult h Gx)).
** apply real_eq_refl.
** apply (real_mult_comm Gx h).
++ apply (real_mult_assoc df h Gx).
* apply (real_opp_mult_r (real_mult df h) Gx).
- (* (Df + opp(df·h))·Gx == Gx·Af *)        apply (real_eq_trans          (real_plus (real_mult Df Gx) (real_mult (real_opp (real_mult df h)) Gx))          (real_mult (real_plus Df (real_opp (real_mult df h))) Gx)          (real_mult Gx Af)).
+ apply (real_distrib_r Df (real_opp (real_mult df h)) Gx).
+ apply (real_eq_trans            (real_mult (real_plus Df (real_opp (real_mult df h))) Gx)            (real_mult (real_plus Fh (real_opp (real_plus Fx (real_mult df h)))) Gx)            (real_mult Gx Af)).
* apply (RealSetoid.real_eq_mult_compat                     (real_plus Df (real_opp (real_mult df h)))                     Gx                     (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))                     Gx).
-- (* Df + opp(df·h) == Fh + opp(Fx + df·h) *)               unfold Df.
apply (real_eq_trans                 (real_plus (real_plus Fh (real_opp Fx)) (real_opp (real_mult df h)))                 (real_plus Fh (real_plus (real_opp Fx) (real_opp (real_mult df h))))                 (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))).
++ apply real_eq_sym.
apply (real_plus_assoc Fh (real_opp Fx)                                                            (real_opp (real_mult df h))).
++ apply (RealSetoid.real_eq_plus_compat Fh                        (real_plus (real_opp Fx) (real_opp (real_mult df h)))                        Fh                        (real_opp (real_plus Fx (real_mult df h)))).
** apply real_eq_refl.
** apply real_eq_sym.
apply (real_opp_plus Fx (real_mult df h)).
-- apply real_eq_refl.
* unfold Af.
apply (real_mult_comm               (real_plus Fh (real_opp (real_plus Fx (real_mult df h)))) Gx).
}    assert (Hbv : real_eq (real_plus (real_mult Fx Dg)                                     (real_opp (real_mult (real_mult Fx dg) h)))                          (real_mult Fx Ag)).
{ (* Fx·Dg + opp(Fx·dg·h) == Fx·(Dg + opp(dg·h)) == Fx·Ag *)      apply (real_eq_trans        (real_plus (real_mult Fx Dg)                   (real_opp (real_mult (real_mult Fx dg) h)))        (real_plus (real_mult Fx Dg) (real_mult Fx (real_opp (real_mult dg h))))        (real_mult Fx Ag)).
- apply (RealSetoid.real_eq_plus_compat                 (real_mult Fx Dg)                 (real_opp (real_mult (real_mult Fx dg) h))                 (real_mult Fx Dg)                 (real_mult Fx (real_opp (real_mult dg h)))).
+ apply real_eq_refl.
+ (* opp(Fx·dg·h) == Fx·opp(dg·h): opp_mult + assoc *)          apply (real_eq_trans            (real_opp (real_mult (real_mult Fx dg) h))            (real_opp (real_mult Fx (real_mult dg h)))            (real_mult Fx (real_opp (real_mult dg h)))).
* apply (RealSetoid.real_eq_opp_compat                     (real_mult (real_mult Fx dg) h)                     (real_mult Fx (real_mult dg h))).
apply real_eq_sym.
apply (real_mult_assoc Fx dg h).
* apply (real_opp_mult Fx (real_mult dg h)).
- apply (real_eq_trans          (real_plus (real_mult Fx Dg) (real_mult Fx (real_opp (real_mult dg h))))          (real_mult Fx (real_plus Dg (real_opp (real_mult dg h))))          (real_mult Fx Ag)).
+ apply real_eq_sym.
apply (real_distrib Fx Dg (real_opp (real_mult dg h))).
+ apply (RealSetoid.real_eq_mult_compat Fx                 (real_plus Dg (real_opp (real_mult dg h)))                 Fx                 (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))).
* apply real_eq_refl.
* unfold Dg.
apply (real_eq_trans              (real_plus (real_plus Gh (real_opp Gx)) (real_opp (real_mult dg h)))              (real_plus Gh (real_plus (real_opp Gx) (real_opp (real_mult dg h))))              (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))).
-- apply real_eq_sym.
apply (real_plus_assoc Gh (real_opp Gx)                                                           (real_opp (real_mult dg h))).
-- apply (RealSetoid.real_eq_plus_compat Gh                     (real_plus (real_opp Gx) (real_opp (real_mult dg h)))                     Gh                     (real_opp (real_plus Gx (real_mult dg h)))).
++ apply real_eq_refl.
++ apply real_eq_sym.
apply (real_opp_plus Gx (real_mult dg h)).
}    apply (real_eq_trans E2 E3 E3).
- unfold E2, E3.
apply (RealSetoid.real_eq_plus_compat               (real_plus (real_plus (real_mult Df Gx)                                     (real_opp (real_mult (real_mult df Gx) h)))                          (real_plus (real_mult Fx Dg)                                     (real_opp (real_mult (real_mult Fx dg) h))))               T3               (real_plus (real_mult Gx Af) (real_mult Fx Ag))               T3).
+ apply (RealSetoid.real_eq_plus_compat                 (real_plus (real_mult Df Gx)                            (real_opp (real_mult (real_mult df Gx) h)))                 (real_plus (real_mult Fx Dg)                            (real_opp (real_mult (real_mult Fx dg) h)))                 (real_mult Gx Af)                 (real_mult Fx Ag)).
* exact Hau.
* exact Hbv.
+ apply real_eq_refl.
- apply real_eq_refl.
}  (* E3 == (T1 + T2) + T3: reordering by comm. *)  assert (HE3T : real_eq E3 (real_plus (real_plus T1 T2) T3)).
{    unfold E3.
apply (RealSetoid.real_eq_plus_compat             (real_plus (real_mult Gx Af) (real_mult Fx Ag))             T3             (real_plus T1 T2)             T3).
- unfold T1, T2.
apply (real_plus_comm (real_mult Gx Af) (real_mult Fx Ag)).
- apply real_eq_refl.
}  (* Assembly. *)  apply (real_eq_trans D E1 (real_plus (real_plus T1 T2) T3)).
- exact HDE1.
- apply (real_eq_trans E1 E2 (real_plus (real_plus T1 T2) T3)).
+ exact HE1E2.
+ apply (real_eq_trans E2 E3 (real_plus (real_plus T1 T2) T3)).
* exact HE2E3.
* exact HE3T.
Qed. (* ============ 5. mult pointwise lemmas (the β ≤ 1 bound and control of |h|²) ============ *)(* 5a: e ≤ k·(1+e) (e > 0, k > 0, 1 < k) — the key step for β ≤ 1   Pointwise: k_n(1+e_n) − e_n = k_n + e_n(k_n−1) ≥ k_n > k0 > k0/2. *)
Lemma real_le_eps_Kone : forall (e k : Real)  (He : real_lt real_zero e) (Hk : real_lt real_zero k)  (Hk1 : real_lt real_one k),  real_le e (real_mult k (real_plus real_one e)).
Proof.
intros e k He Hk Hk1.
destruct He as [e0 [He0 [Ne HNe]]].
destruct Hk as [k0 [Hk0 [Nk HNk]]].
destruct Hk1 as [c1 [Hc1 [N1 HN1]]].
apply (RealSetoid.real_lt_le_iff_req e (real_mult k (real_plus real_one e))).
left.
unfold real_lt.
exists (k0 / 2)%Q.
split.
- apply Qlt_to_QltT.
apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Hk0].
- exists (Nat.max Ne (Nat.max Nk N1)).
intros n Hn.
apply NatLe_drop in Hn.
assert (Hne : (Ne <= n)%nat) by lia.
assert (Hnk : (Nk <= n)%nat) by lia.
assert (Hn1 : (N1 <= n)%nat) by lia.
apply Qlt_to_QltT.
set (en := projT1 e n).
set (kn := projT1 k n).
assert (Hkn : Qlt k0 kn).
{ assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
apply (Qlt_le_trans _ (kn - projT1 real_zero n) _).
- apply QltT_to_Qlt.
exact (HNk n (NatLe_lift _ _ Hnk)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hk1n : Qle 1 kn).
{ apply QleT'_to_Qle. apply (q_lt_diff_le c1 1 kn).
- exact Hc1.
- exact (HN1 n (NatLe_lift _ _ Hn1)).
}    assert (Hen : Qle 0 en).
{ apply (Qlt_le_weak 0 en).
apply (Qlt_trans _ e0 _).
- apply QltT_to_Qlt.
exact He0.
- assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
apply (Qlt_le_trans _ (en - projT1 real_zero n) _).
+ apply QltT_to_Qlt.
exact (HNe n (NatLe_lift _ _ Hne)).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    (* Difference == kn(1+en) − en ≥ kn > k0 > k0/2. *)    assert (Hproj : projT1 (real_mult k (real_plus real_one e)) n == kn * (1 + en)).
{ unfold kn, en.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj k (real_plus real_one e) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one e n)).
cbn [projT1].
reflexivity.
}    setoid_rewrite Hproj.
apply (Qlt_le_trans _ kn _).
{ apply (Qlt_le_trans _ k0 _).
{ apply QltT_to_Qlt.
apply (q_half_lt_self k0).
exact Hk0.
}      { apply Qlt_le_weak.
exact Hkn.
} }    { (* kn ≤ kn(1+en) − en: the difference == en(kn−1) ≥ 0. *)      assert (Heq : kn * (1 + en) - en == kn + en * (kn - 1)) by ring.
rewrite Heq.
apply (Qle_plus_nonneg_r kn (en * (kn - 1))).
apply (Qmult_le_0_compat en (kn - 1)).
{ exact Hen.
}      { apply (proj1 (Qle_minus_iff 1 kn)).
exact Hk1n.
} }
Qed. (* 5b: A·|h|² ≤ (A·eps3)·|h| + eps' (with |h| < eps3, 0 < A, 0 < eps')   Pointwise: A_n ≥ A0 > 0, |h|_n ≤ eps3_n, |h|_n ≥ 0 give difference ≥ eps'_0/2. *)
Lemma real_abs_h_sq_le_eps : forall (A h eps3 eps' : Real),  real_lt real_zero A -> real_lt (real_abs h) eps3 -> real_lt real_zero eps' ->  real_le (real_mult A (real_mult (real_abs h) (real_abs h)))          (real_plus (real_mult (real_mult A eps3) (real_abs h)) eps').
Proof.
intros A h eps3 eps' HA Hh3 Heps'.
destruct HA as [A0 [HA0 [NA HNA]]].
destruct Hh3 as [c1 [Hc1 [N1 HN1]]].
destruct Heps' as [e0 [He0 [Ne HNe]]].
apply (RealSetoid.real_lt_le_iff_req    (real_mult A (real_mult (real_abs h) (real_abs h)))    (real_plus (real_mult (real_mult A eps3) (real_abs h)) eps')).
left.
unfold real_lt.
exists (e0 / 2)%Q.
split.
- apply Qlt_to_QltT.
apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact He0].
- exists (Nat.max Ne (Nat.max NA N1)).
intros n Hn.
apply NatLe_drop in Hn.
assert (Hne : (Ne <= n)%nat) by lia.
assert (Hna : (NA <= n)%nat) by lia.
assert (Hn1 : (N1 <= n)%nat) by lia.
apply Qlt_to_QltT.
set (An := projT1 A n).
set (hn := projT1 (real_abs h) n).
set (e3n := projT1 eps3 n).
set (en' := projT1 eps' n).
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
assert (HAn : Qlt A0 An).
{ apply (Qlt_le_trans _ (An - projT1 real_zero n) _).
- apply QltT_to_Qlt.
exact (HNA n (NatLe_lift _ _ Hna)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hhn : Qle 0 hn).
{ unfold hn.
rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
apply Qabs_nonneg.
}    assert (Hhne : Qle hn e3n).
{ unfold hn, e3n.
apply QleT'_to_Qle. apply (q_lt_diff_le c1 hn e3n).
- exact Hc1.
- assert (Hq0 : Qlt c1 (projT1 eps3 n - projT1 (real_abs h) n)).
{ apply QltT_to_Qlt.
exact (HN1 n (NatLe_lift _ _ Hn1)).
}        apply Qlt_to_QltT.
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)) in Hq0.
unfold hn, e3n.
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
exact Hq0.
}    assert (Hepsn : Qlt e0 en').
{ unfold en'.
apply (Qlt_le_trans _ (projT1 eps' n - projT1 real_zero n) _).
- apply QltT_to_Qlt.
exact (HNe n (NatLe_lift _ _ Hne)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hproj1 : projT1 (real_mult (real_mult A eps3) (real_abs h)) n == (An * e3n) * hn).
{ unfold An, e3n, hn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult A eps3) (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj A eps3 n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
reflexivity.
}    assert (Hproj2 : projT1 (real_mult A (real_mult (real_abs h) (real_abs h))) n == An * (hn * hn)).
{ unfold An, hn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj A (real_mult (real_abs h) (real_abs h)) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_abs h) (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
reflexivity.
}    assert (Hproj3 : projT1 (real_plus (real_mult (real_mult A eps3) (real_abs h)) eps') n == (An * e3n) * hn + en').
{ setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult A eps3) (real_abs h)) eps' n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult A eps3) (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj A eps3 n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
unfold An, e3n, en', hn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
reflexivity.
}    (* P_n − Q_n == ((An·e3n)·hn + en') − An·(hn·hn) (a Qeq restatement, avoiding setoid_rewrite inside QltT). *)    assert (Hdiff : Qeq      (projT1 (real_plus (real_mult (real_mult A eps3) (real_abs h)) eps') n       - projT1 (real_mult A (real_mult (real_abs h) (real_abs h))) n)      (((An * e3n) * hn + en') - An * (hn * hn))).
{ unfold Qminus.
apply (Qplus_comp        (projT1 (real_plus (real_mult (real_mult A eps3) (real_abs h)) eps') n)        ((An * e3n) * hn + en') Hproj3        (Qopp (projT1 (real_mult A (real_mult (real_abs h) (real_abs h))) n))        (Qopp (An * (hn * hn)))).
- apply (Qopp_comp          (projT1 (real_mult A (real_mult (real_abs h) (real_abs h))) n)          (An * (hn * hn))).
exact Hproj2.
}    (* Main chain: QltT (e0/2) (M − N), with M := ((An·e3n)·hn + en') and N := An·(hn·hn). *)    assert (Hmain : QltT (e0 / 2) (((An * e3n) * hn + en') - An * (hn * hn))).
{ apply Qlt_to_QltT.
apply (Qlt_le_trans _ (en' - 0) _).
- (* e0/2 < en' − 0 == en' *)        apply (Qlt_le_trans _ en' _).
+ apply (Qlt_trans _ e0 _).
* apply QltT_to_Qlt.
apply (q_half_lt_self e0).
exact He0.
* exact Hepsn.
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
- (* en' − 0 ≤ M − N: M − N − (en' − 0) == An·hn·(e3n−hn) ≥ 0 *)        apply (Qle_trans _ (en' + (An * hn * (e3n - hn))) _).
apply (Qle_trans _ en' _).
{ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}        { apply (Qle_plus_nonneg_r en' (An * hn * (e3n - hn))).
apply (Qmult_le_0_compat (An * hn) (e3n - hn)).
* apply (Qmult_le_0_compat An hn).
-- apply (Qlt_le_weak 0 An).
apply (Qlt_trans _ A0 _).
apply QltT_to_Qlt.
exact HA0.
exact HAn.
-- exact Hhn.
* apply (proj1 (Qle_minus_iff hn e3n)).
exact Hhne.
}        + apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
unfold An, e3n, en', hn.
cbn [projT1 real_abs].
ring.
}    (* Goal: QltT (e0/2) (P_n − Q_n) — restated back to the original projection shape via Hdiff. *)    apply (Qlt_le_trans _ (((An * e3n) * hn + en') - An * (hn * hn)) _).
{ exact (QltT_to_Qlt _ _ Hmain).
}    { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
apply (Qeq_sym _ _).
exact Hdiff.
}
Qed. (* ============ 6. Multiplicative differentiability (real_differentiable_mult, Bishop per-eps) ============   rdf := f'·g + f·g'; D == f·A_g + g·A_f + Δf·Δg (real_mult_diff_decomp)   Budget: eps4 := quarter·eps (|f·A_g| and |g·A_f| each get eps4|h| + Mf·β / Mg·β)         eps2 := half·eps (|Δf·Δg| ≤ eps2|h| + shares)   Mf := 1+|f x|, Mg := 1+|g x|, Mfp := 1+|df x|, Mgp := 1+|dg x|   eps_f := inv(Mg)·eps4, eps_g := inv(Mf)·eps4 (Mf·eps_g == eps4 and Mg·eps_f == eps4 exactly)   Lf := |df|+eps_f, Lg := |dg|+eps_g, Den := Lf·Lg   K := 64·(Mf+Mg+Mfp+Mgp+1); β := eps'·inv(K(1+eps')) (β ≤ 1: real_le_eps_Kone)   γ := half·β (triangle margin); δ := min(min δf δg, min eps3 (min dKf dKg))   eps3 := inv(Den)·eps2 (the |h|² term); dKf := K·inv(8Lf), dKg := K·inv(8Lg) (β-linear terms absorbed via δ)   margin marg := eps'·inv(64K) (product/triangle margin). *)(* 6a: s·a ≤ s·(a+b+c+d+1) (s, a, b, c, d > 0) — the pointwise basis for K ≥ 64·Mf/Mg   Pointwise: the difference == s_n·(b_n+c_n+d_n+1) ≥ s0/2 > 0. *)
Lemma real_scal_sum_ge : forall (s a b c d : Real)  (Hs : real_lt real_zero s) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b)  (Hc : real_lt real_zero c) (Hd : real_lt real_zero d),  real_le (real_mult s a)          (real_mult s (real_plus (real_plus (real_plus (real_plus a b) c) d) real_one)).
Proof.
intros s a b c d Hs Ha Hb Hc Hd.
destruct Hs as [s0 [Hs0 [Ns HNs]]].
destruct Ha as [a0 [Ha0 [Na HNa]]].
destruct Hb as [b0 [Hb0 [Nb HNb]]].
destruct Hc as [c0 [Hc0 [Nc HNc]]].
destruct Hd as [d0 [Hd0 [Nd HNd]]].
apply (RealSetoid.real_lt_le_iff_req (real_mult s a)          (real_mult s (real_plus (real_plus (real_plus (real_plus a b) c) d) real_one))).
left.
unfold real_lt.
exists (s0 / 2)%Q.
split.
- apply Qlt_to_QltT.
apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Hs0].
- exists (Nat.max Ns (Nat.max Na (Nat.max Nb (Nat.max Nc Nd)))).
intros n Hn.
apply NatLe_drop in Hn.
assert (Hns : (Ns <= n)%nat) by lia.
assert (Hna : (Na <= n)%nat) by lia.
assert (Hnb : (Nb <= n)%nat) by lia.
assert (Hnc : (Nc <= n)%nat) by lia.
assert (Hnd : (Nd <= n)%nat) by lia.
apply Qlt_to_QltT.
set (sn := projT1 s n).
set (an := projT1 a n).
set (bn := projT1 b n).
set (cn := projT1 c n).
set (dn := projT1 d n).
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
assert (Hsn : Qlt (s0 / 2) sn).
{ apply (Qlt_trans _ s0 _).
- apply QltT_to_Qlt.
apply (q_half_lt_self s0).
exact Hs0.
- apply (Qlt_le_trans _ (sn - projT1 real_zero n) _).
+ apply QltT_to_Qlt.
exact (HNs n (NatLe_lift _ _ Hns)).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hbn : Qle 0 bn).
{ apply Qlt_le_weak.
apply (Qlt_trans _ b0 _).
- apply QltT_to_Qlt.
exact Hb0.
- apply (Qlt_le_trans _ (bn - projT1 real_zero n) _).
+ apply QltT_to_Qlt.
exact (HNb n (NatLe_lift _ _ Hnb)).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hcn : Qle 0 cn).
{ apply Qlt_le_weak.
apply (Qlt_trans _ c0 _).
- apply QltT_to_Qlt.
exact Hc0.
- apply (Qlt_le_trans _ (cn - projT1 real_zero n) _).
+ apply QltT_to_Qlt.
exact (HNc n (NatLe_lift _ _ Hnc)).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hdn : Qle 0 dn).
{ apply Qlt_le_weak.
apply (Qlt_trans _ d0 _).
- apply QltT_to_Qlt.
exact Hd0.
- apply (Qlt_le_trans _ (dn - projT1 real_zero n) _).
+ apply QltT_to_Qlt.
exact (HNd n (NatLe_lift _ _ Hnd)).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite Hz.
ring.
}    assert (Hproj1 : projT1 (real_mult s a) n == sn * an).
{ unfold sn, an.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj s a n)).
reflexivity.
}    assert (Hproj2 : projT1 (real_mult s (real_plus (real_plus (real_plus (real_plus a b) c) d) real_one)) n                    == sn * (an + bn + cn + dn + 1)).
{ unfold sn, an, bn, cn, dn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj s (real_plus (real_plus (real_plus (real_plus a b) c) d) real_one) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_plus a b) c) d) real_one n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus a b) c) d n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus a b) c n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj a b n)).
cbn [projT1].
reflexivity.
}    setoid_rewrite Hproj1.
setoid_rewrite Hproj2.
(* s0/2 < sn·(an+bn+cn+dn+1) − sn·an == sn·(bn+cn+dn+1) ≥ s0/2·1 *)    apply (Qlt_le_trans _ (sn * (bn + cn + dn + 1)) _).
assert (Hsum1 : Qle 1 (bn + cn + dn + 1)).
{ apply (Qle_trans _ (1 + (bn + cn + dn)) _).
- apply (Qplus_le_compat 1 1 0 (bn + cn + dn)).
+ apply Qle_refl.
+ apply (Qle_trans _ (bn + (cn + dn)) _).
* apply (Qplus_le_compat 0 bn 0 (cn + dn)).
-- exact Hbn.
-- apply (Qplus_le_compat 0 cn 0 dn).
++ exact Hcn.
++ exact Hdn.
* apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}    assert (Hsn0 : Qle 0 sn).
{ apply (Qlt_le_weak 0 sn).
apply (Qlt_trans _ (s0 / 2) _).
- apply QltT_to_Qlt.
apply (q_half_pos s0).
exact Hs0.
- exact Hsn.
}    (* Main chain: s0/2 < sn·(an+bn+cn+dn+1) − sn·an == sn·(bn+cn+dn+1) ≥ s0/2·1. *)    assert (Hmain : Qlt (s0 / 2) (sn * (bn + cn + dn + 1))).
{ apply (Qlt_le_trans _ (sn * 1) _).
{ apply (Qlt_le_trans _ sn _).
{ exact Hsn.
}        { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
} }      { apply (Qle_trans _ (1 * sn) _).
{ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}        { apply (Qle_trans _ ((bn + cn + dn + 1) * sn) _).
{ apply (Qmult_le_compat_r 1 (bn + cn + dn + 1) sn).
{ exact Hsum1.
}            { exact Hsn0.
} }          { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
} } } }    (* Subgoal 1: Qlt (s0/2) (sn·(bn+cn+dn+1)) — by Hmain. *)    { exact Hmain.
}    (* Subgoal 2: Qle (sn·(bn+cn+dn+1)) (sn·(an+bn+cn+dn+1) − sn·an) — an identity. *)    { apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
unfold Qminus.
ring.
}
Qed. (* ============ 6b0: mult auxiliary — M·eps_g == eps4-style identities (Mf := 1+|Fx|, eps_g := inv(Mf)·eps4)   Verified template (from the T1-min development): assoc + real_inv_pos_correct + comm/one bridges. *)
Lemma real_M_inv_absorb : forall (M x : Real) (HM : real_lt real_zero M),  real_eq (real_mult M (real_mult (real_inv_pos M HM) x)) x.
Proof.
intros M x HM.
apply (real_eq_trans (real_mult M (real_mult (real_inv_pos M HM) x))                       (real_mult (real_mult M (real_inv_pos M HM)) x)                       x).
- apply (real_mult_assoc M (real_inv_pos M HM) x).
- apply (real_eq_trans (real_mult (real_mult M (real_inv_pos M HM)) x)                         (real_mult real_one x)                         x).
+ apply (RealSetoid.real_eq_mult_compat (real_mult M (real_inv_pos M HM)) x real_one x).
* exact (real_inv_pos_correct M HM).
* apply real_eq_refl.
+ apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
* apply (real_mult_comm real_one x).
* apply (real_mult_one x).
Qed. (* ============ 6b1: |f·A_g| ≤ Mf·(eps_g|h|+β_gamma) + marg (the first part of the T1 upper bound)   |f·A_g| == |f|·|A_g| (real_abs_mult_req); |f|≤Mf (real_abs_le_plus_one), |A_g|≤eps_g|h|+β_gamma (HAg)   so real_abs_prod_le_eps gives |f|·|A_g| ≤ Mf·(eps_g|h|+β_gamma) + marg. *)
Lemma real_prod_abs_le_two : forall (a b M B eps : Real),  real_lt real_zero eps ->  real_le (real_abs a) M ->  real_le (real_abs b) B ->  real_le (real_abs (real_mult a b))          (real_plus (real_mult M B) eps).
Proof.
intros a b M B eps Heps HMa HMB.
apply (real_le_trans (real_abs (real_mult a b))                       (real_mult (real_abs a) (real_abs b))                       (real_plus (real_mult M B) eps)).
- apply RealSetoid.real_eq_le.
apply (real_abs_mult_req a b).
- exact (real_abs_prod_le_eps a b M B eps Heps HMa HMB).
Qed. (* ============ 6b2: 8Lf·|h| ≤ K (from |h| < K·inv(8Lf) == dKf; absorbing the T3 β-linear term)   |h| < K·inv(8Lf) gives (8Lf)·|h| < (8Lf)·(K·inv(8Lf)) == K (mult_lt_compat_l + absorbing the inverse). *)
Lemma real_dKf_absorb : forall (K L h : Real) (HK : real_lt real_zero K)  (H8L : real_lt real_zero (real_mult (real_const (Z.of_nat 8 # 1)) L)),  real_lt (real_abs h)          (real_mult K (real_inv_pos (real_mult (real_const (Z.of_nat 8 # 1)) L) H8L)) ->  real_le (real_mult (real_mult (real_const (Z.of_nat 8 # 1)) L) (real_abs h)) K.
Proof.
intros K L h HK H8L Hh.
set (e8 := real_const (Z.of_nat 8 # 1)).
apply (RealSetoid.real_lt_le_iff_req (real_mult (real_mult e8 L) (real_abs h)) K).
left.
apply (real_lt_eq_lt (real_mult (real_mult e8 L) (real_abs h))                       (real_mult (real_mult e8 L) (real_mult K (real_inv_pos (real_mult e8 L) H8L)))                       K).
- apply (real_mult_lt_compat_l (real_abs h) (real_mult K (real_inv_pos (real_mult e8 L) H8L)) (real_mult e8 L)).
+ unfold e8 in Hh.
exact Hh.
+ exact H8L.
- (* (8L)·(K·inv(8L)) == (8L)·(inv(8L)·K) == K *)    apply (real_eq_trans (real_mult (real_mult e8 L) (real_mult K (real_inv_pos (real_mult e8 L) H8L)))                         (real_mult (real_mult e8 L) (real_mult (real_inv_pos (real_mult e8 L) H8L) K))                         K).
+ apply (RealSetoid.real_eq_mult_compat (real_mult e8 L) (real_mult K (real_inv_pos (real_mult e8 L) H8L))                                            (real_mult e8 L) (real_mult (real_inv_pos (real_mult e8 L) H8L) K)).
* apply real_eq_refl.
* apply (real_mult_comm K (real_inv_pos (real_mult e8 L) H8L)).
+ apply (real_eq_trans (real_mult (real_mult e8 L) (real_mult (real_inv_pos (real_mult e8 L) H8L) K))                           (real_mult (real_mult (real_mult e8 L) (real_inv_pos (real_mult e8 L) H8L)) K)                           K).
* apply (real_mult_assoc (real_mult e8 L) (real_inv_pos (real_mult e8 L) H8L) K).
* apply (real_eq_trans (real_mult (real_mult (real_mult e8 L) (real_inv_pos (real_mult e8 L) H8L)) K)                             (real_mult real_one K)                             K).
-- apply (RealSetoid.real_eq_mult_compat (real_mult (real_mult e8 L) (real_inv_pos (real_mult e8 L) H8L)) K real_one K).
++ exact (real_inv_pos_correct (real_mult e8 L) H8L).
++ apply real_eq_refl.
-- apply (real_eq_trans (real_mult real_one K) (real_mult K real_one) K).
++ apply (real_mult_comm real_one K).
++ apply (real_mult_one K).
Qed. (* ============ 6b3: beta ≤ eps'·inv(K) (the budget core: β := eps'·inv(K(1+eps')))   K ≤ K(1+eps') (1 < 1+eps') gives inv(K(1+eps')) ≤ inv(K) (real_inv_pos_lt_contra, strict + iff bridge)   hence eps'·inv(K(1+eps')) ≤ eps'·inv(K) (real_mult_lt_compat_l). *)
Lemma real_beta_le_epsK : forall (K eps' : Real)  (HK : real_lt real_zero K) (Heps' : real_lt real_zero eps'),  real_le (real_mult eps'             (real_inv_pos (real_mult K (real_plus real_one eps'))               (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps'))))          (real_mult eps' (real_inv_pos K HK)).
Proof.
intros K eps' HK Heps'.
apply (real_le_trans (real_mult eps' (real_inv_pos (real_mult K (real_plus real_one eps'))              (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps'))))                       (real_mult eps' (real_inv_pos K HK))                       (real_mult eps' (real_inv_pos K HK))).
- apply (RealSetoid.real_lt_le_iff_req (real_mult eps' (real_inv_pos (real_mult K (real_plus real_one eps'))              (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps'))))                                         (real_mult eps' (real_inv_pos K HK))).
left.
apply (real_mult_lt_compat_l (real_inv_pos (real_mult K (real_plus real_one eps'))              (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps')))                                (real_inv_pos K HK) eps').
+ apply (real_inv_pos_lt_contra K (real_mult K (real_plus real_one eps'))                HK (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps'))).
apply (real_eq_lt_lt K (real_mult K real_one) (real_mult K (real_plus real_one eps'))).
* apply real_eq_sym.
apply (real_mult_one K).
* apply (real_mult_lt_compat_l real_one (real_plus real_one eps') K).
-- apply (real_lt_plus_compat_le_lt real_one real_one real_zero eps').
++ apply real_le_refl.
++ exact Heps'.
-- exact HK.
+ exact Heps'.
- apply real_le_refl.
Qed. (* ============ 6b0: pointwise form of real_le (the eq-branch tolerance of the Or encoding) ============   real_le x y = Or (real_lt x y) (real_eq x y), where the real_eq Cauchy form is not pointwise   (no projT1 X n == projT1 Y n can be extracted).  Pointwise uses therefore go through the tolerance form: x_n ≤ y_n + eps   (the lt branch is strict: x_n < y_n − c ≤ y_n ≤ y_n + eps; the eq branch: |x_n−y_n| < eps gives x_n < y_n + eps).   Use: in mult, the final budgets pointwise-realize the real_le of Hsum_bnd/HT3a/HDen_sq   (each with tolerance e0'/128; 3·tolerance totals 3e0'/128, well under the budget surplus 0.54·e0'). *)
Lemma real_le_pointwise_eps : forall (x y : Real) (eps : Q),  real_le x y -> QltT 0 eps ->  sigT (fun N : nat => forall n : nat, NatLe N n ->        QleT' (projT1 x n) (projT1 y n + eps)).
Proof.
intros x y eps Hxy Heps.
unfold real_le in Hxy.
destruct Hxy as [Hlt | Heq].
- (* lt branch: x_n < y_n − c gives x_n ≤ y_n − c ≤ y_n ≤ y_n + eps. *)    destruct Hlt as [c [Hc [N HN]]].
exists N.
intros n Hn.
apply Qle_to_QleT'.
apply (Qle_trans _ (projT1 y n - c) _).
+ apply Qlt_le_weak.
(* x_n < y_n − c iff 0 < (y_n − c) − x_n; by HN: 0 < (y_n − x_n) − c, a ring equality. *)      apply (proj2 (Qlt_minus_iff (projT1 x n) (projT1 y n - c))).
apply (Qlt_le_trans _ ((projT1 y n - projT1 x n) - c) _).
* apply (proj1 (Qlt_minus_iff c (projT1 y n - projT1 x n))).
apply QltT_to_Qlt.
exact (HN n Hn).
* apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
+ apply (Qle_trans _ (projT1 y n) _).
* apply Qlt_le_weak.
apply (proj2 (Qlt_minus_iff (projT1 y n - c) (projT1 y n))).
apply (Qlt_le_trans _ c _).
-- apply QltT_to_Qlt.
exact Hc.
-- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
* apply (Qle_plus_nonneg_r (projT1 y n) eps).
apply Qlt_le_weak.
apply QltT_to_Qlt.
exact Heps.
- (* eq branch: |x_n − y_n| < eps gives x_n < y_n + eps. *)    destruct (Heq eps Heps) as [N HN].
exists N.
intros n Hn.
apply Qle_to_QleT'.
apply Qlt_le_weak.
apply (Qle_lt_trans _ (projT1 y n + (projT1 x n - projT1 y n)) (projT1 y n + eps)).
+ apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
+ apply (proj2 (Qplus_lt_r (projT1 x n - projT1 y n) eps (projT1 y n))).
apply (proj2 (proj1 (Qabs_Qlt_condition (projT1 x n - projT1 y n) eps)                          (QltT_to_Qlt _ _ (HN n Hn)))).
Qed. (* ============ 6b: real_differentiable_mult (the multiplicative differentiability main theorem) ============
   The mult proof proper follows below; first a supplementary real_inv_proj
   (the real_inv_pos projection equals Qinv(u n) exactly at rates n ≥ the
   witness — avoiding the dead end of unfolding the witness construction by cbn). *)
(* real_inv_pos projection lemma: n ≥ N0 (the witness rate of Hx) gives
   projT1 (real_inv_pos x Hx) n == Qinv (projT1 x n).
   Written once in general form so that Hinv64/HinvK1/HdKfn/HdKgn all reuse it. *)
Lemma real_inv_proj : forall (x : Real) (Hx : real_lt real_zero x),
  sigT (fun N : nat => forall n : nat, NatLe N n -> QeqT (projT1 (real_inv_pos x Hx) n) (Qinv (projT1 x n))).
Proof.
  intros x Hx.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  exists N0.
  intros n Hn.
  apply NatLe_drop in Hn.
  unfold real_inv_pos.
  cbn [projT1].
  rewrite (leb_correct _ _ Hn).
  apply qeq_imp_qeqT.
  reflexivity.
Qed.
(* ============ T3.1: RealDifferentiable of exp (exp_diff_factor + exp_minus_one_linear + real_abs_scaling_le, purely constructive Bishop form) ============ *)
Lemma exp_partial_two_linear : forall (x : Q),
  QeqT (exp_partial 2 x - 1 - x) (Qmult x x / q_fact 2).
Proof.
  intro x. apply qeq_imp_qeqT. simpl. field.
Qed.

Lemma q_fact_two : QeqT (q_fact 2) 2.
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma exp_partial_linear_quad : forall (x : Q) (k : nat),
  (2 <= k)%nat ->
  QleT' (Qmult (1 + 1)%Q (Qabs x)) 3%Q ->
  QleT' (Qabs (exp_partial k x - 1 - x))
        (Qmult (Qmult (Qabs x) (Qabs x)) (3 # 2)).
Proof.
  intros x k Hk2 Hxbound.
  apply Qle_to_QleT'.
  assert (Hsplit : exp_partial k x - 1 - x ==
                   (exp_partial k x - exp_partial 2 x) + (exp_partial 2 x - 1 - x)).
  { ring. }
  set (B1 := exp_partial k x - exp_partial 2 x).
  set (B2 := exp_partial 2 x - 1 - x).
  apply (Qle_trans _ (Qabs B1 + Qabs B2) _).
  - apply (Qle_trans _ (Qabs (B1 + B2)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (exp_partial k x - 1 - x) (B1 + B2)).
      unfold B1, B2. exact Hsplit.
    + apply Qabs_triangle.
  - apply (Qle_trans _ (Qplus (Qmult (Qabs x) (Qabs x))
                              (Qmult (Qmult (Qabs x) (Qabs x)) (1 # 2))) _).
    + apply Qplus_le_compat.
      * assert (Hgeom : forall t : nat, (2 <= t)%nat -> Qle (Qmult (1 + 1)%Q (Qabs x)) (Z.of_nat (t + 1) # 1)).
        { intros t Ht.
          apply (Qle_trans _ 3%Q _).
          - apply QleT'_to_Qle. exact Hxbound.
          - unfold Qle. simpl. lia. }
        apply (Qle_trans _ ((q_pow (Qabs x) 2 / q_fact 2) * (1 + 1)%Q) _).
        -- unfold B1. apply QleT'_to_Qle. apply (exp_partial_diff_bound x (Qabs x) 2 k).
           ++ apply qeq_imp_qeqT. reflexivity.
           ++ apply Qle_to_QleT'. apply Qabs_nonneg.
           ++ intros t Ht. apply Qle_to_QleT'. apply (Hgeom t (NatLe_drop _ _ Ht)).
           ++ exact Hk2.
        -- apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
           rewrite (qeqT_imp_qeq _ _ q_fact_two).
           unfold Qdiv.
           simpl q_pow.
           field.
      * apply (Qle_trans _ (Qabs (Qmult x x / q_fact 2)) _).
        -- unfold B2. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (exp_partial 2 x - 1 - x) (Qmult x x / q_fact 2)).
           exact (qeqT_imp_qeq _ _ (exp_partial_two_linear x)).
        -- rewrite (qeqT_imp_qeq _ _ q_fact_two).
           apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
           unfold Qdiv.
           rewrite (Qabs_Qmult (Qmult x x) (Qinv 2)).
           rewrite (Qabs_Qmult x x).
           assert (Hqinv2 : Qabs (Qinv 2) == Qinv 2).
           { apply (Qabs_pos (Qinv 2)).
             apply (Qlt_le_weak 0 (Qinv 2)).
             apply Qinv_lt_0_compat.
             unfold Qlt. simpl. lia. }
           rewrite Hqinv2.
           field.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
Qed.

(* ============ Stage B: the Real layer ============ *)

(* exp pointwise projection: projT1 (cauchy_real_exp h) n == exp_partial n (projT1 h n). *)
Lemma real_exp_proj : forall (h : Real) (n : nat),
  QeqT (projT1 (cauchy_real_exp h) n) (exp_partial n (projT1 h n)).
Proof.
  intros h n. destruct h as [u Hu]. apply qeq_imp_qeqT. reflexivity.
Qed.

(* Q-layer rearrangement: a < b − c gives c < b − a. *)
Lemma q_lt_minus_shift : forall a b c : Q, QltT a (Qminus b c) -> QltT c (Qminus b a).
Proof.
  intros a b c H.
  apply Qlt_to_QltT.
  apply (Qlt_minus_iff c (Qminus b a)).
  assert (Heq : Qminus (Qminus b a) c == Qminus (Qminus b c) a) by ring.
  rewrite Heq.
  apply (proj1 (Qlt_minus_iff a (Qminus b c))).
  apply QltT_to_Qlt. exact H.
Qed.

(* |exp h - 1 - h| ≤ eps·|h| + eps' (with |h| < delta) — the Bishop linear approximation of exp at 0. *)
Lemma exp_minus_one_linear : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall h : Real, real_lt (real_abs h) delta ->
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros eps Heps.
  set (two_inv := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  set (four_inv := real_mult two_inv two_inv).
  set (delta := real_min two_inv (real_mult eps four_inv)).
  exists delta.
  split.
  - (* 0 < delta *)
    unfold delta, four_inv, two_inv.
    apply real_min_pos.
    + apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
    + apply real_mult_positive.
      * exact Heps.
      * apply real_mult_positive; apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
  - intros h Hh eps' Heps'.
    assert (Hh_half : real_lt (real_abs h) two_inv)
      by (unfold delta in Hh; apply (real_min_lt_l h two_inv (real_mult eps four_inv)); exact Hh).
    assert (Hh_eps4 : real_lt (real_abs h) (real_mult eps four_inv))
      by (unfold delta in Hh; apply (real_min_lt_r h two_inv (real_mult eps four_inv)); exact Hh).
    (* the real_le left branch: build real_lt. *)
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    destruct Hh_half as [eps2 [Heps2 [N2 HN2]]].
    destruct Hh_eps4 as [eps3 [Heps3 [N3 HN3]]].
    destruct (real_inv_proj (real_plus real_one real_one) (real_two_pos_local)) as [Ni HNi].
    exists eps1'.
    split.
    + exact Heps1'.
    + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max (Nat.max N2 N3) Ni)) 2).
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n). set (en' := projT1 eps' n). set (hn := projT1 h n).
      (* Pointwise unfolding of A and B. *)
      assert (HA : projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n ==
                    Qabs (exp_partial n hn - 1 - hn)).
      { unfold hn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp h) (real_opp real_one) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj h n)).
        rewrite (qeqT_imp_qeq _ _ (real_exp_proj h n)).
        cbn [projT1 real_one].
        unfold Qminus. ring. }
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        cbn [projT1]. ring. }
      (* Pointwise bound 1: |hn| < 1/2 (the Hh_half witness + the two_inv projection). *)
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hni : (Ni <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (HN2q : Qlt eps2 (Qminus (Qinv 2) (Qabs hn))).
      { apply (Qlt_le_trans eps2 (Qminus (projT1 two_inv n) (projT1 (real_abs h) n)) (Qminus (Qinv 2) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
        - apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          unfold two_inv.
          rewrite (qeqT_imp_qeq _ _ (HNi n (NatLe_lift _ _ Hni))).
          rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
          cbn [real_one real_const projT1].
          reflexivity. }
      assert (Hhn_half : Qlt (Qabs hn) (Qinv 2)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qinv 2) eps2) (Qinv 2)).
        - apply QltT_to_Qlt. apply (q_lt_minus_shift eps2 (Qinv 2) (Qabs hn)). apply Qlt_to_QltT. exact HN2q.
        - assert (Heps2q : Qle 0 eps2).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
          apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) eps2) (Qinv 2)).
          + apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) 0) (Qplus (Qminus (Qinv 2) eps2) eps2)).
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
            * apply (Qplus_le_compat (Qminus (Qinv 2) eps2) (Qminus (Qinv 2) eps2) 0 eps2 (Qle_refl _) Heps2q).
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      (* Pointwise bound 2: |hn| < en/4 (the Hh_eps4 witness + the eps·four_inv projection). *)
      assert (HN3q : Qlt eps3 (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
      { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps four_inv) n) (projT1 (real_abs h) n))
                                (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
        - apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          unfold four_inv, two_inv, en.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                        (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                         (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (HNi n (NatLe_lift _ _ Hni))).
          rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
          cbn [real_one real_const projT1].
          reflexivity. }
      assert (Hhn_eps4 : Qlt (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                            (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
        - apply QltT_to_Qlt. apply (q_lt_minus_shift eps3 (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)). apply Qlt_to_QltT. exact HN3q.
        - assert (Heps3q : Qle 0 eps3).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
          apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                           (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)
                           (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          + apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                             (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0)
                             (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)).
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                                     (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0 eps3 (Qle_refl _) Heps3q).
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      (* Main chain: B_n − A_n ≥ eps1'. *)
      assert (Hquad : Qle (Qabs (exp_partial n hn - 1 - hn))
                          (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))).
      { apply QleT'_to_Qle. apply (exp_partial_linear_quad hn n).
        - lia.
        - (* 2|hn| ≤ 3: from |hn| < 1/2. *)
          apply Qle_to_QleT'.
          apply (Qlt_le_weak (Qmult (1 + 1)%Q (Qabs hn)) 3%Q).
          apply (Qlt_trans (Qmult (1 + 1)%Q (Qabs hn)) (Qmult (1 + 1)%Q (Qinv 2)) 3%Q).
          + setoid_rewrite (Qmult_comm (1 + 1)%Q (Qabs hn)).
            setoid_rewrite (Qmult_comm (1 + 1)%Q (Qinv 2)).
            apply (Qmult_lt_compat_r (Qabs hn) (Qinv 2) (1 + 1)%Q).
            * unfold Qlt. simpl. lia.
            * exact Hhn_half.
          + unfold Qlt. simpl. lia. }
      assert (Hq2 : Qle (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                        (Qmult (Qmult en (Qabs hn)) (3 # 8))).
      { assert (Hhn_le : Qle (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
        { apply Qlt_le_weak. exact Hhn_eps4. }
        apply (Qle_trans (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                         (Qmult (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)) (3 # 2))
                         (Qmult (Qmult en (Qabs hn)) (3 # 8))).
        - (* |hn|² ≤ (en/4)·|hn|, multiplied by (3/2). *)
          apply (Qmult_le_compat_r (Qmult (Qabs hn) (Qabs hn))
                                   (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))
                                   (3 # 2)).
          + apply (Qmult_le_compat_r (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)).
            * exact Hhn_le.
            * apply Qabs_nonneg.
          + unfold Qle. simpl. lia.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field. }
      assert (Hq3 : Qle (Qmult (Qmult en (Qabs hn)) (3 # 8)) (Qmult en (Qabs hn))).
      { setoid_rewrite (Qmult_comm (Qmult en (Qabs hn)) (3 # 8)).
        apply (Qle_trans (Qmult (3 # 8) (Qmult en (Qabs hn))) (Qmult 1%Q (Qmult en (Qabs hn))) (Qmult en (Qabs hn))).
        - apply (Qmult_le_compat_r (3 # 8) 1%Q (Qmult en (Qabs hn))).
          + unfold Qle. simpl. lia.
          + assert (HN1e : QltT eps1 en).
            { apply Qlt_to_QltT.
              apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
              - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
              - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en. ring. }
            assert (Henq : Qle 0 en).
            { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
              - apply QltT_to_Qlt. exact Heps1.
              - apply QltT_to_Qlt. exact HN1e. }
            apply (Qmult_le_0_compat en (Qabs hn) Henq (Qabs_nonneg hn)).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      assert (Hmain : Qle (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2)) _).
        - exact Hquad.
        - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (3 # 8)) _).
          + exact Hq2.
          + exact Hq3. }
      (* eps1' < B_n − A_n: eps1' < en' ≤ B_n − A_n *)
      assert (Heps1e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en'. ring. }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n)
                           (Qabs (exp_partial n hn - 1 - hn)) HA). }
      assert (Henle : Qle en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
      { apply (Qle_trans en' (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))
                           (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        - apply (Qle_trans en' (Qplus en' 0) (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))).
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          + apply (Qplus_le_compat en' en' 0 (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn)))
                                   (Qle_refl en')
                                   (proj1 (Qle_minus_iff (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))) Hmain)).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' en' (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                             (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
      { apply QltT_to_Qlt. exact Heps1e. }
      { apply (Qle_trans en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))
                               (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                       (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
        - exact Henle.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. }
Qed.

(* ============ T3.1 Phase C: RealDifferentiable of exp (purely constructive, Bishop form) ============ *)

(* C1. 0 < exp x gives 0 < |exp x| (constructed directly per eps: eps1 passed along as eps). *)
Lemma real_abs_exp_pos : forall x : Real,
  real_lt real_zero (real_abs (cauchy_real_exp x)).
Proof.
  intros x.
  destruct (cauchy_real_exp_pos x) as [eps1 [Heps1 [N1 HN1]]].
  unfold real_lt.
  exists eps1.
  split.
  - exact Heps1.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj (cauchy_real_exp x) n)).
    assert (Hposle : Qle 0 (projT1 (cauchy_real_exp x) n)).
    { apply Qlt_le_weak.
      apply (Qlt_trans 0 eps1 (projT1 (cauchy_real_exp x) n)).
      - apply QltT_to_Qlt. exact Heps1.
      - apply QltT_to_Qlt.
        apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 (cauchy_real_exp x) n) (projT1 real_zero n))
                             (projT1 (cauchy_real_exp x) n)).
        + apply QltT_to_Qlt. exact (HN1 n Hn).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring. }
    rewrite (Qabs_pos (projT1 (cauchy_real_exp x) n) Hposle).
    apply QltT_to_Qlt. exact (HN1 n Hn).
Qed.

(* C2. a·b − a·c == a·(b − c): factoring out (pointwise ring). *)
Lemma real_mult_sub_factor : forall a b c : Real,
  real_eq (real_plus (real_mult a b) (real_opp (real_mult a c)))
          (real_mult a (real_plus b (real_opp c))).
Proof.
  intros a b c. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult a b) (real_opp (real_mult a c)) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a b n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult a c) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a c n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a (real_plus b (real_opp c)) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj b (real_opp c) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj c n)).
  simpl. ring.
Qed.

(* C3. Final scaling: |a|·(eps·inv(1+|a|)·|h| + eps'·inv(1+|a|)) ≤ eps·|h| + eps'.
   Pointwise at the Q layer (the Real layer has no 0 ≤ |a|, so product bounds go pointwise);
   unified lower bound eps1'·inv(M+2), with M a Cauchy-norm upper bound of |a| (real_norm_bounded). *)
Lemma real_abs_scaling_le : forall (a eps eps' h : Real),
  real_lt real_zero eps -> real_lt real_zero eps' ->
  real_le (real_mult (real_abs a)
            (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h))
                       (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a)))))
          (real_plus (real_mult eps (real_abs h)) eps').
Proof.
  intros a eps eps' h Heps Heps'.
  unfold real_le. left.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
  destruct (real_norm_bounded a) as [M [HMpos HM]].
  destruct (real_inv_proj (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a)) as [Ni HNi].
  set (M2 := Qplus M 2).
  assert (HM2pos : Qlt 0 M2).
  { unfold M2.
    apply (Qlt_le_trans 0 1 (Qplus M 2)).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans 1 (Qplus 0 1) (Qplus M 2)).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + assert (H12 : Qle 1 2) by (unfold Qle; simpl; lia).
        apply (Qplus_le_compat 0 M 1 2 (Qlt_le_weak 0 M (QltT_to_Qlt _ _ HMpos)) H12). }
  exists (Qmult eps1' (Qinv M2)).
  split.
  - (* QltT 0 (eps1'·inv M2) *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps1' (Qinv M2)).
    + apply QltT_to_Qlt. exact Heps1'.
    + apply Qinv_lt_0_compat. exact HM2pos.
  - (* Pointwise: eps1'·inv M2 < (right_n − left_n). *)
    exists (Nat.max (Nat.max N1 N1') Ni).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn1' : (N1' <= n)%nat) by lia.
    assert (HnNi : (Ni <= n)%nat) by lia.
    set (an := Qabs (projT1 a n)).
    set (en := projT1 eps n).
    set (e'n := projT1 eps' n).
    set (hn := projT1 h n).
    (* Left side projection unfolding. *)
    assert (HA : projT1 (real_mult (real_abs a)
              (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h))
                         (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))))) n
            == Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))).
    { unfold an, en, e'n, hn.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_abs a)
        (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h))
                   (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a)))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj
        (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h))
        (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj
        (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (HNi n (NatLe_lift _ _ HnNi))).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs a) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
      cbn [real_one real_const projT1].
      setoid_rewrite (Qplus_comm 1 (Qabs (projT1 a n))).
      ring. }
    (* Right side projection unfolding. *)
    assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n
                 == Qplus (Qmult en (Qabs hn)) e'n).
    { unfold en, e'n, hn.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      simpl. ring. }
    (* Positivity: the eps tail is > 0. *)
    assert (HN1e : QltT eps1 en).
    { unfold en. apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
      - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring. }
    assert (Hen : Qlt 0 en)
      by (apply (Qlt_trans 0 eps1 en); [apply QltT_to_Qlt; exact Heps1 | apply QltT_to_Qlt; exact HN1e]).
    assert (HN1'e : QltT eps1' e'n).
    { unfold e'n. apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) (projT1 eps' n)).
      - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring. }
    assert (He'n : Qlt 0 e'n)
      by (apply (Qlt_trans 0 eps1' e'n); [apply QltT_to_Qlt; exact Heps1' | apply QltT_to_Qlt; exact HN1'e]).
    assert (Han1 : Qlt 0 (Qplus an 1)).
    { apply (Qlt_le_trans 0 1 (Qplus an 1)).
      - unfold Qlt. simpl. lia.
      - apply (Qle_trans 1 (Qplus 0 1) (Qplus an 1)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qplus_le_compat 0 an 1 1 (Qabs_nonneg (projT1 a n)) (Qle_refl 1)). }
    (* inv strictly decreasing: an+1 ≤ M+1 < M+2 gives inv M2 < inv(an+1). *)
    assert (Hm12 : Qlt (Qplus M 1) (Qplus M 2)).
    { apply (proj2 (Qlt_minus_iff (Qplus M 1) (Qplus M 2))).
      assert (Hd : Qminus (Qplus M 2) (Qplus M 1) == 1) by ring.
      rewrite Hd. unfold Qlt. simpl. lia. }
    assert (Him : Qlt (Qinv M2) (Qinv (Qplus an 1))).
    { assert (Han1nz : ~ (Qplus an 1 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in Han1. exact Han1. }
      assert (HM2nz : ~ (M2 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in HM2pos. exact HM2pos. }
      apply (proj2 (Qlt_minus_iff (Qinv M2) (Qinv (Qplus an 1)))).
      assert (Hdiff : Qminus (Qinv (Qplus an 1)) (Qinv M2)
                      == Qmult (Qminus M2 (Qplus an 1)) (Qinv (Qmult M2 (Qplus an 1)))).
      { field. split.
        - exact Han1nz.
        - exact HM2nz. }
      rewrite Hdiff.
      apply (Qmult_lt_0_compat (Qminus M2 (Qplus an 1)) (Qinv (Qmult M2 (Qplus an 1)))).
      - apply (proj1 (Qlt_minus_iff (Qplus an 1) M2)).
        apply (Qle_lt_trans (Qplus an 1) (Qplus M 1) M2).
        + apply (Qplus_le_compat an M 1 1 (QleT'_to_Qle _ _ (HM n)) (Qle_refl 1)).
        + unfold M2. exact Hm12.
      - apply Qinv_lt_0_compat.
        apply (Qmult_lt_0_compat M2 (Qplus an 1)); [exact HM2pos | exact Han1]. }
    (* Main chain: eps1'·inv M2 < e'n·inv(an+1) ≤ (en|hn|+e'n)·inv(an+1) == right−left. *)
    assert (Hmain : Qlt (Qmult eps1' (Qinv M2))
        (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
           (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
    { assert (Han1nz : ~ (Qplus an 1 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in Han1. exact Han1. }
      assert (Hiden : Qminus (Qplus (Qmult en (Qabs hn)) e'n)
            (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1)))))
            == Qmult (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1))).
      { field. exact Han1nz. }
      apply (Qlt_le_trans (Qmult eps1' (Qinv M2)) (Qmult e'n (Qinv (Qplus an 1)))
             (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
      - apply (Qlt_le_trans (Qmult eps1' (Qinv M2)) (Qmult eps1' (Qinv (Qplus an 1)))
                             (Qmult e'n (Qinv (Qplus an 1)))).
        + setoid_rewrite (Qmult_comm eps1' (Qinv M2)).
          setoid_rewrite (Qmult_comm eps1' (Qinv (Qplus an 1))).
          apply (Qmult_lt_compat_r (Qinv M2) (Qinv (Qplus an 1)) eps1').
          * apply QltT_to_Qlt. exact Heps1'.
          * exact Him.
        + apply (Qmult_le_compat_r eps1' e'n (Qinv (Qplus an 1))).
          * apply Qlt_le_weak. apply QltT_to_Qlt. exact HN1'e.
          * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Han1.
      - apply (Qle_trans (Qmult e'n (Qinv (Qplus an 1)))
               (Qmult (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1)))
               (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                  (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
        + apply (Qmult_le_compat_r e'n (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1))).
          * apply (Qle_trans e'n (Qplus e'n (Qmult en (Qabs hn))) (Qplus (Qmult en (Qabs hn)) e'n)).
            { apply (Qle_plus_nonneg_r e'n (Qmult en (Qabs hn))).
              apply (Qmult_le_compat_nonneg 0 en 0 (Qabs hn)).
              { split; [apply Qle_refl | apply Qlt_le_weak; exact Hen]. }
              { split; [apply Qle_refl | apply Qabs_nonneg]. } }
            { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qplus_comm e'n (Qmult en (Qabs hn))). }
          * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Han1.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hiden. }
    (* Finish: after rewriting the projections, exact Hmain. *)
    apply Qlt_to_QltT.
    assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                (projT1 (real_mult (real_abs a)
                                   (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h))
                                              (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))))) n))
                        (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                           (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
    { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                         (Qplus (Qmult en (Qabs hn)) e'n) HB
                         (projT1 (real_mult (real_abs a)
                            (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h))
                                       (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))))) n)
                         (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))) HA). }
    apply (Qlt_le_trans (Qmult eps1' (Qinv M2))
           (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
              (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))
           (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                   (projT1 (real_mult (real_abs a)
                      (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))) (real_abs h))
                                 (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (real_abs_plus_one_pos a))))) n))).
    { exact Hmain. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. }
Qed.

(* C4. exp differentiability: rdf := exp, Bishop form (exp_diff_factor + exp_minus_one_linear + real_abs_scaling_le). *)
Lemma real_exp_differentiable :
  RealDifferentiable (fun (x : Real) (Hx : real_lt real_zero x) => cauchy_real_exp x).
Proof.
  exists (fun (x : Real) (Hx : real_lt real_zero x) => cauchy_real_exp x).
  intros x Hx eps Heps.
  set (eps0 := real_mult eps (real_inv_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x)))).
  assert (Heps0 : real_lt real_zero eps0).
  { unfold eps0. apply real_mult_positive.
    - exact Heps.
    - apply (real_inv_pos_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x))). }
  destruct (exp_minus_one_linear eps0 Heps0) as [delta0 [Hdelta0 Hlin0]].
  exists delta0.
  split.
  - exact Hdelta0.
  - intros h Hh Hxh eps' Heps'.
    set (eps0' := real_mult eps' (real_inv_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x)))).
    assert (Heps0' : real_lt real_zero eps0').
    { unfold eps0'. apply real_mult_positive.
      - exact Heps'.
      - apply (real_inv_pos_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x))). }
    assert (Hlin : real_le (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                           (real_plus (real_mult eps0 (real_abs h)) eps0')).
    { apply (Hlin0 h Hh eps0' Heps0'). }
    assert (Habs0 : real_le real_zero (real_abs (cauchy_real_exp x))).
    { left. apply real_abs_exp_pos. }
    (* D == exp x·(exp h − 1 − h): exp_diff_factor + factoring the subtraction. *)
    assert (Hxxh : real_eq (real_plus (real_plus x h) (real_opp x)) h).
    { apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus x h) (real_opp x) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj x h n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
      simpl. ring. }
    assert (Hmain_eq : real_eq (real_plus (cauchy_real_exp (real_plus x h))
                      (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h))))
                      (real_mult (cauchy_real_exp x)
                         (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))).
    { apply (real_eq_trans _ (real_plus (real_plus (cauchy_real_exp (real_plus x h)) (real_opp (cauchy_real_exp x)))
                                        (real_opp (real_mult (cauchy_real_exp x) h))) _).
      - apply (real_eq_trans _ (real_plus (cauchy_real_exp (real_plus x h))
                       (real_plus (real_opp (cauchy_real_exp x)) (real_opp (real_mult (cauchy_real_exp x) h)))) _).
        + apply (RealSetoid.real_eq_plus_compat (cauchy_real_exp (real_plus x h))
                 (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))
                 (cauchy_real_exp (real_plus x h))
                 (real_plus (real_opp (cauchy_real_exp x)) (real_opp (real_mult (cauchy_real_exp x) h)))).
          * apply real_eq_refl.
          * apply (real_opp_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)).
        + apply (real_plus_assoc (cauchy_real_exp (real_plus x h))
                                 (real_opp (cauchy_real_exp x))
                                 (real_opp (real_mult (cauchy_real_exp x) h))).
      - apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_exp x)
                   (real_plus (cauchy_real_exp h) (real_opp real_one)))
                   (real_opp (real_mult (cauchy_real_exp x) h))) _).
        + apply (RealSetoid.real_eq_plus_compat
                 (real_plus (cauchy_real_exp (real_plus x h)) (real_opp (cauchy_real_exp x)))
                 (real_opp (real_mult (cauchy_real_exp x) h))
                 (real_mult (cauchy_real_exp x) (real_plus (cauchy_real_exp h) (real_opp real_one)))
                 (real_opp (real_mult (cauchy_real_exp x) h))).
          * apply (real_eq_trans _ (real_mult (cauchy_real_exp x)
                 (real_plus (cauchy_real_exp (real_plus (real_plus x h) (real_opp x))) (real_opp real_one))) _).
            -- apply (exp_diff_factor (real_plus x h) x).
            -- apply (RealSetoid.real_eq_mult_compat (cauchy_real_exp x)
                       (real_plus (cauchy_real_exp (real_plus (real_plus x h) (real_opp x))) (real_opp real_one))
                       (cauchy_real_exp x)
                       (real_plus (cauchy_real_exp h) (real_opp real_one))).
               ++ apply real_eq_refl.
               ++ apply (RealSetoid.real_eq_plus_compat
                          (cauchy_real_exp (real_plus (real_plus x h) (real_opp x)))
                          (real_opp real_one)
                          (cauchy_real_exp h)
                          (real_opp real_one)).
                  ** apply cauchy_real_exp_wd. exact Hxxh.
                  ** apply real_eq_refl.
          * apply real_eq_refl.
        + apply real_mult_sub_factor. }
    (* |D| == |exp x|·|exp h − 1 − h| *)
    assert (HabsD : real_le (real_abs (real_plus (cauchy_real_exp (real_plus x h))
                      (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))))
                      (real_mult (real_abs (cauchy_real_exp x))
                         (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))).
    { apply RealSetoid.real_eq_le.
      apply (real_eq_trans (real_abs (real_plus (cauchy_real_exp (real_plus x h))
                             (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))))
             (real_abs (real_mult (cauchy_real_exp x)
                (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
             (real_mult (real_abs (cauchy_real_exp x))
                (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))).
      - apply real_abs_eq_compat. exact Hmain_eq.
      - apply (real_abs_mult_req (cauchy_real_exp x)
                 (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))). }
    (* Multiply by |exp x|: real_le_mult_compat_weak (0 ≤ |exp x| constructed directly from 0 < exp x). *)
    assert (Hmul0 : real_le (real_mult (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                                       (real_abs (cauchy_real_exp x)))
                            (real_mult (real_plus (real_mult eps0 (real_abs h)) eps0')
                                       (real_abs (cauchy_real_exp x)))).
    { apply (real_le_mult_compat_weak (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                                      (real_plus (real_mult eps0 (real_abs h)) eps0')
                                      (real_abs (cauchy_real_exp x))).
      - exact Habs0.
      - exact Hlin. }
    assert (Hmul : real_le (real_mult (real_abs (cauchy_real_exp x))
                          (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
                          (real_mult (real_abs (cauchy_real_exp x))
                             (real_plus (real_mult eps0 (real_abs h)) eps0'))).
    { apply (real_le_trans (real_mult (real_abs (cauchy_real_exp x))
                            (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
             (real_mult (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                        (real_abs (cauchy_real_exp x)))
             (real_mult (real_abs (cauchy_real_exp x))
                (real_plus (real_mult eps0 (real_abs h)) eps0'))).
      - apply RealSetoid.real_eq_le.
        apply (real_mult_comm (real_abs (cauchy_real_exp x))
               (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))).
      - apply (real_le_trans _ (real_mult (real_plus (real_mult eps0 (real_abs h)) eps0')
                                          (real_abs (cauchy_real_exp x))) _).
        + exact Hmul0.
        + apply RealSetoid.real_eq_le.
          apply (real_mult_comm (real_plus (real_mult eps0 (real_abs h)) eps0')
                                (real_abs (cauchy_real_exp x))). }
    (* Final scaling (pointwise at the Q layer). *)
    assert (Hfinal : real_le (real_mult (real_abs (cauchy_real_exp x))
                            (real_plus (real_mult eps0 (real_abs h)) eps0'))
                            (real_plus (real_mult eps (real_abs h)) eps')).
    { unfold eps0, eps0'.
      apply (real_abs_scaling_le (cauchy_real_exp x) eps eps' h Heps Heps'). }
    apply (real_le_trans (real_abs (real_plus (cauchy_real_exp (real_plus x h))
                   (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))))
             (real_mult (real_abs (cauchy_real_exp x))
                (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
             (real_plus (real_mult eps (real_abs h)) eps')).
    { exact HabsD. }
    { apply (real_le_trans _ (real_mult (real_abs (cauchy_real_exp x))
                               (real_plus (real_mult eps0 (real_abs h)) eps0')) _).
      { exact Hmul. }
      { exact Hfinal. } }
Qed.

Lemma real_differentiable_mult : forall (f g : forall x : Real, real_lt real_zero x -> Real)  (Hf : RealDifferentiable f) (Hg : RealDifferentiable g),  RealDifferentiable (fun x Hx => real_mult (f x Hx) (g x Hx)).
Proof.
intros f g Hf Hg.
exists (fun (x : Real) (Hx : real_lt real_zero x) =>            real_plus (real_mult (rdf f Hf x Hx) (g x Hx))                      (real_mult (f x Hx) (rdf g Hg x Hx))).
intros x Hx eps Heps.
set (half := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
set (quarter := real_mult half half).
set (eps4 := real_mult quarter eps).
set (eps2 := real_mult half eps).
assert (Hhalf : real_lt real_zero half).
{ unfold half.
apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
}  assert (Hquarter : real_lt real_zero quarter).
{ unfold quarter.
apply real_mult_positive; [exact Hhalf | exact Hhalf].
}  assert (Heps4 : real_lt real_zero eps4).
{ unfold eps4.
apply real_mult_positive; [exact Hquarter | exact Heps].
}  assert (Heps2 : real_lt real_zero eps2).
{ unfold eps2.
apply real_mult_positive; [exact Hhalf | exact Heps].
}  set (Mf := real_plus real_one (real_abs (f x Hx))).
set (Mg := real_plus real_one (real_abs (g x Hx))).
set (Mfp := real_plus real_one (real_abs (rdf f Hf x Hx))).
set (Mgp := real_plus real_one (real_abs (rdf g Hg x Hx))).
assert (HMf : real_lt real_zero Mf).
{ unfold Mf.
apply real_abs_plus_one_pos.
}  assert (HMg : real_lt real_zero Mg).
{ unfold Mg.
apply real_abs_plus_one_pos.
}  assert (HMfp : real_lt real_zero Mfp).
{ unfold Mfp.
apply real_abs_plus_one_pos.
}  assert (HMgp : real_lt real_zero Mgp).
{ unfold Mgp.
apply real_abs_plus_one_pos.
}  set (eps_f := real_mult (real_inv_pos Mg HMg) eps4).
set (eps_g := real_mult (real_inv_pos Mf HMf) eps4).
assert (Heps_f : real_lt real_zero eps_f).
{ unfold eps_f.
apply real_mult_positive.
- apply (real_inv_pos_pos Mg HMg).
- exact Heps4.
}  assert (Heps_g : real_lt real_zero eps_g).
{ unfold eps_g.
apply real_mult_positive.
- apply (real_inv_pos_pos Mf HMf).
- exact Heps4.
}  set (Lf := real_plus (real_abs (rdf f Hf x Hx)) eps_f).
set (Lg := real_plus (real_abs (rdf g Hg x Hx)) eps_g).
assert (HLf : real_lt real_zero Lf).
{ unfold Lf.
apply real_abs_plus_pos.
exact Heps_f.
}  assert (HLg : real_lt real_zero Lg).
{ unfold Lg.
apply real_abs_plus_pos.
exact Heps_g.
}  set (Den := real_mult Lf Lg).
assert (HDen : real_lt real_zero Den).
{ unfold Den.
apply real_mult_positive; [exact HLf | exact HLg].
}  set (K := real_mult (real_const (Z.of_nat 64 # 1))            (real_plus (real_plus (real_plus (real_plus Mf Mg) Mfp) Mgp) real_one)).
assert (HK : real_lt real_zero K).
{ unfold K.
apply real_mult_positive.
- apply real_const_pos.
vm_compute.
reflexivity.
- apply real_plus_positive.
+ apply real_plus_positive.
* apply real_plus_positive.
-- apply real_plus_positive; [exact HMf | exact HMg].
-- exact HMfp.
* exact HMgp.
+ apply real_lt_zero_one.
}  (* The |h|² term and β-linear absorption. *)  set (eps3 := real_mult (real_inv_pos Den HDen) eps2).
assert (Heps3 : real_lt real_zero eps3).
{ unfold eps3.
apply real_mult_positive.
- apply (real_inv_pos_pos Den HDen).
- exact Heps2.
}  set (e8 := real_const (Z.of_nat 8 # 1)).
assert (He8 : real_lt real_zero e8).
{ unfold e8.
apply real_const_pos.
vm_compute.
reflexivity.
}  set (dKf := real_mult K (real_inv_pos (real_mult e8 Lf) (real_mult_positive e8 Lf He8 HLf))).
assert (HdKf : real_lt real_zero dKf).
{ unfold dKf.
apply real_mult_positive.
- exact HK.
- apply (real_inv_pos_pos (real_mult e8 Lf) (real_mult_positive e8 Lf He8 HLf)).
}  set (dKg := real_mult K (real_inv_pos (real_mult e8 Lg) (real_mult_positive e8 Lg He8 HLg))).
assert (HdKg : real_lt real_zero dKg).
{ unfold dKg.
apply real_mult_positive.
- exact HK.
- apply (real_inv_pos_pos (real_mult e8 Lg) (real_mult_positive e8 Lg He8 HLg)).
}  (* Correction bounds for f/g (the eps coefficients are eps_f/eps_g). *)  destruct (rdf_correct f Hf x Hx eps_f Heps_f) as [delta_f [Hdf Hf_corr]].
destruct (rdf_correct g Hg x Hx eps_g Heps_g) as [delta_g [Hdg Hg_corr]].
set (delta := real_min (real_min delta_f delta_g)                         (real_min eps3 (real_min dKf dKg))).
exists delta.
split.
- (* 0 < delta *)    unfold delta.
apply real_min_pos.
+ apply real_min_pos; [exact Hdf | exact Hdg].
+ apply real_min_pos; [exact Heps3 | apply real_min_pos; [exact HdKf | exact HdKg]].
- intros h Hh Hxh eps' Heps'.
(* Budget: β := eps'·inv(K(1+eps')), γ := half·β, marg := eps'·inv(64K). *)    set (beta := real_mult eps'                    (real_inv_pos (real_mult K (real_plus real_one eps'))                                  (real_mult_positive K (real_plus real_one eps') HK                                    (real_one_plus_pos eps' Heps')))).
set (gamma := real_mult half beta).
assert (Hc64 : real_lt real_zero (real_const (Z.of_nat 64 # 1))).
{ apply real_const_pos.
vm_compute.
reflexivity.
}    (* marg := β·inv64 (β-based: marg² == β²/4096 ≤ β/4096, linear in eps';       the old marg := eps'·inv(64K) had marg² quadratic in eps', which the pointwise budget cannot control — the lesson of that attempt). *)    set (marg := real_mult beta                    (real_inv_pos (real_const (Z.of_nat 64 # 1)) Hc64)).
assert (Hbeta : real_lt real_zero beta).
{ unfold beta.
apply real_mult_positive.
- exact Heps'.
- apply (real_inv_pos_pos (real_mult K (real_plus real_one eps'))                   (real_mult_positive K (real_plus real_one eps') HK                     (real_one_plus_pos eps' Heps'))).
}    assert (Hgamma : real_lt real_zero gamma).
{ unfold gamma.
apply real_mult_positive; [exact Hhalf | exact Hbeta].
}    assert (Hmarg : real_lt real_zero marg).
{ unfold marg.
apply real_mult_positive.
- exact Hbeta.
- apply (real_inv_pos_pos (real_const (Z.of_nat 64 # 1)) Hc64).
}    (* h branches: |h| < δf/δg/eps3/dKf/dKg. *)    assert (Hhdf : real_lt (real_abs h) delta_f).
{ apply (real_min_lt_l h delta_f delta_g).
apply (real_min_lt_l h (real_min delta_f delta_g) (real_min eps3 (real_min dKf dKg))).
exact Hh.
}    assert (Hhdg : real_lt (real_abs h) delta_g).
{ apply (real_min_lt_r h delta_f delta_g).
apply (real_min_lt_l h (real_min delta_f delta_g) (real_min eps3 (real_min dKf dKg))).
exact Hh.
}    assert (Hheps3 : real_lt (real_abs h) eps3).
{ apply (real_min_lt_l h eps3 (real_min dKf dKg)).
apply (real_min_lt_r h (real_min delta_f delta_g) (real_min eps3 (real_min dKf dKg))).
exact Hh.
}    assert (HhdKf : real_lt (real_abs h) dKf).
{ apply (real_min_lt_l h dKf dKg).
apply (real_min_lt_r h eps3 (real_min dKf dKg)).
apply (real_min_lt_r h (real_min delta_f delta_g) (real_min eps3 (real_min dKf dKg))).
exact Hh.
}    assert (HhdKg : real_lt (real_abs h) dKg).
{ apply (real_min_lt_r h dKf dKg).
apply (real_min_lt_r h eps3 (real_min dKf dKg)).
apply (real_min_lt_r h (real_min delta_f delta_g) (real_min eps3 (real_min dKf dKg))).
exact Hh.
}    (* Correction bounds for A_f/A_g: |A_f| ≤ eps_f|h| + (β+γ) and |A_g| ≤ eps_g|h| + (β+γ). *)    set (beta_gamma := real_plus beta gamma).
assert (Hbg : real_lt real_zero beta_gamma).
{ unfold beta_gamma.
apply real_plus_positive; [exact Hbeta | exact Hgamma].
}    set (Af := real_plus (f (real_plus x h) Hxh)                         (real_opp (real_plus (f x Hx) (real_mult (rdf f Hf x Hx) h)))).
set (Ag := real_plus (g (real_plus x h) Hxh)                         (real_opp (real_plus (g x Hx) (real_mult (rdf g Hg x Hx) h)))).
assert (HAf : real_le (real_abs Af) (real_plus (real_mult eps_f (real_abs h)) beta_gamma)).
{ unfold Af.
exact (Hf_corr h Hhdf Hxh beta_gamma Hbg).
}    assert (HAg : real_le (real_abs Ag) (real_plus (real_mult eps_g (real_abs h)) beta_gamma)).
{ unfold Ag.
exact (Hg_corr h Hhdg Hxh beta_gamma Hbg).
}    (* Goal |D| ≤ eps|h| + eps'; the definition of D. *)    set (D := real_plus (real_mult (f (real_plus x h) Hxh) (g (real_plus x h) Hxh))           (real_opp (real_plus (real_mult (f x Hx) (g x Hx))              (real_mult (real_plus (real_mult (rdf f Hf x Hx) (g x Hx))                                    (real_mult (f x Hx) (rdf g Hg x Hx))) h)))).
(* Decomposition: D == Fx·Ag + Gx·Af + Df·Dg (real_mult_diff_decomp). *)    set (Fh := f (real_plus x h) Hxh).
set (Fx := f x Hx).
set (Gh := g (real_plus x h) Hxh).
set (Gx := g x Hx).
set (df := rdf f Hf x Hx).
set (dg := rdf g Hg x Hx).
set (Df := real_plus Fh (real_opp Fx)).
set (Dg := real_plus Gh (real_opp Gx)).
assert (HD : real_eq D (real_plus (real_plus (real_mult Fx Ag) (real_mult Gx Af))                                      (real_mult Df Dg))).
{ unfold D, Fh, Fx, Gh, Gx, df, dg, Df, Dg, Af, Ag.
exact (real_mult_diff_decomp Fh Fx Gh Gx df dg h).
}    (* Factor bounds: |f x| ≤ Mf and |g x| ≤ Mg (real_abs_le_plus_one). *)    assert (HfM : real_le (real_abs Fx) Mf).
{ unfold Fx, Mf.
exact (real_abs_le_plus_one (f x Hx)).
}    assert (HgM : real_le (real_abs Gx) Mg).
{ unfold Gx, Mg.
exact (real_abs_le_plus_one (g x Hx)).
}    (* |Δf| == |Df| ≤ Lf|h| + β_gamma: triangle |Df| = |A_f + df·h| ≤ |A_f| + |df·h|. *)    assert (Hdfabs : real_le (real_abs (real_mult df h)) (real_mult (real_abs df) (real_abs h))).
{ apply RealSetoid.real_eq_le.
apply (real_abs_mult_req df h).
}    assert (HDf_split : real_eq Df (real_plus Af (real_mult df h))).
{ unfold Df, Af.
(* Fh − Fx == (Fh − (Fx + df·h)) + df·h         Chain: (Fh + (−(Fx+df·h))) + df·h  [assoc]             == Fh + ((−(Fx+df·h)) + df·h)             == Fh + ((−Fx + −df·h) + df·h)  [opp_plus]             == Fh + (−Fx + (−df·h + df·h))  [assoc]             == Fh + (−Fx + 0)  [plus_opp]             == Fh + (−Fx)      [plus_zero]. *)      apply (real_eq_trans        (real_plus Fh (real_opp Fx))        (real_plus Fh (real_plus (real_opp (real_plus Fx (real_mult df h))) (real_mult df h)))        (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h)))) (real_mult df h))).
{ (* X == Y1: Fh + (−Fx) == Fh + ((−(Fx+df·h)) + df·h) *)        apply (RealSetoid.real_eq_plus_compat Fh (real_opp Fx)                                              Fh (real_plus (real_opp (real_plus Fx (real_mult df h))) (real_mult df h))).
{ apply real_eq_refl.
}        { (* −Fx == (−(Fx+df·h)) + df·h: the chain backwards. *)          apply real_eq_sym.
apply (real_eq_trans            (real_plus (real_opp (real_plus Fx (real_mult df h))) (real_mult df h))            (real_plus (real_plus (real_opp Fx) (real_opp (real_mult df h))) (real_mult df h))            (real_opp Fx)).
{ apply (RealSetoid.real_eq_plus_compat (real_opp (real_plus Fx (real_mult df h))) (real_mult df h)                                                 (real_plus (real_opp Fx) (real_opp (real_mult df h))) (real_mult df h)).
{ apply (real_opp_plus Fx (real_mult df h)).
}            { apply real_eq_refl.
} }          { apply (real_eq_trans              (real_plus (real_plus (real_opp Fx) (real_opp (real_mult df h))) (real_mult df h))              (real_plus (real_opp Fx) (real_plus (real_opp (real_mult df h)) (real_mult df h)))              (real_opp Fx)).
{ apply real_eq_sym.
apply (real_plus_assoc (real_opp Fx) (real_opp (real_mult df h)) (real_mult df h)).
}            { apply (real_eq_trans                (real_plus (real_opp Fx) (real_plus (real_opp (real_mult df h)) (real_mult df h)))                (real_plus (real_opp Fx) real_zero)                (real_opp Fx)).
{ apply (RealSetoid.real_eq_plus_compat (real_opp Fx) (real_plus (real_opp (real_mult df h)) (real_mult df h))                                                      (real_opp Fx) real_zero).
{ apply real_eq_refl.
}                { apply (real_eq_trans (real_plus (real_opp (real_mult df h)) (real_mult df h))                                       (real_plus (real_mult df h) (real_opp (real_mult df h)))                                       real_zero).
{ apply (real_plus_comm (real_opp (real_mult df h)) (real_mult df h)).
}                  { apply (real_plus_opp (real_mult df h)).
} } }              { apply (real_plus_zero (real_opp Fx)).
} } } } }      { (* Y1 == Z: assoc (Y1 = Fh + (opp + df·h) == (Fh + opp) + df·h = Z) *)        apply (real_plus_assoc Fh (real_opp (real_plus Fx (real_mult df h))) (real_mult df h)).
} }    assert (HDg_split : real_eq Dg (real_plus Ag (real_mult dg h))).
{ unfold Dg, Ag.
apply (real_eq_trans        (real_plus Gh (real_opp Gx))        (real_plus Gh (real_plus (real_opp (real_plus Gx (real_mult dg h))) (real_mult dg h)))        (real_plus (real_plus Gh (real_opp (real_plus Gx (real_mult dg h)))) (real_mult dg h))).
{ apply (RealSetoid.real_eq_plus_compat Gh (real_opp Gx)                                                Gh (real_plus (real_opp (real_plus Gx (real_mult dg h))) (real_mult dg h))).
{ apply real_eq_refl.
}        { apply real_eq_sym.
apply (real_eq_trans            (real_plus (real_opp (real_plus Gx (real_mult dg h))) (real_mult dg h))            (real_plus (real_plus (real_opp Gx) (real_opp (real_mult dg h))) (real_mult dg h))            (real_opp Gx)).
{ apply (RealSetoid.real_eq_plus_compat (real_opp (real_plus Gx (real_mult dg h))) (real_mult dg h)                                                 (real_plus (real_opp Gx) (real_opp (real_mult dg h))) (real_mult dg h)).
{ apply (real_opp_plus Gx (real_mult dg h)).
}            { apply real_eq_refl.
} }          { apply (real_eq_trans              (real_plus (real_plus (real_opp Gx) (real_opp (real_mult dg h))) (real_mult dg h))              (real_plus (real_opp Gx) (real_plus (real_opp (real_mult dg h)) (real_mult dg h)))              (real_opp Gx)).
{ apply real_eq_sym.
apply (real_plus_assoc (real_opp Gx) (real_opp (real_mult dg h)) (real_mult dg h)).
}            { apply (real_eq_trans                (real_plus (real_opp Gx) (real_plus (real_opp (real_mult dg h)) (real_mult dg h)))                (real_plus (real_opp Gx) real_zero)                (real_opp Gx)).
{ apply (RealSetoid.real_eq_plus_compat (real_opp Gx) (real_plus (real_opp (real_mult dg h)) (real_mult dg h))                                                      (real_opp Gx) real_zero).
{ apply real_eq_refl.
}                { apply (real_eq_trans (real_plus (real_opp (real_mult dg h)) (real_mult dg h))                                       (real_plus (real_mult dg h) (real_opp (real_mult dg h)))                                       real_zero).
{ apply (real_plus_comm (real_opp (real_mult dg h)) (real_mult dg h)).
}                  { apply (real_plus_opp (real_mult dg h)).
} } }              { apply (real_plus_zero (real_opp Gx)).
} } } } }      { apply (real_plus_assoc Gh (real_opp (real_plus Gx (real_mult dg h))) (real_mult dg h)).
} }    (* |Δf| == |Df| ≤ Lf|h| + β_gamma + marg: triangle |Df| = |A_f + df·h| ≤ |A_f| + |df·h| + marg. *)    (* |Df| le Lf|h| + beta_gamma + marg: triangle + HAf + Hdfabs. *)    assert (HDf_le : real_le (real_abs Df)                             (real_plus (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                                    (real_mult (real_abs df) (real_abs h))) marg)).
{ apply (real_le_trans (real_abs Df)                           (real_abs (real_plus Af (real_mult df h)))                           (real_plus (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                                  (real_mult (real_abs df) (real_abs h))) marg)).
- apply RealSetoid.real_eq_le.
apply (real_abs_eq_compat Df (real_plus Af (real_mult df h))).
exact HDf_split.
- apply (real_le_trans (real_abs (real_plus Af (real_mult df h)))                             (real_plus (real_plus (real_abs Af) (real_abs (real_mult df h))) marg)                             (real_plus (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                                    (real_mult (real_abs df) (real_abs h))) marg)).
+ apply (real_abs_triangle_le_eps Af (real_mult df h) marg).
exact Hmarg.
+ apply (real_le_trans            (real_plus (real_plus (real_abs Af) (real_abs (real_mult df h))) marg)            (real_plus (real_plus (real_abs Af) (real_mult (real_abs df) (real_abs h))) marg)            (real_plus (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                   (real_mult (real_abs df) (real_abs h))) marg)).
* apply (real_le_plus_compat              (real_plus (real_abs Af) (real_abs (real_mult df h)))              (real_plus (real_abs Af) (real_mult (real_abs df) (real_abs h)))              marg marg).
-- apply (real_le_plus_compat (real_abs Af) (real_abs Af)                                         (real_abs (real_mult df h)) (real_mult (real_abs df) (real_abs h))).
++ apply real_le_refl.
++ exact Hdfabs.
-- apply real_le_refl.
* apply (real_le_plus_compat              (real_plus (real_abs Af) (real_mult (real_abs df) (real_abs h)))              (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                         (real_mult (real_abs df) (real_abs h)))              marg marg).
-- apply (real_le_plus_compat (real_abs Af)                                         (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                         (real_mult (real_abs df) (real_abs h))                                         (real_mult (real_abs df) (real_abs h))).
++ exact HAf.
++ apply real_le_refl.
-- apply real_le_refl.
}    (* |Dg| le Lg|h| + beta_gamma + marg: triangle + HAg + |dg·h| le |dg||h|. *)    assert (HDg_le : real_le (real_abs Dg)                             (real_plus (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                                    (real_mult (real_abs dg) (real_abs h))) marg)).
{ apply (real_le_trans (real_abs Dg)                           (real_abs (real_plus Ag (real_mult dg h)))                           (real_plus (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                                  (real_mult (real_abs dg) (real_abs h))) marg)).
- apply RealSetoid.real_eq_le.
apply (real_abs_eq_compat Dg (real_plus Ag (real_mult dg h))).
exact HDg_split.
- apply (real_le_trans (real_abs (real_plus Ag (real_mult dg h)))                             (real_plus (real_plus (real_abs Ag) (real_abs (real_mult dg h))) marg)                             (real_plus (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                                    (real_mult (real_abs dg) (real_abs h))) marg)).
+ apply (real_abs_triangle_le_eps Ag (real_mult dg h) marg).
exact Hmarg.
+ apply (real_le_trans            (real_plus (real_plus (real_abs Ag) (real_abs (real_mult dg h))) marg)            (real_plus (real_plus (real_abs Ag) (real_mult (real_abs dg) (real_abs h))) marg)            (real_plus (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                   (real_mult (real_abs dg) (real_abs h))) marg)).
* apply (real_le_plus_compat              (real_plus (real_abs Ag) (real_abs (real_mult dg h)))              (real_plus (real_abs Ag) (real_mult (real_abs dg) (real_abs h)))              marg marg).
-- apply (real_le_plus_compat (real_abs Ag) (real_abs Ag)                                         (real_abs (real_mult dg h)) (real_mult (real_abs dg) (real_abs h))).
++ apply real_le_refl.
++ assert (Hdgabs : real_le (real_abs (real_mult dg h)) (real_mult (real_abs dg) (real_abs h))).
{ apply RealSetoid.real_eq_le.
apply (real_abs_mult_req dg h).
}                  exact Hdgabs.
-- apply real_le_refl.
* apply (real_le_plus_compat              (real_plus (real_abs Ag) (real_mult (real_abs dg) (real_abs h)))              (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                         (real_mult (real_abs dg) (real_abs h)))              marg marg).
-- apply (real_le_plus_compat (real_abs Ag)                                         (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                         (real_mult (real_abs dg) (real_abs h))                                         (real_mult (real_abs dg) (real_abs h))).
++ exact HAg.
++ apply real_le_refl.
-- apply real_le_refl.
}    (* T1 upper bound: |T1| = |Fx·Ag| ≤ eps4|h| + Mf·β_gamma + marg       |Fx·Ag| ≤ Mf·(eps_g|h|+β_gamma) + marg (real_prod_abs_le_two)       Mf·(eps_g|h|+β_gamma) == (Mf·eps_g)|h| + Mf·β_gamma == eps4|h| + Mf·β_gamma *)    set (T1 := real_mult Fx Ag).
assert (HMeps_g : real_eq (real_mult Mf eps_g) eps4).
{ unfold eps_g.
exact (real_M_inv_absorb Mf eps4 HMf).
}    assert (HMeps_f : real_eq (real_mult Mg eps_f) eps4).
{ unfold eps_f.
exact (real_M_inv_absorb Mg eps4 HMg).
}    assert (HT1a : real_le (real_abs T1)                           (real_plus (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma)) marg)).
{ unfold T1.
apply (real_le_trans (real_abs (real_mult Fx Ag))                           (real_plus (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma)) marg)                           (real_plus (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma)) marg)).
- apply (real_prod_abs_le_two Fx Ag Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma) marg).
+ exact Hmarg.
+ exact HfM.
+ exact HAg.
- apply real_le_refl.
}    (* Mf·(eps_g|h|+β_gamma) == (Mf·eps_g)|h| + Mf·β_gamma == eps4|h| + Mf·β_gamma *)    assert (HMfdist : real_eq (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma))                              (real_plus (real_mult (real_mult Mf eps_g) (real_abs h))                                         (real_mult Mf beta_gamma))).
{ apply (real_eq_trans (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma))                           (real_plus (real_mult Mf (real_mult eps_g (real_abs h)))                                      (real_mult Mf beta_gamma))                           (real_plus (real_mult (real_mult Mf eps_g) (real_abs h))                                      (real_mult Mf beta_gamma))).
- apply (real_distrib Mf (real_mult eps_g (real_abs h)) beta_gamma).
- apply (RealSetoid.real_eq_plus_compat (real_mult Mf (real_mult eps_g (real_abs h)))                                              (real_mult Mf beta_gamma)                                              (real_mult (real_mult Mf eps_g) (real_abs h))                                              (real_mult Mf beta_gamma)).
+ apply (real_mult_assoc Mf eps_g (real_abs h)).
+ apply real_eq_refl.
}    assert (HT1 : real_le (real_abs T1)                          (real_plus (real_plus (real_mult eps4 (real_abs h))                                                (real_mult Mf beta_gamma)) marg)).
{ apply (real_le_trans (real_abs T1)                           (real_plus (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma)) marg)                           (real_plus (real_plus (real_mult eps4 (real_abs h))                                                 (real_mult Mf beta_gamma)) marg)).
- exact HT1a.
- apply (real_le_plus_compat (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma))                                   (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma))                                   marg marg).
+ apply RealSetoid.real_eq_le.
apply (real_eq_trans (real_mult Mf (real_plus (real_mult eps_g (real_abs h)) beta_gamma))                               (real_plus (real_mult (real_mult Mf eps_g) (real_abs h)) (real_mult Mf beta_gamma))                               (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma))).
* exact HMfdist.
* apply (RealSetoid.real_eq_plus_compat (real_mult (real_mult Mf eps_g) (real_abs h))                                                  (real_mult Mf beta_gamma)                                                  (real_mult eps4 (real_abs h))                                                  (real_mult Mf beta_gamma)).
-- apply (RealSetoid.real_eq_mult_compat (real_mult Mf eps_g) (real_abs h) eps4 (real_abs h)).
++ exact HMeps_g.
++ apply real_eq_refl.
-- apply real_eq_refl.
+ apply real_le_refl.
}    (* T2 upper bound: by symmetry |T2| = |Gx·Af| ≤ eps4|h| + Mg·β_gamma + marg. *)    set (T2 := real_mult Gx Af).
assert (HT2a : real_le (real_abs T2)                           (real_plus (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma)) marg)).
{ unfold T2.
apply (real_le_trans (real_abs (real_mult Gx Af))                           (real_plus (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma)) marg)                           (real_plus (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma)) marg)).
- apply (real_prod_abs_le_two Gx Af Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma) marg).
+ exact Hmarg.
+ exact HgM.
+ exact HAf.
- apply real_le_refl.
}    assert (HMgdist : real_eq (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma))                              (real_plus (real_mult (real_mult Mg eps_f) (real_abs h))                                         (real_mult Mg beta_gamma))).
{ apply (real_eq_trans (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma))                           (real_plus (real_mult Mg (real_mult eps_f (real_abs h)))                                      (real_mult Mg beta_gamma))                           (real_plus (real_mult (real_mult Mg eps_f) (real_abs h))                                      (real_mult Mg beta_gamma))).
- apply (real_distrib Mg (real_mult eps_f (real_abs h)) beta_gamma).
- apply (RealSetoid.real_eq_plus_compat (real_mult Mg (real_mult eps_f (real_abs h)))                                              (real_mult Mg beta_gamma)                                              (real_mult (real_mult Mg eps_f) (real_abs h))                                              (real_mult Mg beta_gamma)).
+ apply (real_mult_assoc Mg eps_f (real_abs h)).
+ apply real_eq_refl.
}    assert (HT2 : real_le (real_abs T2)                          (real_plus (real_plus (real_mult eps4 (real_abs h))                                                (real_mult Mg beta_gamma)) marg)).
{ apply (real_le_trans (real_abs T2)                           (real_plus (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma)) marg)                           (real_plus (real_plus (real_mult eps4 (real_abs h))                                                 (real_mult Mg beta_gamma)) marg)).
- exact HT2a.
- apply (real_le_plus_compat (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma))                                   (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma))                                   marg marg).
+ apply RealSetoid.real_eq_le.
apply (real_eq_trans (real_mult Mg (real_plus (real_mult eps_f (real_abs h)) beta_gamma))                               (real_plus (real_mult (real_mult Mg eps_f) (real_abs h)) (real_mult Mg beta_gamma))                               (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma))).
* exact HMgdist.
* apply (RealSetoid.real_eq_plus_compat (real_mult (real_mult Mg eps_f) (real_abs h))                                                  (real_mult Mg beta_gamma)                                                  (real_mult eps4 (real_abs h))                                                  (real_mult Mg beta_gamma)).
-- apply (RealSetoid.real_eq_mult_compat (real_mult Mg eps_f) (real_abs h) eps4 (real_abs h)).
++ exact HMeps_f.
++ apply real_eq_refl.
-- apply real_eq_refl.
+ apply real_le_refl.
}    (* T3 upper bound: |T3| = |Df·Dg| ≤ (Lf|h|+β_gamma+marg)(Lg|h|+β_gamma+marg)       first restate |Df| ≤ Lf|h|+β_gamma+marg (Lf := |df|+eps_f, with eps_f|h|+|df||h| == Lf|h|)       then real_abs_prod_le_eps (|Df|≤Lf|h|+β_gamma+marg, |Dg|≤Lg|h|+β_gamma+marg). *)    set (T3 := real_mult Df Dg).
(* Restatement: eps_f|h| + |df||h| == (|df|+eps_f)|h| == Lf|h|. *)    assert (HLf_form : real_eq (real_plus (real_mult eps_f (real_abs h))                                          (real_mult (real_abs df) (real_abs h)))                               (real_mult Lf (real_abs h))).
{ unfold Lf.
apply (real_eq_trans (real_plus (real_mult eps_f (real_abs h))                                      (real_mult (real_abs df) (real_abs h)))                           (real_mult (real_plus eps_f (real_abs df)) (real_abs h))                           (real_mult (real_plus (real_abs df) eps_f) (real_abs h))).
- apply (real_distrib_r eps_f (real_abs df) (real_abs h)).
- apply (RealSetoid.real_eq_mult_compat (real_plus eps_f (real_abs df)) (real_abs h)                                              (real_plus (real_abs df) eps_f) (real_abs h)).
+ apply (real_plus_comm eps_f (real_abs df)).
+ apply real_eq_refl.
}    (* |Df| ≤ Lf|h| + β_gamma + marg: restated from HDf_le. *)    assert (HDf_Lf : real_le (real_abs Df)                             (real_plus (real_mult Lf (real_abs h))                                        (real_plus beta_gamma marg))).
{ apply (real_le_trans (real_abs Df)                           (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                      (real_plus (real_mult (real_abs df) (real_abs h)) marg))                           (real_plus (real_mult Lf (real_abs h))                                      (real_plus beta_gamma marg))).
- (* From HDf_le: |Df| ≤ ((eps_f|h|+β_gamma) + |df||h|) + marg, restated as (eps_f|h|+β_gamma) + (|df||h|+marg). *)        apply (real_le_trans (real_abs Df)                             (real_plus (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                                   (real_mult (real_abs df) (real_abs h))) marg)                             (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                        (real_plus (real_mult (real_abs df) (real_abs h)) marg))).
+ exact HDf_le.
+ apply RealSetoid.real_eq_le.
apply real_eq_sym.
apply (real_plus_assoc (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                                                    (real_mult (real_abs df) (real_abs h)) marg).
- (* (eps_f|h|+β_gamma) + (|df||h|+marg) == (eps_f|h|+|df||h|) + (β_gamma+marg) == Lf|h| + (β_gamma+marg) *)        apply RealSetoid.real_eq_le.
apply (real_eq_trans          (real_plus (real_plus (real_mult eps_f (real_abs h)) beta_gamma)                     (real_plus (real_mult (real_abs df) (real_abs h)) marg))          (real_plus (real_plus (real_mult eps_f (real_abs h)) (real_mult (real_abs df) (real_abs h)))                     (real_plus beta_gamma marg))          (real_plus (real_mult Lf (real_abs h)) (real_plus beta_gamma marg))).
+ apply (real_plus_swap (real_mult eps_f (real_abs h)) beta_gamma                                (real_mult (real_abs df) (real_abs h)) marg).
+ apply (RealSetoid.real_eq_plus_compat                   (real_plus (real_mult eps_f (real_abs h)) (real_mult (real_abs df) (real_abs h)))                   (real_plus beta_gamma marg)                   (real_mult Lf (real_abs h))                   (real_plus beta_gamma marg)).
* exact HLf_form.
* apply real_eq_refl.
}    (* |Dg| ≤ Lg|h| + β_gamma + marg: by symmetry. *)    assert (HLg_form : real_eq (real_plus (real_mult eps_g (real_abs h))                                          (real_mult (real_abs dg) (real_abs h)))                               (real_mult Lg (real_abs h))).
{ unfold Lg.
apply (real_eq_trans (real_plus (real_mult eps_g (real_abs h))                                      (real_mult (real_abs dg) (real_abs h)))                           (real_mult (real_plus eps_g (real_abs dg)) (real_abs h))                           (real_mult (real_plus (real_abs dg) eps_g) (real_abs h))).
- apply (real_distrib_r eps_g (real_abs dg) (real_abs h)).
- apply (RealSetoid.real_eq_mult_compat (real_plus eps_g (real_abs dg)) (real_abs h)                                              (real_plus (real_abs dg) eps_g) (real_abs h)).
+ apply (real_plus_comm eps_g (real_abs dg)).
+ apply real_eq_refl.
}    assert (HDg_Lg : real_le (real_abs Dg)                             (real_plus (real_mult Lg (real_abs h))                                        (real_plus beta_gamma marg))).
{ apply (real_le_trans (real_abs Dg)                           (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                      (real_plus (real_mult (real_abs dg) (real_abs h)) marg))                           (real_plus (real_mult Lg (real_abs h))                                      (real_plus beta_gamma marg))).
- apply (real_le_trans (real_abs Dg)                             (real_plus (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                                   (real_mult (real_abs dg) (real_abs h))) marg)                             (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                        (real_plus (real_mult (real_abs dg) (real_abs h)) marg))).
+ exact HDg_le.
+ apply RealSetoid.real_eq_le.
apply real_eq_sym.
apply (real_plus_assoc (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                                 (real_mult (real_abs dg) (real_abs h)) marg).
- apply RealSetoid.real_eq_le.
apply (real_eq_trans          (real_plus (real_plus (real_mult eps_g (real_abs h)) beta_gamma)                     (real_plus (real_mult (real_abs dg) (real_abs h)) marg))          (real_plus (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs dg) (real_abs h)))                     (real_plus beta_gamma marg))          (real_plus (real_mult Lg (real_abs h)) (real_plus beta_gamma marg))).
+ apply (real_plus_swap (real_mult eps_g (real_abs h)) beta_gamma                                (real_mult (real_abs dg) (real_abs h)) marg).
+ apply (RealSetoid.real_eq_plus_compat                   (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs dg) (real_abs h)))                   (real_plus beta_gamma marg)                   (real_mult Lg (real_abs h))                   (real_plus beta_gamma marg)).
* exact HLg_form.
* apply real_eq_refl.
}    (* |T3| ≤ (Lf|h|+β_gamma+marg)·(Lg|h|+β_gamma+marg) + marg: real_abs_prod_le_eps *)    assert (HT3a : real_le (real_abs T3)                           (real_plus (real_mult (real_plus (real_mult Lf (real_abs h)) (real_plus beta_gamma marg))                                                 (real_plus (real_mult Lg (real_abs h)) (real_plus beta_gamma marg)))                                      marg)).
{ unfold T3.
apply (real_le_trans (real_abs (real_mult Df Dg))                           (real_mult (real_abs Df) (real_abs Dg))                           (real_plus (real_mult (real_plus (real_mult Lf (real_abs h)) (real_plus beta_gamma marg))                                                 (real_plus (real_mult Lg (real_abs h)) (real_plus beta_gamma marg)))                                      marg)).
- apply RealSetoid.real_eq_le.
apply (real_abs_mult_req Df Dg).
- apply (real_abs_prod_le_eps Df Dg               (real_plus (real_mult Lf (real_abs h)) (real_plus beta_gamma marg))               (real_plus (real_mult Lg (real_abs h)) (real_plus beta_gamma marg))               marg).
+ exact Hmarg.
+ exact HDf_Lf.
+ exact HDg_Lg.
}    (* Den·|h|² ≤ eps2|h| + marg: real_abs_h_sq_le_eps (A=Den, eps3=inv(Den)·eps2, |h|<eps3)       with Den·eps3 == eps2 via real_M_inv_absorb. *)    assert (HDen_eps3 : real_eq (real_mult Den eps3) eps2).
{ unfold eps3.
exact (real_M_inv_absorb Den eps2 HDen).
}    assert (HDen_sq : real_le (real_mult Den (real_mult (real_abs h) (real_abs h)))                              (real_plus (real_mult eps2 (real_abs h)) marg)).
{ apply (real_le_trans (real_mult Den (real_mult (real_abs h) (real_abs h)))                           (real_plus (real_mult (real_mult Den eps3) (real_abs h)) marg)                           (real_plus (real_mult eps2 (real_abs h)) marg)).
- apply (real_abs_h_sq_le_eps Den h eps3 marg HDen Hheps3 Hmarg).
- apply (real_le_plus_compat (real_mult (real_mult Den eps3) (real_abs h))                                   (real_mult eps2 (real_abs h))                                   marg marg).
+ apply RealSetoid.real_eq_le.
apply (RealSetoid.real_eq_mult_compat (real_mult Den eps3) (real_abs h) eps2 (real_abs h)).
* exact HDen_eps3.
* apply real_eq_refl.
+ apply real_le_refl.
}    (* T3 expansion: (Lf|h|+B)(Lg|h|+B) == Den|h|² + B·(Lf+Lg)·|h| + B², with B := β_gamma+marg       expansion chain: left distributivity twice → recombination by comm → Den := Lf·Lg *)    set (B := real_plus beta_gamma marg).
assert (HB : real_lt real_zero B) by (unfold B; apply real_plus_positive; [exact Hbg | exact Hmarg]).
(* (Lf|h|+B)(Lg|h|+B) == Lf·Lg·|h|² + (Lf+Lg)·B·|h| + B²       First prove the weaker form: ≤ (Lf|h|+B)(Lg|h|+B) == the expansion (the budget done pointwise at the Q layer).       The pointwise route directly: |T3| ≤ (Lf|h|+B)(Lg|h|+B) + marg is already available (HT3a);       the expanded upper bound of (Lf|h|+B)(Lg|h|+B) is now proved pointwise at the Q layer.       Assembly: |D| ≤ |T1|+|T2|+|T3| + 2marg (triangle twice)              ≤ (eps4+eps4+eps2)|h| + [Mf·β_gamma + Mg·β_gamma + budget_T3] + 5marg       where budget_T3 is pointwise ≤ eps' (at the Q layer: Mf·β_gamma ≤ 3eps'/128, etc.). *)    (* |D| == |T1+T2+T3| restatement bridge (HD) + triangle. *)    set (TSum := real_plus (real_plus T1 T2) T3).
assert (HD_TSum : real_eq D TSum).
{ unfold TSum, T1, T2, T3.
apply (real_eq_trans D        (real_plus (real_plus (real_mult Fx Ag) (real_mult Gx Af)) (real_mult Df Dg))        (real_plus (real_plus T1 T2) T3)).
- exact HD.
- apply real_eq_refl.
}    assert (HTri : real_le (real_abs TSum)                           (real_plus (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) marg) (real_abs T3)) marg)).
{ unfold TSum.
apply (real_le_trans (real_abs (real_plus (real_plus T1 T2) T3))                           (real_plus (real_plus (real_abs (real_plus T1 T2)) (real_abs T3)) marg)                           (real_plus (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) marg) (real_abs T3)) marg)).
- apply (real_abs_triangle_le_eps (real_plus T1 T2) T3 marg).
exact Hmarg.
- apply (real_le_plus_compat          (real_plus (real_abs (real_plus T1 T2)) (real_abs T3))          (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) marg) (real_abs T3))          marg marg).
+ apply (real_le_plus_compat (real_abs (real_plus T1 T2))                                     (real_plus (real_plus (real_abs T1) (real_abs T2)) marg)                                     (real_abs T3) (real_abs T3)).
* apply (real_abs_triangle_le_eps T1 T2 marg).
exact Hmarg.
* apply real_le_refl.
+ apply real_le_refl.
}    (* |D| ≤ |TSum| restatement bridge + triangle + the T1/T2/T3 bounds. *)    assert (HD_le : real_le (real_abs D) (real_abs TSum)).
{ apply RealSetoid.real_eq_le.
apply (real_abs_eq_compat D TSum).
exact HD_TSum.
}    (* |D| ≤ |TSum| ≤ (|T1|+|T2|+|T3|)+2marg (triangle twice)         ≤ ((eps4|h|+Mf·β_gamma+marg) + (eps4|h|+Mg·β_gamma+marg) + |T3|) + 2marg (HT1/HT2)       Target shape: +((eps4|h|+Mf·β_gamma+marg) + (eps4|h|+Mg·β_gamma+marg)) + |T3| + 2marg *)    assert (Hsum_bnd : real_le (real_abs D)        (real_plus          (real_plus (real_plus            (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma)) marg)            (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma)) marg))            (real_abs T3))          (real_plus marg marg))).
{ apply (real_le_trans (real_abs D) (real_abs TSum)        (real_plus          (real_plus (real_plus            (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma)) marg)            (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma)) marg))            (real_abs T3))          (real_plus marg marg))).
- exact HD_le.
- apply (real_le_trans (real_abs TSum)          (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) (real_abs T3)) (real_plus marg marg))          (real_plus            (real_plus (real_plus              (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma)) marg)              (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma)) marg))              (real_abs T3))            (real_plus marg marg))).
+ (* |TSum| ≤ (|T1|+|T2|+|T3|)+2marg: after HTri, absorbing the marg structure gives (|T1|+|T2|+marg+|T3|)+marg == (|T1|+|T2|+|T3|)+(marg+marg). *)          apply (real_le_trans (real_abs TSum)              (real_plus (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) marg) (real_abs T3)) marg)              (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) (real_abs T3)) (real_plus marg marg))).
* exact HTri.
* apply RealSetoid.real_eq_le.
{ apply (real_eq_trans                (real_plus (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) marg) (real_abs T3)) marg)                (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) marg) (real_plus (real_abs T3) marg))                (real_plus (real_plus (real_plus (real_abs T1) (real_abs T2)) (real_abs T3)) (real_plus marg marg))).
{ (* Left == middle: (((a+b)+marg)+|T3|)+marg == ((a+b)+marg)+(|T3|+marg) (assoc backwards). *)                apply real_eq_sym.
apply (real_plus_assoc (real_plus (real_plus (real_abs T1) (real_abs T2)) marg) (real_abs T3) marg).
}              { (* Middle == right: ((a+b)+marg)+(|T3|+marg) == ((a+b)+|T3|)+(marg+marg) (swap). *)                apply (real_plus_swap (real_plus (real_abs T1) (real_abs T2)) marg (real_abs T3) marg).
} }        + (* Substitute HT1/HT2: |T1| ≤ eps4|h|+Mf·β_gamma+marg and |T2| ≤ eps4|h|+Mg·β_gamma+marg. *)          apply (real_le_plus_compat            (real_plus (real_plus (real_abs T1) (real_abs T2)) (real_abs T3))            (real_plus (real_plus              (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma)) marg)              (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma)) marg))              (real_abs T3))            (real_plus marg marg) (real_plus marg marg)).
* apply (real_le_plus_compat              (real_plus (real_abs T1) (real_abs T2))              (real_plus                (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma)) marg)                (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma)) marg))              (real_abs T3) (real_abs T3)).
-- apply (real_le_plus_compat (real_abs T1)                       (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma)) marg)                       (real_abs T2)                       (real_plus (real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma)) marg)).
++ exact HT1.
++ exact HT2.
-- apply real_le_refl.
* apply real_le_refl.
}    (* ============ Final: |D| ≤ eps|h| + eps' (the budget done pointwise at the Q layer; the Or encoding of real_le cannot express a general non-strict ≤) ============       Structure: Hsum_bnd (proved) → replace |T3| by HT3a → expand T3 (ring) → replace Den·|h|² by HDen_sq             → ring rearrangement == eps|h| + ShareSum → budget ≤ c_total·eps' (c_total := 889/ < 1)       The budget is exact pointwise (the real_inv_pos projection == Qinv(u n) at n ≥ N0, βK ≤ eps' and β ≤ 1 without slippage):         Mfβγ ≤ 3eps'/128 (Mf ≤ K/64, βγ == 3β/2, βK ≤ eps'), Mg symmetric         Lin ≤ 97eps'/256 ((Lf+Lg)|h| ≤ K/4, B == 97β/64, βK ≤ eps')         BB ≤ 9409eps'/(4096·320) ≤ eps'/128 (β ≤ 1 gives β² ≤ β, K ≥ 320)         6marg ≤ 3eps'/10240 ≤ eps'/ (marg == β/64)       Witness eps0q := e0'/4; Hsum_bnd/HT3a/HDen_sq are pointwise-realized with tolerance e0'/128 each (real_le_pointwise_eps)       Surplus: 1 − 889/ − 4/128 − 1/4 == 583/ > 0 . *)    set (A1 := real_plus (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma)).
set (A2 := real_plus (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma)).
set (Prod := real_mult (real_plus (real_mult Lf (real_abs h)) B)                           (real_plus (real_mult Lg (real_abs h)) B)).
set (Den_h2 := real_mult Den (real_mult (real_abs h) (real_abs h))).
set (Lin := real_mult (real_mult (real_plus Lf Lg) B) (real_abs h)).
set (BB := real_mult B B).
set (HsumRHS := real_plus      (real_plus (real_plus (real_plus A1 marg) (real_plus A2 marg)) (real_abs T3))      (real_plus marg marg)).
set (Hsum1RHS := real_plus      (real_plus (real_plus (real_plus A1 marg) (real_plus A2 marg)) (real_plus Prod marg))      (real_plus marg marg)).
set (Hsum2RHS := real_plus      (real_plus (real_plus (real_plus A1 marg) (real_plus A2 marg))                 (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h)) marg) Lin) BB) marg))      (real_plus marg marg)).
set (ShareSum := real_plus      (real_plus (real_plus (real_plus (real_mult Mf beta_gamma) (real_mult Mg beta_gamma)) Lin) BB)      (real_plus marg (real_plus marg (real_plus marg (real_plus marg (real_plus marg marg)))))).
assert (Hfinal : real_le (real_abs D) (real_plus (real_mult eps (real_abs h)) eps')).
{      (* Witnesses and rates (destruct the compound witnesses referenced by Heps'/HK/HLf/HLg first, then destruct the objects proper). *)      destruct real_two_pos_local as [e2 [He2 [N2 HN2]]].
pose proof Hc64 as Hc64_orig.
pose proof Hc64 as Hc64_save.
(* destructing the assumption would generalize and rewrite the set body of marg (marg references Hc64);
   destruct the copy Hc64_x instead so that Hc64 survives; with marg ≡ margp (both using Hc64),
   every projection assertion then closes by reflexivity. *)
pose proof Hc64 as Hc64_x.
set (margp := real_mult beta (real_inv_pos (real_const (Z.of_nat 64 # 1)) Hc64)).
destruct Hc64_x as [c64 [Hc64pos [N64 HN64]]].
destruct Hbeta as [b0 [Hb0 [Nb HNb]]].
(* destructing a term generalizes and rewrites the proof terms inside context set bodies (dKf/dKg reference them);
   pose copies first, then destruct the copies, keeping the original proof terms inside the dKf/dKg bodies
   (the same pattern as HK1_pos/Hc64_save). *)
pose proof (real_mult_positive e8 Lf He8 HLf) as H8Lf_pos.
destruct H8Lf_pos as [e8Lf [He8Lf [N8Lf HN8Lf]]].
pose proof (real_mult_positive e8 Lg He8 HLg) as H8Lg_pos.
destruct H8Lg_pos as [e8Lg [He8Lg [N8Lg HN8Lg]]].
(* destructing a term generalizes and replaces proof terms inside context set bodies (the beta body references one);
   pose the copy HK1_pos first, destruct the copy, keeping the original proof term inside the beta body
   (the same lesson as margp/Hc64_save). *)
pose proof (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps')) as HK1_pos.
destruct HK1_pos as [k10 [Hk10 [Nk1 HNk1]]].
pose proof HK as HK_orig.
pose proof HK as HK_save.
pose proof Heps' as Heps'_orig.
pose proof Heps' as Heps'_save.
destruct Heps'_save as [e0' [He0' [N0' HN0']]].
destruct HK_save as [K0 [HK0 [NK HNK]]].
pose proof HLf as HLf_orig.
pose proof HLf as HLf_x.
destruct HLf_x as [eLf [HeLf [NLf HNLf]]].
pose proof HLg as HLg_orig.
pose proof HLg as HLg_x.
destruct HLg_x as [eLg [HeLg [NLg HNLg]]].
destruct HB as [bB [HbB [NB HNB]]].
destruct HhdKf as [cdf [Hcdf [Ndf HNdf]]].
destruct HhdKg as [cdg [Hcdg [Ndg HNdg]]].
set (eps0q := Qmult (Qmake 1 4) e0').
assert (Heps0q : QltT 0 eps0q).
{ apply Qlt_to_QltT.
unfold eps0q.
apply (Qmult_lt_0_compat (Qmake 1 4) e0').
- simpl.
reflexivity.
- apply QltT_to_Qlt.
exact He0'.
}      assert (Hs0 : QltT 0 (Qdiv e0' 128)).
{ apply Qlt_to_QltT.
unfold Qdiv.
apply (Qmult_lt_0_compat e0' (Qinv (Qmake 128 1))).
- apply QltT_to_Qlt.
exact He0'.
- apply Qinv_lt_0_compat.
vm_compute.
reflexivity.
}      (* Initial step: real_le → real_lt (the Or encoding cannot express a general non-strict ≤ directly, so go through the witness). *)      apply (RealSetoid.real_lt_le_iff_req (real_abs D) (real_plus (real_mult eps (real_abs h)) eps')).
left.
unfold real_lt.
exists eps0q.
split.
- exact Heps0q.
- (* Pointwise at the Q layer. *)        (* Pointwise realization of the three real_le chains (each with tolerance e0'/128; the Or-encoding eq branch is handled uniformly by real_le_pointwise_eps). *)        destruct (real_le_pointwise_eps (real_abs D) HsumRHS (Qdiv e0' 128) Hsum_bnd Hs0) as [Nsum HNsum].
destruct (real_le_pointwise_eps (real_abs T3) (real_plus Prod marg) (Qdiv e0' 128) HT3a Hs0) as [Nt3 HNt3].
destruct (real_le_pointwise_eps Den_h2 (real_plus (real_mult eps2 (real_abs h)) marg) (Qdiv e0' 128) HDen_sq Hs0) as [Nden HNden].
(* real_inv_proj rates (the real_inv_pos projection lemma — its returned rates are added into N_max so that n is large enough). *)
destruct (real_inv_proj (real_const (Z.of_nat 64 # 1)) Hc64) as [N64p HN64p].
destruct (real_inv_proj (real_mult K (real_plus real_one eps'))
           (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps')))
  as [NK1p HNK1p].
destruct (real_inv_proj (real_mult e8 Lf) (real_mult_positive e8 Lf He8 HLf)) as [N8Lfp HN8Lfp].
destruct (real_inv_proj (real_mult e8 Lg) (real_mult_positive e8 Lg He8 HLg)) as [N8Lgp HN8Lgp].
set (N_extra := Nat.max N64p (Nat.max NK1p (Nat.max N8Lfp N8Lgp))).
(* A binary let-tree for N_max (lia explodes exponentially on max with 2^15 cases and 4.9GB of memory — lia must not be used;           use the deterministic le_max_l/r chain instead, which runs in milliseconds; unify unfolds the lets automatically so apply Nat.le_max_l hits directly). *)        set (N_a := Nat.max N0' N2).
set (N_b := Nat.max N64 Nb).
set (N_c := Nat.max NK NLf).
set (N_d := Nat.max NLg NB).
set (N_e := Nat.max N8Lf N8Lg).
set (N_f := Nat.max Nk1 Ndf).
set (N_g := Nat.max Ndg Nsum).
set (N_h := Nat.max Nt3 Nden).
set (N_ab := Nat.max N_a N_b).
set (N_cd := Nat.max N_c N_d).
set (N_ef := Nat.max N_e N_f).
set (N_gh := Nat.max N_g N_h).
set (N_abcd := Nat.max N_ab N_cd).
set (N_efgh := Nat.max N_ef N_gh).
set (N_max := Nat.max N_abcd N_efgh).
exists (Nat.max N_max N_extra).
intros n Hn.
assert (Hn_max : (N_max <= n)%nat).
{ apply (Nat.le_trans _ (Nat.max N_max N_extra) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
assert (Hn0' : (N0' <= n)%nat).
{ apply (Nat.le_trans _ N_a _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_ab _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (Hn2 : (N2 <= n)%nat).
{ apply (Nat.le_trans _ N_a _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_ab _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (Hn64 : (N64 <= n)%nat).
{ apply (Nat.le_trans _ N_b _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_ab _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (Hnb : (Nb <= n)%nat).
{ apply (Nat.le_trans _ N_b _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_ab _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (Hnk : (NK <= n)%nat).
{ apply (Nat.le_trans _ N_c _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_cd _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (HnLf : (NLf <= n)%nat).
{ apply (Nat.le_trans _ N_c _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_cd _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (HnLg : (NLg <= n)%nat).
{ apply (Nat.le_trans _ N_d _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_cd _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (HnB : (NB <= n)%nat).
{ apply (Nat.le_trans _ N_d _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_cd _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_abcd _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_l | exact Hn_max].
}        assert (Hn8Lf : (N8Lf <= n)%nat).
{ apply (Nat.le_trans _ N_e _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_ef _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}        assert (Hn8Lg : (N8Lg <= n)%nat).
{ apply (Nat.le_trans _ N_e _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_ef _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}        assert (Hnk1 : (Nk1 <= n)%nat).
{ apply (Nat.le_trans _ N_f _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_ef _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}        assert (Hndf : (Ndf <= n)%nat).
{ apply (Nat.le_trans _ N_f _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_ef _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}        assert (Hndg : (Ndg <= n)%nat).
{ apply (Nat.le_trans _ N_g _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_gh _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}        assert (Hnsum : (Nsum <= n)%nat).
{ apply (Nat.le_trans _ N_g _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_gh _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}        assert (Hnt3 : (Nt3 <= n)%nat).
{ apply (Nat.le_trans _ N_h _); [apply Nat.le_max_l | ].
apply (Nat.le_trans _ N_gh _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}        assert (Hnden : (Nden <= n)%nat).
{ apply (Nat.le_trans _ N_h _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_gh _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_efgh _); [apply Nat.le_max_r | ].
apply (Nat.le_trans _ N_max _); [apply Nat.le_max_r | exact Hn_max].
}
      (* real_inv_proj rates ≤ n (a 4-level N_extra chain; lia must not be used). *)
      assert (HN64p_le : (N64p <= n)%nat).
      { apply (Nat.le_trans _ N_extra _); [apply Nat.le_max_l | ].
        apply (Nat.le_trans _ (Nat.max N_max N_extra) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      assert (HNK1p_le : (NK1p <= n)%nat).
      { apply (Nat.le_trans _ (Nat.max NK1p (Nat.max N8Lfp N8Lgp)) _).
        - apply Nat.le_max_l.
        - apply (Nat.le_trans _ N_extra _); [apply Nat.le_max_r | ].
          apply (Nat.le_trans _ (Nat.max N_max N_extra) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      assert (HN8Lfp_le : (N8Lfp <= n)%nat).
      { apply (Nat.le_trans _ (Nat.max N8Lfp N8Lgp) _).
        - apply Nat.le_max_l.
        - apply (Nat.le_trans _ (Nat.max NK1p (Nat.max N8Lfp N8Lgp)) _).
          + apply Nat.le_max_r.
          + apply (Nat.le_trans _ N_extra _); [apply Nat.le_max_r | ].
            apply (Nat.le_trans _ (Nat.max N_max N_extra) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      assert (HN8Lgp_le : (N8Lgp <= n)%nat).
      { apply (Nat.le_trans _ (Nat.max N8Lfp N8Lgp) _).
        - apply Nat.le_max_r.
        - apply (Nat.le_trans _ (Nat.max NK1p (Nat.max N8Lfp N8Lgp)) _).
          + apply Nat.le_max_r.
          + apply (Nat.le_trans _ N_extra _); [apply Nat.le_max_r | ].
            apply (Nat.le_trans _ (Nat.max N_max N_extra) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      (* Projection abbreviations. *)      set (hn := projT1 (real_abs h) n).
set (en := projT1 eps n).
set (en' := projT1 eps' n).
set (halfn := projT1 half n).
set (quartern := projT1 quarter n).
set (eps4n := projT1 eps4 n).
set (eps2n := projT1 eps2 n).
set (Mfn := projT1 Mf n).
set (Mgn := projT1 Mg n).
set (Mfpn := projT1 Mfp n).
set (Mgpn := projT1 Mgp n).
set (Kn := projT1 K n).
set (betan := projT1 beta n).
set (gaman := projT1 gamma n).
set (bgamman := projT1 beta_gamma n).
set (margn := projT1 margp n).
set (Lfn := projT1 Lf n).
set (Lgn := projT1 Lg n).
set (Denn := projT1 Den n).
set (Bn := projT1 B n).
set (T3n := projT1 (real_abs T3) n).
set (Prodn := projT1 Prod n).
set (Denh2n := projT1 Den_h2 n).
set (Linn := projT1 Lin n).
set (BBn := projT1 BB n).
set (S12n := projT1 (real_plus (real_mult Mf beta_gamma) (real_mult Mg beta_gamma)) n).
set (ShareSumn := projT1 ShareSum n).
set (A1n := projT1 A1 n).
set (A2n := projT1 A2 n).
set (HsumRn := projT1 HsumRHS n).
set (Hsum1n := projT1 Hsum1RHS n).
set (Hsum2n := projT1 Hsum2RHS n).
set (inv64n := projT1 (real_inv_pos (real_const (Z.of_nat 64 # 1)) Hc64) n).
set (invK1n := projT1 (real_inv_pos (real_mult K (real_plus real_one eps'))                  (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps'))) n).
(* Constant bridges (by vm_compute). *)      assert (Hc2 : Qeq (Qinv (Qmake 2 1)) (Qmake 1 2)) by (vm_compute; reflexivity).
assert (Hc64q : Qeq (Qinv (Qmake 64 1)) (Qmake 1 64)) by (vm_compute; reflexivity).
assert (Hc8q : Qeq (Qinv (Qmake 8 1)) (Qmake 1 8)) by (vm_compute; reflexivity).
assert (Hc32 : Qeq (Qmake 1 2 + Qmake 1 1) (Qmake 3 2)) by (vm_compute; reflexivity).
assert (Hc97 : Qeq (Qmake 3 2 + Qmake 1 64) (Qmake 97 64)) by (vm_compute; reflexivity).
assert (Hc9409 : Qeq (Qmult (Qmake 97 64) (Qmake 97 64)) (Qmake 9409 4096)) by (vm_compute; reflexivity).
assert (Hc9409b : Qle (Qmake 9409 1310720) (Qmake 1 128)) by (vm_compute; discriminate).
assert (Hc3_10240 : Qle (Qmake 3 10240) (Qmake 1 2048)) by (vm_compute; discriminate).
assert (Hc_total : Qeq (Qmake 3 64 + Qmake 97 256 + Qmake 1 128 + Qmake 1 2048) (Qmake 889 2048)) by (vm_compute; reflexivity).
assert (Hc_slack : Qlt 0 (Qmake 1 1 - Qmake 889 2048 - Qmake 3 128 - Qmake 1 4)) by (vm_compute; reflexivity).
(* Basic pointwise facts. *)      assert (Heps0'n : Qlt e0' en').
{ unfold en'.
apply (Qlt_le_trans _ (projT1 eps' n - projT1 real_zero n) _).
- apply QltT_to_Qlt.
exact (HN0' n (NatLe_lift _ _ Hn0')).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
rewrite Hz.
ring.
}      assert (Hen'pos : Qlt 0 en').
{ apply (Qlt_trans _ e0' _); [apply QltT_to_Qlt; exact He0' | exact Heps0'n].
}      assert (Hhalf_pt : halfn == Qinv (Qmake 2 1)).
{ unfold halfn, half.
cbn [real_inv_pos real_plus real_one projT1].
assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
rewrite Hl.
reflexivity.
}      assert (Hinv64 : inv64n == Qinv (Z.of_nat 64 # 1)).
{ change (projT1 (real_inv_pos (real_const (Z.of_nat 64 # 1)) Hc64) n == Qinv (Z.of_nat 64 # 1)).
apply (qeqT_imp_qeq _ _ (HN64p n (NatLe_lift _ _ HN64p_le))).
}
      assert (Hinv64' : inv64n == Qinv (Qmake 64 1)).
{ apply (Qeq_trans _ _ _ Hinv64).
vm_compute.
reflexivity.
}      assert (HinvK1 : invK1n == Qinv (Kn * (1 + en'))).
{ change (projT1 (real_inv_pos (real_mult K (real_plus real_one eps'))
                   (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps'))) n
        == Qinv (Kn * (1 + en'))).
assert (Hp : projT1 (real_mult K (real_plus real_one eps')) n == Kn * (1 + en')).
{ unfold Kn, en'.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj K (real_plus real_one eps') n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one eps' n)).
  cbn [projT1].
  reflexivity. }
rewrite <- Hp.
apply (qeqT_imp_qeq _ _ (HNK1p n (NatLe_lift _ _ HNK1p_le))).
}
      (* Projection-unfolding assertion. *)      assert (HprojA1 : A1n == eps4n * hn + Mfn * bgamman).
{ unfold A1n, A1, eps4n, hn, Mfn, bgamman.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps4 (real_abs h)) (real_mult Mf beta_gamma) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps4 (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Mf beta_gamma n)).
reflexivity.
}      assert (HprojA2 : A2n == eps4n * hn + Mgn * bgamman).
{ unfold A2n, A2, eps4n, hn, Mgn, bgamman.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps4 (real_abs h)) (real_mult Mg beta_gamma) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps4 (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Mg beta_gamma n)).
reflexivity.
}      assert (HprojProd : Prodn == (Lfn * hn + Bn) * (Lgn * hn + Bn)).
{ unfold Prodn, Prod, Lfn, Lgn, hn, Bn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_plus (real_mult Lf (real_abs h)) B)                                       (real_plus (real_mult Lg (real_abs h)) B) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult Lf (real_abs h)) B n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Lf (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult Lg (real_abs h)) B n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Lg (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
reflexivity.
}      assert (HDenn : Denn == Lfn * Lgn).
{ unfold Denn, Den, Lfn, Lgn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Lf Lg n)).
reflexivity.
}      assert (HprojDenh2 : Denh2n == Denn * (hn * hn)).
{ unfold Denh2n, Den_h2, Denn, hn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Den (real_mult (real_abs h) (real_abs h)) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_abs h) (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
reflexivity.
}      assert (HprojLin : Linn == (Lfn + Lgn) * Bn * hn).
{ unfold Linn, Lin, Lfn, Lgn, Bn, hn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult (real_plus Lf Lg) B) (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_plus Lf Lg) B n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Lf Lg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
reflexivity.
}      assert (HprojBB : BBn == Bn * Bn).
{ unfold BBn, BB, Bn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj B B n)).
reflexivity.
}      assert (Hprojmarg : margn == betan * inv64n).
{ change (projT1 (real_mult beta (real_inv_pos (real_const (Z.of_nat 64 # 1)) Hc64)) n == betan * inv64n).
unfold betan, inv64n.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj beta (real_inv_pos (real_const (Z.of_nat 64 # 1)) Hc64) n)).
reflexivity.
}      assert (Hprojbg : bgamman == betan + gaman).
{ unfold bgamman, beta_gamma, betan, gaman.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj beta gamma n)).
reflexivity.
}      assert (Hprojgam : gaman == halfn * betan).
{ unfold gaman, gamma, halfn, betan.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj half beta n)).
reflexivity.
}      assert (Hprojeps4 : eps4n == quartern * en).
{ unfold eps4n, eps4, quartern, en.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj quarter eps n)).
reflexivity.
}      assert (Hprojeps2 : eps2n == halfn * en).
{ unfold eps2n, eps2, halfn, en.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj half eps n)).
reflexivity.
}      assert (Hprojq : quartern == halfn * halfn).
{ unfold quartern, quarter, halfn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj half half n)).
reflexivity.
}      assert (Hprojbeta : betan == en' * invK1n).
{ change (projT1 (real_mult eps' (real_inv_pos (real_mult K (real_plus real_one eps'))
                 (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps')))) n
          == en' * invK1n).
unfold en', invK1n.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_inv_pos (real_mult K (real_plus real_one eps'))
                 (real_mult_positive K (real_plus real_one eps') HK (real_one_plus_pos eps' Heps'))) n)).
reflexivity.
}      assert (HprojS12 : S12n == Mfn * bgamman + Mgn * bgamman).
{ unfold S12n, Mfn, Mgn, bgamman.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult Mf beta_gamma) (real_mult Mg beta_gamma) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Mf beta_gamma n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Mg beta_gamma n)).
reflexivity.
}      assert (HprojShare : ShareSumn == S12n + Linn + BBn + (margn + (margn + (margn + (margn + (margn + margn)))))).
{ unfold ShareSumn, ShareSum, S12n, Linn, BBn, margn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj          (real_plus (real_plus (real_plus (real_mult Mf beta_gamma) (real_mult Mg beta_gamma)) Lin) BB)          (real_plus marg (real_plus marg (real_plus marg (real_plus marg (real_plus marg marg))))) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj          (real_plus (real_plus (real_mult Mf beta_gamma) (real_mult Mg beta_gamma)) Lin) BB n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj          (real_plus (real_mult Mf beta_gamma) (real_mult Mg beta_gamma)) Lin n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult Mf beta_gamma) (real_mult Mg beta_gamma) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Mf beta_gamma n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj Mg beta_gamma n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg (real_plus marg (real_plus marg (real_plus marg (real_plus marg marg)))) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg (real_plus marg (real_plus marg (real_plus marg marg))) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg (real_plus marg (real_plus marg marg)) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg (real_plus marg marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg marg n)).
(* Lin/BB kept as projT1 Lin n / projT1 BB n (the RHS has the same shape), so reflexivity closes directly. *)
reflexivity.
}      assert (HprojHsumR : HsumRn == ((A1n + margn) + (A2n + margn) + T3n) + (margn + margn)).
{ unfold HsumRn, HsumRHS, A1n, A2n, margn, T3n.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_plus A1 marg) (real_plus A2 marg)) (real_abs T3))                                       (real_plus marg marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus A1 marg) (real_plus A2 marg)) (real_abs T3) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus A1 marg) (real_plus A2 marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj A1 marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj A2 marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg marg n)).
reflexivity.
}      assert (HprojHsum1 : Hsum1n == ((A1n + margn) + (A2n + margn) + (Prodn + margn)) + (margn + margn)).
{ unfold Hsum1n, Hsum1RHS, A1n, A2n, margn, Prodn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_plus A1 marg) (real_plus A2 marg)) (real_plus Prod marg))                                       (real_plus marg marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus A1 marg) (real_plus A2 marg)) (real_plus Prod marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus A1 marg) (real_plus A2 marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj A1 marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj A2 marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Prod marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg marg n)).
reflexivity.
}      assert (HprojHsum2 : Hsum2n ==        ((A1n + margn) + (A2n + margn) + (((eps2n * hn + margn) + Linn) + BBn + margn)) + (margn + margn)).
{ unfold Hsum2n, Hsum2RHS, A1n, A2n, margn, eps2n, hn, Linn, BBn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_plus A1 marg) (real_plus A2 marg))                  (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h)) marg) Lin) BB) marg))                  (real_plus marg marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus A1 marg) (real_plus A2 marg))                  (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h)) marg) Lin) BB) marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus A1 marg) (real_plus A2 marg) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj A1 marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj A2 marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h)) marg) Lin) BB) marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_mult eps2 (real_abs h)) marg) Lin) BB n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_mult eps2 (real_abs h)) marg) Lin n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps2 (real_abs h)) marg n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps2 (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
(* Lin/BB kept as projT1 Lin n / projT1 BB n (the RHS has the same shape Linn/BBn), so reflexivity closes. *)
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj marg marg n)).
reflexivity.
}      assert (HprojBterm : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * hn + en').
{ unfold en, hn, en'.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
reflexivity.
}      assert (HprojD : projT1 (real_abs D) n == Qabs (projT1 D n)).
{ apply qeqT_imp_qeq. apply (real_abs_proj D n).
}      (* Structural facts: Mf/Mg/Mfp/Mgp ≥ 1, K ≥ 320, 64Mf ≤ K, βK ≤ eps', β ≤ 1. *)      assert (HMf1 : Qle (Qmake 1 1) Mfn).
{ unfold Mfn, Mf.
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs (f x Hx)) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (f x Hx) n)).
cbn [projT1].
apply (Qle_plus_nonneg_r (Qmake 1 1) (Qabs (projT1 (f x Hx) n))).
apply Qabs_nonneg.
}      assert (HMg1 : Qle (Qmake 1 1) Mgn) by (unfold Mgn, Mg;        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs (g x Hx)) n));        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (g x Hx) n)); cbn [projT1];        apply (Qle_plus_nonneg_r (Qmake 1 1) (Qabs (projT1 (g x Hx) n))); apply Qabs_nonneg).
assert (HMfp1 : Qle (Qmake 1 1) Mfpn) by (unfold Mfpn, Mfp;        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs (rdf f Hf x Hx)) n));        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (rdf f Hf x Hx) n)); cbn [projT1];        apply (Qle_plus_nonneg_r (Qmake 1 1) (Qabs (projT1 (rdf f Hf x Hx) n))); apply Qabs_nonneg).
assert (HMgp1 : Qle (Qmake 1 1) Mgpn) by (unfold Mgpn, Mgp;        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs (rdf g Hg x Hx)) n));        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (rdf g Hg x Hx) n)); cbn [projT1];        apply (Qle_plus_nonneg_r (Qmake 1 1) (Qabs (projT1 (rdf g Hg x Hx) n))); apply Qabs_nonneg).
assert (HKn_form : Kn == Qmake 64 1 * (Mfn + Mgn + Mfpn + Mgpn + 1)).
{ unfold Kn, K, Mfn, Mgn, Mfpn, Mgpn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj (Z.of_nat 64 # 1)          (real_plus (real_plus (real_plus (real_plus Mf Mg) Mfp) Mgp) real_one) n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_plus Mf Mg) Mfp) Mgp) real_one n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus Mf Mg) Mfp) Mgp n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus Mf Mg) Mfp n)).
setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Mf Mg n)).
assert (Hc : Qeq (Z.of_nat 64 # 1) (Qmake 64 1)) by (vm_compute; reflexivity).
(* rewriting with Hc would expand the Qeq into a Qnum/Qden cross-product shape that the literal Q in the goal does not match — use change instead. *)
change (Z.of_nat 64 # 1) with (Qmake 64 1).
reflexivity.
}      assert (HKn_ge : Qle (Qmake 320 1) Kn).
{ rewrite HKn_form.
apply (Qle_trans _ (Qmake 64 1 * (Qmake 1 1 + Qmake 1 1 + Qmake 1 1 + Qmake 1 1 + 1)) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
- (* Goal 64·5 ≤ 64·(Mfn+...): Qmult_le_compat_nonneg matches directly (no comm needed). *)        apply (Qmult_le_compat_nonneg (Qmake 64 1) (Qmake 64 1)
                 (Qmake 1 1 + Qmake 1 1 + Qmake 1 1 + Qmake 1 1 + 1) (Mfn + Mgn + Mfpn + Mgpn + 1)).
  + split; [vm_compute; discriminate | vm_compute; discriminate].   (* 0 ≤ 64 ≤ 64 (Qle reduces to Lt<>Gt, closed by discriminate). *)
  + split; [vm_compute; discriminate | apply (Qplus_le_compat (Qmake 1 1 + Qmake 1 1 + Qmake 1 1 + Qmake 1 1) (Mfn + Mgn + Mfpn + Mgpn) 1 1)].
* apply (Qplus_le_compat (Qmake 1 1 + Qmake 1 1 + Qmake 1 1) (Mfn + Mgn + Mfpn) 1 Mgpn).
-- apply (Qplus_le_compat (Qmake 1 1 + Qmake 1 1) (Mfn + Mgn) 1 Mfpn).
++ apply (Qplus_le_compat (Qmake 1 1) Mfn 1 Mgn); [exact HMf1 | exact HMg1].
++ exact HMfp1.
-- exact HMgp1.
* apply Qle_refl.
}      assert (HKn_pos : Qlt 0 Kn).
{ apply (Qlt_le_trans _ (Qmake 320 1) _); [vm_compute; reflexivity | exact HKn_ge].
}      assert (HMfK : Qle (Qmake 64 1 * Mfn) Kn).
{ rewrite HKn_form.
  apply (Qmult_le_compat_nonneg (Qmake 64 1) (Qmake 64 1) Mfn (Mfn + Mgn + Mfpn + Mgpn + 1)).
  - split; [vm_compute; discriminate | vm_compute; discriminate].   (* 0 ≤ 64 ≤ 64 *)
  - split.
    + apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMf1].   (* 0 ≤ Mfn *)
    + apply (Qle_trans _ (Qplus (Qplus (Qplus Mfn Mgn) Mfpn) Mgpn) _).   (* Mfn ≤ Mfn+..., the left-associative chain. *)
      * apply (Qle_trans _ (Qplus (Qplus Mfn Mgn) Mfpn) _).
        -- apply (Qle_trans _ (Qplus Mfn Mgn) _).
           ++ apply (Qle_plus_nonneg_r Mfn Mgn). apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMg1].
           ++ apply (Qle_plus_nonneg_r (Qplus Mfn Mgn) Mfpn). apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMfp1].
        -- apply (Qle_plus_nonneg_r (Qplus (Qplus Mfn Mgn) Mfpn) Mgpn). apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMgp1].
      * apply (Qle_plus_nonneg_r (Qplus (Qplus (Qplus Mfn Mgn) Mfpn) Mgpn) (Qmake 1 1)). vm_compute; discriminate.
}      assert (HMgK : Qle (Qmake 64 1 * Mgn) Kn).
{ rewrite HKn_form.
  apply (Qmult_le_compat_nonneg (Qmake 64 1) (Qmake 64 1) Mgn (Mfn + Mgn + Mfpn + Mgpn + 1)).
  - split; [vm_compute; discriminate | vm_compute; discriminate].   (* 0 ≤ 64 ≤ 64 *)
  - split.
    + apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMg1].   (* 0 ≤ Mgn *)
    + apply (Qle_trans _ (Qplus (Qplus (Qplus Mfn Mgn) Mfpn) Mgpn) _).   (* Mgn ≤ Mfn+Mgn+..., the left-associative chain. *)
      * apply (Qle_trans _ (Qplus (Qplus Mfn Mgn) Mfpn) _).
        -- apply (Qle_trans _ (Qplus Mfn Mgn) _).
           ++ apply (Qle_trans _ (Qplus Mgn Mfn) _).
              ** apply (Qle_plus_nonneg_r Mgn Mfn). apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMf1].
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qplus_comm.
           ++ apply (Qle_plus_nonneg_r (Qplus Mfn Mgn) Mfpn). apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMfp1].
        -- apply (Qle_plus_nonneg_r (Qplus (Qplus Mfn Mgn) Mfpn) Mgpn). apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMgp1].
      * apply (Qle_plus_nonneg_r (Qplus (Qplus (Qplus Mfn Mgn) Mfpn) Mgpn) (Qmake 1 1)). vm_compute; discriminate.
}      assert (HMf_le : Qle Mfn (Kn * Qinv (Qmake 64 1))).
{ apply (Qle_trans _ ((Qmake 64 1 * Mfn) * Qinv (Qmake 64 1)) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq (Qmake 64 1 * Qinv (Qmake 64 1)) 1) by (vm_compute; reflexivity).
ring [Hc].
- apply (Qmult_le_compat_r (Qmake 64 1 * Mfn) Kn (Qinv (Qmake 64 1))).
+ exact HMfK.
+ apply Qlt_le_weak.
apply Qinv_lt_0_compat.
vm_compute.
reflexivity.
}      assert (HMg_le : Qle Mgn (Kn * Qinv (Qmake 64 1))).
{ apply (Qle_trans _ ((Qmake 64 1 * Mgn) * Qinv (Qmake 64 1)) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq (Qmake 64 1 * Qinv (Qmake 64 1)) 1) by (vm_compute; reflexivity).
ring [Hc].
- apply (Qmult_le_compat_r (Qmake 64 1 * Mgn) Kn (Qinv (Qmake 64 1))).
+ exact HMgK.
+ apply Qlt_le_weak.
apply Qinv_lt_0_compat.
vm_compute.
reflexivity.
}      (* β facts: β == en'·invK1 (exactly), βK ≤ en', β ≤ 1. *)      assert (HK1pos : Qlt 0 (Kn * (1 + en'))).
{ apply (Qmult_lt_0_compat Kn (1 + en')).
- exact HKn_pos.
- apply (Qlt_le_trans _ (Qmake 1 1) _); [vm_compute; reflexivity | ].
apply (Qle_plus_nonneg_r (Qmake 1 1) en').
apply Qlt_le_weak.
exact Hen'pos.
}      assert (HnzK1 : ~ Kn * (1 + en') == 0) by (intro Heq; destruct (q_neq_of_lt _ (Qlt_to_QltT _ _ HK1pos) (qeq_imp_qeqT _ _ Heq))).
assert (HKn1 : Qle (Qmake 1 1) Kn).
{ apply (Qle_trans _ (Qmake 320 1) _); [vm_compute; discriminate | exact HKn_ge].
}      assert (HinvK1pos : Qle 0 (Qinv (Kn * (1 + en')))).
{ apply Qlt_le_weak.
apply Qinv_lt_0_compat.
exact HK1pos.
}      assert (HinvK1le1 : Qle (Qinv (Kn * (1 + en')) * Kn) 1).
{ apply (Qle_trans _ (Qinv (Kn * (1 + en')) * (Kn * (1 + en'))) _).
  - apply (Qmult_le_compat_nonneg (Qinv (Kn * (1 + en'))) (Qinv (Kn * (1 + en'))) Kn (Kn * (1 + en'))).
    + split; [exact HinvK1pos | apply Qle_refl].   (* 0 ≤ Qinv ≤ Qinv *)
    + split.
      * apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HKn1].   (* 0 ≤ Kn *)
      * apply (Qle_trans _ (Qmult Kn (Qmake 1 1)) _).   (* Kn ≤ Kn·(1+en'): the Kn·1 == Kn bridge + nonnegativity. *)
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qmult_le_compat_nonneg Kn Kn (Qmake 1 1) (Qmake 1 1 + en')).
           ++ split; [apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HKn1] | apply Qle_refl].
           ++ split; [vm_compute; discriminate | apply (Qle_plus_nonneg_r (Qmake 1 1) en'); apply Qlt_le_weak; exact Hen'pos].
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    apply (Qeq_trans _ (Qmult (Kn * (1 + en')) (Qinv (Kn * (1 + en')))) _).
    + apply Qmult_comm.
    + apply (Qmult_inv_r (Kn * (1 + en')) HnzK1).
}      assert (HbetaK : Qle (betan * Kn) en').
{ rewrite Hprojbeta.
rewrite HinvK1.
apply (Qle_trans _ (en' * 1) _).
- (* en'·Qinv(K1n)·Kn ≤ en'·1: first bridge by assoc into en'·(Qinv·Kn), then nonnegativity. *)          apply (Qle_trans _ (en' * (Qinv (Kn * (1 + en')) * Kn)) _).
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  + apply (Qmult_le_compat_nonneg en' en' (Qinv (Kn * (1 + en')) * Kn) 1).
* split; [apply Qlt_le_weak; exact Hen'pos | apply Qle_refl].
* split; [apply (Qmult_le_0_compat (Qinv (Kn * (1 + en'))) Kn); [exact HinvK1pos | apply Qlt_le_weak; exact HKn_pos] | exact HinvK1le1].
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}      assert (Hbeta_le1 : Qle betan 1).
{ rewrite Hprojbeta.
rewrite HinvK1.
apply (Qle_trans _ ((Kn * (1 + en')) * Qinv (Kn * (1 + en'))) _).
- (* en'·Qinv(K1n) ≤ K1n·Qinv(K1n) ⟸ en' ≤ K1n *)          apply (Qmult_le_compat_nonneg en' (Kn * (1 + en')) (Qinv (Kn * (1 + en'))) (Qinv (Kn * (1 + en')))).
+ split.
* apply Qlt_le_weak.
exact Hen'pos.
* (* en' ≤ Kn(1+en'): the difference Kn + en'(Kn−1) is ≥ 0. *)              apply (proj2 (Qle_minus_iff en' (Kn * (1 + en')))).
apply (Qle_trans _ (Kn + en' * (Kn - 1)) _).
-- apply (Qle_trans _ Kn _); [apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HKn1] | apply (Qle_plus_nonneg_r Kn (en' * (Kn - 1))); apply (Qmult_le_0_compat en' (Kn - 1)); [apply Qlt_le_weak; exact Hen'pos | apply (proj1 (Qle_minus_iff (Qmake 1 1) Kn)); exact HKn1]].
-- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
+ split; [exact HinvK1pos | apply Qle_refl].
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite (Qmult_inv_r (Kn * (1 + en')) HnzK1).
ring.
}      assert (Hbetapos : Qlt 0 betan).
{ apply (Qlt_le_trans _ b0 _); [apply QltT_to_Qlt; exact Hb0 | ].
apply (Qle_trans _ (betan - projT1 real_zero n) _).
- apply Qlt_le_weak.
  apply QltT_to_Qlt.
exact (HNb n (NatLe_lift _ _ Hnb)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
rewrite Hz.
ring.
}      (* dKf/dKg: Lf·|h| ≤ K/8 and Lg·|h| ≤ K/8 (exact, from |h| < dKf == K·inv(8Lf)). *)      assert (HLfnpos : Qlt 0 Lfn).
{ apply (Qlt_le_trans _ eLf _); [apply QltT_to_Qlt; exact HeLf | ].
apply (Qle_trans _ (Lfn - projT1 real_zero n) _).
- apply Qlt_le_weak.
  apply QltT_to_Qlt.
exact (HNLf n (NatLe_lift _ _ HnLf)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
rewrite Hz.
ring.
}      assert (HLgnpos : Qlt 0 Lgn).
{ apply (Qlt_le_trans _ eLg _); [apply QltT_to_Qlt; exact HeLg | ].
apply (Qle_trans _ (Lgn - projT1 real_zero n) _).
- apply Qlt_le_weak.
  apply QltT_to_Qlt.
exact (HNLg n (NatLe_lift _ _ HnLg)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
rewrite Hz.
ring.
}      assert (H8Lfn_pos : Qlt 0 (Qmake 8 1 * Lfn)).
{ apply (Qmult_lt_0_compat (Qmake 8 1) Lfn); [vm_compute; reflexivity | exact HLfnpos].
}      assert (H8Lgn_pos : Qlt 0 (Qmake 8 1 * Lgn)).
{ apply (Qmult_lt_0_compat (Qmake 8 1) Lgn); [vm_compute; reflexivity | exact HLgnpos].
}      assert (Hnz8Lf : ~ Qmake 8 1 * Lfn == 0) by (intro Heq; destruct (q_neq_of_lt _ (Qlt_to_QltT _ _ H8Lfn_pos) (qeq_imp_qeqT _ _ Heq))).
assert (Hnz8Lg : ~ Qmake 8 1 * Lgn == 0) by (intro Heq; destruct (q_neq_of_lt _ (Qlt_to_QltT _ _ H8Lgn_pos) (qeq_imp_qeqT _ _ Heq))).
assert (HdKfn : projT1 dKf n == Kn * Qinv (Qmake 8 1 * Lfn)).
{ unfold dKf, Kn, Lfn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj K (real_inv_pos (real_mult e8 Lf) (real_mult_positive e8 Lf He8 HLf)) n)).
assert (Hinv : projT1 (real_inv_pos (real_mult e8 Lf) (real_mult_positive e8 Lf He8 HLf)) n == Qinv (Qmake 8 1 * Lfn)).
{ assert (Hp8 : projT1 (real_mult e8 Lf) n == Qmake 8 1 * Lfn).
  { unfold Lfn, e8.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj (Z.of_nat 8 # 1) Lf n)).
    assert (Hc : Qeq (Z.of_nat 8 # 1) (Qmake 8 1)) by (vm_compute; reflexivity).
    change (Z.of_nat 8 # 1) with (Qmake 8 1). reflexivity. }
  rewrite <- Hp8.
  apply (qeqT_imp_qeq _ _ (HN8Lfp n (NatLe_lift _ _ HN8Lfp_le))).
}        rewrite Hinv.
reflexivity.
}      assert (HdKgn : projT1 dKg n == Kn * Qinv (Qmake 8 1 * Lgn)).
{ unfold dKg, Kn, Lgn.
setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj K (real_inv_pos (real_mult e8 Lg) (real_mult_positive e8 Lg He8 HLg)) n)).
assert (Hinv : projT1 (real_inv_pos (real_mult e8 Lg) (real_mult_positive e8 Lg He8 HLg)) n == Qinv (Qmake 8 1 * Lgn)).
{ assert (Hp8 : projT1 (real_mult e8 Lg) n == Qmake 8 1 * Lgn).
  { unfold Lgn, e8.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj (Z.of_nat 8 # 1) Lg n)).
    assert (Hc : Qeq (Z.of_nat 8 # 1) (Qmake 8 1)) by (vm_compute; reflexivity).
    change (Z.of_nat 8 # 1) with (Qmake 8 1). reflexivity. }
  rewrite <- Hp8.
  apply (qeqT_imp_qeq _ _ (HN8Lgp n (NatLe_lift _ _ HN8Lgp_le))).
}        rewrite Hinv.
reflexivity.
}      assert (HhdKfn : Qlt hn (Kn * Qinv (Qmake 8 1 * Lfn))).
{ apply (Qlt_le_trans _ (projT1 dKf n - cdf) _).
- (* hn < dKfn − cdf: from cdf < dKfn − hn (HNdf) via the Qlt_minus_iff chain + a ring bridge. *)        apply (proj2 (Qlt_minus_iff hn (projT1 dKf n - cdf))).
  apply (Qlt_le_trans _ ((projT1 dKf n - hn) - cdf) _).
  + apply (proj1 (Qlt_minus_iff cdf (projT1 dKf n - hn))).
    apply QltT_to_Qlt.
    exact (HNdf n (NatLe_lift _ _ Hndf)).
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
- apply (Qle_trans _ (projT1 dKf n) _).
  + apply (proj2 (Qle_minus_iff (projT1 dKf n - cdf) (projT1 dKf n))).
    apply (Qle_trans _ cdf _); [apply Qlt_le_weak; apply QltT_to_Qlt; exact Hcdf | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring].
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite HdKfn. ring.
}      assert (HhdKgn : Qlt hn (Kn * Qinv (Qmake 8 1 * Lgn))).
{ apply (Qlt_le_trans _ (projT1 dKg n - cdg) _).
- (* hg < dKgn − cdg: from cdg < dKgn − hn (HNdg) via the Qlt_minus_iff chain + a ring bridge. *)        apply (proj2 (Qlt_minus_iff hn (projT1 dKg n - cdg))).
  apply (Qlt_le_trans _ ((projT1 dKg n - hn) - cdg) _).
  + apply (proj1 (Qlt_minus_iff cdg (projT1 dKg n - hn))).
    apply QltT_to_Qlt.
    exact (HNdg n (NatLe_lift _ _ Hndg)).
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
- apply (Qle_trans _ (projT1 dKg n) _).
  + apply (proj2 (Qle_minus_iff (projT1 dKg n - cdg) (projT1 dKg n))).
    apply (Qle_trans _ cdg _); [apply Qlt_le_weak; apply QltT_to_Qlt; exact Hcdg | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring].
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite HdKgn. ring.
}      assert (HdKf_pt : Qle (Qmake 8 1 * Lfn * hn) Kn).
{ apply (Qle_trans _ (hn * (Qmake 8 1 * Lfn)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.   (* 8·Lfn·hn == hn·(8·Lfn) (in a Qle chain: qeq_le cannot fire on a Qlt goal). *)
  - apply (Qle_trans _ ((Kn * Qinv (Qmake 8 1 * Lfn)) * (Qmake 8 1 * Lfn)) _).
    + apply (Qmult_le_compat_r hn (Kn * Qinv (Qmake 8 1 * Lfn)) (Qmake 8 1 * Lfn)).
      * apply Qlt_le_weak. exact HhdKfn.
      * apply Qlt_le_weak. exact H8Lfn_pos.
    + assert (Hinv8 : Qeq (Qmake 8 1 * Lfn * Qinv (Qmake 8 1 * Lfn)) 1) by (apply (Qmult_inv_r (Qmake 8 1 * Lfn) Hnz8Lf)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring [Hinv8].
}      assert (HdKg_pt : Qle (Qmake 8 1 * Lgn * hn) Kn).
{ apply (Qle_trans _ (hn * (Qmake 8 1 * Lgn)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.   (* 8·Lgn·hn == hn·(8·Lgn) (E197-4) *)
  - apply (Qle_trans _ ((Kn * Qinv (Qmake 8 1 * Lgn)) * (Qmake 8 1 * Lgn)) _).
    + apply (Qmult_le_compat_r hn (Kn * Qinv (Qmake 8 1 * Lgn)) (Qmake 8 1 * Lgn)).
      * apply Qlt_le_weak. exact HhdKgn.
      * apply Qlt_le_weak. exact H8Lgn_pos.
    + assert (Hinv8 : Qeq (Qmake 8 1 * Lgn * Qinv (Qmake 8 1 * Lgn)) 1) by (apply (Qmult_inv_r (Qmake 8 1 * Lgn) Hnz8Lg)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring [Hinv8].
}      assert (HLfhn : Qle (Lfn * hn) (Kn * Qinv (Qmake 8 1))).
{ (* (8·Lfn)·hn ≤ Kn ⟹ Lfn·hn ≤ Kn/8: Lfn·hn == (8·Lfn·hn)·Qinv(8) ≤ Kn·Qinv(8) (E197-4) *)        apply (Qle_trans _ ((Qmake 8 1 * Lfn * hn) * Qinv (Qmake 8 1)) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq (Qmake 8 1 * Qinv (Qmake 8 1)) 1) by (vm_compute; reflexivity).
ring [Hc].
- apply (Qmult_le_compat_r (Qmake 8 1 * Lfn * hn) Kn (Qinv (Qmake 8 1))).
+ exact HdKf_pt.
+ apply Qlt_le_weak.
apply Qinv_lt_0_compat.
vm_compute.
reflexivity.
}      assert (HLghn : Qle (Lgn * hn) (Kn * Qinv (Qmake 8 1))).
{ (* (8·Lgn)·hn ≤ Kn ⟹ Lgn·hn ≤ Kn/8: Lgn·hn == (8·Lgn·hn)·Qinv(8) ≤ Kn·Qinv(8) (E197-4) *)        apply (Qle_trans _ ((Qmake 8 1 * Lgn * hn) * Qinv (Qmake 8 1)) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq (Qmake 8 1 * Qinv (Qmake 8 1)) 1) by (vm_compute; reflexivity).
ring [Hc].
- apply (Qmult_le_compat_r (Qmake 8 1 * Lgn * hn) Kn (Qinv (Qmake 8 1))).
+ exact HdKg_pt.
+ apply Qlt_le_weak.
apply Qinv_lt_0_compat.
vm_compute.
reflexivity.
}      assert (Hbeta_le_epK : Qle betan (en' * Qinv (Qmake 320 1))).
{ rewrite Hprojbeta.
rewrite HinvK1.
(* β == en'·Qinv(K1n) ≤ en'·Qinv(Kn) (Kn≤K1n, antitone) ≤ en'·Qinv(320) (320≤Kn, antitone). *)        apply (Qle_trans _ (en' * Qinv Kn) _).
- apply (Qmult_le_compat_nonneg en' en' (Qinv (Kn * (1 + en'))) (Qinv Kn)).
  + split; [apply Qlt_le_weak; exact Hen'pos | apply Qle_refl].   (* 0 ≤ en' ≤ en' (nonnegativity matches the en'-first shape). *)
  + split; [exact HinvK1pos | apply QleT'_to_Qle; apply (q_inv_le_contravar (Kn * (1 + en')) Kn); [apply Qlt_to_QltT; exact HK1pos | apply Qlt_to_QltT; exact HKn_pos | apply Qle_to_QleT'; apply (proj2 (Qle_minus_iff Kn (Kn * (1 + en')))); apply (Qle_trans _ (Kn * en') _); [apply (Qmult_le_0_compat Kn en'); [apply Qlt_le_weak; exact HKn_pos | apply Qlt_le_weak; exact Hen'pos] | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring]]].   (* 0 ≤ Qinv(K1n) ≤ Qinv(Kn) *)
- apply (Qmult_le_compat_nonneg en' en' (Qinv Kn) (Qinv (Qmake 320 1))).
  + split; [apply Qlt_le_weak; exact Hen'pos | apply Qle_refl].
  + split; [apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HKn_pos | apply QleT'_to_Qle; apply (q_inv_le_contravar Kn (Qmake 320 1)); [apply Qlt_to_QltT; exact HKn_pos | vm_compute; reflexivity | apply Qle_to_QleT'; exact HKn_ge]].   (* 0 ≤ Qinv(Kn) ≤ Qinv(320) *)
}      (* Budget bounds: βγ == (3/2)β and B == (97/64)β. *)      assert (Hbg_form : bgamman == betan * (Qmake 3 2)).
{ rewrite Hprojbg.
rewrite Hprojgam.
rewrite Hhalf_pt.
rewrite Hc2.
ring.
}      assert (HB_form : Bn == betan * (Qmake 97 64)).
{ change (projT1 (real_plus beta_gamma marg) n == betan * (Qmake 97 64)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj beta_gamma marg n)).
  change (bgamman + margn == betan * (Qmake 97 64)).
  rewrite Hprojbg.
  rewrite Hprojgam.
  rewrite Hhalf_pt.
  rewrite Hc2.
  rewrite Hprojmarg.
  rewrite Hinv64'.
  ring [Hc64q].
}      assert (HBpos : Qlt 0 Bn).
{ apply (Qlt_le_trans _ bB _); [apply QltT_to_Qlt; exact HbB | ].
apply (Qle_trans _ (Bn - projT1 real_zero n) _).
- apply Qlt_le_weak.
  apply QltT_to_Qlt.
exact (HNB n (NatLe_lift _ _ HnB)).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
rewrite Hz.
ring.
}      assert (Hbgpos : Qle 0 bgamman).
{ rewrite Hbg_form.
apply (Qmult_le_0_compat betan (Qmake 3 2)).
- apply Qlt_le_weak.
exact Hbetapos.
- vm_compute.
discriminate.
}      assert (Hb32pos : Qle 0 (betan * (Qmake 3 2))).
{ apply (Qmult_le_0_compat betan (Qmake 3 2)).
- apply Qlt_le_weak.
exact Hbetapos.
- vm_compute.
discriminate.
}      (* Mfβγ ≤ 3eps'/128, Mgβγ ≤ 3eps'/128 (Mf ≤ K/64, βγ == 3β/2, βK ≤ eps') *)      assert (HMfbeta : Qle (Mfn * bgamman) ((Qmake 3 128) * en')).
{ (* Mf·βγ == Mf·β·(3/2) ≤ (K/64)·β·(3/2) == (3/128)·β·K ≤ (3/128)·en' *)        apply (Qle_trans _ (Mfn * (betan * (Qmake 3 2))) _).
- apply (Qmult_le_compat_nonneg Mfn Mfn bgamman (betan * (Qmake 3 2))).
+ split; [apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMf1] | apply Qle_refl].
+ split; [exact Hbgpos | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; rewrite Hbg_form; ring].
- apply (Qle_trans _ ((Kn * Qinv (Qmake 64 1)) * (betan * (Qmake 3 2))) _).
+ apply (Qmult_le_compat_nonneg Mfn (Kn * Qinv (Qmake 64 1)) (betan * (Qmake 3 2)) (betan * (Qmake 3 2))).
* split; [apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMf1] | exact HMf_le].
* split; [exact Hb32pos | apply Qle_refl].
+ apply (Qle_trans _ ((Qmake 3 128) * (betan * Kn)) _).
  * (* (Kn·Qinv64)·(β·3/2) == (3/128)·(β·Kn) (the middle term should be β·Kn; en' enters at the last step). *)              apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    assert (Hc : Qeq (Qinv (Qmake 64 1) * (Qmake 3 2)) (Qmake 3 128)) by (vm_compute; reflexivity).
    ring [Hc].
  * apply (Qmult_le_compat_nonneg (Qmake 3 128) (Qmake 3 128) (betan * Kn) en').
    -- split; [vm_compute; discriminate | vm_compute; discriminate].   (* 0 ≤ 3/128 ≤ 3/128 *)
    -- split; [apply (Qmult_le_0_compat betan Kn); [apply Qlt_le_weak; exact Hbetapos | apply Qlt_le_weak; exact HKn_pos] | exact HbetaK].   (* 0 ≤ β·Kn ≤ en' (nonnegativity matches the goal with 3/128 stated first). *)
}      assert (HMgbeta : Qle (Mgn * bgamman) ((Qmake 3 128) * en')).
{ apply (Qle_trans _ (Mgn * (betan * (Qmake 3 2))) _).
- apply (Qmult_le_compat_nonneg Mgn Mgn bgamman (betan * (Qmake 3 2))).
+ split; [apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMg1] | apply Qle_refl].
+ split; [exact Hbgpos | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; rewrite Hbg_form; ring].
- apply (Qle_trans _ ((Kn * Qinv (Qmake 64 1)) * (betan * (Qmake 3 2))) _).
+ apply (Qmult_le_compat_nonneg Mgn (Kn * Qinv (Qmake 64 1)) (betan * (Qmake 3 2)) (betan * (Qmake 3 2))).
* split; [apply (Qle_trans _ (Qmake 1 1) _); [vm_compute; discriminate | exact HMg1] | exact HMg_le].
* split; [exact Hb32pos | apply Qle_refl].
+ apply (Qle_trans _ ((Qmake 3 128) * (betan * Kn)) _).
  * (* (Kn·Qinv64)·(β·3/2) == (3/128)·(β·Kn) (the middle term should be β·Kn; en' enters at the last step). *)              apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    assert (Hc : Qeq (Qinv (Qmake 64 1) * (Qmake 3 2)) (Qmake 3 128)) by (vm_compute; reflexivity).
    ring [Hc].
  * apply (Qmult_le_compat_nonneg (Qmake 3 128) (Qmake 3 128) (betan * Kn) en').
    -- split; [vm_compute; discriminate | vm_compute; discriminate].   (* 0 ≤ 3/128 ≤ 3/128 *)
    -- split; [apply (Qmult_le_0_compat betan Kn); [apply Qlt_le_weak; exact Hbetapos | apply Qlt_le_weak; exact HKn_pos] | exact HbetaK].   (* 0 ≤ β·Kn ≤ en' (nonnegativity matches the goal with 3/128 stated first). *)
}      assert (HS12 : Qle S12n ((Qmake 3 64) * en')).
{ rewrite HprojS12.
apply (Qle_trans _ ((Qmake 3 128) * en' + (Qmake 3 128) * en') _).
- apply (Qplus_le_compat (Mfn * bgamman) ((Qmake 3 128) * en') (Mgn * bgamman) ((Qmake 3 128) * en')); [exact HMfbeta | exact HMgbeta].
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}      (* Lin ≤ 97eps'/256 ((Lf+Lg)|h| ≤ K/4, B == (97/64)β, βK ≤ eps') *)      assert (HLin_bound : Qle Linn ((Qmake 97 256) * en')).
{ (* Lin == (Lf+Lg)·B·hn ≤ (K/4)·B == (97/256)·β·K ≤ (97/256)·en' *)        rewrite HprojLin.
apply (Qle_trans _ ((Lfn * hn + Lgn * hn) * Bn) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
- apply (Qle_trans _ ((Kn * Qinv (Qmake 4 1)) * Bn) _).
+ apply (Qmult_le_compat_r (Lfn * hn + Lgn * hn) (Kn * Qinv (Qmake 4 1)) Bn).
* apply (Qle_trans _ (Kn * Qinv (Qmake 8 1) + Kn * Qinv (Qmake 8 1)) _).
-- apply (Qplus_le_compat (Lfn * hn) (Kn * Qinv (Qmake 8 1)) (Lgn * hn) (Kn * Qinv (Qmake 8 1))); [exact HLfhn | exact HLghn].
-- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq (Qinv (Qmake 8 1) + Qinv (Qmake 8 1)) (Qinv (Qmake 4 1))) by (vm_compute; reflexivity).
ring [Hc].
* apply Qlt_le_weak.
exact HBpos.
+ apply (Qle_trans _ ((Qmake 97 256) * (betan * Kn)) _).
* (* (K/4)·B == (97/256)·β·K *)              apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
rewrite HB_form.
assert (Hc : Qeq ((Qinv (Qmake 4 1)) * (Qmake 97 64)) (Qmake 97 256)) by (vm_compute; reflexivity).
ring [Hc].
* apply (Qle_trans _ ((Qmake 97 256) * en') _).
-- apply (Qmult_le_compat_nonneg (Qmake 97 256) (Qmake 97 256) (betan * Kn) en').
   ++ split; [vm_compute; discriminate | vm_compute; discriminate].
   ++ split; [apply (Qmult_le_0_compat betan Kn); [apply Qlt_le_weak; exact Hbetapos | apply Qlt_le_weak; exact HKn_pos] | exact HbetaK].
-- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
ring.
}      (* BB ≤ eps'/128 (β ≤ 1 ⟹ β² ≤ β, β ≤ en'·Qinv(320), Kn ≥ 320) *)      assert (HBB_bound : Qle BBn ((Qmake 1 128) * en')).
{ (* BB == (β·97/64)² == β²·(97/64)² ≤ β·(97/64)² (β≤1, β≥0)== β·(9409/4096)             ≤ (9409/4096)·en'·Qinv(320) == (9409/1310720)·en' ≤ (1/128)·en' *)        rewrite HprojBB.
rewrite HB_form.
apply (Qle_trans _ (betan * (Qmake 9409 4096)) _).
- apply (Qle_trans _ ((betan * betan) * (Qmake 9409 4096)) _).
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.   (* (β·(97/64))·(β·(97/64)) == (β·β)·(9409/4096): plain ring (Qmake constants are seen as rationals); do not ring [Hc] — the Hc proof term contains a closed term over Opaque Qred and hangs. *)
  + apply (Qmult_le_compat_nonneg (betan * betan) betan (Qmake 9409 4096) (Qmake 9409 4096)).
    * split.
      -- apply (Qmult_le_0_compat betan betan); apply Qlt_le_weak; exact Hbetapos.
      -- (* β² ≤ β: β·β ≤ 1·β (β≤1, 0≤β)== 1·β ≡ β *)              apply (Qle_trans _ (Qmake 1 1 * betan) _).
         ++ apply (Qmult_le_compat_r betan (Qmake 1 1) betan); [exact Hbeta_le1 | apply Qlt_le_weak; exact Hbetapos].
         ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    * split; [vm_compute; discriminate | apply Qle_refl].
- apply (Qle_trans _ ((en' * Qinv (Qmake 320 1)) * (Qmake 9409 4096)) _).
+ apply (Qmult_le_compat_r betan (en' * Qinv (Qmake 320 1)) (Qmake 9409 4096)).
* exact Hbeta_le_epK.
* vm_compute.
discriminate.
+ apply (Qle_trans _ ((Qmake 9409 1310720) * en') _).
* apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq ((Qmake 9409 4096) * Qinv (Qmake 320 1)) (Qmake 9409 1310720)) by (vm_compute; reflexivity).
ring [Hc].
* apply (Qmult_le_compat_r (Qmake 9409 1310720) (Qmake 1 128) en').
-- exact Hc9409b.
-- apply Qlt_le_weak.
exact Hen'pos.
}      (* 6marg ≤ eps'/ (marg == β·Qinv(64), β ≤ en'·Qinv(320)) *)      assert (Hmarg6 : Qle (margn + (margn + (margn + (margn + (margn + margn))))) ((Qmake 1 2048) * en')).
{ (* 6marg == 6·β·Qinv(64) == (3/32)·β ≤ (3/32)·en'·Qinv(320) == (3/10240)·en' ≤ (1/)·en' *)        rewrite Hprojmarg.
rewrite Hinv64'.
apply (Qle_trans _ (betan * (Qmake 3 32)) _).
- apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq (Qmake 6 1 * Qinv (Qmake 64 1)) (Qmake 3 32)) by (vm_compute; reflexivity).
ring [Hc].
- apply (Qle_trans _ ((en' * Qinv (Qmake 320 1)) * (Qmake 3 32)) _).
+ apply (Qmult_le_compat_r betan (en' * Qinv (Qmake 320 1)) (Qmake 3 32)).
* exact Hbeta_le_epK.
* vm_compute.
discriminate.
+ apply (Qle_trans _ ((Qmake 3 10240) * en') _).
* apply QleT'_to_Qle. apply qeq_le.
apply qeq_imp_qeqT.
assert (Hc : Qeq ((Qmake 3 32) * Qinv (Qmake 320 1)) (Qmake 3 10240)) by (vm_compute; reflexivity).
ring [Hc].
* apply (Qmult_le_compat_r (Qmake 3 10240) (Qmake 1 2048) en').
-- exact Hc3_10240.
-- apply Qlt_le_weak.
exact Hen'pos.
}      (* Budget summary: ShareSum == S12 + Lin + BB + 6marg ≤ (3/64+97/256+1/128+1/)·en' == (889/)·en'. *)      assert (HShare : Qle ShareSumn ((Qmake 889 2048) * en')).
{ rewrite HprojShare.
apply (Qle_trans _ ((((Qmake 3 64) * en' + (Qmake 97 256) * en') + (Qmake 1 128) * en') + (Qmake 1 2048) * en') _).
- apply (Qplus_le_compat (S12n + Linn + BBn) (((Qmake 3 64) * en' + (Qmake 97 256) * en') + (Qmake 1 128) * en')                                 (margn + (margn + (margn + (margn + (margn + margn))))) ((Qmake 1 2048) * en')).
+ apply (Qplus_le_compat (S12n + Linn) ((Qmake 3 64) * en' + (Qmake 97 256) * en') BBn ((Qmake 1 128) * en')).
* apply (Qplus_le_compat S12n ((Qmake 3 64) * en') Linn ((Qmake 97 256) * en')); [exact HS12 | exact HLin_bound].
* exact HBB_bound.
+ exact Hmarg6.
- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.   (* (3/64+97/256+1/128+1/)·en' == (889/)·en': plain ring (do not vm_compute — it unfolds projT1 of a term containing the variable en' and hangs). *)
}      (* Chain: A_n == Qabs(D_n) ≤ HsumRn + s ≤ Hsum1n + 2s ≤ Hsum2n + 3s == en·hn + ShareSumn + 3s. *)      assert (Hchain : Qle (projT1 (real_abs D) n) (en * hn + ShareSumn + 3 * (Qdiv e0' 128))).
{ (* Keep the projT1 (real_abs D) n shape (the HNsum pointwise conclusion has the same shape; do not rewrite HprojD). *)        apply (Qle_trans _ (HsumRn + Qdiv e0' 128) _).
- exact (QleT'_to_Qle _ _ (HNsum n (NatLe_lift _ _ Hnsum))).
- apply (Qle_trans _ (Hsum1n + Qdiv e0' 128 + Qdiv e0' 128) _).   (* The intermediate term in addition shape, matching the conclusion of Qplus_le_compat. *)
  + apply (Qplus_le_compat HsumRn (Hsum1n + Qdiv e0' 128) (Qdiv e0' 128) (Qdiv e0' 128)).
    * (* HsumRn ≤ Hsum1n + s: the difference == (Prodn+margn+s) − T3n ≥ 0 (HNt3). *)              apply (proj2 (Qle_minus_iff HsumRn (Hsum1n + Qdiv e0' 128))).
      apply (Qle_trans _ ((Prodn + margn + Qdiv e0' 128) - T3n) _).
      -- apply (proj1 (Qle_minus_iff T3n (Prodn + margn + Qdiv e0' 128))).   (* sub1: 0 ≤ X−T3n comes from HNt3 (positivity stated first, plus the projection bridge). *)
         apply (Qle_trans _ (projT1 (real_plus Prod marg) n + Qdiv e0' 128) _).
         ++ change (projT1 (real_abs T3) n <= projT1 (real_plus Prod marg) n + Qdiv e0' 128).
            exact (QleT'_to_Qle _ _ (HNt3 n (NatLe_lift _ _ Hnt3))).
         ++ apply (Qplus_le_compat (projT1 (real_plus Prod marg) n) (Prodn + margn) (Qdiv e0' 128) (Qdiv e0' 128)).
            ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (real_plus_proj Prod marg n)). unfold Prodn, margn. reflexivity.
            ** apply Qle_refl.
      -- apply QleT'_to_Qle. apply qeq_le.   (* sub2: X−T3n == (Hsum1n+s)−HsumRn, an algebraic identity. *)
      apply qeq_imp_qeqT.
         rewrite HprojHsumR.
         rewrite HprojHsum1.
         ring.
    * apply Qle_refl.
  + apply (Qle_trans _ (Hsum1n + 2 * (Qdiv e0' 128)) _).   (* Bridge: the addition shape == the multiplication shape. *)
    * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    * apply (Qle_trans _ (Hsum2n + Qdiv e0' 128 + 2 * (Qdiv e0' 128)) _).
      -- apply (Qplus_le_compat Hsum1n (Hsum2n + Qdiv e0' 128) (2 * (Qdiv e0' 128)) (2 * (Qdiv e0' 128))).
         ++ (* Hsum1n ≤ Hsum2n + s: the difference == s + (eps2n·hn+margn) − Denh2n ≥ 0 (HNden). *)                 apply (proj2 (Qle_minus_iff Hsum1n (Hsum2n + Qdiv e0' 128))).
            apply (Qle_trans _ ((eps2n * hn + margn) + (Qdiv e0' 128) - Denh2n) _).
             +++ apply (proj1 (Qle_minus_iff Denh2n (eps2n * hn + margn + Qdiv e0' 128))).   (* sub1: from HNden (positivity first, plus the projection bridge). *)
                 apply (Qle_trans _ (projT1 (real_plus (real_mult eps2 (real_abs h)) marg) n + Qdiv e0' 128) _).
                 ++++ change (projT1 Den_h2 n <= projT1 (real_plus (real_mult eps2 (real_abs h)) marg) n + Qdiv e0' 128).
                      exact (QleT'_to_Qle _ _ (HNden n (NatLe_lift _ _ Hnden))).
                 ++++ apply (Qplus_le_compat (projT1 (real_plus (real_mult eps2 (real_abs h)) marg) n) (eps2n * hn + margn) (Qdiv e0' 128) (Qdiv e0' 128)).
                      +++++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold eps2n, hn, margn. rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps2 (real_abs h)) marg n)). rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps2 (real_abs h) n)). rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)). reflexivity.
                      +++++ apply Qle_refl.
             +++ apply QleT'_to_Qle. apply qeq_le.   (* sub2: an algebraic identity (Prodn == Denh2n+Linn+BBn). *)
             apply qeq_imp_qeqT.
                 rewrite HprojHsum1.
                 rewrite HprojHsum2.
                 rewrite HprojProd.
                 rewrite HprojDenh2.
                 rewrite HDenn.
                 rewrite HprojLin.
                 rewrite HprojBB.
                 ring.
          ++ apply Qle_refl.
      -- apply (Qle_trans _ (Hsum2n + 3 * (Qdiv e0' 128)) _).   (* Bridge. *)
         ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
         ++ apply (Qle_trans _ (en * hn + ShareSumn + 3 * (Qdiv e0' 128)) _).
            ** (* Hsum2n == en·hn + ShareSumn: ring (eps4+eps4+eps2 == eps via halfn == Qinv2). *)                 apply QleT'_to_Qle. apply qeq_le.
            apply qeq_imp_qeqT.
               rewrite HprojHsum2.
               rewrite HprojA1.
               rewrite HprojA2.
               rewrite Hprojeps4.
               rewrite Hprojeps2.
               rewrite Hprojq.
               rewrite Hhalf_pt.
               rewrite Hc2.
               rewrite HprojShare.
               rewrite HprojS12.
               ring.
            ** apply Qle_refl.
}      (* Final: B_n − A_n ≥ en' − ShareSumn − 3s ≥ (1−889/)·en' − 3s > eps0q.
        Route note: the direct Qmult_le_0_compat attack on
        (1−c−3/128−1/4)e0' ≤ (1−c)(en'−e0') is unprovable (en'−e0' has no lower
        bound); instead use the difference chain 0 < (1−c−3/128−1/4)·e0' ≤ (1−c)·en'−3s−e0'/4,
        whose difference == (1−c)(en'−e0') ≥ 0 (Qle_minus_iff on differences + field identities). *)
        { apply Qlt_to_QltT.
rewrite HprojBterm.
apply (Qlt_le_trans _ ((Qmake 1 1 - Qmake 889 2048) * en' - 3 * (Qdiv e0' 128)) _).
- (* sub1: eps0q < (1−c)·en' − 3s *)
  unfold eps0q.
  apply (proj2 (Qlt_minus_iff (Qmult (Qmake 1 4) e0') ((Qmake 1 1 - Qmake 889 2048) * en' - 3 * (Qdiv e0' 128)))).
  apply (Qlt_le_trans _ ((Qmake 1 1 - Qmake 889 2048 - Qmake 3 128 - Qmake 1 4) * e0') _).
  + (* 0 < (1−c−3/128−1/4)·e0': e0' > 0 and Hc_slack. *)
    apply (Qmult_lt_0_compat (Qmake 1 1 - Qmake 889 2048 - Qmake 3 128 - Qmake 1 4) e0').
    * exact Hc_slack.
    * apply QltT_to_Qlt. exact He0'.
  + (* (1−c−3/128−1/4)·e0' ≤ (1−c)·en' − 3s − e0'/4: the difference == (1−c)·(en'−e0') ≥ 0. *)
    apply (proj2 (Qle_minus_iff ((Qmake 1 1 - Qmake 889 2048 - Qmake 3 128 - Qmake 1 4) * e0') ((Qmake 1 1 - Qmake 889 2048) * en' - 3 * (Qdiv e0' 128) - (Qmake 1 4) * e0'))).
    apply (Qle_trans _ ((Qmake 1 1 - Qmake 889 2048) * (en' - e0')) _).
    * apply (Qmult_le_0_compat (Qmake 1 1 - Qmake 889 2048) (en' - e0')).
      -- vm_compute. discriminate.   (* 0 ≤ 1−c: the Qle constant reduces to Lt<>Gt. *)
      -- apply Qlt_le_weak. apply (proj1 (Qlt_minus_iff e0' en')). exact Heps0'n.   (* 0 ≤ en'−e0' *)
    * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv, Qminus. field.   (* (1−c)(en'−e0') == the difference: contains Qinv, so use field. *)
- (* sub2: (1−c)·en' − 3s ≤ B_n − A_n: the HShare + Hchain difference chain. *)
  apply (Qle_trans _ (en' - ShareSumn - 3 * (Qdiv e0' 128)) _).
  + (* (1−c)·en' − 3s ≤ en' − ShareSumn − 3s ⟺ ShareSumn ≤ (889/)·en' (HShare) *)
    apply (proj2 (Qle_minus_iff ((Qmake 1 1 - Qmake 889 2048) * en' - 3 * (Qdiv e0' 128)) (en' - ShareSumn - 3 * (Qdiv e0' 128)))).
    apply (Qle_trans _ ((Qmake 889 2048) * en' - ShareSumn) _).
    * apply (proj1 (Qle_minus_iff ShareSumn ((Qmake 889 2048) * en'))). exact HShare.
    * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  + (* en' − ShareSumn − 3s ≤ (en·hn+en') − A_n: the Hchain difference. *)
    apply (proj2 (Qle_minus_iff (en' - ShareSumn - 3 * (Qdiv e0' 128)) ((en * hn + en') - (projT1 (real_abs D) n)))).
    apply (Qle_trans _ ((en * hn + ShareSumn + 3 * (Qdiv e0' 128)) - (projT1 (real_abs D) n)) _).
    * apply (proj1 (Qle_minus_iff (projT1 (real_abs D) n) (en * hn + ShareSumn + 3 * (Qdiv e0' 128)))). exact Hchain.
    * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
}
}    exact Hfinal.

Qed.
(* ============ 6c: compose error decomposition (D == T1 + T2) ============
   D := Fh − (Fx + (df·dg)·h), T1 := Fh − (Fx + df·Dg) (the error of f at Dg),
   T2 := df·(Dg − dg·h) (the error of g scaled by df), with Dg := Gh − Gx.
   A pure real_eq ring-algebra chain (real_eq_sym makes the first argument the goal's RHS;
   real_eq_plus_compat (a,b,c,d) concludes a+b==c+d from the premises a==c and b==d;
   real_opp_mult opp(a·b)==a·opp(b) needs sym in the reverse direction; real_plus_assoc
   x+(y+z)==(x+y)+z needs sym in the reverse direction). *)
Lemma real_compose_diff_decomp : forall (Fh Fx df dg Gh Gx h : Real),
  real_eq (real_plus Fh (real_opp (real_plus Fx (real_mult (real_mult df dg) h))))
          (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df (real_plus Gh (real_opp Gx))))))
                     (real_mult df (real_plus (real_plus Gh (real_opp Gx)) (real_opp (real_mult dg h))))).
Proof.
  intros Fh Fx df dg Gh Gx h.
  set (Dg := real_plus Gh (real_opp Gx)).
  set (Xp := real_mult df Dg).
  set (Yp := real_mult df (real_mult dg h)).
  set (Yq := real_mult (real_mult df dg) h).
  assert (HYeq : real_eq Yp Yq).
  { unfold Yp, Yq.
    apply (real_eq_trans (real_mult df (real_mult dg h))
                         (real_mult (real_mult df dg) h)
                         (real_mult (real_mult df dg) h)).
    - apply (real_mult_assoc df dg h).
    - apply real_eq_refl. }
  assert (HoppY : real_eq (real_opp Yp) (real_opp Yq)).
  { apply (RealSetoid.real_eq_opp_compat Yp Yq). exact HYeq. }
  apply (real_eq_trans
    (real_plus Fh (real_opp (real_plus Fx (real_mult (real_mult df dg) h))))
    (real_plus Fh (real_plus (real_opp Fx) (real_opp (real_mult (real_mult df dg) h))))
    (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df Dg))))
               (real_mult df (real_plus Dg (real_opp (real_mult dg h)))))).
  - apply (RealSetoid.real_eq_plus_compat Fh (real_opp (real_plus Fx (real_mult (real_mult df dg) h)))
                                          Fh (real_plus (real_opp Fx) (real_opp (real_mult (real_mult df dg) h)))).
    + apply real_eq_refl.
    + apply (real_opp_plus Fx (real_mult (real_mult df dg) h)).
  - apply (real_eq_trans
      (real_plus Fh (real_plus (real_opp Fx) (real_opp (real_mult (real_mult df dg) h))))
      (real_plus (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp)))
      (real_plus (real_plus Fh (real_opp (real_plus Fx Xp)))
                 (real_mult df (real_plus Dg (real_opp (real_mult dg h)))))).
    + apply (real_eq_trans
        (real_plus Fh (real_plus (real_opp Fx) (real_opp (real_mult (real_mult df dg) h))))
        (real_plus Fh (real_plus (real_opp Fx) (real_opp Yp)))
        (real_plus (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp)))).
      * apply (RealSetoid.real_eq_plus_compat Fh (real_plus (real_opp Fx) (real_opp (real_mult (real_mult df dg) h)))
                                              Fh (real_plus (real_opp Fx) (real_opp Yp))).
        -- apply real_eq_refl.
        -- apply (RealSetoid.real_eq_plus_compat (real_opp Fx) (real_opp (real_mult (real_mult df dg) h))
                                                (real_opp Fx) (real_opp Yp)).
           ++ apply real_eq_refl.
           ++ apply (real_eq_sym (real_opp Yp) (real_opp (real_mult (real_mult df dg) h))).
              exact HoppY.
      * apply (real_eq_trans
          (real_plus Fh (real_plus (real_opp Fx) (real_opp Yp)))
          (real_plus (real_plus Fh (real_opp Fx)) (real_opp Yp))
          (real_plus (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp)))).
        -- apply (real_plus_assoc Fh (real_opp Fx) (real_opp Yp)).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus Fh (real_opp Fx)) (real_opp Yp)
                                                 (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp))).
           ++ apply real_eq_refl.
           ++ apply (real_eq_sym (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp)) (real_opp Yp)).
              apply (real_eq_trans
                (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp))
                (real_plus real_zero (real_opp Yp))
                (real_opp Yp)).
              ** apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp Xp) Xp) (real_opp Yp) real_zero (real_opp Yp)).
                 --- apply (real_eq_trans (real_plus (real_opp Xp) Xp) (real_plus Xp (real_opp Xp)) real_zero).
                     ++++ apply (real_plus_comm (real_opp Xp) Xp).
                     ++++ apply (real_plus_opp Xp).
                 --- apply real_eq_refl.
              ** apply (real_eq_trans (real_plus real_zero (real_opp Yp)) (real_plus (real_opp Yp) real_zero) (real_opp Yp)).
                 --- apply (real_plus_comm real_zero (real_opp Yp)).
                 --- apply (real_plus_zero (real_opp Yp)).
    + apply real_eq_sym.
      apply (real_eq_trans
        (real_plus (real_plus Fh (real_opp (real_plus Fx Xp)))
                   (real_mult df (real_plus Dg (real_opp (real_mult dg h)))))
        (real_plus (real_plus Fh (real_plus (real_opp Fx) (real_opp Xp)))
                   (real_plus Xp (real_opp Yp)))
        (real_plus (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp)))).
      * apply (RealSetoid.real_eq_plus_compat
          (real_plus Fh (real_opp (real_plus Fx Xp)))
          (real_mult df (real_plus Dg (real_opp (real_mult dg h))))
          (real_plus Fh (real_plus (real_opp Fx) (real_opp Xp)))
          (real_plus Xp (real_opp Yp))).
        -- apply (RealSetoid.real_eq_plus_compat Fh (real_opp (real_plus Fx Xp))
                                              Fh (real_plus (real_opp Fx) (real_opp Xp))).
           ++ apply real_eq_refl.
           ++ apply (real_opp_plus Fx Xp).
        -- apply (real_eq_trans
             (real_mult df (real_plus Dg (real_opp (real_mult dg h))))
             (real_plus (real_mult df Dg) (real_mult df (real_opp (real_mult dg h))))
             (real_plus Xp (real_opp Yp))).
           ++ apply (real_distrib df Dg (real_opp (real_mult dg h))).
           ++ apply (RealSetoid.real_eq_plus_compat (real_mult df Dg) (real_mult df (real_opp (real_mult dg h)))
                                                    Xp (real_opp Yp)).
              ** unfold Xp. apply real_eq_refl.
              ** unfold Yp.
                 apply (real_eq_sym (real_opp (real_mult df (real_mult dg h)))
                                    (real_mult df (real_opp (real_mult dg h)))).
                 apply (real_opp_mult df (real_mult dg h)).
      * apply (real_eq_trans
          (real_plus (real_plus Fh (real_plus (real_opp Fx) (real_opp Xp)))
                     (real_plus Xp (real_opp Yp)))
          (real_plus (real_plus (real_plus Fh (real_opp Fx)) (real_opp Xp))
                     (real_plus Xp (real_opp Yp)))
          (real_plus (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp)))).
        -- apply (RealSetoid.real_eq_plus_compat
             (real_plus Fh (real_plus (real_opp Fx) (real_opp Xp)))
             (real_plus Xp (real_opp Yp))
             (real_plus (real_plus Fh (real_opp Fx)) (real_opp Xp))
             (real_plus Xp (real_opp Yp))).
           ++ apply (real_plus_assoc Fh (real_opp Fx) (real_opp Xp)).
           ++ apply real_eq_refl.
        -- apply (real_eq_trans
             (real_plus (real_plus (real_plus Fh (real_opp Fx)) (real_opp Xp))
                        (real_plus Xp (real_opp Yp)))
             (real_plus (real_plus Fh (real_opp Fx))
                        (real_plus (real_opp Xp) (real_plus Xp (real_opp Yp))))
             (real_plus (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp)))).
           ++ apply (real_eq_sym (real_plus (real_plus Fh (real_opp Fx))
                                            (real_plus (real_opp Xp) (real_plus Xp (real_opp Yp))))
                                 (real_plus (real_plus (real_plus Fh (real_opp Fx)) (real_opp Xp))
                                            (real_plus Xp (real_opp Yp)))).
              apply (real_plus_assoc (real_plus Fh (real_opp Fx)) (real_opp Xp) (real_plus Xp (real_opp Yp))).
           ++ apply (RealSetoid.real_eq_plus_compat (real_plus Fh (real_opp Fx)) (real_plus (real_opp Xp) (real_plus Xp (real_opp Yp)))
                                                    (real_plus Fh (real_opp Fx)) (real_plus (real_plus (real_opp Xp) Xp) (real_opp Yp))).
              ** apply real_eq_refl.
              ** apply (real_plus_assoc (real_opp Xp) Xp (real_opp Yp)).
Qed.

(* ============ 6d2: a comm variant with the inverse absorbed ((inv_M·x)·M == x) ============
   real_M_inv_absorb gives M·(inv_M·x) == x; commuting (inv_M·x) with M yields it. The 2-step
   proof for eps_f·Lp == eps2 (eps_f := inv_Lp·eps2 gives (inv_Lp·eps2)·Lp == eps2). *)
Lemma real_inv_absorb_comm : forall (M x : Real) (HM : real_lt real_zero M),
  real_eq (real_mult (real_mult (real_inv_pos M HM) x) M) x.
Proof.
  intros M x HM.
  apply (real_eq_trans (real_mult (real_mult (real_inv_pos M HM) x) M)
                       (real_mult M (real_mult (real_inv_pos M HM) x))
                       x).
  - apply (real_mult_comm (real_mult (real_inv_pos M HM) x) M).
  - apply (real_M_inv_absorb M x HM).
Qed.

(* ============ 6d: the abstract |Dg| bound (shared by HDg1/HDg2) ============
   Dg == Gerr + rdfg·h, |Gerr| ≤ eps_g|h|+epsq, |rdfg·h| == |rdfg||h|, and the
   linear term ≤ Lp|h| give |Dg| ≤ Lp|h| + epsq + ept (the triangle lemma
   real_abs_triangle_le_eps requires a 0<ept premise; omitting a 0<eps premise
   makes apply leave a subgoal and every later bullet report "not finished").
   real_abs_triangle_le_eps : forall a b eps, 0<eps -> |a+b| ≤ |a|+|b|+eps
   — the 4th argument 0<eps must be supplied; if omitted, apply leaves a
   subgoal and any subsequent bullet reports not finished. *)
Lemma real_dg_bound_g : forall (Dg Gerr rdfg h eps_g epsq_g1 Lp ept1 : Real)
  (Hept1 : real_lt real_zero ept1)
  (HDg_split : real_eq Dg (real_plus Gerr (real_mult rdfg h)))
  (HGerr1 : real_le (real_abs Gerr) (real_plus (real_mult eps_g (real_abs h)) epsq_g1))
  (Habs : real_le (real_abs (real_mult rdfg h)) (real_mult (real_abs rdfg) (real_abs h)))
  (HLp : real_le (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs rdfg) (real_abs h)))
                 (real_mult Lp (real_abs h))),
  real_le (real_abs Dg) (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g1) ept1).
Proof.
  intros.
  apply (real_le_trans (real_abs Dg) (real_abs (real_plus Gerr (real_mult rdfg h)))
                       (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g1) ept1)).
  - apply RealSetoid.real_eq_le.
    apply (real_abs_eq_compat Dg (real_plus Gerr (real_mult rdfg h))).
    exact HDg_split.
  - apply (real_le_trans (real_abs (real_plus Gerr (real_mult rdfg h)))
                         (real_plus (real_plus (real_abs Gerr) (real_abs (real_mult rdfg h))) ept1)
                         (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g1) ept1)).
    + apply (real_abs_triangle_le_eps Gerr (real_mult rdfg h) ept1 Hept1).
    + apply (real_le_plus_compat (real_plus (real_abs Gerr) (real_abs (real_mult rdfg h)))
                                 (real_plus (real_mult Lp (real_abs h)) epsq_g1) ept1 ept1).
      * apply (real_le_trans (real_plus (real_abs Gerr) (real_abs (real_mult rdfg h)))
                             (real_plus (real_plus (real_mult eps_g (real_abs h)) epsq_g1) (real_mult (real_abs rdfg) (real_abs h)))
                             (real_plus (real_mult Lp (real_abs h)) epsq_g1)).
        -- apply (real_le_plus_compat (real_abs Gerr) (real_plus (real_mult eps_g (real_abs h)) epsq_g1)
                                      (real_abs (real_mult rdfg h)) (real_mult (real_abs rdfg) (real_abs h))).
           ++ exact HGerr1.
           ++ exact Habs.
        -- apply (real_le_trans (real_plus (real_plus (real_mult eps_g (real_abs h)) epsq_g1) (real_mult (real_abs rdfg) (real_abs h)))
                               (real_plus (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs rdfg) (real_abs h))) epsq_g1)
                               (real_plus (real_mult Lp (real_abs h)) epsq_g1)).
           ++ apply RealSetoid.real_eq_le.
              apply (real_eq_trans (real_plus (real_plus (real_mult eps_g (real_abs h)) epsq_g1) (real_mult (real_abs rdfg) (real_abs h)))
                                   (real_plus (real_mult eps_g (real_abs h)) (real_plus epsq_g1 (real_mult (real_abs rdfg) (real_abs h))))
                                   (real_plus (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs rdfg) (real_abs h))) epsq_g1)).
              ** apply (real_eq_sym (real_plus (real_mult eps_g (real_abs h)) (real_plus epsq_g1 (real_mult (real_abs rdfg) (real_abs h))))
                                    (real_plus (real_plus (real_mult eps_g (real_abs h)) epsq_g1) (real_mult (real_abs rdfg) (real_abs h)))).
                 apply (real_plus_assoc (real_mult eps_g (real_abs h)) epsq_g1 (real_mult (real_abs rdfg) (real_abs h))).
              ** apply (real_eq_trans (real_plus (real_mult eps_g (real_abs h)) (real_plus epsq_g1 (real_mult (real_abs rdfg) (real_abs h))))
                                     (real_plus (real_mult eps_g (real_abs h)) (real_plus (real_mult (real_abs rdfg) (real_abs h)) epsq_g1))
                                     (real_plus (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs rdfg) (real_abs h))) epsq_g1)).
                 --- apply (RealSetoid.real_eq_plus_compat (real_mult eps_g (real_abs h)) (real_plus epsq_g1 (real_mult (real_abs rdfg) (real_abs h)))
                                                           (real_mult eps_g (real_abs h)) (real_plus (real_mult (real_abs rdfg) (real_abs h)) epsq_g1)).
                     ++++ apply real_eq_refl.
                     ++++ apply (real_plus_comm epsq_g1 (real_mult (real_abs rdfg) (real_abs h))).
                 --- apply (real_plus_assoc (real_mult eps_g (real_abs h)) (real_mult (real_abs rdfg) (real_abs h)) epsq_g1).
           ++ apply (real_le_plus_compat (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs rdfg) (real_abs h)))
                                         (real_mult Lp (real_abs h)) epsq_g1 epsq_g1).
              ** exact HLp.
              ** apply real_le_refl.
      * apply real_le_refl.
Qed.

(* ============ 6d2: the compose main-term merge/reorder lemma (verified on a minimal MCP reproduction) ============
   Generalization of the L8481/L8483 goals: A:=eps2|h| B:=eps_f·epsq_g2 C:=eps_f·eps_tri_g2 D:=epsq_f
   F:=M·epsq_g2 G:=marg2 H:=eps_tri
   LHS = (((A+(B+C))+D) + ((A+F)+G)) + H == MID1 = (((A+A)+(B+F))+C) + (D+(G+H))
   MID1 == MID = (A+A) + ((B+F) + (C + (D + (G+H))))
   Chain: LHS → assoc backwards ×2 → swap → reorder core ((A+(B+C))+(A+F) == ((A+A)+(B+F))+C).
   assoc backwards = real_eq_sym (first argument = goal RHS, second = goal LHS) + real_plus_assoc;
   real_plus_swap a b c d : (a+b)+(c+d) == (a+c)+(b+d), and the goal must be in the
   (a+b)+(c+d) shape before swapping; assoc forward x+(y+z)==(x+y)+z applies directly without sym. *)
Lemma real_reorder_main : forall A B C D F G H : Real,
  real_eq
    (real_plus (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) G)) H)
    (real_plus (real_plus (real_plus (real_plus A A) (real_plus B F)) C) (real_plus D (real_plus G H))).
Proof.
  intros.
  apply (real_eq_trans
    (real_plus (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) G)) H)
    (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) (real_plus G H)))
    (real_plus (real_plus (real_plus (real_plus A A) (real_plus B F)) C) (real_plus D (real_plus G H)))).
  - apply (real_eq_trans
      (real_plus (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) G)) H)
      (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus (real_plus A F) G) H))
      (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) (real_plus G H)))).
    + apply (real_eq_sym (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus (real_plus A F) G) H))
                         (real_plus (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) G)) H)).
      apply (real_plus_assoc (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) G) H).
    + apply (RealSetoid.real_eq_plus_compat (real_plus (real_plus A (real_plus B C)) D)
                                            (real_plus (real_plus (real_plus A F) G) H)
                                            (real_plus (real_plus A (real_plus B C)) D)
                                            (real_plus (real_plus A F) (real_plus G H))).
      * apply real_eq_refl.
      * apply (real_eq_sym (real_plus (real_plus A F) (real_plus G H))
                           (real_plus (real_plus (real_plus A F) G) H)).
        apply (real_plus_assoc (real_plus A F) G H).
  - apply (real_eq_trans
      (real_plus (real_plus (real_plus A (real_plus B C)) D) (real_plus (real_plus A F) (real_plus G H)))
      (real_plus (real_plus (real_plus A (real_plus B C)) (real_plus A F)) (real_plus D (real_plus G H)))
      (real_plus (real_plus (real_plus (real_plus A A) (real_plus B F)) C) (real_plus D (real_plus G H)))).
    + apply (real_plus_swap (real_plus A (real_plus B C)) D (real_plus A F) (real_plus G H)).
    + apply (RealSetoid.real_eq_plus_compat
        (real_plus (real_plus A (real_plus B C)) (real_plus A F))
        (real_plus D (real_plus G H))
        (real_plus (real_plus (real_plus A A) (real_plus B F)) C)
        (real_plus D (real_plus G H))).
      * apply (real_eq_trans
          (real_plus (real_plus A (real_plus B C)) (real_plus A F))
          (real_plus A (real_plus (real_plus B C) (real_plus A F)))
          (real_plus (real_plus (real_plus A A) (real_plus B F)) C)).
        -- apply (real_eq_sym (real_plus A (real_plus (real_plus B C) (real_plus A F)))
                              (real_plus (real_plus A (real_plus B C)) (real_plus A F))).
           apply (real_plus_assoc A (real_plus B C) (real_plus A F)).
        -- apply (real_eq_trans
             (real_plus A (real_plus (real_plus B C) (real_plus A F)))
             (real_plus A (real_plus (real_plus B A) (real_plus C F)))
             (real_plus (real_plus (real_plus A A) (real_plus B F)) C)).
           ++ apply (RealSetoid.real_eq_plus_compat A
                (real_plus (real_plus B C) (real_plus A F))
                A
                (real_plus (real_plus B A) (real_plus C F))).
              ** apply real_eq_refl.
              ** apply (real_plus_swap B C A F).
           ++ apply (real_eq_trans
                (real_plus A (real_plus (real_plus B A) (real_plus C F)))
                (real_plus (real_plus (real_plus A A) B) (real_plus F C))
                (real_plus (real_plus (real_plus A A) (real_plus B F)) C)).
              ** apply (real_eq_trans
                   (real_plus A (real_plus (real_plus B A) (real_plus C F)))
                   (real_plus (real_plus A (real_plus B A)) (real_plus C F))
                   (real_plus (real_plus (real_plus A A) B) (real_plus F C))).
                 --- apply (real_plus_assoc A (real_plus B A) (real_plus C F)).
                 --- apply (RealSetoid.real_eq_plus_compat
                       (real_plus A (real_plus B A)) (real_plus C F)
                       (real_plus (real_plus A A) B) (real_plus F C)).
                     ++++ apply (real_eq_trans (real_plus A (real_plus B A))
                                               (real_plus A (real_plus A B))
                                               (real_plus (real_plus A A) B)).
                          +++++ apply (RealSetoid.real_eq_plus_compat A (real_plus B A) A (real_plus A B)).
                               ++++++ apply real_eq_refl.
                               ++++++ apply (real_plus_comm B A).
                          +++++ apply (real_plus_assoc A A B).
                     ++++ apply (real_plus_comm C F).
              ** apply (real_eq_trans
                   (real_plus (real_plus (real_plus A A) B) (real_plus F C))
                   (real_plus (real_plus (real_plus (real_plus A A) B) F) C)
                   (real_plus (real_plus (real_plus A A) (real_plus B F)) C)).
                 --- apply (real_plus_assoc (real_plus (real_plus A A) B) F C).
                 --- apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_plus (real_plus A A) B) F) C
                       (real_plus (real_plus A A) (real_plus B F)) C).
                     ++++ apply (real_eq_sym (real_plus (real_plus A A) (real_plus B F))
                                             (real_plus (real_plus (real_plus A A) B) F)).
                          apply (real_plus_assoc (real_plus A A) B F).
                     ++++ apply real_eq_refl.
      * apply real_eq_refl.
Qed.

Lemma real_reorder_mid : forall A B C D F G H : Real,
  real_eq
    (real_plus (real_plus (real_plus (real_plus A A) (real_plus B F)) C) (real_plus D (real_plus G H)))
    (real_plus (real_plus A A) (real_plus (real_plus B F) (real_plus C (real_plus D (real_plus G H))))).
Proof.
  intros.
  apply (real_eq_trans
    (real_plus (real_plus (real_plus (real_plus A A) (real_plus B F)) C) (real_plus D (real_plus G H)))
    (real_plus (real_plus (real_plus A A) (real_plus B F)) (real_plus C (real_plus D (real_plus G H))))
    (real_plus (real_plus A A) (real_plus (real_plus B F) (real_plus C (real_plus D (real_plus G H)))))).
  - apply (real_eq_sym (real_plus (real_plus (real_plus A A) (real_plus B F)) (real_plus C (real_plus D (real_plus G H))))
                       (real_plus (real_plus (real_plus (real_plus A A) (real_plus B F)) C) (real_plus D (real_plus G H)))).
    apply (real_plus_assoc (real_plus (real_plus A A) (real_plus B F)) C (real_plus D (real_plus G H))).
  - apply (real_eq_sym (real_plus (real_plus A A) (real_plus (real_plus B F) (real_plus C (real_plus D (real_plus G H)))))
                       (real_plus (real_plus (real_plus A A) (real_plus B F)) (real_plus C (real_plus D (real_plus G H))))).
    apply (real_plus_assoc (real_plus A A) (real_plus B F) (real_plus C (real_plus D (real_plus G H)))).
Qed.

(* ============ 6e: real_differentiable_compose (on the Set-layer template) ============
   rdf := rdf_f(gx)·rdf_g(x); g carries the positivity premise Hgpos (the input of f needs 0<g x)
   and f the real-valued extensionality Hfwd (restating f(g(x+h)) == f(gx+Dg); RealDifferentiable
   has no wd field).
   Budget (Bishop per-eps, everything == exactly assembling eps'):
     eps2 := half·eps; M := 1+|rdf_f(gx)|; eps_g := inv_M·eps2 (M·eps_g == eps2)
     Lp := |rdf_g(x)|+eps_g; eps_f := inv_Lp·eps2 (eps_f·Lp == eps2)
     Dg := g(x+h)−gx; |Dg| ≤ Lp|h| + epsq_g1 + eps_tri_g1 (the |Dg|<dfd argument,
     with epsq_g1 := eps_tri_g1 := half³·dfd, Lp|h| < half·dfd, half³·dfd < dfd/4 respectively)
     T1 ≤ eps2|h| + eps_f·epsq_g2 + eps_f·eps_tri_g2 + epsq_f
       (epsq_g2 := inv(eps_f+M)·(half·eps'), so (eps_f+M)·epsq_g2 == eps'/2;
        eps_tri_g2 := inv_eps_f·(eps'/8), so eps_f·eps_tri_g2 == eps'/8)
     T2 ≤ eps2|h| + M·epsq_g2 + marg2 (real_prod_abs_le_two)
     surplus == eps'/2 + eps'/8 + eps'/8 + eps'/8 + eps'/8 == eps' .
   real_eq_sym used explicitly (first argument = goal RHS); real_eq_plus_compat (a,b,c,d)
   concludes a+b==c+d from the premises a==c and b==d; real_opp_mult opp(a·b)==a·opp(b)
   needs sym in the reverse direction; real_plus_assoc x+(y+z)==(x+y)+z needs sym in the
   reverse direction; coefficient comparisons go through
   real_half_lt_self + real_half_plus_half (== exactly assembling eps', avoiding le_mult on |h|). *)
Lemma real_differentiable_compose :
  forall (f g : forall x : Real, real_lt real_zero x -> Real)
    (Hf : RealDifferentiable f) (Hg : RealDifferentiable g)
    (Hgpos : forall (x : Real) (Hx : real_lt real_zero x), real_lt real_zero (g x Hx))
    (Hfwd : forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
              real_eq x y -> real_eq (f x Hx) (f y Hy)),
  RealDifferentiable (fun x Hx => f (g x Hx) (Hgpos x Hx)).
Proof.
  intros f g Hf Hg Hgpos Hfwd.
  destruct Hf as [rdf_f Hf_corr].
  destruct Hg as [rdf_g Hg_corr].
  exists (fun (x : Real) (Hx : real_lt real_zero x) =>
            real_mult (rdf_f (g x Hx) (Hgpos x Hx)) (rdf_g x Hx)).
  intros x Hx eps Heps.
  set (half := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  assert (Hhalf : real_lt real_zero half).
  { unfold half. apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)). }
  set (eps2 := real_mult half eps).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive; [exact Hhalf | exact Heps]. }
  set (gx := g x Hx).
  set (M := real_plus real_one (real_abs (rdf_f gx (Hgpos x Hx)))).
  assert (HM : real_lt real_zero M).
  { unfold M. apply (real_abs_plus_one_pos (rdf_f gx (Hgpos x Hx))). }
  set (eps_g := real_mult (real_inv_pos M HM) eps2).
  assert (Heps_g : real_lt real_zero eps_g).
  { unfold eps_g. apply real_mult_positive; [apply (real_inv_pos_pos M HM) | exact Heps2]. }
  set (Lp := real_plus (real_abs (rdf_g x Hx)) eps_g).
  assert (HLp : real_lt real_zero Lp).
  { unfold Lp. apply (real_abs_plus_pos (rdf_g x Hx) eps_g). exact Heps_g. }
  set (eps_f := real_mult (real_inv_pos Lp HLp) eps2).
  assert (Heps_f : real_lt real_zero eps_f).
  { unfold eps_f. apply real_mult_positive; [apply (real_inv_pos_pos Lp HLp) | exact Heps2]. }
  destruct (Hf_corr gx (Hgpos x Hx) eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  set (epsq_g1 := real_mult half (real_mult half (real_mult half dfd))).
  assert (Hepsq_g1 : real_lt real_zero epsq_g1).
  { unfold epsq_g1.
    apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Hdf1]]]. }
  set (eps_tri_g1 := real_mult half (real_mult half (real_mult half dfd))).
  assert (Heptr_g1 : real_lt real_zero eps_tri_g1).
  { unfold eps_tri_g1.
    apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Hdf1]]]. }
  assert (Hepsq1_mid : real_lt epsq_g1 (real_mult half (real_mult half dfd))).
  { unfold epsq_g1.
    apply (real_half_lt_self (real_mult half (real_mult half dfd))).
    apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Hdf1]]. }
  assert (Heptr1_mid : real_lt eps_tri_g1 (real_mult half (real_mult half dfd))).
  { unfold eps_tri_g1.
    apply (real_half_lt_self (real_mult half (real_mult half dfd))).
    apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Hdf1]]. }
  destruct (Hg_corr x Hx eps_g Heps_g) as [dgd1 [Hdg1 Hdg2_1]].
  destruct (Hg_corr x Hx eps_g Heps_g) as [dgd2 [Hdg2 Hdg2_2]].
  set (delta_fd := real_mult (real_inv_pos Lp HLp) (real_mult half dfd)).
  assert (Hdelta_fd : real_lt real_zero delta_fd).
  { unfold delta_fd.
    apply real_mult_positive.
    - apply (real_inv_pos_pos Lp HLp).
    - apply real_mult_positive; [exact Hhalf | exact Hdf1]. }
  set (delta := real_min dgd1 (real_min dgd2 delta_fd)).
  assert (Hdelta : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos; [exact Hdg1 | apply real_min_pos; [exact Hdg2 | exact Hdelta_fd]]. }
  exists delta.
  split.
  - exact Hdelta.
  - intros h Hh Hxh eps' Heps'.
    (* Premise chain: |h| < dgd1, dgd2, delta_fd. *)
    assert (Hh_dgd1 : real_lt (real_abs h) dgd1).
    { apply (real_min_lt_l h dgd1 (real_min dgd2 delta_fd)). exact Hh. }
    assert (Hh_dgd2 : real_lt (real_abs h) dgd2).
    { apply (real_min_lt_l h dgd2 delta_fd).
      apply (real_min_lt_r h dgd1 (real_min dgd2 delta_fd)). exact Hh. }
    assert (Hh_dfd : real_lt (real_abs h) delta_fd).
    { apply (real_min_lt_r h dgd2 delta_fd).
      apply (real_min_lt_r h dgd1 (real_min dgd2 delta_fd)). exact Hh. }
    (* eps'-related constants. *)
    assert (HepsfM : real_lt real_zero (real_plus eps_f M)).
    { apply (real_plus_positive eps_f M Heps_f HM). }
    set (epsq_g2 := real_mult (real_inv_pos (real_plus eps_f M) HepsfM) (real_mult half eps')).
    assert (Hepsq_g2 : real_lt real_zero epsq_g2).
    { unfold epsq_g2.
      apply real_mult_positive.
      - apply (real_inv_pos_pos (real_plus eps_f M) HepsfM).
      - apply real_mult_positive; [exact Hhalf | exact Heps']. }
    set (eps_tri_g2 := real_mult (real_inv_pos eps_f Heps_f) (real_mult half (real_mult half (real_mult half eps')))).
    assert (Heptr_g2 : real_lt real_zero eps_tri_g2).
    { unfold eps_tri_g2.
      apply real_mult_positive.
      - apply (real_inv_pos_pos eps_f Heps_f).
      - apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Heps']]]. }
    set (epsq_f := real_mult half (real_mult half (real_mult half eps'))).
    assert (Hepsq_f : real_lt real_zero epsq_f).
    { unfold epsq_f.
      apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Heps']]]. }
    set (marg2 := real_mult half (real_mult half (real_mult half eps'))).
    assert (Hmarg2 : real_lt real_zero marg2).
    { unfold marg2.
      apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Heps']]]. }
    set (eps_tri := real_mult half (real_mult half (real_mult half eps'))).
    assert (Heptr : real_lt real_zero eps_tri).
    { unfold eps_tri.
      apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | apply real_mult_positive; [exact Hhalf | exact Heps']]]. }
    (* Dg := g(x+h)−gx; Gerr := Dg − rdf_g·h (the g error). *)
    set (Gh := g (real_plus x h) Hxh).
    set (Dg := real_plus Gh (real_opp gx)).
    set (Gerr := real_plus Dg (real_opp (real_mult (rdf_g x Hx) h))).
    (* Gerr == Gh − (gx + rdf_g·h): split by opp_plus, restated by assoc. *)
    assert (HGerr : real_eq Gerr
                      (real_plus Gh (real_opp (real_plus gx (real_mult (rdf_g x Hx) h))))).
    { unfold Gerr, Dg.
      apply (real_eq_trans (real_plus (real_plus Gh (real_opp gx)) (real_opp (real_mult (rdf_g x Hx) h)))
                           (real_plus Gh (real_plus (real_opp gx) (real_opp (real_mult (rdf_g x Hx) h))))
                           (real_plus Gh (real_opp (real_plus gx (real_mult (rdf_g x Hx) h))))).
      - apply real_eq_sym. apply (real_plus_assoc Gh (real_opp gx) (real_opp (real_mult (rdf_g x Hx) h))).
      - apply (RealSetoid.real_eq_plus_compat Gh
               (real_plus (real_opp gx) (real_opp (real_mult (rdf_g x Hx) h)))
               Gh
               (real_opp (real_plus gx (real_mult (rdf_g x Hx) h)))).
        + apply real_eq_refl.
        + apply real_eq_sym. apply (real_opp_plus gx (real_mult (rdf_g x Hx) h)). }
    (* |Gerr| ≤ eps_g|h| + epsq_g1 (Hg_corr at epsq_g1, Gerr restated). *)
    assert (HGerr1 : real_le (real_abs Gerr)
                             (real_plus (real_mult eps_g (real_abs h)) epsq_g1)).
    { apply (real_le_trans (real_abs Gerr)
                           (real_abs (real_plus Gh (real_opp (real_plus gx (real_mult (rdf_g x Hx) h)))))
                           (real_plus (real_mult eps_g (real_abs h)) epsq_g1)).
      - apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat Gerr (real_plus Gh (real_opp (real_plus gx (real_mult (rdf_g x Hx) h))))).
        exact HGerr.
      - exact (Hdg2_1 h Hh_dgd1 Hxh epsq_g1 Hepsq_g1). }
    (* |Gerr| ≤ eps_g|h| + epsq_g2 (Hg_corr at epsq_g2). *)
    assert (HGerr2 : real_le (real_abs Gerr)
                             (real_plus (real_mult eps_g (real_abs h)) epsq_g2)).
    { apply (real_le_trans (real_abs Gerr)
                           (real_abs (real_plus Gh (real_opp (real_plus gx (real_mult (rdf_g x Hx) h)))))
                           (real_plus (real_mult eps_g (real_abs h)) epsq_g2)).
      - apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat Gerr (real_plus Gh (real_opp (real_plus gx (real_mult (rdf_g x Hx) h))))).
        exact HGerr.
      - exact (Hdg2_2 h Hh_dgd2 Hxh epsq_g2 Hepsq_g2). }
    (* Lp|h| < half·dfd (Hh_dfd via inv_correct). *)
    assert (HLph : real_lt (real_mult Lp (real_abs h)) (real_mult half dfd)).
    { apply (real_lt_le_trans (real_mult Lp (real_abs h))
                              (real_mult Lp delta_fd)
                              (real_mult half dfd)).
      - (* Lp·|h| < Lp·delta_fd: mult_lt_compat_l (0 < Lp, |h| < delta_fd) *)
        apply (real_mult_lt_compat_l (real_abs h) delta_fd Lp Hh_dfd HLp).
      - (* Lp·delta_fd ≤ half·dfd: an == restatement (inv_correct). *)
        apply RealSetoid.real_eq_le.
        unfold delta_fd.
        apply (real_eq_trans (real_mult Lp (real_mult (real_inv_pos Lp HLp) (real_mult half dfd)))
                             (real_mult (real_mult Lp (real_inv_pos Lp HLp)) (real_mult half dfd))
                             (real_mult half dfd)).
        + apply (real_mult_assoc Lp (real_inv_pos Lp HLp) (real_mult half dfd)).
        + apply (real_eq_trans (real_mult (real_mult Lp (real_inv_pos Lp HLp)) (real_mult half dfd))
                               (real_mult real_one (real_mult half dfd))
                               (real_mult half dfd)).
          * apply (RealSetoid.real_eq_mult_compat (real_mult Lp (real_inv_pos Lp HLp)) (real_mult half dfd)
                                                  real_one (real_mult half dfd)).
            -- apply (real_inv_pos_correct Lp HLp).
            -- apply real_eq_refl.
          * apply (real_eq_trans (real_mult real_one (real_mult half dfd))
                                 (real_mult (real_mult half dfd) real_one)
                                 (real_mult half dfd)).
            -- apply (real_mult_comm real_one (real_mult half dfd)).
            -- apply (real_mult_one (real_mult half dfd)). }
    (* |Dg| ≤ Lp|h| + epsq_g1 + eps_tri_g1 (HDg1: mirroring the mult HDf structure — HDg_split + triangle + the linear term). *)
    assert (HDg_split : real_eq Dg (real_plus Gerr (real_mult (rdf_g x Hx) h))).
    { unfold Gerr, Dg.
      set (A := real_plus Gh (real_opp gx)).
      set (X := real_mult (rdf_g x Hx) h).
      apply (real_eq_sym (real_plus (real_plus A (real_opp X)) X) A).
      apply (real_eq_trans (real_plus (real_plus A (real_opp X)) X)
                           (real_plus X (real_plus A (real_opp X)))
                           A).
      - apply (real_plus_comm (real_plus A (real_opp X)) X).
      - apply (real_plus_minus_cancel X A). }
    assert (Habs : real_le (real_abs (real_mult (rdf_g x Hx) h)) (real_mult (real_abs (rdf_g x Hx)) (real_abs h))).
    { apply RealSetoid.real_eq_le.
      apply (real_abs_mult_req (rdf_g x Hx) h). }
    assert (HLp1 : real_le (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs (rdf_g x Hx)) (real_abs h)))
                           (real_mult Lp (real_abs h))).
    { apply RealSetoid.real_eq_le.
      apply (real_eq_trans (real_plus (real_mult eps_g (real_abs h)) (real_mult (real_abs (rdf_g x Hx)) (real_abs h)))
                           (real_mult (real_plus eps_g (real_abs (rdf_g x Hx))) (real_abs h))
                           (real_mult Lp (real_abs h))).
      - apply (real_distrib_r eps_g (real_abs (rdf_g x Hx)) (real_abs h)).
      - apply (RealSetoid.real_eq_mult_compat (real_plus eps_g (real_abs (rdf_g x Hx))) (real_abs h)
                                              Lp (real_abs h)).
        + apply (real_plus_comm eps_g (real_abs (rdf_g x Hx))).
        + apply real_eq_refl. }
    assert (HDg1 : real_le (real_abs Dg)
                           (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g1) eps_tri_g1)).
    { exact (real_dg_bound_g Dg Gerr (rdf_g x Hx) h eps_g epsq_g1 Lp eps_tri_g1
                             Heptr_g1 HDg_split HGerr1 Habs HLp1). }
    (* |Dg| ≤ Lp|h| + epsq_g2 + eps_tri_g2 (HDg2) *)
    assert (HDg2 : real_le (real_abs Dg)
                           (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2)).
    { exact (real_dg_bound_g Dg Gerr (rdf_g x Hx) h eps_g epsq_g2 Lp eps_tri_g2
                             Heptr_g2 HDg_split HGerr2 Habs HLp1). }
    (* |Dg| < dfd: |Dg| ≤ Lp|h|+epsq_g1+eps_tri_g1 < half·dfd + half·(half·dfd) + half·(half·dfd) == dfd *)
    assert (HdfDg : real_lt (real_abs Dg) dfd).
    { apply (real_le_lt_trans (real_abs Dg)
                              (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g1) eps_tri_g1)
                              dfd).
      - exact HDg1.
      - apply (real_lt_le_trans (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g1) eps_tri_g1)
                                (real_plus (real_plus (real_mult half dfd) (real_mult half (real_mult half dfd))) (real_mult half (real_mult half dfd)))
                                dfd).
        + apply (real_lt_plus_compat (real_plus (real_mult Lp (real_abs h)) epsq_g1)
                                     (real_plus (real_mult half dfd) (real_mult half (real_mult half dfd)))
                                     eps_tri_g1 (real_mult half (real_mult half dfd))).
          * apply (real_lt_plus_compat (real_mult Lp (real_abs h)) (real_mult half dfd)
                                       epsq_g1 (real_mult half (real_mult half dfd))).
            -- exact HLph.
            -- exact Hepsq1_mid.
          * exact Heptr1_mid.
        + apply RealSetoid.real_eq_le.
          apply (real_eq_trans
            (real_plus (real_plus (real_mult half dfd) (real_mult half (real_mult half dfd))) (real_mult half (real_mult half dfd)))
            (real_plus (real_mult half dfd) (real_plus (real_mult half (real_mult half dfd)) (real_mult half (real_mult half dfd))))
            dfd).
          * apply real_eq_sym.
            apply (real_plus_assoc (real_mult half dfd) (real_mult half (real_mult half dfd)) (real_mult half (real_mult half dfd))).
          * apply (real_eq_trans
              (real_plus (real_mult half dfd) (real_plus (real_mult half (real_mult half dfd)) (real_mult half (real_mult half dfd))))
              (real_plus (real_mult half dfd) (real_mult half dfd))
              dfd).
            -- apply (RealSetoid.real_eq_plus_compat (real_mult half dfd)
                                                     (real_plus (real_mult half (real_mult half dfd)) (real_mult half (real_mult half dfd)))
                                                     (real_mult half dfd) (real_mult half dfd)).
               ++ apply real_eq_refl.
               ++ apply (real_half_plus_half (real_mult half dfd)).
            -- apply (real_half_plus_half dfd). }
    (* 0 < gx + Dg (Hgpos (x+h) Hxh restated via real_lt_eq_lt: Gh == gx+Dg). *)
    assert (Hxh' : real_lt real_zero (real_plus gx Dg)).
    { apply (real_lt_eq_lt real_zero Gh (real_plus gx Dg)).
      - exact (Hgpos (real_plus x h) Hxh).
      - unfold Dg.
        apply (real_eq_sym (real_plus gx (real_plus Gh (real_opp gx))) Gh).
        apply (real_plus_minus_cancel gx Gh). }
    (* ============ T1/T2 bounds + summary ============ *)
    (* T1 := f(g(x+h)) − f(gx) − rdf_f·Dg; T2 := rdf_f·(Dg − rdf_g·h) *)
    set (T1 := real_plus (f (g (real_plus x h) Hxh) (Hgpos (real_plus x h) Hxh))
                         (real_opp (real_plus (f gx (Hgpos x Hx))
                                              (real_mult (rdf_f gx (Hgpos x Hx)) Dg)))).
    set (T2 := real_mult (rdf_f gx (Hgpos x Hx))
                         (real_plus Dg (real_opp (real_mult (rdf_g x Hx) h)))).
    (* |T1| ≤ eps_f·|Dg| + epsq_f: Hf2 at Dg (f(gx+Dg) == f(g(x+h)) via Hfwd). *)
    assert (HT1 : real_le (real_abs T1) (real_plus (real_mult eps_f (real_abs Dg)) epsq_f)).
    { apply (real_le_trans (real_abs T1)
                           (real_abs (real_plus (f (real_plus gx Dg) Hxh')
                                                (real_opp (real_plus (f gx (Hgpos x Hx)) (real_mult (rdf_f gx (Hgpos x Hx)) Dg)))))
                           (real_plus (real_mult eps_f (real_abs Dg)) epsq_f)).
      - apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat T1
                                  (real_plus (f (real_plus gx Dg) Hxh')
                                             (real_opp (real_plus (f gx (Hgpos x Hx)) (real_mult (rdf_f gx (Hgpos x Hx)) Dg))))).
        unfold T1.
        apply (RealSetoid.real_eq_plus_compat (f (g (real_plus x h) Hxh) (Hgpos (real_plus x h) Hxh))
                                              (real_opp (real_plus (f gx (Hgpos x Hx)) (real_mult (rdf_f gx (Hgpos x Hx)) Dg)))
                                              (f (real_plus gx Dg) Hxh')
                                              (real_opp (real_plus (f gx (Hgpos x Hx)) (real_mult (rdf_f gx (Hgpos x Hx)) Dg)))).
        + apply (Hfwd (g (real_plus x h) Hxh) (real_plus gx Dg)
                      (Hgpos (real_plus x h) Hxh) Hxh').
          unfold Dg.
          apply (real_eq_sym (real_plus gx (real_plus (g (real_plus x h) Hxh) (real_opp gx))) (g (real_plus x h) Hxh)).
          apply (real_plus_minus_cancel gx (g (real_plus x h) Hxh)).
        + apply real_eq_refl.
      - exact (Hdf2 Dg HdfDg Hxh' epsq_f Hepsq_f). }
    (* |T2| ≤ M·(eps_g|h| + epsq_g2) + marg2: real_prod_abs_le_two (|rdf_f| ≤ M, |g error| ≤ eps_g|h|+epsq_g2). *)
    assert (HT2a : real_le (real_abs T2)
                           (real_plus (real_mult M (real_plus (real_mult eps_g (real_abs h)) epsq_g2)) marg2)).
    { unfold T2.
      apply (real_prod_abs_le_two (rdf_f gx (Hgpos x Hx))
                                  (real_plus Dg (real_opp (real_mult (rdf_g x Hx) h)))
                                  M (real_plus (real_mult eps_g (real_abs h)) epsq_g2) marg2).
      - exact Hmarg2.
      - unfold M. apply (real_abs_le_plus_one (rdf_f gx (Hgpos x Hx))).
      - apply (real_le_trans (real_abs (real_plus Dg (real_opp (real_mult (rdf_g x Hx) h))))
                             (real_abs Gerr)
                             (real_plus (real_mult eps_g (real_abs h)) epsq_g2)).
        + apply RealSetoid.real_eq_le.
          apply (real_abs_eq_compat (real_plus Dg (real_opp (real_mult (rdf_g x Hx) h))) Gerr).
          unfold Gerr. apply real_eq_refl.
        + exact HGerr2. }
    (* |T2| ≤ eps2|h| + M·epsq_g2 + marg2 *)
    assert (HT2b : real_le (real_abs T2)
                           (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2)).
    { apply (real_le_trans (real_abs T2)
                           (real_plus (real_mult M (real_plus (real_mult eps_g (real_abs h)) epsq_g2)) marg2)
                           (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2)).
      - exact HT2a.
      - apply RealSetoid.real_eq_le.
        apply (real_eq_trans
          (real_plus (real_mult M (real_plus (real_mult eps_g (real_abs h)) epsq_g2)) marg2)
          (real_plus (real_plus (real_mult (real_mult M eps_g) (real_abs h)) (real_mult M epsq_g2)) marg2)
          (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2)).
        + apply (real_eq_trans (real_plus (real_mult M (real_plus (real_mult eps_g (real_abs h)) epsq_g2)) marg2)
                               (real_plus (real_plus (real_mult M (real_mult eps_g (real_abs h))) (real_mult M epsq_g2)) marg2)
                               (real_plus (real_plus (real_mult (real_mult M eps_g) (real_abs h)) (real_mult M epsq_g2)) marg2)).
          * apply (RealSetoid.real_eq_plus_compat (real_mult M (real_plus (real_mult eps_g (real_abs h)) epsq_g2)) marg2
                                                  (real_plus (real_mult M (real_mult eps_g (real_abs h))) (real_mult M epsq_g2)) marg2).
            -- apply (real_distrib M (real_mult eps_g (real_abs h)) epsq_g2).
            -- apply real_eq_refl.
          * apply (RealSetoid.real_eq_plus_compat (real_plus (real_mult M (real_mult eps_g (real_abs h))) (real_mult M epsq_g2)) marg2
                                                  (real_plus (real_mult (real_mult M eps_g) (real_abs h)) (real_mult M epsq_g2)) marg2).
            -- apply (RealSetoid.real_eq_plus_compat (real_mult M (real_mult eps_g (real_abs h))) (real_mult M epsq_g2)
                                                    (real_mult (real_mult M eps_g) (real_abs h)) (real_mult M epsq_g2)).
               ++ apply (real_mult_assoc M eps_g (real_abs h)).
               ++ apply real_eq_refl.
            -- apply real_eq_refl.
        + apply (RealSetoid.real_eq_plus_compat (real_plus (real_mult (real_mult M eps_g) (real_abs h)) (real_mult M epsq_g2)) marg2
                                                (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2).
          * apply (RealSetoid.real_eq_plus_compat (real_mult (real_mult M eps_g) (real_abs h)) (real_mult M epsq_g2)
                                                  (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)).
            -- apply (RealSetoid.real_eq_mult_compat (real_mult M eps_g) (real_abs h) eps2 (real_abs h)).
               ++ unfold eps_g. apply (real_M_inv_absorb M eps2 HM).
               ++ apply real_eq_refl.
            -- apply real_eq_refl.
          * apply real_eq_refl. }
    (* |T1| ≤ eps2|h| + eps_f·epsq_g2 + eps_f·eps_tri_g2 + epsq_f: eps_f·|Dg| ≤ eps_f·(Lp|h|+epsq_g2+eps_tri_g2) == eps2|h|+... *)
    assert (HT1b : real_le (real_abs T1)
                           (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                 (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))
                                      epsq_f)).
    { apply (real_le_trans (real_abs T1)
                           (real_plus (real_mult eps_f (real_abs Dg)) epsq_f)
                           (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                 (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))
                                      epsq_f)).
      - exact HT1.
      - apply (real_le_plus_compat (real_mult eps_f (real_abs Dg))
                                   (real_plus (real_mult eps2 (real_abs h))
                                              (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))
                                   epsq_f epsq_f).
        + apply (real_le_trans (real_mult eps_f (real_abs Dg))
                               (real_mult eps_f (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2))
                               (real_plus (real_mult eps2 (real_abs h))
                                          (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))).
          * apply (real_le_trans (real_mult eps_f (real_abs Dg))
                                 (real_mult (real_abs Dg) eps_f)
                                 (real_mult eps_f (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2))).
            -- apply RealSetoid.real_eq_le.
               apply (real_mult_comm eps_f (real_abs Dg)).
            -- apply (real_le_trans (real_mult (real_abs Dg) eps_f)
                                   (real_mult (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2) eps_f)
                                   (real_mult eps_f (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2))).
               ++ apply (real_le_mult_compat (real_abs Dg) (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2) eps_f Heps_f HDg2).
               ++ apply RealSetoid.real_eq_le.
                  apply (real_mult_comm (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2) eps_f).
          * (* eps_f·(Lp|h|+epsq_g2+eps_tri_g2) == eps2|h| + eps_f·epsq_g2 + eps_f·eps_tri_g2 (eps_f·Lp == eps2 via real_inv_absorb_comm). *)
            apply RealSetoid.real_eq_le.
            apply (real_eq_trans
              (real_mult eps_f (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2))
              (real_plus (real_plus (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2)) (real_mult eps_f eps_tri_g2))
              (real_plus (real_mult eps2 (real_abs h))
                         (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))).
            -- (* distributivity expanded twice. *)
               apply (real_eq_trans
                 (real_mult eps_f (real_plus (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2))
                 (real_plus (real_mult eps_f (real_plus (real_mult Lp (real_abs h)) epsq_g2)) (real_mult eps_f eps_tri_g2))
                 (real_plus (real_plus (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2)) (real_mult eps_f eps_tri_g2))).
               ++ apply (real_distrib eps_f (real_plus (real_mult Lp (real_abs h)) epsq_g2) eps_tri_g2).
               ++ apply (RealSetoid.real_eq_plus_compat (real_mult eps_f (real_plus (real_mult Lp (real_abs h)) epsq_g2)) (real_mult eps_f eps_tri_g2)
                                                        (real_plus (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2)) (real_mult eps_f eps_tri_g2)).
                  ** apply (real_eq_trans (real_mult eps_f (real_plus (real_mult Lp (real_abs h)) epsq_g2))
                                          (real_plus (real_mult eps_f (real_mult Lp (real_abs h))) (real_mult eps_f epsq_g2))
                                          (real_plus (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2))).
                     --- apply (real_distrib eps_f (real_mult Lp (real_abs h)) epsq_g2).
                     --- apply (RealSetoid.real_eq_plus_compat (real_mult eps_f (real_mult Lp (real_abs h))) (real_mult eps_f epsq_g2)
                                                               (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2)).
                         +++ apply (real_mult_assoc eps_f Lp (real_abs h)).
                         +++ apply real_eq_refl.
                  ** apply real_eq_refl.
            -- (* ((eps_f·Lp)|h| + eps_f·epsq_g2) + eps_f·eps_tri_g2 == eps2|h| + (eps_f·epsq_g2 + eps_f·eps_tri_g2) *)
               apply (real_eq_trans
                 (real_plus (real_plus (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2)) (real_mult eps_f eps_tri_g2))
                 (real_plus (real_mult (real_mult eps_f Lp) (real_abs h))
                            (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))
                 (real_plus (real_mult eps2 (real_abs h))
                            (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))).
               ++ apply (real_eq_sym (real_plus (real_mult (real_mult eps_f Lp) (real_abs h))
                                                (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)))
                                     (real_plus (real_plus (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2)) (real_mult eps_f eps_tri_g2))).
                  apply (real_plus_assoc (real_mult (real_mult eps_f Lp) (real_abs h)) (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2)).
               ++ apply (RealSetoid.real_eq_plus_compat (real_mult (real_mult eps_f Lp) (real_abs h))
                                                        (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))
                                                        (real_mult eps2 (real_abs h))
                                                        (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))).
                  ** apply (RealSetoid.real_eq_mult_compat (real_mult eps_f Lp) (real_abs h) eps2 (real_abs h)).
                     --- unfold eps_f. apply (real_inv_absorb_comm Lp eps2 HLp).
                     --- apply real_eq_refl.
                  ** apply real_eq_refl.
        + apply real_le_refl. }
    (* ============ Final summary: |D| ≤ eps|h| + eps' (D == T1 + T2 + surplus == eps'). ============ *)
    { apply (real_le_trans
      (real_abs (real_plus (f (g (real_plus x h) Hxh) (Hgpos (real_plus x h) Hxh))
                           (real_opp (real_plus (f gx (Hgpos x Hx))
                                                (real_mult (real_mult (rdf_f gx (Hgpos x Hx)) (rdf_g x Hx)) h)))))
      (real_plus (real_plus (real_abs T1) (real_abs T2)) eps_tri)
      (real_plus (real_mult eps (real_abs h)) eps')).
    - (* |D| ≤ |T1|+|T2|+eps_tri: D == T1+T2 (real_compose_diff_decomp) *)
      apply (real_le_trans
        (real_abs (real_plus (f (g (real_plus x h) Hxh) (Hgpos (real_plus x h) Hxh))
                             (real_opp (real_plus (f gx (Hgpos x Hx))
                                                  (real_mult (real_mult (rdf_f gx (Hgpos x Hx)) (rdf_g x Hx)) h)))))
        (real_abs (real_plus T1 T2))
        (real_plus (real_plus (real_abs T1) (real_abs T2)) eps_tri)).
      + apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
          (real_plus (f (g (real_plus x h) Hxh) (Hgpos (real_plus x h) Hxh))
                     (real_opp (real_plus (f gx (Hgpos x Hx))
                                          (real_mult (real_mult (rdf_f gx (Hgpos x Hx)) (rdf_g x Hx)) h))))
          (real_plus T1 T2)).
        unfold T1, T2.
        apply (real_compose_diff_decomp
                 (f (g (real_plus x h) Hxh) (Hgpos (real_plus x h) Hxh))
                 (f gx (Hgpos x Hx))
                 (rdf_f gx (Hgpos x Hx))
                 (rdf_g x Hx)
                 (g (real_plus x h) Hxh) gx h).
      + apply (real_abs_triangle_le_eps T1 T2 eps_tri Heptr).
    - (* |T1|+|T2|+eps_tri ≤ eps|h| + eps': the T1/T2 bounds + surplus == eps'. *)
      apply (real_le_trans
        (real_plus (real_plus (real_abs T1) (real_abs T2)) eps_tri)
        (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                    (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))) epsq_f)
                               (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2))
                   eps_tri)
        (real_plus (real_mult eps (real_abs h)) eps')).
      + apply (real_le_plus_compat (real_plus (real_abs T1) (real_abs T2))
                                   (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                                     (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))) epsq_f)
                                              (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2))
                                   eps_tri eps_tri).
        * apply (real_le_plus_compat (real_abs T1)
                                     (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                           (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))) epsq_f)
                                     (real_abs T2)
                                     (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2)).
          -- exact HT1b.
          -- exact HT2b.
        * apply real_le_refl.
      + (* Middle == eps|h| + eps': an == restatement (eps2+eps2==eps, surplus==half·eps'+4·(eps'/8)==eps'). *)
        apply RealSetoid.real_eq_le.
        set (Sh1 := real_mult (real_plus eps_f M) epsq_g2).
        set (Sh2 := real_mult eps_f eps_tri_g2).
        apply (real_eq_trans
          (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                      (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))) epsq_f)
                                 (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2))
                     eps_tri)
          (real_plus (real_mult eps (real_abs h))
                     (real_plus (real_plus Sh1 Sh2) (real_plus epsq_f (real_plus marg2 eps_tri))))
          (real_plus (real_mult eps (real_abs h)) eps')).
        { (* Main-term merge: the goal LHS == eps|h| + (Sh1 + (Sh2 + (epsq_f + (marg2 + eps_tri)))). *)
          (* The goal (trans subgoal 1) is already LHS == A0; trans through LHS == MID == A0 directly. *)
          apply (real_eq_trans
            (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                        (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))) epsq_f)
                                   (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2))
                       eps_tri)
            (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult eps2 (real_abs h)))
                       (real_plus (real_plus (real_mult eps_f epsq_g2) (real_mult M epsq_g2))
                                  (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri)))))
            (real_plus (real_mult eps (real_abs h))
                       (real_plus (real_plus Sh1 Sh2) (real_plus epsq_f (real_plus marg2 eps_tri))))).
          - (* LHS == MID: reordering (A,B,C,D,A,F,G,H → A,A,B+F,C,D,G,H). *)
            apply (real_eq_trans
              (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h))
                                                          (real_plus (real_mult eps_f epsq_g2) (real_mult eps_f eps_tri_g2))) epsq_f)
                                     (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult M epsq_g2)) marg2))
                         eps_tri)
              (real_plus (real_plus (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult eps2 (real_abs h)))
                                               (real_plus (real_mult eps_f epsq_g2) (real_mult M epsq_g2)))
                                    (real_mult eps_f eps_tri_g2))
                         (real_plus epsq_f (real_plus marg2 eps_tri)))
              (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult eps2 (real_abs h)))
                         (real_plus (real_plus (real_mult eps_f epsq_g2) (real_mult M epsq_g2))
                                    (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri)))))).
            -- (* LHS == MID1 (left-associative flattening: A+A+B+F+C+D+G+H all left-associated). *)
               apply (real_reorder_main (real_mult eps2 (real_abs h))
                                        (real_mult eps_f epsq_g2)
                                        (real_mult eps_f eps_tri_g2)
                                        epsq_f
                                        (real_mult M epsq_g2)
                                        marg2
                                        eps_tri).
            -- (* MID1 == MID: folding by assoc. *)
               apply (real_reorder_mid (real_mult eps2 (real_abs h))
                                       (real_mult eps_f epsq_g2)
                                       (real_mult eps_f eps_tri_g2)
                                       epsq_f
                                       (real_mult M epsq_g2)
                                       marg2
                                       eps_tri).
          - (* MID == A0: (eps2|h|+eps2|h|) == eps|h| (half_plus_half), B+F == Sh1 (unfold+distrib backwards), C' == Sh2 (unfold). *)
            apply (real_eq_trans
              (real_plus (real_plus (real_mult eps2 (real_abs h)) (real_mult eps2 (real_abs h)))
                         (real_plus (real_plus (real_mult eps_f epsq_g2) (real_mult M epsq_g2))
                                    (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri)))))
              (real_plus (real_mult eps (real_abs h))
                         (real_plus (real_mult (real_plus eps_f M) epsq_g2)
                                    (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri)))))
              (real_plus (real_mult eps (real_abs h))
                         (real_plus (real_plus Sh1 Sh2) (real_plus epsq_f (real_plus marg2 eps_tri))))).
            -- (* MID == middle2: eps2|h|+eps2|h| == eps|h| (half_plus_half) and (B+F) == (eps_f+M)·epsq_g2 (distrib backwards). *)
               apply (RealSetoid.real_eq_plus_compat (real_plus (real_mult eps2 (real_abs h)) (real_mult eps2 (real_abs h)))
                                                     (real_plus (real_plus (real_mult eps_f epsq_g2) (real_mult M epsq_g2))
                                                                (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri))))
                                                     (real_mult eps (real_abs h))
                                                     (real_plus (real_mult (real_plus eps_f M) epsq_g2)
                                                                (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri))))).
               ++ (* eps2|h|+eps2|h| == eps|h|: trans (distrib backwards + half_plus_half). *)
                  apply (real_eq_trans (real_plus (real_mult eps2 (real_abs h)) (real_mult eps2 (real_abs h)))
                                       (real_mult (real_plus eps2 eps2) (real_abs h))
                                       (real_mult eps (real_abs h))).
                  ** apply (real_distrib_r eps2 eps2 (real_abs h)).
                  ** apply (RealSetoid.real_eq_mult_compat (real_plus eps2 eps2) (real_abs h) eps (real_abs h)).
                     --- unfold eps2. apply (real_half_plus_half eps).
                     --- apply real_eq_refl.
               ++ (* (B+F) == (eps_f+M)·epsq_g2: distrib backwards. *)
                  apply (RealSetoid.real_eq_plus_compat (real_plus (real_mult eps_f epsq_g2) (real_mult M epsq_g2))
                                                        (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri)))
                                                        (real_mult (real_plus eps_f M) epsq_g2)
                                                        (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri)))).
                  ** apply (real_distrib_r eps_f M epsq_g2).
                  ** apply real_eq_refl.
            -- (* Middle2 == A0: replacing (eps_f+M)·epsq_g2 == Sh1 and eps_f·eps_tri_g2 == Sh2. *)
               apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))
                                                     (real_plus (real_mult (real_plus eps_f M) epsq_g2)
                                                                (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri))))
                                                     (real_mult eps (real_abs h))
                                                     (real_plus (real_plus Sh1 Sh2) (real_plus epsq_f (real_plus marg2 eps_tri)))).
               ++ apply real_eq_refl.
               ++ (* X+(Y+Z) == (X+Y)+Z: assoc first, then replace the whole term (X+Y) == Sh1+Sh2. *)
                  apply (real_eq_trans
                    (real_plus (real_mult (real_plus eps_f M) epsq_g2)
                               (real_plus (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri))))
                    (real_plus (real_plus (real_mult (real_plus eps_f M) epsq_g2) (real_mult eps_f eps_tri_g2))
                               (real_plus epsq_f (real_plus marg2 eps_tri)))
                    (real_plus (real_plus Sh1 Sh2) (real_plus epsq_f (real_plus marg2 eps_tri)))).
                  ** apply (real_plus_assoc (real_mult (real_plus eps_f M) epsq_g2) (real_mult eps_f eps_tri_g2) (real_plus epsq_f (real_plus marg2 eps_tri))).
                  ** apply (RealSetoid.real_eq_plus_compat (real_plus (real_mult (real_plus eps_f M) epsq_g2) (real_mult eps_f eps_tri_g2))
                                                          (real_plus epsq_f (real_plus marg2 eps_tri))
                                                          (real_plus Sh1 Sh2)
                                                          (real_plus epsq_f (real_plus marg2 eps_tri))).
                     --- (* (eps_f+M)·epsq_g2 + eps_f·eps_tri_g2 == Sh1+Sh2: unfolding at both places. *)
                         apply (real_eq_sym (real_plus Sh1 Sh2) (real_plus (real_mult (real_plus eps_f M) epsq_g2) (real_mult eps_f eps_tri_g2))).
                         apply (RealSetoid.real_eq_plus_compat Sh1 Sh2 (real_mult (real_plus eps_f M) epsq_g2) (real_mult eps_f eps_tri_g2)).
                         ++++ unfold Sh1. apply real_eq_refl.
                         ++++ unfold Sh2. apply real_eq_refl.
                     --- apply real_eq_refl.
        }
        { (* Surplus == eps': Sh1 == half·eps', Sh2 == eps'/8, epsq_f+marg2+eps_tri == 3·(eps'/8), half+1/2 == 1. *)
          apply (real_eq_trans
            (real_plus (real_mult eps (real_abs h))
                       (real_plus (real_plus Sh1 Sh2) (real_plus epsq_f (real_plus marg2 eps_tri))))
            (real_plus (real_mult eps (real_abs h))
                       (real_plus (real_plus (real_mult half eps')
                                             (real_mult half (real_mult half (real_mult half eps'))))
                                  (real_plus (real_mult half (real_mult half (real_mult half eps')))
                                             (real_plus (real_mult half (real_mult half (real_mult half eps')))
                                                        (real_mult half (real_mult half (real_mult half eps')))))))
            (real_plus (real_mult eps (real_abs h)) eps')).
          * apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))
                                                  (real_plus (real_plus Sh1 Sh2) (real_plus epsq_f (real_plus marg2 eps_tri)))
                                                  (real_mult eps (real_abs h))
                                                  (real_plus (real_plus (real_mult half eps')
                                                                        (real_mult half (real_mult half (real_mult half eps'))))
                                                             (real_plus (real_mult half (real_mult half (real_mult half eps')))
                                                                        (real_plus (real_mult half (real_mult half (real_mult half eps')))
                                                                                   (real_mult half (real_mult half (real_mult half eps'))))))).
            -- apply real_eq_refl.
            -- (* Replacing Sh1+Sh2 and epsq_f+marg2+eps_tri: Sh1 == half·eps', Sh2 == eps'/8, epsq_f==eps'/8, marg2==eps'/8, eps_tri==eps'/8. *)

               apply (RealSetoid.real_eq_plus_compat (real_plus Sh1 Sh2)
                                                     (real_plus epsq_f (real_plus marg2 eps_tri))
                                                     (real_plus (real_mult half eps')
                                                                (real_mult half (real_mult half (real_mult half eps'))))
                                                     (real_plus (real_mult half (real_mult half (real_mult half eps')))
                                                                (real_plus (real_mult half (real_mult half (real_mult half eps')))
                                                                           (real_mult half (real_mult half (real_mult half eps')))))).
               ++ (* Sh1+Sh2 == half·eps' + eps'/8 *)
                  apply (RealSetoid.real_eq_plus_compat Sh1 Sh2
                                                        (real_mult half eps')
                                                        (real_mult half (real_mult half (real_mult half eps')))).
                  ** (* Sh1 == half·eps': unfold Sh1 + absorb *)
                     unfold Sh1, epsq_g2.
                     apply (real_eq_trans (real_mult (real_plus eps_f M) (real_mult (real_inv_pos (real_plus eps_f M) HepsfM) (real_mult half eps')))
                                          (real_mult (real_mult (real_plus eps_f M) (real_inv_pos (real_plus eps_f M) HepsfM)) (real_mult half eps'))
                                          (real_mult half eps')).
                     --- apply (real_mult_assoc (real_plus eps_f M) (real_inv_pos (real_plus eps_f M) HepsfM) (real_mult half eps')).
                     --- apply (real_eq_trans (real_mult (real_mult (real_plus eps_f M) (real_inv_pos (real_plus eps_f M) HepsfM)) (real_mult half eps'))
                                              (real_mult real_one (real_mult half eps'))
                                              (real_mult half eps')).
                         ++++ apply (RealSetoid.real_eq_mult_compat (real_mult (real_plus eps_f M) (real_inv_pos (real_plus eps_f M) HepsfM)) (real_mult half eps')
                                                                    real_one (real_mult half eps')).
                              +++++ apply (real_inv_pos_correct (real_plus eps_f M) HepsfM).
                              +++++ apply real_eq_refl.
                         ++++ apply (real_eq_trans (real_mult real_one (real_mult half eps'))
                                                   (real_mult (real_mult half eps') real_one)
                                                   (real_mult half eps')).
                              +++++ apply (real_mult_comm real_one (real_mult half eps')).
                              +++++ apply (real_mult_one (real_mult half eps')).
                  ** (* Sh2 == eps'/8: unfold Sh2 + absorb *)
                     unfold Sh2, eps_tri_g2.
                     apply (real_eq_trans (real_mult eps_f (real_mult (real_inv_pos eps_f Heps_f) (real_mult half (real_mult half (real_mult half eps')))))
                                          (real_mult (real_mult eps_f (real_inv_pos eps_f Heps_f)) (real_mult half (real_mult half (real_mult half eps'))))
                                          (real_mult half (real_mult half (real_mult half eps')))).
                     --- apply (real_mult_assoc eps_f (real_inv_pos eps_f Heps_f) (real_mult half (real_mult half (real_mult half eps')))).
                     --- apply (real_eq_trans (real_mult (real_mult eps_f (real_inv_pos eps_f Heps_f)) (real_mult half (real_mult half (real_mult half eps'))))
                                              (real_mult real_one (real_mult half (real_mult half (real_mult half eps'))))
                                              (real_mult half (real_mult half (real_mult half eps')))).
                         ++++ apply (RealSetoid.real_eq_mult_compat (real_mult eps_f (real_inv_pos eps_f Heps_f)) (real_mult half (real_mult half (real_mult half eps')))
                                                                    real_one (real_mult half (real_mult half (real_mult half eps')))).
                              +++++ apply (real_inv_pos_correct eps_f Heps_f).
                              +++++ apply real_eq_refl.
                         ++++ apply (real_eq_trans (real_mult real_one (real_mult half (real_mult half (real_mult half eps'))))
                                                   (real_mult (real_mult half (real_mult half (real_mult half eps'))) real_one)
                                                   (real_mult half (real_mult half (real_mult half eps')))).
                              +++++ apply (real_mult_comm real_one (real_mult half (real_mult half (real_mult half eps')))).
                              +++++ apply (real_mult_one (real_mult half (real_mult half (real_mult half eps')))).
               ++ (* epsq_f + (marg2+eps_tri) == eps'/8 + (eps'/8 + eps'/8): unfold + refl *)
                  apply (RealSetoid.real_eq_plus_compat epsq_f (real_plus marg2 eps_tri)
                                                            (real_mult half (real_mult half (real_mult half eps')))
                                                            (real_plus (real_mult half (real_mult half (real_mult half eps')))
                                                                       (real_mult half (real_mult half (real_mult half eps'))))).
                  ** unfold epsq_f. apply real_eq_refl.
                  ** apply (RealSetoid.real_eq_plus_compat marg2 eps_tri
                                                        (real_mult half (real_mult half (real_mult half eps')))
                                                        (real_mult half (real_mult half (real_mult half eps')))).
                     --- unfold marg2. apply real_eq_refl.
                     --- unfold eps_tri. apply real_eq_refl.
          * (* half·eps' + 4·(eps'/8) == eps': split by assoc + the 4e8 == half·eps' + half_plus_half chain. *)
            set (e8 := real_mult half (real_mult half (real_mult half eps'))).
            apply (real_eq_trans
              (real_plus (real_mult eps (real_abs h))
                         (real_plus (real_plus (real_mult half eps') e8)
                                    (real_plus e8 (real_plus e8 e8))))
              (real_plus (real_mult eps (real_abs h))
                         (real_plus (real_mult half eps') (real_plus e8 (real_plus e8 (real_plus e8 e8)))))
              (real_plus (real_mult eps (real_abs h)) eps')).
            -- (* (half·eps'+e8) + (e8+(e8+e8)) == half·eps' + (e8+(e8+(e8+e8))): assoc backwards. *)
               apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))
                                                     (real_plus (real_plus (real_mult half eps') e8)
                                                                (real_plus e8 (real_plus e8 e8)))
                                                     (real_mult eps (real_abs h))
                                                     (real_plus (real_mult half eps') (real_plus e8 (real_plus e8 (real_plus e8 e8))))).
               ++ apply real_eq_refl.
               ++ apply (real_eq_sym (real_plus (real_mult half eps') (real_plus e8 (real_plus e8 (real_plus e8 e8))))
                                     (real_plus (real_plus (real_mult half eps') e8) (real_plus e8 (real_plus e8 e8)))).
                  apply (real_plus_assoc (real_mult half eps') e8 (real_plus e8 (real_plus e8 e8))).
            -- (* Middle1 == eps|h|+eps': (half·eps' + 4e8) == half·eps'+half·eps' (merging 4e8) == eps'. *)
               apply (real_eq_trans
                 (real_plus (real_mult eps (real_abs h))
                            (real_plus (real_mult half eps') (real_plus e8 (real_plus e8 (real_plus e8 e8)))))
                 (real_plus (real_mult eps (real_abs h)) (real_plus (real_mult half eps') (real_mult half eps')))
                 (real_plus (real_mult eps (real_abs h)) eps')).
               ++ (* 4e8 == half·eps': (e8+(e8+(e8+e8))) == (e8+e8)+(e8+e8) == half·(half·eps')+half·(half·eps') == half·eps' *)
                  apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))
                                                        (real_plus (real_mult half eps') (real_plus e8 (real_plus e8 (real_plus e8 e8))))
                                                        (real_mult eps (real_abs h))
                                                        (real_plus (real_mult half eps') (real_mult half eps'))).
                  ** apply real_eq_refl.
                  ** apply (RealSetoid.real_eq_plus_compat (real_mult half eps')
                                                           (real_plus e8 (real_plus e8 (real_plus e8 e8)))
                                                           (real_mult half eps') (real_mult half eps')).
                     --- apply real_eq_refl.
                     --- (* 4e8 == half·eps': (e8+(e8+(e8+e8))) == (e8+e8)+(e8+e8) == half·(half·eps')+half·(half·eps') == half·eps' *)
                         apply (real_eq_trans
                           (real_plus e8 (real_plus e8 (real_plus e8 e8)))
                           (real_plus (real_plus e8 e8) (real_plus e8 e8))
                           (real_mult half eps')).
                         ++++ apply (real_plus_assoc e8 e8 (real_plus e8 e8)).
                         ++++ apply (real_eq_trans
                              (real_plus (real_plus e8 e8) (real_plus e8 e8))
                              (real_plus (real_mult half (real_mult half eps')) (real_mult half (real_mult half eps')))
                              (real_mult half eps')).
                              +++++ apply (RealSetoid.real_eq_plus_compat (real_plus e8 e8) (real_plus e8 e8)
                                                                          (real_mult half (real_mult half eps')) (real_mult half (real_mult half eps'))).
                                   ++++++ unfold e8. apply (real_half_plus_half (real_mult half (real_mult half eps'))).
                                   ++++++ unfold e8. apply (real_half_plus_half (real_mult half (real_mult half eps'))).
                              +++++ apply (real_half_plus_half (real_mult half eps')).
               ++ apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))
                                                        (real_plus (real_mult half eps') (real_mult half eps'))
                                                        (real_mult eps (real_abs h)) eps').
                  ** apply real_eq_refl.
                  ** apply (real_half_plus_half eps').
        }
    }
Qed.

(* ============ 6f: generic Real-layer entropy assembly (translated from the Set-layer template) ============
   real_entropy_ent E_A := k_B · log(real_Omega_total_ent E_A)
   real_Omega_total_ent E_A := Omega_A E_A · Omega_B (real_E_B_ent E_A), with real_E_B_ent E_A := E_total − E_A
   Assembly: const/minus/id/mult/compose + real_log_differentiable (df:=1/x).
   Real-layer differences vs the Set layer (where a pure function R->R needs no premises):
   (1) the RealDifferentiable record requires a 0<x domain premise, so Omega_A/Omega_B are defined on the positive domain;
   (2) compose needs the outer wd (Hfwd), hence the honest premise Omega_B_wd (a Set-layer pure function carries wd implicitly);
   (3) compose needs positivity of the inner value (Hgpos), hence the honest premise E_B_pos (E_total−E_A > 0; physically E_A<E_total);
   (4) the outer wd of log = real_log_wd (already available; no new premise needed).
   compose assembly = real_differentiable_compose f g Hf Hg Hgpos Hfwd with all five parameters supplied;
   minus assembly = real_differentiable_minus (fun _ _ => E_total) (fun x Hx => x). *)
Variable Omega_A : forall (E_A : Real), real_lt real_zero E_A -> Real.
Variable Omega_B : forall (E_B : Real), real_lt real_zero E_B -> Real.
Variable dOmega_A : RealDifferentiable Omega_A.
Variable dOmega_B : RealDifferentiable Omega_B.
Variable Omega_A_pos : forall (E_A : Real) (H : real_lt real_zero E_A),
  real_lt real_zero (Omega_A E_A H).
Variable Omega_B_pos : forall (E_B : Real) (H : real_lt real_zero E_B),
  real_lt real_zero (Omega_B E_B H).
Variable Omega_B_wd : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq a b -> real_eq (Omega_B a Ha) (Omega_B b Hb).
Variable E_total : Real.
Variable k_B : Real.
Variable E_B_pos : forall (E_A : Real) (H : real_lt real_zero E_A),
  real_lt real_zero (real_plus E_total (real_opp E_A)).

Definition real_E_B_ent (E_A : Real) (H : real_lt real_zero E_A) : Real :=
  real_plus E_total (real_opp E_A).
Definition real_Omega_total_ent (E_A : Real) (H : real_lt real_zero E_A) : Real :=
  real_mult (Omega_A E_A H) (Omega_B (real_E_B_ent E_A H) (E_B_pos E_A H)).
Lemma real_Omega_total_pos : forall (E_A : Real) (H : real_lt real_zero E_A),
  real_lt real_zero (real_Omega_total_ent E_A H).
Proof.
  intros E_A H. unfold real_Omega_total_ent.
  apply (real_mult_positive (Omega_A E_A H) (Omega_B (real_E_B_ent E_A H) (E_B_pos E_A H))).
  - exact (Omega_A_pos E_A H).
  - exact (Omega_B_pos (real_E_B_ent E_A H) (E_B_pos E_A H)).
Qed.
Definition real_entropy_ent (E_A : Real) (H : real_lt real_zero E_A) : Real :=
  real_mult k_B (real_log (real_Omega_total_ent E_A H) (real_Omega_total_pos E_A H)).

Lemma real_entropy_differentiable : RealDifferentiable real_entropy_ent.
Proof.
  unfold real_entropy_ent.
  (* Outer mult: the k_B constant × (log ∘ real_Omega_total_ent). *)
  apply (real_differentiable_mult (fun (x : Real) (Hx : real_lt real_zero x) => k_B)
         (fun (E_A : Real) (H : real_lt real_zero E_A) =>
            real_log (real_Omega_total_ent E_A H) (real_Omega_total_pos E_A H))).
  - apply (real_differentiable_const k_B).
  - (* log ∘ real_Omega_total_ent: compose real_log real_Omega_total_ent Hlog HOmega_d real_Omega_total_pos real_log_wd *)
    assert (HOmega_d : RealDifferentiable real_Omega_total_ent).
    { unfold real_Omega_total_ent.
      apply (real_differentiable_mult Omega_A
               (fun (E_A : Real) (H : real_lt real_zero E_A) =>
                  Omega_B (real_E_B_ent E_A H) (E_B_pos E_A H))).
      - exact dOmega_A.
      - (* Omega_B ∘ real_E_B_ent: compose dOmega_B HEB_d E_B_pos Omega_B_wd *)
        assert (HEB_d : RealDifferentiable real_E_B_ent).
        { unfold real_E_B_ent.
          apply (real_differentiable_minus (fun (x : Real) (Hx : real_lt real_zero x) => E_total)
                                           (fun (x : Real) (Hx : real_lt real_zero x) => x)).
          - apply (real_differentiable_const E_total).
          - apply real_differentiable_id. }
        apply (real_differentiable_compose Omega_B real_E_B_ent
                 dOmega_B HEB_d E_B_pos Omega_B_wd). }
    apply (real_differentiable_compose real_log real_Omega_total_ent
             (real_log_differentiable real_one real_lt_zero_one)
             HOmega_d real_Omega_total_pos real_log_wd).
Qed.

End EntropyDiffReal.

(* ================================================================
   Closing gap one of paper-4 in the Real layer (gradient_zero → is_truth), item 4.
   Honest interface real_entropy_tangent (a tangent-line inequality for a
   concave function in the Real layer, the first-order condition)
   gives real_gradient_zero_entropy_max: a stationary point (g(x)==0) is the
   global maximum of the entropy,
   then real_gradient_zero_neg_entropy_truth: the is_truth bridge (loss = negative entropy).
   Differences vs the Set layer (same shape as the Set-layer version): the Real
   layer has no real_minus (x−y := x+(−y)), and all real_eq/real_le lemmas are
   explicit (RealSetoid.real_le_id_r is a Module-qualified name).
   This avoids the trichotomy law and integration (the Real layer has no RInt/FTC).
   Discipline: purely constructive / Set layer / zero admissions / zero classical axioms.
   ================================================================ *)
Section RealGapOne.

Variable real_entropy : Real -> Real.
Variable real_entropy_gradient : Real -> Real.

(* The concavity tangent inequality (a Real-layer honest interface, with x−y := x + (−y)):
   f(y) ≤ f(x) + f'(x)·(y−x). *)
Variable real_entropy_tangent : forall x y : Real,
  real_le (real_entropy y)
          (real_plus (real_entropy x)
                     (real_mult (real_entropy_gradient x)
                                (real_plus y (real_opp x)))).

(* Closing gap one (Real layer): a stationary point (g(x)==0) is the global maximum of the entropy.
   Proof: the tangent inequality + g(x)==0 gives f(y) ≤ f(x) + 0·(y−x) == f(x).
   Algebra chain: g(x)·(y−x) == 0·(y−x) (Hg) == (y−x)·0 == 0
   (real_mult_comm + real_mult_zero), so real_plus absorbs it (real_plus_zero). *)
Theorem real_gradient_zero_entropy_max : forall x : Real,
  real_eq (real_entropy_gradient x) real_zero ->
  forall y : Real, real_le (real_entropy y) (real_entropy x).
Proof.
  intros x Hg y.
  (* Tangent inequality: f(y) ≤ f(x) + g(x)·(y−x). *)
  assert (Htangent : real_le (real_entropy y)
                              (real_plus (real_entropy x)
                                         (real_mult (real_entropy_gradient x)
                                                    (real_plus y (real_opp x)))))
    by exact (real_entropy_tangent x y).
  (* Algebra: g(x)·(y−x) == 0·(y−x) == (y−x)·0 == 0. *)
  assert (Hmult : real_eq (real_mult (real_entropy_gradient x) (real_plus y (real_opp x)))
                          real_zero).
  {
    apply (real_eq_trans _ (real_mult real_zero (real_plus y (real_opp x))) _).
    - apply (RealSetoid.real_eq_mult_compat (real_entropy_gradient x) (real_plus y (real_opp x))
                                            real_zero (real_plus y (real_opp x)) Hg (real_eq_refl _)).
    - apply (real_eq_trans _ (real_mult (real_plus y (real_opp x)) real_zero) _).
      + apply real_mult_comm.
      + apply real_mult_zero.
  }
  (* Algebra: f(x) + 0 == f(x). *)
  assert (Hid : real_eq (real_plus (real_entropy x)
                                   (real_mult (real_entropy_gradient x) (real_plus y (real_opp x))))
                        (real_entropy x)).
  {
    apply (real_eq_trans _ (real_plus (real_entropy x) real_zero) _).
    - apply (RealSetoid.real_eq_plus_compat (real_entropy x)
                                            (real_mult (real_entropy_gradient x) (real_plus y (real_opp x)))
                                            (real_entropy x) real_zero
                                            (real_eq_refl _) Hmult).
    - apply real_plus_zero.
  }
  (* Assembly: f(y) ≤ f(x) + g(x)(y−x) and f(x) + g(x)(y−x) == f(x) give f(y) ≤ f(x). *)
  exact (RealSetoid.real_le_id_r (real_entropy y)
                      (real_plus (real_entropy x)
                                 (real_mult (real_entropy_gradient x) (real_plus y (real_opp x))))
                      (real_entropy x)
                      Hid Htangent).
Qed.

(* The is_truth bridge (Real layer): g(x)==0 means (−entropy) has a global minimum at x (loss = negative entropy). *)
Theorem real_gradient_zero_neg_entropy_truth : forall x : Real,
  real_eq (real_entropy_gradient x) real_zero ->
  forall y : Real, real_le (real_opp (real_entropy x)) (real_opp (real_entropy y)).
Proof.
  intros x Hg y.
  (* From gap one: f(y) ≤ f(x) gives −f(x) ≤ −f(y) (real_opp_le_compat, reversing the sign). *)
  apply (real_opp_le_compat (real_entropy y) (real_entropy x)).
  exact (real_gradient_zero_entropy_max x Hg y).
Qed.

End RealGapOne.

(* ================================================================
   Closing gap one of paper-4 in the Real layer: the κ-contraction (positive branch), item 5.
   Interfaces: real_dynamics_gradient_step (the dynamics is a gradient-ascent step) and
   real_strong_concavity (μ-strong concavity, a standard optimization premise, not a classical axiom).
   Outputs: real_dynamics_step_unfold (K0), real_gradient_step_contraction
   (K1a, single step without absolute values), real_gradient_step_abs_contraction (K1c, absolute values),
   real_gradient_iterate_abs_decay (K2, single-step iteration), and
   real_grad_decay_positive_iter (K3, the κ-power decay |g(x_{n+k})| ≤ κ^k·|g(x_n)|).
   Real-layer differences vs the Set layer: no minus (x−y := x+(−y)), no r_pow
   (real_r_pow is built here, with power positivity/nonnegativity lemmas), and no
   le_mult_compat_r (built here with the common factor on the left, via a weak + comm bridge).
   The fully signed version remains blocked by the trichotomy law.
   Discipline: purely constructive / Set layer / zero admissions / zero classical axioms.
   ================================================================ *)
Section RealKappa.

Variable real_entropy_gradient : Real -> Real.
Variable real_dynamics : Real -> Real.
Variable eta : Real.
Variable mu : Real.
Variable mu_pos : real_lt real_zero mu.
Variable eta_pos : real_lt real_zero eta.

(* The dynamics is a gradient-ascent step (honest interface). *)
Variable real_dynamics_gradient_step : forall x : Real,
  real_eq (real_dynamics x)
          (real_plus x (real_mult eta (real_entropy_gradient x))).

(* μ-strong concavity (honest interface, a standard optimization premise): x < y gives μ·(y−x) ≤ g(x) − g(y). *)
Variable real_strong_concavity : forall x y : Real,
  real_lt x y ->
  real_le (real_mult mu (real_plus y (real_opp x)))
          (real_plus (real_entropy_gradient x)
                     (real_opp (real_entropy_gradient y))).

(* ===== K0 single-step unfolding of the dynamics ===== *)
Lemma real_dynamics_step_unfold : forall x : Real,
  real_eq (real_dynamics x)
          (real_plus x (real_mult eta (real_entropy_gradient x))).
Proof. intros x. exact (real_dynamics_gradient_step x). Qed.

(* Tool: minus_plus_cancel_gap: plus (minus a b) b == a (the Real version). *)
Lemma real_minus_plus_cancel : forall a b : Real,
  real_eq (real_plus (real_plus a (real_opp b)) b) a.
Proof.
  intros a b.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) b)) _).
  - apply real_eq_sym. apply (real_plus_assoc a (real_opp b) b).
  - apply (real_eq_trans _ (real_plus a (real_plus b (real_opp b))) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus (real_opp b) b) a (real_plus b (real_opp b))
                                            (real_eq_refl _) (real_plus_comm (real_opp b) b)).
    + apply (real_eq_trans _ (real_plus a real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat a (real_plus b (real_opp b)) a real_zero
                                              (real_eq_refl _) (real_plus_opp b)).
      * apply real_plus_zero.
Qed.

(* ===== K1a positive-branch single-step contraction (without absolute values):
   g(x)>0 gives g(dyn x) ≤ (1−ημ)·g(x).
   Chain: x < dyn (η·g>0); strong concavity gives μ(dyn−x) ≤ g(x)−g(dyn);
       (ημ)·g ≤ g(x)−g(dyn) (substituting dyn−x == η·g);
       rearranging gives g(dyn) ≤ g(x)−(ημ)·g == (1−ημ)·g. *)
Theorem real_gradient_step_contraction : forall x : Real,
  real_lt real_zero (real_entropy_gradient x) ->
  real_le (real_entropy_gradient (real_dynamics x))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_entropy_gradient x)).
Proof.
  intros x Hgx.
  (* x < dynamics x: η·g(x) > 0 ⟹ x < x + η·g(x) *)
  assert (Heta_g : real_lt real_zero (real_mult eta (real_entropy_gradient x)))
    by exact (real_mult_positive eta (real_entropy_gradient x) eta_pos Hgx).
  assert (Hlt : real_lt x (real_dynamics x)).
  {
    apply (RealSetoid.real_lt_id_l x (real_plus x real_zero) (real_dynamics x)
                                   (real_eq_sym _ _ (real_plus_zero x))).
    apply (RealSetoid.real_lt_id_r (real_plus x real_zero) (real_plus x (real_mult eta (real_entropy_gradient x))) (real_dynamics x)
                                   (real_eq_sym _ _ (real_dynamics_step_unfold x))).
    apply (real_lt_plus_compat_le_lt x x real_zero (real_mult eta (real_entropy_gradient x)) (RealSetoid.real_eq_le _ _ (real_eq_refl x)) Heta_g).
  }
  (* Strong concavity: μ(dyn−x) ≤ g(x) − g(dyn). *)
  pose proof (real_strong_concavity x (real_dynamics x) Hlt) as Hsc.
  (* dyn − x == η·g(x) (Hdiff) *)
  assert (Hdiff : real_eq (real_plus (real_dynamics x) (real_opp x))
                          (real_mult eta (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_plus (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)) _).
    - apply (RealSetoid.real_eq_plus_compat (real_dynamics x) (real_opp x)
                                            (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)
                                            (real_dynamics_step_unfold x) (real_eq_refl _)).
    - apply (real_eq_trans _ (real_plus x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))) _).
      + apply real_eq_sym. apply (real_plus_assoc x (real_mult eta (real_entropy_gradient x)) (real_opp x)).
      + apply (real_eq_trans _ (real_plus x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))) _).
        * apply (RealSetoid.real_eq_plus_compat x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))
                                                x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))
                                                (real_eq_refl _) (real_plus_comm _ _)).
        * apply (real_eq_trans _ (real_plus (real_plus x (real_opp x)) (real_mult eta (real_entropy_gradient x))) _).
          -- apply (real_plus_assoc x (real_opp x) (real_mult eta (real_entropy_gradient x))).
          -- apply (real_eq_trans _ (real_plus real_zero (real_mult eta (real_entropy_gradient x))) _).
             --- apply (RealSetoid.real_eq_plus_compat (real_plus x (real_opp x))
                                                      (real_mult eta (real_entropy_gradient x))
                                                      real_zero (real_mult eta (real_entropy_gradient x))
                                                      (real_plus_opp x) (real_eq_refl _)).
             --- apply (real_eq_trans _ (real_plus (real_mult eta (real_entropy_gradient x)) real_zero) _).
                 ---- apply real_plus_comm.
                 ---- apply real_plus_zero.
  }
  (* Substitute Hdiff: μ·(η·g(x)) ≤ g(x) − g(dyn). *)
  assert (Hsc' : real_le (real_mult mu (real_mult eta (real_entropy_gradient x)))
                         (real_plus (real_entropy_gradient x)
                                    (real_opp (real_entropy_gradient (real_dynamics x))))).
  {
    apply (RealSetoid.real_le_id_l (real_mult mu (real_mult eta (real_entropy_gradient x)))
                                   (real_mult mu (real_plus (real_dynamics x) (real_opp x)))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_entropy_gradient (real_dynamics x))))
                                   (RealSetoid.real_eq_mult_compat mu
                                                                    (real_mult eta (real_entropy_gradient x))
                                                                    mu
                                                                    (real_plus (real_dynamics x) (real_opp x))
                                                                    (real_eq_refl _) (real_eq_sym _ _ Hdiff))
                                   Hsc).
  }
  (* Restatement: (ημ)·g(x) ≤ g(x) − g(dyn) (the μ(η·g) == (ημ)·g bridge). *)
  assert (Hmm : real_eq (real_mult mu (real_mult eta (real_entropy_gradient x)))
                        (real_mult (real_mult eta mu) (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_mult mu (real_mult (real_entropy_gradient x) eta)) _).
    - apply (RealSetoid.real_eq_mult_compat mu (real_mult eta (real_entropy_gradient x))
                                            mu (real_mult (real_entropy_gradient x) eta)
                                            (real_eq_refl _) (real_mult_comm eta (real_entropy_gradient x))).
    - apply (real_eq_trans _ (real_mult (real_mult mu (real_entropy_gradient x)) eta) _).
      + apply (real_mult_assoc mu (real_entropy_gradient x) eta).
      + apply (real_eq_trans _ (real_mult (real_mult (real_entropy_gradient x) mu) eta) _).
        * apply (RealSetoid.real_eq_mult_compat (real_mult mu (real_entropy_gradient x)) eta
                                                (real_mult (real_entropy_gradient x) mu) eta
                                                (real_mult_comm mu (real_entropy_gradient x)) (real_eq_refl _)).
        * apply (real_eq_trans _ (real_mult (real_entropy_gradient x) (real_mult mu eta)) _).
          -- apply real_eq_sym. apply (real_mult_assoc (real_entropy_gradient x) mu eta).
          -- apply (real_eq_trans _ (real_mult (real_entropy_gradient x) (real_mult eta mu)) _).
             ++ apply (RealSetoid.real_eq_mult_compat (real_entropy_gradient x) (real_mult mu eta)
                                                      (real_entropy_gradient x) (real_mult eta mu)
                                                      (real_eq_refl _) (real_mult_comm mu eta)).
             ++ apply (real_mult_comm (real_entropy_gradient x) (real_mult eta mu)).
  }
  assert (Hsc'' : real_le (real_mult (real_mult eta mu) (real_entropy_gradient x))
                          (real_plus (real_entropy_gradient x)
                                     (real_opp (real_entropy_gradient (real_dynamics x))))).
  {
    apply (RealSetoid.real_le_id_l (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                   (real_mult mu (real_mult eta (real_entropy_gradient x)))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_entropy_gradient (real_dynamics x))))
                                   (real_eq_sym _ _ Hmm) Hsc').
  }
  (* Rearrangement: from A ≤ B−C derive C ≤ B−A.
     1. Add C: le (A+C) ((B−C)+C) == B gives le (A+C) B.
     2. Add (opp A): le ((A+C)+opp A) (B+opp A) gives le C (B−A). *)
  pose (A := real_mult (real_mult eta mu) (real_entropy_gradient x)).
  pose (B := real_entropy_gradient x).
  pose (C := real_entropy_gradient (real_dynamics x)).
  assert (H1 : real_le (real_plus A C) B).
  {
    apply (RealSetoid.real_le_id_r (real_plus A C) (real_plus (real_plus B (real_opp C)) C) B).
    - exact (real_minus_plus_cancel B C).
    - apply (real_le_plus_compat A (real_plus B (real_opp C)) C C Hsc'' (RealSetoid.real_eq_le _ _ (real_eq_refl C))).
  }
  assert (H2 : real_le (real_plus (real_plus A C) (real_opp A)) (real_plus B (real_opp A))).
  {
    apply (real_le_plus_compat (real_plus A C) B (real_opp A) (real_opp A) H1 (RealSetoid.real_eq_le _ _ (real_eq_refl _))).
  }
  (* Left side simplified: (A+C)+opp A == C. *)
  assert (H3 : real_eq (real_plus (real_plus A C) (real_opp A)) C).
  {
    unfold A, C.
    apply (real_eq_trans _ (real_plus (real_plus (real_entropy_gradient (real_dynamics x))
                                                 (real_mult (real_mult eta mu) (real_entropy_gradient x)))
                                      (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_plus A C) (real_opp A)
                                            (real_plus C A) (real_opp A)
                                            (real_plus_comm A C) (real_eq_refl _)).
    - apply (real_eq_trans _ (real_plus (real_entropy_gradient (real_dynamics x))
                                        (real_plus (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                                   (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))) _).
      + apply real_eq_sym. apply (real_plus_assoc C (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                                    (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))).
      + apply (real_eq_trans _ (real_plus C real_zero) _).
        * apply (RealSetoid.real_eq_plus_compat C (real_plus (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                                             (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                                C real_zero
                                                (real_eq_refl _) (real_plus_opp _)).
        * apply real_plus_zero.
  }
  (* Right side: plus B (opp A) == minus (g x) ((ημ)g) == the target shape. *)
  assert (H4 : real_eq (real_plus B (real_opp A))
                       (real_plus (real_entropy_gradient x)
                                  (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))).
  { unfold A, B. apply real_eq_refl. }
  (* Assembly: le C (B − (ημ)g). *)
  assert (H5 : real_le C (real_plus (real_entropy_gradient x)
                                    (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))).
  {
    apply (RealSetoid.real_le_id_l C (real_plus (real_plus A C) (real_opp A))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                   (real_eq_sym _ _ H3)).
    apply (RealSetoid.real_le_id_r (real_plus (real_plus A C) (real_opp A))
                                   (real_plus B (real_opp A))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                   H4 H2).
  }
  (* Goal: le (g dyn) (mult (minus one (ημ)) (g x));
     needs (1−ημ)·g == g − (ημ)g: distrib + mult_one + opp_mult_r. *)
  assert (H6 : real_eq (real_plus (real_entropy_gradient x)
                                  (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                       (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                  (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_plus (real_mult real_one (real_entropy_gradient x))
                                      (real_mult (real_opp (real_mult eta mu)) (real_entropy_gradient x))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_entropy_gradient x)
                                            (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))
                                            (real_mult real_one (real_entropy_gradient x))
                                            (real_mult (real_opp (real_mult eta mu)) (real_entropy_gradient x))
                                            (real_eq_trans _ (real_mult (real_entropy_gradient x) real_one) _
                                               (real_eq_sym _ _ (real_mult_one (real_entropy_gradient x)))
                                               (real_mult_comm (real_entropy_gradient x) real_one))
                                            (real_opp_mult_r (real_mult eta mu) (real_entropy_gradient x))).
    - apply (real_distrib_r real_one (real_opp (real_mult eta mu)) (real_entropy_gradient x)).
  }
  apply (RealSetoid.real_le_id_r C
                                 (real_plus (real_entropy_gradient x)
                                            (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_entropy_gradient x))
                                 H6 H5).
Qed.

(* ===== K1c absolute-value single-step contraction: two-sided positivity gives |g(dyn)| ≤ (1−ημ)·|g(x)|.
   Proof: K1a gives g(dyn) ≤ (1−ημ)·g(x); two-sided positivity gives |g| = g (real_abs_pos_req),
   so the result is a direct restatement (rewriting abs on both sides). *)
Theorem real_gradient_step_abs_contraction : forall x : Real,
  real_lt real_zero (real_entropy_gradient x) ->
  real_lt real_zero (real_entropy_gradient (real_dynamics x)) ->
  real_le (real_abs (real_entropy_gradient (real_dynamics x)))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_abs (real_entropy_gradient x))).
Proof.
  intros x Hgx Hgdyn.
  (* |g(dyn)| == g(dyn) (real_abs_pos_req) *)
  assert (Habsd : real_eq (real_abs (real_entropy_gradient (real_dynamics x)))
                          (real_entropy_gradient (real_dynamics x)))
    by exact (real_abs_pos_req (real_entropy_gradient (real_dynamics x)) Hgdyn).
  (* |g(x)| == g(x) *)
  assert (Habsx : real_eq (real_abs (real_entropy_gradient x)) (real_entropy_gradient x))
    by exact (real_abs_pos_req (real_entropy_gradient x) Hgx).
  (* Goal restatement: g(dyn) ≤ (1−ημ)·g(x) (K1a). *)
  apply (RealSetoid.real_le_id_l (real_abs (real_entropy_gradient (real_dynamics x)))
                                 (real_entropy_gradient (real_dynamics x))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_abs (real_entropy_gradient x)))
                                 Habsd).
  apply (RealSetoid.real_le_id_r (real_entropy_gradient (real_dynamics x))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_entropy_gradient x))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_abs (real_entropy_gradient x)))
                                 (RealSetoid.real_eq_mult_compat (real_plus real_one (real_opp (real_mult eta mu)))
                                                                 (real_entropy_gradient x)
                                                                 (real_plus real_one (real_opp (real_mult eta mu)))
                                                                 (real_abs (real_entropy_gradient x))
                                                                 (real_eq_refl _) (real_eq_sym _ _ Habsx))
                                 (real_gradient_step_contraction x Hgx)).
Qed.

(* ===== Real-layer power: real_r_pow x n (the Set-layer r_pow transposed to R := Real) ===== *)
Fixpoint real_r_pow (x : Real) (n : nat) : Real :=
  match n with
  | 0%nat => real_one
  | Datatypes.S m => real_mult x (real_r_pow x m)
  end.

(* Power positivity: 0 < x gives 0 < x^n. *)
Lemma real_r_pow_pos : forall x n, real_lt real_zero x -> real_lt real_zero (real_r_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH]; simpl.
  - exact real_lt_zero_one.
  - apply (real_mult_positive x (real_r_pow x m) Hx IH).
Qed.

(* Power nonnegativity: 0 < x gives 0 ≤ x^n. *)
Lemma real_r_pow_nonneg : forall x n, real_lt real_zero x -> real_le real_zero (real_r_pow x n).
Proof.
  intros x n Hx.
  apply (RealSetoid.real_lt_le_iff_req real_zero (real_r_pow x n)). left.
  exact (real_r_pow_pos x n Hx).
Qed.

(* Multiplicative monotonicity (left factor): 0 ≤ a and b ≤ c give a·b ≤ a·c (transposed from the Set-layer le_mult_compat_r). *)
Lemma real_le_mult_compat_r : forall a b c : Real,
  real_le real_zero a -> real_le b c -> real_le (real_mult a b) (real_mult a c).
Proof.
  intros a b c Ha Hbc.
  apply (RealSetoid.real_le_id_l (real_mult a b) (real_mult b a) (real_mult a c)
                                 (real_mult_comm a b)).
  apply (RealSetoid.real_le_id_r (real_mult b a) (real_mult c a) (real_mult a c)
                                 (real_eq_sym _ _ (real_mult_comm a c))).
  exact (real_le_mult_compat_weak b c a Ha Hbc).
Qed.

(* ===== K2 positive-branch single-step iterate contraction: positivity at every step (premise) gives |g(x_{n+1})| ≤ κ·|g(x_n)|.
   κ := 1−ημ; proof: K1c instantiated at x := iterate dynamics n E_A. *)
Theorem real_gradient_iterate_abs_decay : forall (E_A : Real) (n : nat),
  (forall k : nat, NatLe k (Datatypes.S n) -> real_lt real_zero (real_entropy_gradient (iterate real_dynamics k E_A))) ->
  real_le (real_abs (real_entropy_gradient (iterate real_dynamics (Datatypes.S n) E_A)))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
Proof.
  intros E_A n Hall.
  (* x := iterate dynamics n E_A; premises g(x) > 0 and g(dyn x) > 0. *)
  assert (Hgn : real_lt real_zero (real_entropy_gradient (iterate real_dynamics n E_A))).
  { apply Hall. apply NatLe_lift. lia. }
  assert (Hgn1 : real_lt real_zero (real_entropy_gradient (iterate real_dynamics (Datatypes.S n) E_A))).
  { apply Hall. apply NatLe_lift. lia. }
  (* dynamics (iterate dynamics n E_A) and iterate (S n) E_A are definitionally equal (iterate is a Fixpoint). *)
  exact (real_gradient_step_abs_contraction (iterate real_dynamics n E_A) Hgn Hgn1).
Qed.

(* ===== K3 positive-branch κ-power decay: |g(x_{n+k})| ≤ κ^k·|g(x_n)| (by induction, in the shape of grad_decay_iter).
   κ := 1−ημ; premises: κ > 0 (1−ημ > 0) + the whole orbit positive (j ≤ n+k). *)
Theorem real_grad_decay_positive_iter : forall (E_A : Real) (n k : nat),
  real_lt real_zero (real_plus real_one (real_opp (real_mult eta mu))) ->
  (forall j : nat, NatLe j (n + k) -> real_lt real_zero (real_entropy_gradient (iterate real_dynamics j E_A))) ->
  real_le (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
          (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                     (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
Proof.
  intros E_A n k Hkpos Hall.
  induction k as [| k IH]; simpl.
  - (* k = 0: |g(x_n)| ≤ 1·|g(x_n)| *)
    rewrite (Nat.add_0_r n).
    apply (RealSetoid.real_le_id_r _ (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))) _).
    + apply (real_eq_trans _ (real_mult (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))) real_one) _).
      * apply real_eq_sym. apply (real_mult_one (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
      * apply real_mult_comm.
    + apply RealSetoid.real_eq_le. apply real_eq_refl.
  - (* k = S k': |g(x_{n+S k'})| ≤ κ·|g(x_{n+k'})| ≤ κ·(κ^{k'}·|g(x_n)|) == κ^{S k'}·|g(x_n)| *)
    apply (real_le_trans _ (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                      (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))) _).
    + (* Single step: K2 at (n+k), with the premise j ≤ S(n+k) supplied by Hall (n + S k' == S(n+k)). *)
      rewrite (Nat.add_succ_r n k).
      apply (real_gradient_iterate_abs_decay E_A (n + k)).
      intros j Hj. apply NatLe_drop in Hj. apply Hall. apply NatLe_lift. lia.
    + (* Induction step: κ·(κ^{k'}·|g(x_n)|) == κ^{S k'}·|g(x_n)| (mult_assoc + a comm restatement). *)
      assert (IH' : real_le (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
                            (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                       (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))).
      { apply IH. intros j Hj. apply NatLe_drop in Hj. apply Hall. apply NatLe_lift. lia. }
      apply (RealSetoid.real_le_id_r (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A))))
                                     (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                           (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))))
                                     (real_mult (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                           (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k))
                                                (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                     (real_mult_assoc (real_plus real_one (real_opp (real_mult eta mu)))
                                                      (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                      (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                     (real_le_mult_compat_r (real_plus real_one (real_opp (real_mult eta mu)))
                                                           (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
                                                           (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                                      (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                                           (RealSetoid.real_lt_le_iff_req _ _ (inl Hkpos))
                                                           IH')).
Qed.

End RealKappa.
Section RealKappaSignReal.

(* Honest-interface Variables in the same style as RealKappa. *)
Variable real_entropy_gradient : Real -> Real.
Variable real_dynamics : Real -> Real.
Variable eta : Real.
Variable mu : Real.
Variable mu_pos : real_lt real_zero mu.
Variable eta_pos : real_lt real_zero eta.

Variable real_dynamics_gradient_step : forall x : Real,
  real_eq (real_dynamics x)
          (real_plus x (real_mult eta (real_entropy_gradient x))).

Variable real_strong_concavity : forall x y : Real,
  real_lt x y ->
  real_le (real_mult mu (real_plus y (real_opp x)))
          (real_plus (real_entropy_gradient x)
                     (real_opp (real_entropy_gradient y))).

(* New: Real-layer Lipschitz (same shape as the Set-layer ConvergenceCauchy gradient_lipschitz). *)
Variable L : Real.
Variable real_gradient_lipschitz : forall x y : Real,
  real_le (real_abs (real_plus (real_entropy_gradient x) (real_opp (real_entropy_gradient y))))
          (real_mult L (real_abs (real_plus x (real_opp y)))).

(* New: the sign-preserving step-size condition η < 1/L (mathematically necessary). *)
Variable eta_lt_inv_L : real_lt (real_mult L eta) real_one.

(* ===== (1) real_abs_neg_req: a < 0 gives |a| == −a (pointwise Qabs_neg, mirroring real_abs_pos_req) ===== *)
Lemma real_abs_neg_req : forall a : Real,
  real_lt a real_zero -> real_eq (real_abs a) (real_opp a).
Proof.
  intros a Ha.
  destruct Ha as [eps0 [Heps0 [N0 HN0]]].
  unfold real_eq.
  intros eps Heps.
  exists N0.
  intros n Hn.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj a n)).
  (* Goal: QltT eps (Qabs (Qabs (a_n) − (−a_n))); the tail a_n < −eps0 < 0 gives |a_n| == −a_n, so the difference == 0. *)
  assert (Hneg : Qlt (projT1 a n) 0).
  {
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hraw : Qlt eps0 (projT1 real_zero n - projT1 a n)).
    { apply QltT_to_Qlt. exact (HN0 n Hn). }
    rewrite Hz in Hraw.
    (* Hraw : eps0 < 0 − a_n == −a_n *)
    assert (Hopp : Qlt eps0 (- (projT1 a n))).
    { apply (Qlt_le_trans _ (projT1 real_zero n - projT1 a n) _).
      - exact Hraw.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hz. ring. }
    (* eps0 < −a_n ⟹ a_n < −eps0 (Qopp_lt_compat: x<y → −y<−x) *)
    assert (Han : Qlt (projT1 a n) (- eps0)).
    {
      apply (Qle_lt_trans (projT1 a n) (- (- (projT1 a n))) (- eps0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - apply (Qopp_lt_compat eps0 (- (projT1 a n))). exact Hopp.
    }
    (* a_n < −eps0 < 0 *)
    apply (Qlt_trans _ (- eps0) _).
    - exact Han.
    - apply (Qlt_le_trans (- eps0) (- 0) 0).
      + apply (Qopp_lt_compat 0 eps0). apply QltT_to_Qlt. exact Heps0.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  }
  assert (Habs : Qabs (projT1 a n) == - (projT1 a n)).
  { apply Qabs_neg. apply (Qlt_le_weak (projT1 a n) 0). exact Hneg. }
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    rewrite Habs.
    transitivity (Qabs 0).
    + apply Qabs_wd. unfold Qminus. ring.
    + apply (Qabs_pos 0). apply Qle_refl.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* ===== (2) real_lipschitz_diff_bound: |g(dyn)−g(x)| ≤ (L·η)·|g(x)| =====
   Chain: Lipschitz (dyn, x) gives |g(dyn)−g(x)| ≤ L·|dyn−x|;
       dyn−x == η·g(x) (Hdynx, mirroring K1a's Hdiff);
       |dyn−x| == |η·g| == |η|·|g| (real_abs_mult_req) == η·|g| (|η|==η, eta_pos);
       L·(η·|g|) == (L·η)·|g| (real_mult_assoc). *)
Lemma real_lipschitz_diff_bound : forall x : Real,
  real_le (real_abs (real_plus (real_entropy_gradient (real_dynamics x))
                               (real_opp (real_entropy_gradient x))))
          (real_mult (real_mult L eta) (real_abs (real_entropy_gradient x))).
Proof.
  intros x.
  apply (RealSetoid.real_le_id_r (real_abs (real_plus (real_entropy_gradient (real_dynamics x))
                                                      (real_opp (real_entropy_gradient x))))
                                 (real_mult L (real_abs (real_plus (real_dynamics x) (real_opp x))))
                                 (real_mult (real_mult L eta) (real_abs (real_entropy_gradient x)))).
  - (* L·|dyn−x| == (L·η)·|g(x)|: dyn−x == η·g; |η·g| == |η|·|g| == η·|g|; L·(η·|g|) == (Lη)·|g| *)
    (* First prove dyn−x == η·g(x) (Hdynx, a copy of K1a's Hdiff). *)
    assert (Hdynx : real_eq (real_plus (real_dynamics x) (real_opp x))
                            (real_mult eta (real_entropy_gradient x))).
    {
      apply (real_eq_trans _ (real_plus (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)) _).
      - apply (RealSetoid.real_eq_plus_compat (real_dynamics x) (real_opp x)
                                              (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)
                                              (real_dynamics_gradient_step x) (real_eq_refl _)).
      - apply (real_eq_trans _ (real_plus x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))) _).
        + apply real_eq_sym. apply (real_plus_assoc x (real_mult eta (real_entropy_gradient x)) (real_opp x)).
        + apply (real_eq_trans _ (real_plus x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))) _).
          * apply (RealSetoid.real_eq_plus_compat x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))
                                                  x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))
                                                  (real_eq_refl _) (real_plus_comm _ _)).
          * apply (real_eq_trans _ (real_plus (real_plus x (real_opp x)) (real_mult eta (real_entropy_gradient x))) _).
            -- apply (real_plus_assoc x (real_opp x) (real_mult eta (real_entropy_gradient x))).
            -- apply (real_eq_trans _ (real_plus real_zero (real_mult eta (real_entropy_gradient x))) _).
               --- apply (RealSetoid.real_eq_plus_compat (real_plus x (real_opp x))
                                                         (real_mult eta (real_entropy_gradient x))
                                                         real_zero (real_mult eta (real_entropy_gradient x))
                                                         (real_plus_opp x) (real_eq_refl _)).
               --- apply (real_eq_trans _ (real_plus (real_mult eta (real_entropy_gradient x)) real_zero) _).
                   ---- apply real_plus_comm.
                   ---- apply real_plus_zero.
    }
    apply (real_eq_trans _ (real_mult L (real_mult (real_abs eta) (real_abs (real_entropy_gradient x)))) _).
    + apply (RealSetoid.real_eq_mult_compat L (real_abs (real_plus (real_dynamics x) (real_opp x)))
                                             L (real_mult (real_abs eta) (real_abs (real_entropy_gradient x)))
                                             (real_eq_refl _)
                                             (real_eq_trans _ (real_abs (real_mult eta (real_entropy_gradient x))) _
                                                 (RealSetoid.real_eq_abs_compat (real_plus (real_dynamics x) (real_opp x))
                                                                     (real_mult eta (real_entropy_gradient x))
                                                                     Hdynx)
                                                 (real_abs_mult_req eta (real_entropy_gradient x)))).
    + apply (real_eq_trans _ (real_mult L (real_mult eta (real_abs (real_entropy_gradient x)))) _).
      * apply (RealSetoid.real_eq_mult_compat L (real_mult (real_abs eta) (real_abs (real_entropy_gradient x)))
                                               L (real_mult eta (real_abs (real_entropy_gradient x)))
                                               (real_eq_refl _)
                                               (RealSetoid.real_eq_mult_compat (real_abs eta) (real_abs (real_entropy_gradient x))
                                                                               eta (real_abs (real_entropy_gradient x))
                                                                               (real_abs_pos_req eta eta_pos) (real_eq_refl _))).
      * apply (real_mult_assoc L eta (real_abs (real_entropy_gradient x))).
  - apply (real_gradient_lipschitz (real_dynamics x) x).
Qed.

(* ===== (3) Sign-preserving positive branch: g(x) > 0 and η<1/L give g(dyn) > 0 =====
   Per eps: given epsx (a positive lower-bound witness for g(x)) and epsL (a positive lower-bound
   witness for 1−Lη): g(dyn)_n ≥ (1−(Lη)_n)·(gx)_n − c ≥ epsL·epsx − c; taking c := epsL·epsx/2
   gives g(dyn)_n > epsL·epsx/2 > 0.  Witness eps0 := epsL·epsx/2. *)
Theorem real_sign_preservation_pos : forall x : Real,
  real_lt real_zero (real_entropy_gradient x) ->
  real_lt real_zero (real_entropy_gradient (real_dynamics x)).
Proof.
  intros x Hx.
  destruct Hx as [epsx [Hepsx [Nx HNx]]].
  destruct eta_lt_inv_L as [epsL [HepsL [NL HNL]]].
  (* Witness and margin c := (epsL·epsx)/2. *)
  set (c := (epsL * epsx) / 2).
  assert (Hc : QltT 0 c).
  {
    unfold c. apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - change (Qlt 0 2). compute. reflexivity.
    - apply (Qmult_lt_0_compat epsL epsx).
      + apply QltT_to_Qlt. exact HepsL.
      + apply QltT_to_Qlt. exact Hepsx.
  }
  (* Pointwise Lipschitz extraction: |g(dyn)−g(x)|_n ≤ ((Lη)|g|)_n + c (real_abs_le_extract). *)
  destruct (real_abs_le_extract (real_plus (real_entropy_gradient (real_dynamics x))
                                           (real_opp (real_entropy_gradient x)))
                                (real_mult (real_mult L eta) (real_abs (real_entropy_gradient x)))
                                c Hc (real_lipschitz_diff_bound x)) as [Nc HNc].
  set (N := Nat.max (Nat.max Nx NL) Nc).
  exists c. split.
  - exact Hc.
  - exists N. intros n Hn.
    apply NatLe_drop in Hn.
    apply Qlt_to_QltT.
    (* Goal: QltT c ((g dyn)_n − 0) == (g dyn)_n > c. *)
    assert (Hn1 : (Nx <= n)%nat) by (unfold N in Hn; lia).
    assert (Hn2 : (NL <= n)%nat) by (unfold N in Hn; lia).
    assert (Hn3 : (Nc <= n)%nat) by (unfold N in Hn; lia).
    (* Pointwise facts: epsx < (gx)_n (HNx); epsL < 1 − (Lη)_n (HNL); |(gdyn−gx)_n| ≤ ((Lη)|g|)_n + c (HNc). *)
    assert (Hgx : Qlt epsx (projT1 (real_entropy_gradient x) n)).
    {
      assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hraw : Qlt epsx (projT1 (real_entropy_gradient x) n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNx n (NatLe_lift _ _ Hn1)). }
      rewrite Hz in Hraw.
      apply (Qlt_le_trans _ (projT1 (real_entropy_gradient x) n - 0) _).
      - exact Hraw.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    }
    (* 1 − (Lη)_n > epsL: HNL : QltT epsL (1_n − (Lη)_n) *)
    assert (Hone : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    assert (HLeta : Qlt epsL (1 - (projT1 L n * projT1 eta n))).
    {
      assert (Hraw : Qlt epsL (projT1 real_one n - projT1 (real_mult L eta) n)).
      { apply QltT_to_Qlt. exact (HNL n (NatLe_lift _ _ Hn2)). }
      rewrite Hone in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj L eta n)) in Hraw.
      exact Hraw.
    }
    (* 1 − (Lη)_n > 0 (from > epsL > 0). *)
    assert (H1m : Qlt 0 (1 - (projT1 L n * projT1 eta n))).
    { apply (Qlt_trans _ epsL _). - apply QltT_to_Qlt. exact HepsL. - exact HLeta. }
    (* |(gdyn−gx)_n| ≤ ((Lη)_n)·|(gx)_n| + c (HNc expanded; the Qplus shape (gdyn)_n + −(gx)_n). *)
    assert (Hbd : Qle (Qabs (projT1 (real_entropy_gradient (real_dynamics x)) n
                             + - projT1 (real_entropy_gradient x) n))
                      ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c)).
    {
      assert (Hraw : Qle (Qabs (projT1 (real_plus (real_entropy_gradient (real_dynamics x))
                                                  (real_opp (real_entropy_gradient x))) n))
                         (projT1 (real_mult (real_mult L eta) (real_abs (real_entropy_gradient x))) n + c)).
      { exact (QleT'_to_Qle _ _ (HNc n (NatLe_lift _ _ Hn3))). }
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_entropy_gradient (real_dynamics x)) (real_opp (real_entropy_gradient x)) n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_entropy_gradient x) n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult L eta) (real_abs (real_entropy_gradient x)) n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj L eta n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_entropy_gradient x) n)) in Hraw.
      exact Hraw.
    }
    (* Qabs lower bound: |d| ≤ m gives d ≥ −m; d := (gdyn)_n + −(gx)_n (the Qplus shape). *)
    assert (Hlo : Qle (- ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c))
                      (projT1 (real_entropy_gradient (real_dynamics x)) n
                       + - projT1 (real_entropy_gradient x) n)).
    {
      apply (Qle_trans _ (- (Qabs (projT1 (real_entropy_gradient (real_dynamics x)) n
                                   + - projT1 (real_entropy_gradient x) n))) _).
      - (* −m ≤ −|d|: Qopp_le_compat |d| m, from Hbd : |d| ≤ m. *)
        apply (Qopp_le_compat (Qabs (projT1 (real_entropy_gradient (real_dynamics x)) n
                                    + - projT1 (real_entropy_gradient x) n))
                              ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c)).
        exact Hbd.
      - (* −|d| ≤ d: branch on Qlt_le_dec (|d| == −d when d<0; == d when d≥0). *)
        destruct (Qlt_le_dec (projT1 (real_entropy_gradient (real_dynamics x)) n
                              + - projT1 (real_entropy_gradient x) n) 0) as [Hdlt | Hdge].
        + { apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
            rewrite (Qabs_neg _ (Qlt_le_weak _ _ Hdlt)). ring. }
        + { apply (Qle_trans _ 0 _).
            { apply (Qle_trans _ (- (projT1 (real_entropy_gradient (real_dynamics x)) n
                                      + - projT1 (real_entropy_gradient x) n)) _).
              { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (Qabs_pos _ Hdge). ring. }
              { apply (Qle_trans _ (- 0) _).
                { apply (Qopp_le_compat 0 (projT1 (real_entropy_gradient (real_dynamics x)) n
                                           + - projT1 (real_entropy_gradient x) n)). exact Hdge. }
                { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. } }
            }
            { exact Hdge. } }
    }
    (* Assembly: c < MID ≤ (gdyn)_n, with MID := (gx)_n − ((Lη)_n·|(gx)_n| + c). *)
    assert (Htarget : Qlt c (projT1 (real_entropy_gradient (real_dynamics x)) n)).
    {
      set (MID := projT1 (real_entropy_gradient x) n
                  - ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c)).
      apply (Qlt_le_trans c MID (projT1 (real_entropy_gradient (real_dynamics x)) n)).
      - (* c < MID: |gx|==gx gives MID == (1−Lη)(gx) − c; and (1−Lη)(gx) > epsL·epsx == 2c. *)
        unfold MID.
        assert (Hgxpos : Qlt 0 (projT1 (real_entropy_gradient x) n)).
        { apply (Qlt_trans _ epsx _). - apply QltT_to_Qlt. exact Hepsx. - exact Hgx. }
        assert (Habs_eq : Qabs (projT1 (real_entropy_gradient x) n) == projT1 (real_entropy_gradient x) n).
        { apply Qabs_pos. apply (Qlt_le_weak 0 (projT1 (real_entropy_gradient x) n)). exact Hgxpos. }
        (* (1−(Lη)_n)·(gx)_n > epsL·epsx: Qmult_lt_compat_nonneg (conjunctive premises, conclusion x·z < y·t). *)
        assert (Hprod : Qlt (epsL * epsx) ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n))).
        {
          apply (Qmult_lt_compat_nonneg epsL (1 - (projT1 L n * projT1 eta n))
                                        epsx (projT1 (real_entropy_gradient x) n)).
          + split.
            * apply (Qlt_le_weak 0 epsL). apply QltT_to_Qlt. exact HepsL.
            * exact HLeta.
          + split.
            * apply (Qlt_le_weak 0 epsx). apply QltT_to_Qlt. exact Hepsx.
            * exact Hgx.
        }
        (* epsL·epsx == 2c ⟹ 2c < (1−Lη)(gx)_n ⟹ c < (1−Lη)(gx)_n − c == MID *)
        assert (Htwo : epsL * epsx == 2 * c).
        { unfold c. field. }
        assert (H2c : Qlt (2 * c) ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n))).
        { rewrite <- Htwo. exact Hprod. }
        (* Qlt c MID: Qlt c (X−c) (2c<X gives c<X−c) + Qle (X−c) MID (restating Habs_eq). *)
        apply (Qlt_le_trans c ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n) - c) MID).
        + (* Qlt c (X − c) *)
          apply (Qle_lt_trans c ((2 * c) + (- c))
                                ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n) - c)).
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          * apply (Qplus_lt_le_compat (2 * c) ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n))
                                          (- c) (- c)).
            { exact H2c. }
            { apply Qle_refl. }
        + (* Qle (X − c) MID: unfold MID + setoid_rewrite Habs_eq + ring *)
          apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold MID. setoid_rewrite Habs_eq. ring.
      - (* MID ≤ (gdyn)_n: rearranging Hlo (adding (gx)_n). *)
        unfold MID.
        apply (Qle_trans _ ((projT1 (real_entropy_gradient x) n)
                            + ((projT1 (real_entropy_gradient (real_dynamics x)) n
                                + - projT1 (real_entropy_gradient x) n))) _).
        + apply (Qplus_le_compat (projT1 (real_entropy_gradient x) n) (projT1 (real_entropy_gradient x) n)
                                 (- ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c))
                                 (projT1 (real_entropy_gradient (real_dynamics x)) n
                                  + - projT1 (real_entropy_gradient x) n)).
          * apply Qle_refl.
          * exact Hlo.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    }
    (* Goal: Qlt c ((g dyn)_n − projT1 real_zero n) (in the checking environment `<` resolves to the std Qlt) —
       first prove Hq at the Qlt layer, then exact. *)
    assert (Hq : Qlt c (projT1 (real_entropy_gradient (real_dynamics x)) n - projT1 real_zero n)).
    {
      apply (Qlt_le_trans c (projT1 (real_entropy_gradient (real_dynamics x)) n)
                           (projT1 (real_entropy_gradient (real_dynamics x)) n - projT1 real_zero n)).
      - exact Htarget.
      - apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        rewrite Hz. ring.
    }
    exact Hq.
Qed.
(* Sign-preserving negative branch: g(x) < 0 and η<1/L give g(dyn) < 0 (by symmetry, per eps).
   Derivation: g(dyn)_n ≤ (gx)_n + ((Lη)_n·|(gx)_n| + c) (the Hhi upper bound)
         ≤ (1−(Lη)_n)(gx)_n + c (|gx|==−gx)
         < (1−(Lη)_n)(−epsx) + c ≤ −epsL·epsx + c == −c < 0.
   Witness eps0 := c (QltT c (0 − (gdyn)_n)). *)
Theorem real_sign_preservation_neg : forall x : Real,
  real_lt (real_entropy_gradient x) real_zero ->
  real_lt (real_entropy_gradient (real_dynamics x)) real_zero.
Proof.
  intros x Hx.
  destruct Hx as [epsx [Hepsx [Nx HNx]]].
  destruct eta_lt_inv_L as [epsL [HepsL [NL HNL]]].
  set (c := (epsL * epsx) / 2).
  assert (Hc : QltT 0 c).
  {
    unfold c. apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - change (Qlt 0 2). compute. reflexivity.
    - apply (Qmult_lt_0_compat epsL epsx).
      + apply QltT_to_Qlt. exact HepsL.
      + apply QltT_to_Qlt. exact Hepsx.
  }
  destruct (real_abs_le_extract (real_plus (real_entropy_gradient (real_dynamics x))
                                           (real_opp (real_entropy_gradient x)))
                                (real_mult (real_mult L eta) (real_abs (real_entropy_gradient x)))
                                c Hc (real_lipschitz_diff_bound x)) as [Nc HNc].
  set (N := Nat.max (Nat.max Nx NL) Nc).
  exists c. split.
  - exact Hc.
  - exists N. intros n Hn.
    apply NatLe_drop in Hn.
    (* Goal: Qlt c (0 − (gdyn)_n) (in the checking environment `<` is the std Qlt). *)
    assert (Hn1 : (Nx <= n)%nat) by (unfold N in Hn; lia).
    assert (Hn2 : (NL <= n)%nat) by (unfold N in Hn; lia).
    assert (Hn3 : (Nc <= n)%nat) by (unfold N in Hn; lia).
    (* Pointwise facts: 0 − (gx)_n > epsx (HNx gives (gx)_n < −epsx); 1 − (Lη)_n > epsL; |d| ≤ m + c (HNc). *)
    assert (Hgx : Qlt (projT1 (real_entropy_gradient x) n) (- epsx)).
    {
      assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hraw : Qlt epsx (projT1 real_zero n - projT1 (real_entropy_gradient x) n)).
      { apply QltT_to_Qlt. exact (HNx n (NatLe_lift _ _ Hn1)). }
      rewrite Hz in Hraw.
      (* epsx < 0 − (gx)_n == −(gx)_n ⟹ (gx)_n < −epsx (Qopp_lt_compat) *)
      apply (Qle_lt_trans (projT1 (real_entropy_gradient x) n) (- (- (projT1 (real_entropy_gradient x) n))) (- epsx)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - apply (Qopp_lt_compat epsx (- (projT1 (real_entropy_gradient x) n))).
        apply (Qlt_le_trans _ (projT1 real_zero n - projT1 (real_entropy_gradient x) n) _).
        + exact Hraw.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hz. ring.
    }
    assert (Hone : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    assert (HLeta : Qlt epsL (1 - (projT1 L n * projT1 eta n))).
    {
      assert (Hraw : Qlt epsL (projT1 real_one n - projT1 (real_mult L eta) n)).
      { apply QltT_to_Qlt. exact (HNL n (NatLe_lift _ _ Hn2)). }
      rewrite Hone in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj L eta n)) in Hraw.
      exact Hraw.
    }
    assert (H1m : Qlt 0 (1 - (projT1 L n * projT1 eta n))).
    { apply (Qlt_trans _ epsL _). - apply QltT_to_Qlt. exact HepsL. - exact HLeta. }
    (* |(gdyn)+−(gx)_n| ≤ ((Lη)_n)·|(gx)_n| + c (HNc expanded, the Qplus shape). *)
    assert (Hbd : Qle (Qabs (projT1 (real_entropy_gradient (real_dynamics x)) n
                             + - projT1 (real_entropy_gradient x) n))
                      ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c)).
    {
      assert (Hraw : Qle (Qabs (projT1 (real_plus (real_entropy_gradient (real_dynamics x))
                                                  (real_opp (real_entropy_gradient x))) n))
                         (projT1 (real_mult (real_mult L eta) (real_abs (real_entropy_gradient x))) n + c)).
      { exact (QleT'_to_Qle _ _ (HNc n (NatLe_lift _ _ Hn3))). }
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_entropy_gradient (real_dynamics x)) (real_opp (real_entropy_gradient x)) n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_entropy_gradient x) n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult L eta) (real_abs (real_entropy_gradient x)) n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj L eta n)) in Hraw.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_entropy_gradient x) n)) in Hraw.
      exact Hraw.
    }
    (* Qabs upper bound: |d| ≤ m gives d ≤ m (q_le_abs: d ≤ |d| ≤ m). *)
    assert (Hhi : Qle (projT1 (real_entropy_gradient (real_dynamics x)) n
                       + - projT1 (real_entropy_gradient x) n)
                      ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c)).
    {
      apply (Qle_trans _ (Qabs (projT1 (real_entropy_gradient (real_dynamics x)) n
                               + - projT1 (real_entropy_gradient x) n)) _).
      - exact (QleT'_to_Qle _ _ (q_le_abs (projT1 (real_entropy_gradient (real_dynamics x)) n
                         + - projT1 (real_entropy_gradient x) n))).
      - exact Hbd.
    }
    (* Assembly: 0 − (gdyn)_n > c follows from (gdyn)_n < −c; the chain (gdyn)_n ≤ (gx)_n + m ≤ (1−Lη)(gx)_n + c < −c. *)
    assert (Htarget : Qlt (projT1 (real_entropy_gradient (real_dynamics x)) n) (- c)).
    {
      (* (gx)_n < 0 (from < −epsx < 0) and |(gx)_n| == −(gx)_n. *)
      assert (Hgxneg : Qlt (projT1 (real_entropy_gradient x) n) 0).
      { apply (Qlt_trans _ (- epsx) _). - exact Hgx. - apply (Qopp_lt_compat 0 epsx). apply QltT_to_Qlt. exact Hepsx. }
      assert (Habs_eq : Qabs (projT1 (real_entropy_gradient x) n) == - (projT1 (real_entropy_gradient x) n)).
      { apply Qabs_neg. apply (Qlt_le_weak (projT1 (real_entropy_gradient x) n) 0). exact Hgxneg. }
      (* (1−Lη)_n·(gx)_n < epsL·(−epsx): the chain (1−Lη)(gx) < (1−Lη)(−epsx) (Hgx times a positive) + (1−Lη)(−epsx) ≤ epsL·(−epsx) (sign reversal). *)
      assert (Hprod : Qlt ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n))
                          (epsL * (- epsx))).
      {
        (* Chain: (1−Lη)(gx)_n ≤ (gx)_n(1−Lη) (a Qle restatement)
              < (−epsx)(1−Lη) (Qmult_lt_compat_r H1m Hgx)
              ≤ (1−Lη)(−epsx) (a Qle restatement)
              < −epsL·epsx (sign reversal: (1−Lη)>epsL times −epsx<0 reverses)
              == epsL·(−epsx) (restated). *)
        apply (Qle_lt_trans ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n))
                            ((projT1 (real_entropy_gradient x) n) * (1 - (projT1 L n * projT1 eta n)))
                            (epsL * (- epsx))).
        - apply QleT'_to_Qle. apply (qeq_le ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n))
                        ((projT1 (real_entropy_gradient x) n) * (1 - (projT1 L n * projT1 eta n)))).
        apply qeq_imp_qeqT.
          ring.
        - apply (Qlt_le_trans ((projT1 (real_entropy_gradient x) n) * (1 - (projT1 L n * projT1 eta n)))
                              ((- epsx) * (1 - (projT1 L n * projT1 eta n)))
                              (epsL * (- epsx))).
          + apply (Qmult_lt_compat_r (projT1 (real_entropy_gradient x) n) (- epsx)
                                     (1 - (projT1 L n * projT1 eta n))).
            * exact H1m.
            * exact Hgx.
          + (* Qle (−epsx)(1−Lη) (epsL·(−epsx)): the Qle_trans chain (restatement + sign reversal + restatement). *)
            apply (Qle_trans _ ((1 - (projT1 L n * projT1 eta n)) * (- epsx)) _).
            * (* (−epsx)(1−Lη) ≤ (1−Lη)(−epsx): a restatement. *)
              apply QleT'_to_Qle. apply (qeq_le ((- epsx) * (1 - (projT1 L n * projT1 eta n)))
                            ((1 - (projT1 L n * projT1 eta n)) * (- epsx))).
              apply qeq_imp_qeqT.
              ring.
            * (* (1−Lη)(−epsx) ≤ epsL·(−epsx) *)
              apply (Qle_trans _ (- (epsL * epsx)) _).
              -- (* (1−Lη)(−epsx) ≤ −epsL·epsx: sign reversal (strict turns weak). *)
                 apply Qlt_le_weak.
                 apply (Qle_lt_trans ((1 - (projT1 L n * projT1 eta n)) * (- epsx))
                                     (- ((1 - (projT1 L n * projT1 eta n)) * epsx))
                                     (- (epsL * epsx))).
                 ++ apply QleT'_to_Qle. apply (qeq_le ((1 - (projT1 L n * projT1 eta n)) * (- epsx))
                                 (- ((1 - (projT1 L n * projT1 eta n)) * epsx))).
                 apply qeq_imp_qeqT.
                    ring.
                 ++ apply (Qopp_lt_compat (epsL * epsx) ((1 - (projT1 L n * projT1 eta n)) * epsx)).
                    apply (Qmult_lt_compat_r epsL (1 - (projT1 L n * projT1 eta n)) epsx).
                    ** apply QltT_to_Qlt. exact Hepsx.
                    ** exact HLeta.
              -- (* −epsL·epsx ≤ epsL·(−epsx): a restatement. *)
                 apply QleT'_to_Qle. apply (qeq_le (- (epsL * epsx)) (epsL * (- epsx))).
                 apply qeq_imp_qeqT.
                 ring.
      }
      (* The c < 0 − (gdyn)_n chain: c == epsL·epsx/2 < ... gives (gdyn)_n < −c. *)
      (* Chain: (gdyn)_n ≤ (gx)_n + m == (1−Lη)(gx)_n + c < epsL·(−epsx) + c == −c. *)
      (* Use (gdyn)_n < −c directly: first prove (gdyn)_n + c < 0? *)
      apply (Qle_lt_trans (projT1 (real_entropy_gradient (real_dynamics x)) n)
                          ((projT1 (real_entropy_gradient x) n)
                           + ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c))
                          (- c)).
      - (* (gdyn)_n ≤ (gx)_n + m: rearranging Hhi ((gdyn)_n + −(gx)_n ≤ m, then adding (gx)_n). *)
        apply (Qle_trans _ (((projT1 (real_entropy_gradient (real_dynamics x)) n
                              + - projT1 (real_entropy_gradient x) n)
                             + projT1 (real_entropy_gradient x) n)) _).
        + (* (gdyn)_n ≤ ((gdyn)_n + −(gx)_n) + (gx)_n: simplification by ring (an equality). *)
          apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qle_trans _ (((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c)
                              + projT1 (real_entropy_gradient x) n) _).
          * (* ((gdyn)_n + −(gx)_n) + (gx)_n ≤ m + (gx)_n: Qplus_le_compat Hhi *)
            apply (Qplus_le_compat ((projT1 (real_entropy_gradient (real_dynamics x)) n
                                     + - projT1 (real_entropy_gradient x) n))
                                   ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c)
                                   (projT1 (real_entropy_gradient x) n) (projT1 (real_entropy_gradient x) n)
                                   Hhi (Qle_refl _)).
          * (* m + (gx)_n == (gx)_n + m: a ring restatement. *)
            apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - (* (gx)_n + m < −c: |gx|==−gx ⟹ == (1−Lη)(gx)_n + c < epsL·(−epsx) + c == −c *)
        (* Restatement: (gx)_n + m == (1−Lη)(gx)_n + c (Habs_eq + ring). *)
        (* Chain: (1−Lη)(gx)_n < epsL·(−epsx) (Hprod) gives +c < epsL·(−epsx) + c == −2c + c == −c. *)
        assert (Hmid : Qlt ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n) + c)
                           (- c)).
        {
          apply (Qlt_le_trans ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n) + c)
                              (epsL * (- epsx) + c)
                              (- c)).
          - apply (Qplus_lt_le_compat ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n))
                                      (epsL * (- epsx)) c c).
            + exact Hprod.
            + apply Qle_refl.
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold c. field.
        }
        apply (Qle_lt_trans ((projT1 (real_entropy_gradient x) n)
                             + ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c))
                            ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n) + c)
                            (- c)).
        + (* Qle ((gx)_n + m) ((1−Lη)(gx)_n + c): restated (Habs_eq). *)
          apply QleT'_to_Qle. apply (qeq_le ((projT1 (real_entropy_gradient x) n)
                         + ((projT1 L n * projT1 eta n) * Qabs (projT1 (real_entropy_gradient x) n) + c))
                        ((1 - (projT1 L n * projT1 eta n)) * (projT1 (real_entropy_gradient x) n) + c)).
          apply qeq_imp_qeqT.
          setoid_rewrite Habs_eq. ring.
        + (* Qlt ((1−Lη)(gx)_n + c) (−c): Hmid *)
          exact Hmid.
    }
    (* Goal: QltT c (0 − (gdyn)_n) (the negative-branch real_lt unfolded to QltT); first prove Hq' at the Qlt layer, then Qlt_to_QltT. *)
    assert (Hopp : Qlt c (- (projT1 (real_entropy_gradient (real_dynamics x)) n))).
    {
      apply (Qle_lt_trans c (- (- c)) (- (projT1 (real_entropy_gradient (real_dynamics x)) n))).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - apply (Qopp_lt_compat (projT1 (real_entropy_gradient (real_dynamics x)) n) (- c)).
        exact Htarget.
    }
    assert (Hq' : Qlt c (projT1 real_zero n - projT1 (real_entropy_gradient (real_dynamics x)) n)).
    {
      apply (Qlt_le_trans c (- (projT1 (real_entropy_gradient (real_dynamics x)) n))
                           (projT1 real_zero n - projT1 (real_entropy_gradient (real_dynamics x)) n)).
      - exact Hopp.
      - apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        rewrite Hz. ring.
    }
    exact (Qlt_to_QltT c (projT1 real_zero n - projT1 (real_entropy_gradient (real_dynamics x)) n) Hq').
Qed.

(* ===== Step 1 addendum: the negative-branch mirror (a renamed copy). ===== *)
Lemma real_dynamics_step_unfold_sign : forall x : Real,
  real_eq (real_dynamics x)
          (real_plus x (real_mult eta (real_entropy_gradient x))).
Proof. intros x. exact (real_dynamics_gradient_step x). Qed.

Theorem real_gradient_step_contraction_neg : forall x : Real,
  real_lt (real_entropy_gradient x) real_zero ->
  real_le (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_entropy_gradient x))
          (real_entropy_gradient (real_dynamics x)).
Proof.
  intros x Hgx.
  (* (1) η·g(x) < 0 *)
  assert (Heta_g : real_lt (real_mult eta (real_entropy_gradient x)) real_zero).
  {
    apply (RealSetoid.real_lt_id_l (real_mult eta (real_entropy_gradient x))
                                   (real_mult (real_entropy_gradient x) eta)
                                   real_zero
                                   (real_mult_comm eta (real_entropy_gradient x))).
    apply (RealSetoid.real_lt_id_r (real_mult (real_entropy_gradient x) eta)
                                   (real_mult real_zero eta)
                                   real_zero
                                   (real_eq_trans _ (real_mult eta real_zero) _
                                               (real_mult_comm real_zero eta)
                                               (real_mult_zero eta))
                                   (real_mult_lt_compat (real_entropy_gradient x) real_zero eta Hgx eta_pos)).
  }
  (* (2) dyn < x *)
  assert (Hlt : real_lt (real_dynamics x) x).
  {
    apply (RealSetoid.real_lt_id_l (real_dynamics x)
                                   (real_plus x (real_mult eta (real_entropy_gradient x)))
                                   x
                                   (real_dynamics_step_unfold_sign x)).
    apply (RealSetoid.real_lt_id_r (real_plus x (real_mult eta (real_entropy_gradient x)))
                                   (real_plus x real_zero)
                                   x
                                   (real_plus_zero x)).
    apply (real_lt_plus_compat_le_lt x x (real_mult eta (real_entropy_gradient x)) real_zero
                                    (RealSetoid.real_eq_le _ _ (real_eq_refl x)) Heta_g).
  }
  (* (3) strong concavity at (dyn, x). *)
  pose proof (real_strong_concavity (real_dynamics x) x Hlt) as Hsc.
  (* (4) dyn − x == η·g(x) *)
  assert (Hdynx : real_eq (real_plus (real_dynamics x) (real_opp x))
                          (real_mult eta (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_plus (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)) _).
    - apply (RealSetoid.real_eq_plus_compat (real_dynamics x) (real_opp x)
                                            (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)
                                            (real_dynamics_step_unfold_sign x) (real_eq_refl _)).
    - apply (real_eq_trans _ (real_plus x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))) _).
      + apply real_eq_sym. apply (real_plus_assoc x (real_mult eta (real_entropy_gradient x)) (real_opp x)).
      + apply (real_eq_trans _ (real_plus x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))) _).
        * apply (RealSetoid.real_eq_plus_compat x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))
                                                x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))
                                                (real_eq_refl _) (real_plus_comm _ _)).
        * apply (real_eq_trans _ (real_plus (real_plus x (real_opp x)) (real_mult eta (real_entropy_gradient x))) _).
          -- apply (real_plus_assoc x (real_opp x) (real_mult eta (real_entropy_gradient x))).
          -- apply (real_eq_trans _ (real_plus real_zero (real_mult eta (real_entropy_gradient x))) _).
             --- apply (RealSetoid.real_eq_plus_compat (real_plus x (real_opp x))
                                                       (real_mult eta (real_entropy_gradient x))
                                                       real_zero (real_mult eta (real_entropy_gradient x))
                                                       (real_plus_opp x) (real_eq_refl _)).
             --- apply (real_eq_trans _ (real_plus (real_mult eta (real_entropy_gradient x)) real_zero) _).
                 ---- apply real_plus_comm.
                 ---- apply real_plus_zero.
  }
  (* (5) x − dyn == η·(opp g(x)) *)
  assert (Hdiff : real_eq (real_plus x (real_opp (real_dynamics x)))
                          (real_mult eta (real_opp (real_entropy_gradient x)))).
  {
    apply (real_eq_trans _ (real_plus (real_opp (real_dynamics x)) x) _).
    - apply real_plus_comm.
    - apply (real_eq_trans _ (real_plus (real_opp (real_dynamics x)) (real_opp (real_opp x))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp (real_dynamics x)) x
                                              (real_opp (real_dynamics x)) (real_opp (real_opp x))
                                              (real_eq_refl _) (real_eq_sym _ _ (real_opp_opp x))).
      + apply (real_eq_trans _ (real_opp (real_plus (real_dynamics x) (real_opp x))) _).
        * apply real_eq_sym. apply (real_opp_plus (real_dynamics x) (real_opp x)).
        * apply (real_eq_trans _ (real_opp (real_mult eta (real_entropy_gradient x))) _).
          -- apply (RealSetoid.real_eq_opp_compat (real_plus (real_dynamics x) (real_opp x))
                                                  (real_mult eta (real_entropy_gradient x))
                                                  Hdynx).
          -- apply real_eq_sym. apply (real_mult_opp_l eta (real_entropy_gradient x)).
  }
  (* (6) substitute Hdiff. *)
  assert (Hsc' : real_le (real_mult mu (real_mult eta (real_opp (real_entropy_gradient x))))
                         (real_plus (real_entropy_gradient (real_dynamics x))
                                    (real_opp (real_entropy_gradient x)))).
  {
    apply (RealSetoid.real_le_id_l (real_mult mu (real_mult eta (real_opp (real_entropy_gradient x))))
                                   (real_mult mu (real_plus x (real_opp (real_dynamics x))))
                                   (real_plus (real_entropy_gradient (real_dynamics x))
                                              (real_opp (real_entropy_gradient x)))
                                   (RealSetoid.real_eq_mult_compat mu
                                                                    (real_mult eta (real_opp (real_entropy_gradient x)))
                                                                    mu
                                                                    (real_plus x (real_opp (real_dynamics x)))
                                                                    (real_eq_refl _) (real_eq_sym _ _ Hdiff))
                                   Hsc).
  }
  (* (7) restatement: (ημ)·(opp g) ≤ g(dyn) − g(x). *)
  assert (Hmm : real_eq (real_mult mu (real_mult eta (real_opp (real_entropy_gradient x))))
                        (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))).
  {
    apply (real_eq_trans _ (real_mult mu (real_mult (real_opp (real_entropy_gradient x)) eta)) _).
    - apply (RealSetoid.real_eq_mult_compat mu (real_mult eta (real_opp (real_entropy_gradient x)))
                                            mu (real_mult (real_opp (real_entropy_gradient x)) eta)
                                            (real_eq_refl _) (real_mult_comm eta (real_opp (real_entropy_gradient x)))).
    - apply (real_eq_trans _ (real_mult (real_mult mu (real_opp (real_entropy_gradient x))) eta) _).
      + apply (real_mult_assoc mu (real_opp (real_entropy_gradient x)) eta).
      + apply (real_eq_trans _ (real_mult (real_mult (real_opp (real_entropy_gradient x)) mu) eta) _).
        * apply (RealSetoid.real_eq_mult_compat (real_mult mu (real_opp (real_entropy_gradient x))) eta
                                                (real_mult (real_opp (real_entropy_gradient x)) mu) eta
                                                (real_mult_comm mu (real_opp (real_entropy_gradient x))) (real_eq_refl _)).
        * apply (real_eq_trans _ (real_mult (real_opp (real_entropy_gradient x)) (real_mult mu eta)) _).
          -- apply real_eq_sym. apply (real_mult_assoc (real_opp (real_entropy_gradient x)) mu eta).
          -- apply (real_eq_trans _ (real_mult (real_opp (real_entropy_gradient x)) (real_mult eta mu)) _).
             ++ apply (RealSetoid.real_eq_mult_compat (real_opp (real_entropy_gradient x)) (real_mult mu eta)
                                                      (real_opp (real_entropy_gradient x)) (real_mult eta mu)
                                                      (real_eq_refl _) (real_mult_comm mu eta)).
             ++ apply (real_mult_comm (real_opp (real_entropy_gradient x)) (real_mult eta mu)).
  }
  assert (Hsc'' : real_le (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))
                          (real_plus (real_entropy_gradient (real_dynamics x))
                                     (real_opp (real_entropy_gradient x)))).
  {
    apply (RealSetoid.real_le_id_l (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))
                                   (real_mult mu (real_mult eta (real_opp (real_entropy_gradient x))))
                                   (real_plus (real_entropy_gradient (real_dynamics x))
                                              (real_opp (real_entropy_gradient x)))
                                   (real_eq_sym _ _ Hmm) Hsc').
  }
  (* (8) rearrangement: from A ≤ B−C derive C ≤ B−A. *)
  pose (A := real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x))).
  pose (B := real_entropy_gradient (real_dynamics x)).
  pose (C := real_entropy_gradient x).
  assert (H1 : real_le (real_plus A C) B).
  {
    apply (RealSetoid.real_le_id_r (real_plus A C) (real_plus (real_plus B (real_opp C)) C) B).
    - exact (real_minus_plus_cancel B C).
    - apply (real_le_plus_compat A (real_plus B (real_opp C)) C C Hsc'' (RealSetoid.real_eq_le _ _ (real_eq_refl C))).
  }
  assert (H2 : real_le (real_plus (real_plus A C) (real_opp A)) (real_plus B (real_opp A))).
  {
    apply (real_le_plus_compat (real_plus A C) B (real_opp A) (real_opp A) H1 (RealSetoid.real_eq_le _ _ (real_eq_refl _))).
  }
  assert (H3 : real_eq (real_plus (real_plus A C) (real_opp A)) C).
  {
    unfold A, C.
    apply (real_eq_trans _ (real_plus (real_plus (real_entropy_gradient x)
                                                 (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x))))
                                      (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x))))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_plus A C) (real_opp A)
                                            (real_plus C A) (real_opp A)
                                            (real_plus_comm A C) (real_eq_refl _)).
    - apply (real_eq_trans _ (real_plus (real_entropy_gradient x)
                                        (real_plus (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))
                                                   (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))))) _).
      + apply real_eq_sym. apply (real_plus_assoc C (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))
                                                    (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x))))).
      + apply (real_eq_trans _ (real_plus C real_zero) _).
        * apply (RealSetoid.real_eq_plus_compat C (real_plus (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))
                                                             (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))))
                                                C real_zero
                                                (real_eq_refl _) (real_plus_opp _)).
        * apply real_plus_zero.
  }
  assert (H4 : real_eq (real_plus B (real_opp A))
                       (real_plus (real_entropy_gradient (real_dynamics x))
                                  (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))))).
  { unfold A, B. apply real_eq_refl. }
  assert (H5 : real_le C (real_plus (real_entropy_gradient (real_dynamics x))
                                    (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))))).
  {
    apply (RealSetoid.real_le_id_l C (real_plus (real_plus A C) (real_opp A))
                                   (real_plus (real_entropy_gradient (real_dynamics x))
                                              (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))))
                                   (real_eq_sym _ _ H3)).
    apply (RealSetoid.real_le_id_r (real_plus (real_plus A C) (real_opp A))
                                   (real_plus B (real_opp A))
                                   (real_plus (real_entropy_gradient (real_dynamics x))
                                              (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))))
                                   H4 H2).
  }
  (* (9) restating the RHS. *)
  assert (H5' : real_le C (real_plus (real_entropy_gradient (real_dynamics x))
                                     (real_mult (real_mult eta mu) (real_entropy_gradient x)))).
  {
    apply (RealSetoid.real_le_id_r C
                                   (real_plus (real_entropy_gradient (real_dynamics x))
                                              (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))))
                                   (real_plus (real_entropy_gradient (real_dynamics x))
                                              (real_mult (real_mult eta mu) (real_entropy_gradient x)))
                                   (RealSetoid.real_eq_plus_compat (real_entropy_gradient (real_dynamics x))
                                                                   (real_opp (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x))))
                                                                   (real_entropy_gradient (real_dynamics x))
                                                                   (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                                                   (real_eq_refl _)
                                                                   (real_eq_trans _ (real_opp (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))) _
                                                                       (RealSetoid.real_eq_opp_compat (real_mult (real_mult eta mu) (real_opp (real_entropy_gradient x)))
                                                                                                       (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))
                                                                                                       (real_mult_opp_l (real_mult eta mu) (real_entropy_gradient x)))
                                                                       (real_opp_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))))
                                   H5).
  }
  (* (10) rearranging backwards. *)
  pose (A' := real_mult (real_mult eta mu) (real_entropy_gradient x)).
  assert (H6 : real_le (real_plus C (real_opp A')) (real_entropy_gradient (real_dynamics x))).
  {
    apply (RealSetoid.real_le_id_r (real_plus C (real_opp A'))
                                   (real_plus (real_plus (real_entropy_gradient (real_dynamics x)) A') (real_opp A'))
                                   (real_entropy_gradient (real_dynamics x))
                                   (real_eq_trans _ (real_plus (real_entropy_gradient (real_dynamics x))
                                                               (real_plus A' (real_opp A'))) _
                                       (real_eq_sym _ _ (real_plus_assoc (real_entropy_gradient (real_dynamics x)) A' (real_opp A')))
                                       (real_eq_trans _ (real_plus (real_entropy_gradient (real_dynamics x)) real_zero) _
                                           (RealSetoid.real_eq_plus_compat (real_entropy_gradient (real_dynamics x))
                                                                           (real_plus A' (real_opp A'))
                                                                           (real_entropy_gradient (real_dynamics x)) real_zero
                                                                           (real_eq_refl _) (real_plus_opp A'))
                                           (real_plus_zero (real_entropy_gradient (real_dynamics x)))))
                                   (real_le_plus_compat C (real_plus (real_entropy_gradient (real_dynamics x)) A')
                                                        (real_opp A') (real_opp A')
                                                        H5' (RealSetoid.real_eq_le _ _ (real_eq_refl _)))).
  }
  assert (H7 : real_eq (real_plus C (real_opp A'))
                       (real_plus (real_entropy_gradient x) (real_opp A'))).
  { unfold C. apply real_eq_refl. }
  assert (H8 : real_le (real_plus (real_entropy_gradient x) (real_opp A'))
                       (real_entropy_gradient (real_dynamics x))).
  {
    apply (RealSetoid.real_le_id_l (real_plus (real_entropy_gradient x) (real_opp A'))
                                   (real_plus C (real_opp A'))
                                   (real_entropy_gradient (real_dynamics x))
                                   (real_eq_sym _ _ H7) H6).
  }
  (* (11) restating the goal. *)
  assert (H9 : real_eq (real_plus (real_entropy_gradient x)
                                  (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                       (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                  (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_plus (real_mult real_one (real_entropy_gradient x))
                                      (real_mult (real_opp (real_mult eta mu)) (real_entropy_gradient x))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_entropy_gradient x)
                                            (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))
                                            (real_mult real_one (real_entropy_gradient x))
                                            (real_mult (real_opp (real_mult eta mu)) (real_entropy_gradient x))
                                            (real_eq_trans _ (real_mult (real_entropy_gradient x) real_one) _
                                               (real_eq_sym _ _ (real_mult_one (real_entropy_gradient x)))
                                               (real_mult_comm (real_entropy_gradient x) real_one))
                                            (real_opp_mult_r (real_mult eta mu) (real_entropy_gradient x))).
    - apply (real_distrib_r real_one (real_opp (real_mult eta mu)) (real_entropy_gradient x)).
  }
  apply (RealSetoid.real_le_id_l (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_entropy_gradient x))
                                 (real_plus (real_entropy_gradient x)
                                            (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                 (real_entropy_gradient (real_dynamics x))
                                 (real_eq_sym _ _ H9) H8).
Qed.

(* ===== Step 3: unifying abs over the two branches ===== *)

(* A copy of K1a (renamed, with real_dynamics_step_unfold_sign). *)
Theorem real_gradient_step_contraction_k1a : forall x : Real,
  real_lt real_zero (real_entropy_gradient x) ->
  real_le (real_entropy_gradient (real_dynamics x))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_entropy_gradient x)).
Proof.
  intros x Hgx.
  assert (Heta_g : real_lt real_zero (real_mult eta (real_entropy_gradient x)))
    by exact (real_mult_positive eta (real_entropy_gradient x) eta_pos Hgx).
  assert (Hlt : real_lt x (real_dynamics x)).
  {
    apply (RealSetoid.real_lt_id_l x (real_plus x real_zero) (real_dynamics x)
                                   (real_eq_sym _ _ (real_plus_zero x))).
    apply (RealSetoid.real_lt_id_r (real_plus x real_zero) (real_plus x (real_mult eta (real_entropy_gradient x))) (real_dynamics x)
                                   (real_eq_sym _ _ (real_dynamics_step_unfold_sign x))).
    apply (real_lt_plus_compat_le_lt x x real_zero (real_mult eta (real_entropy_gradient x)) (RealSetoid.real_eq_le _ _ (real_eq_refl x)) Heta_g).
  }
  pose proof (real_strong_concavity x (real_dynamics x) Hlt) as Hsc.
  assert (Hdiff : real_eq (real_plus (real_dynamics x) (real_opp x))
                          (real_mult eta (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_plus (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)) _).
    - apply (RealSetoid.real_eq_plus_compat (real_dynamics x) (real_opp x)
                                            (real_plus x (real_mult eta (real_entropy_gradient x))) (real_opp x)
                                            (real_dynamics_step_unfold_sign x) (real_eq_refl _)).
    - apply (real_eq_trans _ (real_plus x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))) _).
      + apply real_eq_sym. apply (real_plus_assoc x (real_mult eta (real_entropy_gradient x)) (real_opp x)).
      + apply (real_eq_trans _ (real_plus x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))) _).
        * apply (RealSetoid.real_eq_plus_compat x (real_plus (real_mult eta (real_entropy_gradient x)) (real_opp x))
                                                x (real_plus (real_opp x) (real_mult eta (real_entropy_gradient x)))
                                                (real_eq_refl _) (real_plus_comm _ _)).
        * apply (real_eq_trans _ (real_plus (real_plus x (real_opp x)) (real_mult eta (real_entropy_gradient x))) _).
          -- apply (real_plus_assoc x (real_opp x) (real_mult eta (real_entropy_gradient x))).
          -- apply (real_eq_trans _ (real_plus real_zero (real_mult eta (real_entropy_gradient x))) _).
             --- apply (RealSetoid.real_eq_plus_compat (real_plus x (real_opp x))
                                                       (real_mult eta (real_entropy_gradient x))
                                                       real_zero (real_mult eta (real_entropy_gradient x))
                                                       (real_plus_opp x) (real_eq_refl _)).
             --- apply (real_eq_trans _ (real_plus (real_mult eta (real_entropy_gradient x)) real_zero) _).
                 ---- apply real_plus_comm.
                 ---- apply real_plus_zero.
  }
  assert (Hsc' : real_le (real_mult mu (real_mult eta (real_entropy_gradient x)))
                         (real_plus (real_entropy_gradient x)
                                    (real_opp (real_entropy_gradient (real_dynamics x))))).
  {
    apply (RealSetoid.real_le_id_l (real_mult mu (real_mult eta (real_entropy_gradient x)))
                                   (real_mult mu (real_plus (real_dynamics x) (real_opp x)))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_entropy_gradient (real_dynamics x))))
                                   (RealSetoid.real_eq_mult_compat mu
                                                                    (real_mult eta (real_entropy_gradient x))
                                                                    mu
                                                                    (real_plus (real_dynamics x) (real_opp x))
                                                                    (real_eq_refl _) (real_eq_sym _ _ Hdiff))
                                   Hsc).
  }
  assert (Hmm : real_eq (real_mult mu (real_mult eta (real_entropy_gradient x)))
                        (real_mult (real_mult eta mu) (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_mult mu (real_mult (real_entropy_gradient x) eta)) _).
    - apply (RealSetoid.real_eq_mult_compat mu (real_mult eta (real_entropy_gradient x))
                                            mu (real_mult (real_entropy_gradient x) eta)
                                            (real_eq_refl _) (real_mult_comm eta (real_entropy_gradient x))).
    - apply (real_eq_trans _ (real_mult (real_mult mu (real_entropy_gradient x)) eta) _).
      + apply (real_mult_assoc mu (real_entropy_gradient x) eta).
      + apply (real_eq_trans _ (real_mult (real_mult (real_entropy_gradient x) mu) eta) _).
        * apply (RealSetoid.real_eq_mult_compat (real_mult mu (real_entropy_gradient x)) eta
                                                (real_mult (real_entropy_gradient x) mu) eta
                                                (real_mult_comm mu (real_entropy_gradient x)) (real_eq_refl _)).
        * apply (real_eq_trans _ (real_mult (real_entropy_gradient x) (real_mult mu eta)) _).
          -- apply real_eq_sym. apply (real_mult_assoc (real_entropy_gradient x) mu eta).
          -- apply (real_eq_trans _ (real_mult (real_entropy_gradient x) (real_mult eta mu)) _).
             ++ apply (RealSetoid.real_eq_mult_compat (real_entropy_gradient x) (real_mult mu eta)
                                                      (real_entropy_gradient x) (real_mult eta mu)
                                                      (real_eq_refl _) (real_mult_comm mu eta)).
             ++ apply (real_mult_comm (real_entropy_gradient x) (real_mult eta mu)).
  }
  assert (Hsc'' : real_le (real_mult (real_mult eta mu) (real_entropy_gradient x))
                          (real_plus (real_entropy_gradient x)
                                     (real_opp (real_entropy_gradient (real_dynamics x))))).
  {
    apply (RealSetoid.real_le_id_l (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                   (real_mult mu (real_mult eta (real_entropy_gradient x)))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_entropy_gradient (real_dynamics x))))
                                   (real_eq_sym _ _ Hmm) Hsc').
  }
  pose (A := real_mult (real_mult eta mu) (real_entropy_gradient x)).
  pose (B := real_entropy_gradient x).
  pose (C := real_entropy_gradient (real_dynamics x)).
  assert (H1 : real_le (real_plus A C) B).
  {
    apply (RealSetoid.real_le_id_r (real_plus A C) (real_plus (real_plus B (real_opp C)) C) B).
    - exact (real_minus_plus_cancel B C).
    - apply (real_le_plus_compat A (real_plus B (real_opp C)) C C Hsc'' (RealSetoid.real_eq_le _ _ (real_eq_refl C))).
  }
  assert (H2 : real_le (real_plus (real_plus A C) (real_opp A)) (real_plus B (real_opp A))).
  {
    apply (real_le_plus_compat (real_plus A C) B (real_opp A) (real_opp A) H1 (RealSetoid.real_eq_le _ _ (real_eq_refl _))).
  }
  assert (H3 : real_eq (real_plus (real_plus A C) (real_opp A)) C).
  {
    unfold A, C.
    apply (real_eq_trans _ (real_plus (real_plus (real_entropy_gradient (real_dynamics x))
                                                 (real_mult (real_mult eta mu) (real_entropy_gradient x)))
                                      (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_plus A C) (real_opp A)
                                            (real_plus C A) (real_opp A)
                                            (real_plus_comm A C) (real_eq_refl _)).
    - apply (real_eq_trans _ (real_plus (real_entropy_gradient (real_dynamics x))
                                        (real_plus (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                                   (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))) _).
      + apply real_eq_sym. apply (real_plus_assoc C (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                                    (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))).
      + apply (real_eq_trans _ (real_plus C real_zero) _).
        * apply (RealSetoid.real_eq_plus_compat C (real_plus (real_mult (real_mult eta mu) (real_entropy_gradient x))
                                                             (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                                C real_zero
                                                (real_eq_refl _) (real_plus_opp _)).
        * apply real_plus_zero.
  }
  assert (H4 : real_eq (real_plus B (real_opp A))
                       (real_plus (real_entropy_gradient x)
                                  (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))).
  { unfold A, B. apply real_eq_refl. }
  assert (H5 : real_le C (real_plus (real_entropy_gradient x)
                                    (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))).
  {
    apply (RealSetoid.real_le_id_l C (real_plus (real_plus A C) (real_opp A))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                   (real_eq_sym _ _ H3)).
    apply (RealSetoid.real_le_id_r (real_plus (real_plus A C) (real_opp A))
                                   (real_plus B (real_opp A))
                                   (real_plus (real_entropy_gradient x)
                                              (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                   H4 H2).
  }
  assert (H6 : real_eq (real_plus (real_entropy_gradient x)
                                  (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                       (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                  (real_entropy_gradient x))).
  {
    apply (real_eq_trans _ (real_plus (real_mult real_one (real_entropy_gradient x))
                                      (real_mult (real_opp (real_mult eta mu)) (real_entropy_gradient x))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_entropy_gradient x)
                                            (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x)))
                                            (real_mult real_one (real_entropy_gradient x))
                                            (real_mult (real_opp (real_mult eta mu)) (real_entropy_gradient x))
                                            (real_eq_trans _ (real_mult (real_entropy_gradient x) real_one) _
                                               (real_eq_sym _ _ (real_mult_one (real_entropy_gradient x)))
                                               (real_mult_comm (real_entropy_gradient x) real_one))
                                            (real_opp_mult_r (real_mult eta mu) (real_entropy_gradient x))).
    - apply (real_distrib_r real_one (real_opp (real_mult eta mu)) (real_entropy_gradient x)).
  }
  apply (RealSetoid.real_le_id_r C
                                 (real_plus (real_entropy_gradient x)
                                            (real_opp (real_mult (real_mult eta mu) (real_entropy_gradient x))))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_entropy_gradient x))
                                 H6 H5).
Qed.

(* Positive branch: g(x)>0 gives |g(dyn)| ≤ κ|g(x)| (sign-preserving positive + K1a + abs_pos). *)
Theorem real_gradient_step_abs_contraction_pos : forall x : Real,
  real_lt real_zero (real_entropy_gradient x) ->
  real_le (real_abs (real_entropy_gradient (real_dynamics x)))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_abs (real_entropy_gradient x))).
Proof.
  intros x Hgx.
  assert (Hgdyn : real_lt real_zero (real_entropy_gradient (real_dynamics x)))
    by exact (real_sign_preservation_pos x Hgx).
  assert (Habsd : real_eq (real_abs (real_entropy_gradient (real_dynamics x)))
                          (real_entropy_gradient (real_dynamics x)))
    by exact (real_abs_pos_req (real_entropy_gradient (real_dynamics x)) Hgdyn).
  assert (Habsx : real_eq (real_abs (real_entropy_gradient x)) (real_entropy_gradient x))
    by exact (real_abs_pos_req (real_entropy_gradient x) Hgx).
  apply (RealSetoid.real_le_id_l (real_abs (real_entropy_gradient (real_dynamics x)))
                                 (real_entropy_gradient (real_dynamics x))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_abs (real_entropy_gradient x)))
                                 Habsd).
  apply (RealSetoid.real_le_id_r (real_entropy_gradient (real_dynamics x))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_entropy_gradient x))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_abs (real_entropy_gradient x)))
                                 (RealSetoid.real_eq_mult_compat (real_plus real_one (real_opp (real_mult eta mu)))
                                                                 (real_entropy_gradient x)
                                                                 (real_plus real_one (real_opp (real_mult eta mu)))
                                                                 (real_abs (real_entropy_gradient x))
                                                                 (real_eq_refl _) (real_eq_sym _ _ Habsx))
                                 (real_gradient_step_contraction_k1a x Hgx)).
Qed.

(* Negative branch: g(x)<0 gives |g(dyn)| ≤ κ|g(x)| (sign-preserving negative + K1b negative + abs_neg + opp_le_compat). *)
Theorem real_gradient_step_abs_contraction_neg : forall x : Real,
  real_lt (real_entropy_gradient x) real_zero ->
  real_le (real_abs (real_entropy_gradient (real_dynamics x)))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_abs (real_entropy_gradient x))).
Proof.
  intros x Hgx.
  assert (Hgdyn : real_lt (real_entropy_gradient (real_dynamics x)) real_zero)
    by exact (real_sign_preservation_neg x Hgx).
  assert (Habsd : real_eq (real_abs (real_entropy_gradient (real_dynamics x)))
                          (real_opp (real_entropy_gradient (real_dynamics x))))
    by exact (real_abs_neg_req (real_entropy_gradient (real_dynamics x)) Hgdyn).
  assert (Habsx : real_eq (real_abs (real_entropy_gradient x)) (real_opp (real_entropy_gradient x)))
    by exact (real_abs_neg_req (real_entropy_gradient x) Hgx).
  assert (Hneg : real_le (real_opp (real_entropy_gradient (real_dynamics x)))
                         (real_opp (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                              (real_entropy_gradient x)))).
  {
    apply (real_opp_le_compat (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                         (real_entropy_gradient x))
                               (real_entropy_gradient (real_dynamics x))).
    exact (real_gradient_step_contraction_neg x Hgx).
  }
  apply (RealSetoid.real_le_id_l (real_abs (real_entropy_gradient (real_dynamics x)))
                                 (real_opp (real_entropy_gradient (real_dynamics x)))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_abs (real_entropy_gradient x)))
                                 Habsd).
  apply (RealSetoid.real_le_id_r (real_opp (real_entropy_gradient (real_dynamics x)))
                                 (real_opp (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                      (real_entropy_gradient x)))
                                 (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                            (real_abs (real_entropy_gradient x)))
                                 (real_eq_trans _ (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                             (real_opp (real_entropy_gradient x))) _
                                     (real_eq_sym _ _ (real_mult_opp_l (real_plus real_one (real_opp (real_mult eta mu)))
                                                                       (real_entropy_gradient x)))
                                     (RealSetoid.real_eq_mult_compat (real_plus real_one (real_opp (real_mult eta mu)))
                                                                     (real_opp (real_entropy_gradient x))
                                                                     (real_plus real_one (real_opp (real_mult eta mu)))
                                                                     (real_abs (real_entropy_gradient x))
                                                                     (real_eq_refl _) (real_eq_sym _ _ Habsx)))
                                 Hneg).
Qed.

(* ===== Step 4: fully-negative-orbit iterate (the K2/K3 negative versions) ===== *)

(* K2 negative: a fully negative orbit gives |g(x_{n+1})| ≤ κ·|g(x_n)| (the negative instantiation of step 3; no g(dyn)<0 premise needed). *)
Theorem real_gradient_iterate_abs_decay_neg : forall (E_A : Real) (n : nat),
  (forall k : nat, NatLe k (Datatypes.S n) ->
    real_lt (real_entropy_gradient (iterate real_dynamics k E_A)) real_zero) ->
  real_le (real_abs (real_entropy_gradient (iterate real_dynamics (Datatypes.S n) E_A)))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
Proof.
  intros E_A n Hall.
  assert (Hgn : real_lt (real_entropy_gradient (iterate real_dynamics n E_A)) real_zero).
  { apply Hall. apply NatLe_lift. lia. }
  exact (real_gradient_step_abs_contraction_neg (iterate real_dynamics n E_A) Hgn).
Qed.

(* K3 negative: a fully negative orbit gives |g(x_{n+k})| ≤ κ^k·|g(x_n)| (by induction, in the shape of real_grad_decay_positive_iter). *)
Theorem real_grad_decay_negative_iter : forall (E_A : Real) (n k : nat),
  real_lt real_zero (real_plus real_one (real_opp (real_mult eta mu))) ->
  (forall j : nat, NatLe j (n + k) ->
    real_lt (real_entropy_gradient (iterate real_dynamics j E_A)) real_zero) ->
  real_le (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
          (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                     (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
Proof.
  intros E_A n k Hkpos Hall.
  induction k as [| k IH]; simpl.
  - rewrite (Nat.add_0_r n).
    apply (RealSetoid.real_le_id_r _ (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))) _).
    + apply (real_eq_trans _ (real_mult (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))) real_one) _).
      * apply real_eq_sym. apply (real_mult_one (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
      * apply real_mult_comm.
    + apply RealSetoid.real_eq_le. apply real_eq_refl.
  - apply (real_le_trans _ (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                      (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))) _).
    + rewrite (Nat.add_succ_r n k).
      apply (real_gradient_iterate_abs_decay_neg E_A (n + k)).
      intros j Hj. apply NatLe_drop in Hj. apply Hall. apply NatLe_lift. lia.
    + assert (IH' : real_le (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
                            (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                       (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))).
      { apply IH. intros j Hj. apply NatLe_drop in Hj. apply Hall. apply NatLe_lift. lia. }
      apply (RealSetoid.real_le_id_r (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A))))
                                     (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                           (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))))
                                     (real_mult (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                           (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k))
                                                (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                     (real_mult_assoc (real_plus real_one (real_opp (real_mult eta mu)))
                                                      (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                      (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                     (real_le_mult_compat_r (real_plus real_one (real_opp (real_mult eta mu)))
                                                            (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
                                                            (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                                       (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                                            (RealSetoid.real_lt_le_iff_req _ _ (inl Hkpos))
                                                            IH')).
Qed.

(* ============================================================ *)
(* T4.3: the fully-signed κ under a trichotomy premise (the      *)
(*   conditional theorem of paper-4, responding to S3).          *)
(*   Under the explicit trichotomy sign_dec, the positive/negative/zero *)
(*   branches unify into the single-step contraction             *)
(*   |g(dyn x)| ≤ κ·|g x|; induction gives the geometric decay of the   *)
(*   fully-signed orbit |g(x_{n+k})| ≤ κ^k·|g(x_n)| (κ := 1 − ημ).      *)
(*   Honest-interface premises (valid for decidable gradients —       *)
(*   rational-valued/computable instances):                    *)
(*     real_sign_dec            — gradient trichotomy (Set-layer Or) *)
(*     real_entropy_gradient_wd — gradient req extensionality (zero branch) *)
(* ============================================================ *)
(* A gradient trichotomy is an instance of the LPO-style whole-order *)
(* decision (see the rLPO equivalence records) — it holds for decidable *)
(* gradients (rational-valued/computable instances), which are the *)
(* candidate suppliers at the instance layer; no proof attempt is made *)
(* at the interface layer. *)
Variable real_sign_dec : forall x : Real,
  Or (real_lt real_zero (real_entropy_gradient x))
     (Or (real_eq (real_entropy_gradient x) real_zero)
         (real_lt (real_entropy_gradient x) real_zero)).
Variable real_entropy_gradient_wd : forall x y : Real,
  real_eq x y -> real_eq (real_entropy_gradient x) (real_entropy_gradient y).

(* Single-step, three-branch unification: |g(dyn x)| ≤ κ·|g x| (merging the positive/zero/negative branches). *)
Theorem real_grad_step_abs_contraction_full : forall x : Real,
  real_le (real_abs (real_entropy_gradient (real_dynamics x)))
          (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                     (real_abs (real_entropy_gradient x))).
Proof.
  intros x.
  destruct (real_sign_dec x) as [Hpos | [Hzero | Hneg]].
  - (* g x > 0: the positive-branch abs_contraction_pos (already available in this Section, internally using positive sign preservation). *)
    apply (real_gradient_step_abs_contraction_pos x Hpos).
  - (* g x == 0: dyn x == x + η·0 == x ⟹ g(dyn x) == 0 ⟹ |g(dyn x)| == 0 == κ·0 == κ·|g x| *)
    assert (Hdyn : real_eq (real_dynamics x) x).
    { apply (real_eq_trans (real_dynamics x) (real_plus x (real_mult eta (real_entropy_gradient x))) x).
      - apply real_dynamics_gradient_step.
      - apply (real_eq_trans (real_plus x (real_mult eta (real_entropy_gradient x)))
                             (real_plus x (real_mult eta real_zero)) x).
        + apply (RealSetoid.real_eq_plus_compat x (real_mult eta (real_entropy_gradient x)) x (real_mult eta real_zero)
                  (real_eq_refl x)
                  (RealSetoid.real_eq_mult_compat eta (real_entropy_gradient x) eta real_zero
                     (real_eq_refl eta) Hzero)).
        + apply (real_eq_trans (real_plus x (real_mult eta real_zero)) (real_plus x real_zero) x).
          * apply (RealSetoid.real_eq_plus_compat x (real_mult eta real_zero) x real_zero
                    (real_eq_refl x) (real_mult_zero eta)).
          * apply (real_plus_zero x). }
    assert (Hg0 : real_eq (real_entropy_gradient (real_dynamics x)) real_zero).
    { apply (real_eq_trans (real_entropy_gradient (real_dynamics x)) (real_entropy_gradient x) real_zero).
      - apply real_entropy_gradient_wd. exact Hdyn.
      - exact Hzero. }
    assert (Habs0 : real_eq (real_abs (real_entropy_gradient (real_dynamics x))) real_zero).
    { apply (real_eq_trans (real_abs (real_entropy_gradient (real_dynamics x))) (real_abs real_zero) real_zero).
      - apply real_abs_eq_compat. exact Hg0.
      - apply real_abs_zero_req. }
    assert (Hrhs0 : real_eq (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                             (real_abs (real_entropy_gradient x))) real_zero).
    { apply (real_eq_trans (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                      (real_abs (real_entropy_gradient x)))
             (real_mult (real_plus real_one (real_opp (real_mult eta mu))) (real_abs real_zero))
             real_zero).
      - apply (RealSetoid.real_eq_mult_compat (real_plus real_one (real_opp (real_mult eta mu)))
                                              (real_abs (real_entropy_gradient x))
                                              (real_plus real_one (real_opp (real_mult eta mu))) (real_abs real_zero)
                (real_eq_refl (real_plus real_one (real_opp (real_mult eta mu))))
                (real_abs_eq_compat (real_entropy_gradient x) real_zero Hzero)).
      - apply (real_eq_trans (real_mult (real_plus real_one (real_opp (real_mult eta mu))) (real_abs real_zero))
                             (real_mult (real_plus real_one (real_opp (real_mult eta mu))) real_zero)
                             real_zero).
        + apply (RealSetoid.real_eq_mult_compat (real_plus real_one (real_opp (real_mult eta mu)))
                                                (real_abs real_zero)
                                                (real_plus real_one (real_opp (real_mult eta mu))) real_zero
                  (real_eq_refl (real_plus real_one (real_opp (real_mult eta mu))))
                  real_abs_zero_req).
        + apply (real_mult_zero (real_plus real_one (real_opp (real_mult eta mu)))). }
    apply (RealSetoid.real_le_id_l (real_abs (real_entropy_gradient (real_dynamics x))) real_zero
           (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                      (real_abs (real_entropy_gradient x)))).
    { exact Habs0. }
    { apply (RealSetoid.real_le_id_r real_zero real_zero
             (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                        (real_abs (real_entropy_gradient x)))).
      { exact (real_eq_sym (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                               (real_abs (real_entropy_gradient x))) real_zero Hrhs0). }
      { apply real_le_refl. } }
  - (* g x < 0: the negative-branch abs_contraction_neg (already available in this Section, internally using negative sign preservation). *)
    apply (real_gradient_step_abs_contraction_neg x Hneg).
Qed.

(* Main theorem: the fully-signed geometric orbit decay under trichotomy, |g(x_{n+k})| ≤ κ^k·|g(x_n)|. *)
Theorem real_grad_decay_full_sign_iter : forall (E_A : Real) (n k : nat),
  real_lt real_zero (real_plus real_one (real_opp (real_mult eta mu))) ->
  real_le (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
          (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                     (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
Proof.
  intros E_A n k Hkpos.
  induction k as [| k IH]; simpl.
  - (* k = 0: |g(x_n)| ≤ 1·|g(x_n)| *)
    rewrite (Nat.add_0_r n).
    apply (RealSetoid.real_le_id_r _ (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))) _).
    + apply (real_eq_trans _ (real_mult (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))) real_one) _).
      * apply real_eq_sym. apply (real_mult_one (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))).
      * apply real_mult_comm.
    + apply RealSetoid.real_eq_le. apply real_eq_refl.
  - (* k = S k': |g(x_{n+S k'})| ≤ κ·|g(x_{n+k'})| ≤ κ·(κ^{k'}·|g(x_n)|) == κ^{S k'}·|g(x_n)| *)
    apply (real_le_trans _ (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                      (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))) _).
    + (* Single step (three-branch unification): |g(dyn x_{n+k})| ≤ κ·|g x_{n+k}|. *)
      rewrite (Nat.add_succ_r n k).
      apply (real_grad_step_abs_contraction_full (iterate real_dynamics (n + k) E_A)).
    + (* Induction step: κ·|g(x_{n+k})| ≤ κ·(κ^{k'}·|g(x_n)|) == κ^{S k'}·|g(x_n)|. *)
      assert (IH' : real_le (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
                            (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                       (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))).
      { exact IH. }
      apply (RealSetoid.real_le_id_r (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A))))
                                     (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                           (real_abs (real_entropy_gradient (iterate real_dynamics n E_A)))))
                                     (real_mult (real_mult (real_plus real_one (real_opp (real_mult eta mu)))
                                                           (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k))
                                                (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                     (real_mult_assoc (real_plus real_one (real_opp (real_mult eta mu)))
                                                      (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                      (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                     (real_le_mult_compat_r (real_plus real_one (real_opp (real_mult eta mu)))
                                                            (real_abs (real_entropy_gradient (iterate real_dynamics (n + k) E_A)))
                                                            (real_mult (real_r_pow (real_plus real_one (real_opp (real_mult eta mu))) k)
                                                                       (real_abs (real_entropy_gradient (iterate real_dynamics n E_A))))
                                                            (RealSetoid.real_lt_le_iff_req _ _ (inl Hkpos))
                                                            IH')).
Qed.

End RealKappaSignReal.

(* ================================================================ *)
(* T3.2 (the secondary main theorem of paper-3, incorporated): the    *)
(* exp-log ordered-group isomorphism assembly.                        *)
(* New content: the range characterization (sigT, both directions) +  *)
(* order-isomorphism image-side completeness (reflecting the order).  *)
(* Discipline: Set layer (real_lt/real_eq are both Set-valued), informative *)
(* sigT, zero classical axioms (no trichotomy), zero admissions.      *)
(* Dependencies: log_inv_exp_neg_thm (left inverse) / cw_log_exp_right (right inverse) / *)
(* real_log_lt_mono (log strictly increasing) / the cauchy_real_exp_* family. *)
(* ================================================================ *)
Section ExpLogGroupIso.

(* K1 (main theorem): the order is reflected by exp: exp x < exp y gives x < y.
   Left inverse (log_inv_exp_neg_thm) + log strictly increasing (real_log_lt_mono) + an extensionality chain:
   e^x < e^y gives log(e^x) < log(e^y), hence x < y. *)
Lemma exp_reflects_lt : forall x y : Real,
  real_lt (cauchy_real_exp x) (cauchy_real_exp y) -> real_lt x y.
Proof.
  intros x y Hexp.
  (* x == log(e^x) (left inverse), y == log(e^y). *)
  apply (real_lt_eq_lt x (cw_log (cauchy_real_exp y) (cauchy_real_exp_pos y)) y).
  - (* x < log(e^y): x == log(e^x) < log(e^y) (log strictly increasing). *)
    apply (real_eq_lt_lt x (cw_log (cauchy_real_exp x) (cauchy_real_exp_pos x))
                          (cw_log (cauchy_real_exp y) (cauchy_real_exp_pos y))).
    + apply real_eq_sym. apply (log_inv_exp_neg_thm x (cauchy_real_exp_pos x)).
    + apply (real_log_lt_mono (cauchy_real_exp x) (cauchy_real_exp y)
                              (cauchy_real_exp_pos x) (cauchy_real_exp_pos y)).
      exact Hexp.
  - apply (log_inv_exp_neg_thm y (cauchy_real_exp_pos y)).
Qed.

(* K2: range characterization, the exists direction (informative): 0 < y gives some x with e^x == y, witnessed by cw_log y Hy. *)
Lemma exp_surj_pos : forall (y : Real) (Hy : real_lt real_zero y),
  sigT (fun x : Real => real_eq (cauchy_real_exp x) y).
Proof.
  intros y Hy.
  exists (cw_log y Hy).
  exact (cw_log_exp_right y Hy).
Qed.

(* K3: range characterization, the second direction: some x with e^x == y gives 0 < y (positivity + extensional replacement). *)
Lemma exp_image_pos : forall (y : Real),
  sigT (fun x : Real => real_eq (cauchy_real_exp x) y) -> real_lt real_zero y.
Proof.
  intros y [x Hxy].
  apply (real_lt_eq_lt real_zero (cauchy_real_exp x) y).
  - apply cauchy_real_exp_pos.
  - exact Hxy.
Qed.

(* K4: log reflects the order (image-side completeness): log a < log b gives a < b.
   exp order-preserving + the right inverse (cw_log_exp_right) + an extensionality chain (real_eq_lt_lt / real_lt_eq_lt). *)
Lemma cw_log_reflects_lt : forall (a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt (cw_log a Ha) (cw_log b Hb) -> real_lt a b.
Proof.
  intros a b Ha Hb Hlog.
  assert (Hexp : real_lt (cauchy_real_exp (cw_log a Ha))
                         (cauchy_real_exp (cw_log b Hb))).
  { apply (cauchy_real_exp_mono (cw_log a Ha) (cw_log b Hb)). exact Hlog. }
  apply (real_lt_eq_lt a (cauchy_real_exp (cw_log b Hb)) b).
  - apply (real_eq_lt_lt a (cauchy_real_exp (cw_log a Ha))
                          (cauchy_real_exp (cw_log b Hb))).
    + apply real_eq_sym. exact (cw_log_exp_right a Ha).
    + exact Hexp.
  - exact (cw_log_exp_right b Hb).
Qed.

(* K5 (structural theorem assembly): exp is an order embedding (order-preserving in both directions), and its being a group
   homomorphism/injection/surjection/onto its range is the Set-layer construction of paper-3's
   "order-preserving group isomorphism". *)
Lemma exp_order_embedding : forall x y : Real,
  And (real_lt x y -> real_lt (cauchy_real_exp x) (cauchy_real_exp y))
      (real_lt (cauchy_real_exp x) (cauchy_real_exp y) -> real_lt x y).
Proof.
  intros x y.
  split.
  - intro Hxy. apply (cauchy_real_exp_mono x y). exact Hxy.
  - intro Hexp. apply (exp_reflects_lt x y). exact Hexp.
Qed.

End ExpLogGroupIso.
(* ================================================================ *)
(* T3.3 (paper-3, incorporated): the exp inequality family (responding to S4). *)
(* (1) real_exp_ge_linear: 0 < t gives 1 + t < e^t (non-eps, an upgrade of the eps version).   *)
(* (2) real_exp_le_inv_one_minus: 0 < x ⟹ x < 1 ⟹ e^x ≤ 1/(1−x)        *)
(* (3) real_exp_abs_minus_one_eps: |e^x − 1| ≤ |x|·e^{|x|} + eps       *)
(*    (the non-eps version needs the trichotomy to decide the sign of the gap; this is the eps-margin form at that boundary).    *)
(* Discipline: Set layer, purely constructive, zero classical axioms, zero admissions.        *)
(* Dependencies: exp_partial/q_pow/q_fact (QExpPartial), real_abs/real_inv_pos. *)
(* ================================================================ *)
Section ExpInequalities.
(* ==================== Q layer: geometric partial sums and lower bounds for tails ==================== *)

(* Geometric partial sum Σ_{k=0}^n x^k (a 0-based Fixpoint isomorphic to exp_partial). *)
Fixpoint geom_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => geom_partial m x + q_pow x (Datatypes.S m)
  end.

(* 1 ≤ k! (a factorial lower bound, the basis of the termwise 1/k! ≤ 1). *)
Lemma q_fact_ge_one : forall n : nat, QleT' 1 (q_fact n).
Proof.
  intro n. apply Qle_to_QleT'.
  induction n as [| m IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (q_fact m) _).
    + exact IH.
    + apply (Qle_trans _ (1 * q_fact m) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qmult_le_compat_r 1 (Z.of_nat (Datatypes.S m) # 1) (q_fact m)).
        -- unfold Qle. simpl. lia.
        -- apply (Qlt_le_weak 0 (q_fact m)). apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* Tail lower bound: n ≥ 2 and x ≥ 0 give x²/2 ≤ exp_partial n x − 1 − x (Σ_{k≥2} x^k/k! ≥ x²/2). *)
Lemma exp_partial_tail_ge_sq : forall (n : nat) (x : Q),
  (2 <= n)%nat -> QleT' 0 x ->
  QleT' (Qmult (Qmult x x) (1 # 2)) (exp_partial n x - 1 - x).
Proof.
  intros n x Hn Hx.
  apply Qle_to_QleT'.
  destruct n as [|[|m']].
  - lia.
  - lia.
  - induction m' as [| m'' IH].
    + simpl.
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
    + simpl.
      assert (Hre : exp_partial (Datatypes.S (Datatypes.S m'')) x +
                  q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m''))) - 1 - x ==
                  (exp_partial (Datatypes.S (Datatypes.S m'')) x - 1 - x) +
                  q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m'')))).
      { unfold Qdiv. ring. }
      rewrite Hre.
      apply (Qle_trans _ (exp_partial (Datatypes.S (Datatypes.S m'')) x - 1 - x) _).
      { assert (Hn' : (2 <= Datatypes.S (Datatypes.S m''))%nat) by lia.
        exact (IH Hn'). }
      { apply (Qle_trans _ ((exp_partial (Datatypes.S (Datatypes.S m'')) x - 1 - x) + 0) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qplus_le_compat (exp_partial (Datatypes.S (Datatypes.S m'')) x - 1 - x)
                                 (exp_partial (Datatypes.S (Datatypes.S m'')) x - 1 - x)
                                 0 (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m''))))).
          { apply Qle_refl. }
          { unfold Qdiv.
            apply Qmult_le_0_compat.
            { apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx. }
            { apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m'')))))).
              apply (Qinv_lt_0_compat (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m''))))).
              apply QltT_to_Qlt. apply q_fact_pos. } } } }
Qed.

(* Telescoping: (1−x)·geom_partial n x == 1 − x^{S n}. *)
Lemma geom_mult_minus : forall (n : nat) (x : Q),
  QeqT (Qmult (1 - x) (geom_partial n x)) (1 - q_pow x (Datatypes.S n)).
Proof.
  induction n as [| m IH]; intro x.
  - (* n = 0: Qmult (1−x) 1 == 1 − x·1 *)
    change (Qmult (1 - x) (geom_partial 0 x)) with (Qmult (1 - x) 1).
    change (q_pow x (Datatypes.S 0)) with (q_pow x 1).
    change (q_pow x 1) with (x * 1).
    apply qeq_imp_qeqT.
    ring.
  - (* n = S m: (1−x)·(g_m + x^{S m}) == 1 − x^{S(S m)} *)
    change (Qmult (1 - x) (geom_partial (Datatypes.S m) x)) with
           (Qmult (1 - x) (geom_partial m x + q_pow x (Datatypes.S m))).
    apply qeq_imp_qeqT.
    rewrite (Qmult_plus_distr_r (1 - x) (geom_partial m x) (q_pow x (Datatypes.S m))).
    rewrite (qeqT_imp_qeq _ _ (IH x)).
    change (q_pow x (Datatypes.S (Datatypes.S m))) with (x * q_pow x (Datatypes.S m)).
    ring.
Qed.

(* Reciprocal upper bound in the times-a-positive form: 0 < b and a·b ≤ 1 give a ≤ Qinv b
   (a == (a·b)·Qinv b ≤ 1·Qinv b == Qinv b). *)
Lemma q_le_inv_mult : forall (a b : Q), QltT 0 b -> QleT' (Qmult a b) 1 -> QleT' a (Qinv b).
Proof.
  intros a b Hb Hle.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qmult (Qmult a b) (Qinv b)) _).
  - (* a ≤ (a·b)·Qinv b: a == a·(b·Qinv b) == (a·b)·Qinv b *)
    assert (Heq : Qmult (Qmult a b) (Qinv b) == a).
    { rewrite <- (Qmult_assoc a b (Qinv b)).
      rewrite (Qmult_inv_r b).
      - ring.
      - intro Heq0. destruct (q_neq_of_lt _ Hb (qeq_imp_qeqT _ _ Heq0)). }
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Heq.
  - (* (a·b)·Qinv b ≤ 1·Qinv b == Qinv b *)
    apply (Qle_trans _ (1 * Qinv b) _).
    + apply (Qmult_le_compat_r (Qmult a b) 1 (Qinv b)).
      * apply QleT'_to_Qle. exact Hle.
      * apply (Qlt_le_weak 0 (Qinv b)). apply (Qinv_lt_0_compat b). apply QltT_to_Qlt. exact Hb.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* Geometric partial sum ≤ 1/(1−x) for 0 ≤ x < 1 ((1−x)·g_n == 1 − x^{S n} ≤ 1 + q_le_inv_mult). *)
Lemma geom_partial_le_inv : forall (n : nat) (x : Q),
  QleT' 0 x -> QltT x 1 -> QleT' (geom_partial n x) (Qinv (1 - x)).
Proof.
  intros n x Hx Hx1.
  apply (q_le_inv_mult (geom_partial n x) (1 - x)).
  - apply Qlt_to_QltT. apply (proj1 (Qlt_minus_iff x 1)). apply QltT_to_Qlt. exact Hx1.
  - apply Qle_to_QleT'.
    assert (Hgm : Qmult (geom_partial n x) (1 - x) == 1 - q_pow x (Datatypes.S n)).
    { transitivity (Qmult (1 - x) (geom_partial n x)).
      - apply Qmult_comm.
      - apply (qeqT_imp_qeq _ _ (geom_mult_minus n x)). }
    rewrite Hgm.
    apply (proj2 (Qle_minus_iff (1 - q_pow x (Datatypes.S n)) 1)).
    assert (Hsh : 1 - (1 - q_pow x (Datatypes.S n)) == q_pow x (Datatypes.S n)) by ring.
    rewrite Hsh.
    apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx.
Qed.

(* Geometric − exp ≥ x²/2: for n ≥ 2 and x ≥ 0 (the k=2 term x²(1−1/2!) is kept; the rest are nonnegative). *)
Lemma geom_minus_exp_ge_sq : forall (n : nat) (x : Q),
  (2 <= n)%nat -> QleT' 0 x ->
  QleT' (Qmult (Qmult x x) (1 # 2)) (geom_partial n x - exp_partial n x).
Proof.
  intros n x Hn Hx.
  apply Qle_to_QleT'.
  destruct n as [|[|m']].
  - lia.
  - lia.
  - induction m' as [| m'' IH].
    + simpl.
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
    + simpl.
      assert (Hre : geom_partial (Datatypes.S (Datatypes.S m'')) x +
                  q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) -
                  (exp_partial (Datatypes.S (Datatypes.S m'')) x +
                   q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m'')))) ==
                  (geom_partial (Datatypes.S (Datatypes.S m'')) x - exp_partial (Datatypes.S (Datatypes.S m'')) x) +
                  (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) -
                   q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m''))))).
      { unfold Qdiv. ring. }
      rewrite Hre.
      apply (Qle_trans _ (geom_partial (Datatypes.S (Datatypes.S m'')) x - exp_partial (Datatypes.S (Datatypes.S m'')) x) _).
      { assert (Hn' : (2 <= Datatypes.S (Datatypes.S m''))%nat) by lia.
        exact (IH Hn'). }
      { apply (Qle_trans _ ((geom_partial (Datatypes.S (Datatypes.S m'')) x - exp_partial (Datatypes.S (Datatypes.S m'')) x) + 0) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qplus_le_compat (geom_partial (Datatypes.S (Datatypes.S m'')) x - exp_partial (Datatypes.S (Datatypes.S m'')) x)
                                 (geom_partial (Datatypes.S (Datatypes.S m'')) x - exp_partial (Datatypes.S (Datatypes.S m'')) x)
                                 0 (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) -
                                    q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m''))))).
          { apply Qle_refl. }
          { apply (proj1 (Qle_minus_iff (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m''))))
                                        (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m'')))))).
            unfold Qdiv.
            apply (Qle_trans _ (Qmult 1 (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))))) _).
            { apply (Qle_trans _ (Qmult (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m'')))))
                                        (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))))) _).
              { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
              { apply (Qmult_le_compat_r (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m''))))) 1
                                         (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m''))))).
                { apply (Qle_trans _ (Qinv 1) _).
                  { apply QleT'_to_Qle. apply (q_inv_le_contravar (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m'')))) 1).
                    { apply q_fact_pos. }
                    { apply Qlt_to_QltT. change (Qlt 0 1). unfold Qlt. simpl. lia. }
                    { exact (q_fact_ge_one (Datatypes.S (Datatypes.S (Datatypes.S m'')))). } }
                  { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity. } }
                { apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx. } } }
            { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. } } } }
Qed.

(* ==================== Q layer: the truncated version of |e^x − 1| ≤ |x|·e^{|x|} ==================== *)

(* Shifted partial sum Σ_{k=0}^m x^k/q_fact (k+1) (the truncation of e^x − 1 = x·Σ x^k/(k+1)!). *)
Fixpoint exp_shift_partial (m : nat) (x : Q) : Q :=
  match m with
  | 0%nat => 1%Q
  | Datatypes.S k => exp_shift_partial k x + q_pow x (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k))
  end.

(* A pure-variable ring identity (ring is unreliable on goals inside proofs that mention
   Fixpoint atoms, so an independent pure-variable lemma is taken and applied instead) —
   the proof shape of the exp_partial_shift_factor induction step. *)
Lemma q_ring_shift_factor : forall (a s p f : Q),
  QeqT (Qplus (Qmult a s) (Qmult (Qmult a p) f)) (Qmult a (Qplus s (Qmult p f))).
Proof.
  intros a s p f. apply qeq_imp_qeqT. ring.
Qed.

(* Factoring out: exp_partial (S m) x − 1 == x · exp_shift_partial m x. *)
Lemma exp_partial_shift_factor : forall (m : nat) (x : Q),
  QeqT (exp_partial (Datatypes.S m) x - 1) (x * exp_shift_partial m x).
Proof.
  induction m as [| k IH]; intro x; simpl.
  - apply qeq_imp_qeqT. field.
  - assert (Hre : (exp_partial (Datatypes.S k) x +
                   q_pow x (Datatypes.S (Datatypes.S k)) / q_fact (Datatypes.S (Datatypes.S k))) - 1 ==
                  (exp_partial (Datatypes.S k) x - 1) +
                  q_pow x (Datatypes.S (Datatypes.S k)) / q_fact (Datatypes.S (Datatypes.S k))).
    { unfold Qdiv. ring. }
    apply qeq_imp_qeqT.
    rewrite Hre.
    rewrite (qeqT_imp_qeq _ _ (IH x)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ x (Datatypes.S k))).
    unfold Qdiv.
    apply (qeqT_imp_qeq _ _ (q_ring_shift_factor x (exp_shift_partial k x) (q_pow x (Datatypes.S k))
                                (Qinv (q_fact (Datatypes.S (Datatypes.S k)))))).
Qed.

(* The absolute value of the shifted partial sum is ≤ the nonneg-substituted sum: |Σ x^k/(k+1)!| ≤ Σ |x|^k/(k+1)!. *)
Lemma exp_shift_partial_abs : forall (m : nat) (x : Q),
  QleT' (Qabs (exp_shift_partial m x)) (exp_shift_partial m (Qabs x)).
Proof.
  induction m as [| k IH]; intro x.
  - simpl. apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    change (exp_shift_partial (Datatypes.S k) x) with
           (exp_shift_partial k x + q_pow x (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k))).
    change (exp_shift_partial (Datatypes.S k) (Qabs x)) with
           (exp_shift_partial k (Qabs x) + q_pow (Qabs x) (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k))).
    apply (Qle_trans _ (Qabs (exp_shift_partial k x) + Qabs (q_pow x (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k)))) _).
    + apply Qabs_triangle.
    + apply (Qplus_le_compat (Qabs (exp_shift_partial k x)) (exp_shift_partial k (Qabs x))
                             (Qabs (q_pow x (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k))))
                             (q_pow (Qabs x) (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k)))).
      * exact (QleT'_to_Qle _ _ (IH x)).
      * assert (Habs : Qabs (q_pow x (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k))) ==
                       q_pow (Qabs x) (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k))).
        { unfold Qdiv.
          rewrite Qabs_Qmult.
          rewrite (qeqT_imp_qeq _ _ (q_pow_abs x (Datatypes.S k))).
          rewrite (Qabs_pos (Qinv (q_fact (Datatypes.S (Datatypes.S k))))).
          - reflexivity.
          - apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S k))))).
            apply (Qinv_lt_0_compat (q_fact (Datatypes.S (Datatypes.S k)))).
            apply QltT_to_Qlt. apply q_fact_pos. }
        apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs.
Qed.

(* Factorial monotonicity: q_fact k ≤ q_fact (S k). *)
Lemma q_fact_succ_le : forall k : nat, QleT' (q_fact k) (q_fact (Datatypes.S k)).
Proof.
  intro k.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (1 * q_fact k) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qmult_le_compat_r 1 (Z.of_nat (Datatypes.S k) # 1) (q_fact k)).
    + unfold Qle. simpl. lia.
    + apply (Qlt_le_weak 0 (q_fact k)). apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* Shifted partial sum ≤ exp_partial: for x ≥ 0 (termwise 1/(k+1)! ≤ 1/k!). *)
Lemma exp_shift_partial_le_exp : forall (m : nat) (x : Q), QleT' 0 x ->
  QleT' (exp_shift_partial m x) (exp_partial m x).
Proof.
  induction m as [| k IH]; intro x; intro Hx.
  - apply Qle_to_QleT'. simpl. apply Qle_refl.
  - apply Qle_to_QleT'.
    change (exp_shift_partial (Datatypes.S k) x) with
           (exp_shift_partial k x + q_pow x (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k))).
    change (exp_partial (Datatypes.S k) x) with
           (exp_partial k x + q_pow x (Datatypes.S k) / q_fact (Datatypes.S k)).
    apply (Qplus_le_compat (exp_shift_partial k x) (exp_partial k x)
                           (q_pow x (Datatypes.S k) / q_fact (Datatypes.S (Datatypes.S k)))
                           (q_pow x (Datatypes.S k) / q_fact (Datatypes.S k))).
    + exact (QleT'_to_Qle _ _ (IH x Hx)).
    + apply QleT'_to_Qle. apply (q_le_div_le (q_pow x (Datatypes.S k)) (q_fact (Datatypes.S (Datatypes.S k)))
                         (q_pow x (Datatypes.S k)) (q_fact (Datatypes.S k))).
      * apply q_fact_pos.
      * apply q_fact_pos.
      * apply Qle_to_QleT'. apply (Qle_trans _ (Qmult (q_fact (Datatypes.S k)) (q_pow x (Datatypes.S k))) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qle_trans _ (Qmult (q_fact (Datatypes.S (Datatypes.S k))) (q_pow x (Datatypes.S k))) _).
          { apply (Qmult_le_compat_r (q_fact (Datatypes.S k)) (q_fact (Datatypes.S (Datatypes.S k)))
                                     (q_pow x (Datatypes.S k))).
            { exact (QleT'_to_Qle _ _ (q_fact_succ_le (Datatypes.S k))). }
            { apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx. } }
          { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. } }
Qed.

(* |exp_partial n x − 1| ≤ |x|·exp_partial n |x| (a global pointwise bound, no sign premise). *)
Lemma exp_partial_abs_diff_le : forall (n : nat) (x : Q),
  QleT' (Qabs (exp_partial n x - 1)) (Qmult (Qabs x) (exp_partial n (Qabs x))).
Proof.
  intros n x.
  apply Qle_to_QleT'.
  destruct n as [| m].
  - simpl.
    apply Qmult_le_0_compat.
    + apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply Qle_0_1.
  - rewrite (qeqT_imp_qeq _ _ (exp_partial_shift_factor m x)).
    assert (Habs : Qabs (x * exp_shift_partial m x) == Qmult (Qabs x) (Qabs (exp_shift_partial m x))).
    { apply Qabs_Qmult. }
    rewrite Habs.
    apply (Qle_trans _ (Qmult (Qabs x) (exp_shift_partial m (Qabs x))) _).
    + apply (Qle_trans _ (Qmult (Qabs (exp_shift_partial m x)) (Qabs x)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ (Qmult (exp_shift_partial m (Qabs x)) (Qabs x)) _).
        { apply (Qmult_le_compat_r (Qabs (exp_shift_partial m x)) (exp_shift_partial m (Qabs x)) (Qabs x)).
          { apply QleT'_to_Qle. apply (exp_shift_partial_abs m x). }
          { apply Qabs_nonneg. } }
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    + apply (Qle_trans _ (Qmult (Qabs x) (exp_partial m (Qabs x))) _).
      * apply (Qle_trans _ (Qmult (exp_shift_partial m (Qabs x)) (Qabs x)) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qle_trans _ (Qmult (exp_partial m (Qabs x)) (Qabs x)) _).
          { apply (Qmult_le_compat_r (exp_shift_partial m (Qabs x)) (exp_partial m (Qabs x)) (Qabs x)).
            { apply QleT'_to_Qle. apply (exp_shift_partial_le_exp m (Qabs x)). apply Qle_to_QleT'. apply Qabs_nonneg. }
            { apply Qabs_nonneg. } }
          { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. } }
      * apply (Qle_trans _ (Qmult (exp_partial (Datatypes.S m) (Qabs x)) (Qabs x)) _).
        { apply (Qle_trans _ (Qmult (exp_partial m (Qabs x)) (Qabs x)) _).
          { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
          { apply (Qmult_le_compat_r (exp_partial m (Qabs x)) (exp_partial (Datatypes.S m) (Qabs x)) (Qabs x)).
            { simpl.
              apply (Qle_trans _ (exp_partial m (Qabs x) + 0) _).
              { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
              { apply (Qplus_le_compat (exp_partial m (Qabs x)) (exp_partial m (Qabs x))
                                       0 (q_pow (Qabs x) (Datatypes.S m) / q_fact (Datatypes.S m))).
                { apply Qle_refl. }
                { unfold Qdiv.
                  apply Qmult_le_0_compat.
                  { apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. apply Qabs_nonneg. }
                  { apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S m)))).
                    apply (Qinv_lt_0_compat (q_fact (Datatypes.S m))).
                    apply QltT_to_Qlt. apply q_fact_pos. } } } }
            { apply Qabs_nonneg. } } }
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
Qed.

(* Strict order preservation under multiplying a positive (with the right factor commuted): a < b and 0 < c give a·c < c·b
   (Qmult_lt_compat_r gives a·c < b·c, and comm rewrites the RHS — there is no Qmult_lt_compat_l). *)
Lemma q_lt_mult_comm_r : forall (a b c : Q), QltT a b -> QltT 0 c -> QltT (Qmult a c) (Qmult c b).
Proof.
  intros a b c Hab Hc.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ (Qmult b c) _).
  - apply (Qmult_lt_compat_r a b c). apply QltT_to_Qlt. exact Hc. apply QltT_to_Qlt. exact Hab.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ==================== Real layer: the exp inequality family ==================== *)

(* T3.3-(1) (main theorem): 0 < t gives 1 + t < e^t.
   Witness eps' := eps0²/2: pointwise exp_partial n (u n) − 1 − u n ≥ (u n)²/2 > eps0²/2. *)
Lemma real_exp_ge_linear : forall t : Real, real_lt real_zero t ->
  real_lt (real_plus real_one t) (cauchy_real_exp t).
Proof.
  intros t Ht.
  destruct t as [u Hu].
  destruct Ht as [eps0 [Heps0 [N0 HN0]]].
  set (eps' := Qmult (Qmult eps0 eps0) (1 # 2)).
  assert (Heps' : QltT 0 eps').
  { unfold eps'. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult eps0 eps0) (1 # 2)).
    - apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  unfold real_lt.
  exists eps'. split.
  - exact Heps'.
  - exists (Nat.max N0 2)%nat.
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (HnN0 : (N0 <= n)%nat) by lia.
    assert (Hn2 : (2 <= n)%nat) by lia.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_exp_proj (existT (fun s : Qseq => cauchy s) u Hu) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (existT (fun s : Qseq => cauchy s) u Hu) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
    assert (Hsh : exp_partial n (u n) - (1 + u n) == exp_partial n (u n) - 1 - u n) by ring.
    rewrite Hsh.
    assert (Hun : Qlt eps0 (u n)).
    { apply (Qlt_le_trans _ (u n - 0) _).
      - apply QltT_to_Qlt. apply (HN0 n). apply NatLe_lift. exact HnN0.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hun0 : Qlt 0 (u n)).
    { apply (Qlt_trans _ eps0 _). apply QltT_to_Qlt. exact Heps0. exact Hun. }
    apply (Qlt_le_trans _ (Qmult (Qmult (u n) (u n)) (1 # 2)) _).
    + unfold eps'.
      apply (Qmult_lt_compat_r (Qmult eps0 eps0) (Qmult (u n) (u n)) (1 # 2)).
      * change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
      * apply (Qlt_trans _ (Qmult eps0 (u n)) _).
        -- apply QltT_to_Qlt. apply (q_lt_mult_comm_r eps0 (u n) eps0). apply Qlt_to_QltT. exact Hun. exact Heps0.
        -- apply QltT_to_Qlt. apply (q_lt_mult_comm_r eps0 (u n) (u n)). apply Qlt_to_QltT. exact Hun. apply Qlt_to_QltT. exact Hun0.
    + apply QleT'_to_Qle. apply (exp_partial_tail_ge_sq n (u n) Hn2).
      apply Qle_to_QleT'. apply (Qlt_le_weak 0 (u n)). exact Hun0.
Qed.

(* T3.3-(2): 0 < x ⟹ x < 1 ⟹ e^x ≤ 1/(1−x)
   Witness eps' := eps0²/2: pointwise Qinv (1 − u n) − exp_partial n (u n) ≥ (u n)²/2 > eps0²/2. *)
Lemma real_exp_le_inv_one_minus : forall (x : Real)
  (Hx0 : real_lt real_zero x) (Hx1 : real_lt x real_one),
  real_le (cauchy_real_exp x)
          (real_inv_pos (real_plus real_one (real_opp x)) (real_lt_opp_plus x real_one Hx1)).
Proof.
  intros x Hx0 Hx1.
  set (Hx01 := real_lt_opp_plus x real_one Hx1).
  destruct x as [u Hu].
  destruct Hx0 as [eps0 [Heps0 [N0 HN0]]].
  destruct Hx1 as [eps1 [Heps1 [N1 HN1]]].
  destruct (real_inv_proj (real_plus real_one (real_opp (existT (fun s : Qseq => cauchy s) u Hu)))
                          Hx01)
    as [N_inv HN_inv].
  set (eps' := Qmult (Qmult eps0 eps0) (1 # 2)).
  assert (Heps' : QltT 0 eps').
  { unfold eps'. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult eps0 eps0) (1 # 2)).
    - apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  unfold real_le.
  left.
  unfold real_lt.
  exists eps'. split.
  - exact Heps'.
  - exists (Nat.max N0 (Nat.max N1 (Nat.max N_inv 2)))%nat.
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (HnN0 : (N0 <= n)%nat) by lia.
    assert (HnN1 : (N1 <= n)%nat) by lia.
    assert (Hn2 : (2 <= n)%nat) by lia.
    assert (HnNinv : (N_inv <= n)%nat) by lia.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_exp_proj (existT (fun s : Qseq => cauchy s) u Hu) n)).
    assert (Hinvn : projT1 (real_inv_pos (real_plus real_one (real_opp (existT (fun s : Qseq => cauchy s) u Hu)))
                                         Hx01) n ==
                     Qinv (1 - u n)).
    { rewrite (qeqT_imp_qeq _ _ (HN_inv n (NatLe_lift _ _ HnNinv))).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_opp (existT (fun s : Qseq => cauchy s) u Hu)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (existT (fun s : Qseq => cauchy s) u Hu) n)).
      reflexivity. }
    rewrite Hinvn.
    assert (Hun : Qlt eps0 (u n)).
    { apply (Qlt_le_trans _ (u n - 0) _).
      - apply QltT_to_Qlt. apply (HN0 n). apply NatLe_lift. exact HnN0.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hun0 : Qlt 0 (u n)).
    { apply (Qlt_trans _ eps0 _). apply QltT_to_Qlt. exact Heps0. exact Hun. }
    assert (Hun1 : Qlt (u n) 1).
    { apply (Qlt_trans _ (1 - eps1) _).
      - apply (proj2 (Qlt_minus_iff (u n) (1 - eps1))).
        assert (Hm : Qlt 0 ((1 - u n) - eps1)).
        { apply (proj1 (Qlt_minus_iff eps1 (1 - u n))).
          apply QltT_to_Qlt. apply (HN1 n). apply NatLe_lift. exact HnN1. }
        assert (Hsh : (1 - eps1) - u n == (1 - u n) - eps1) by ring.
        rewrite Hsh. exact Hm.
      - apply (proj2 (Qlt_minus_iff (1 - eps1) 1)).
        assert (Hsh : 1 - (1 - eps1) == eps1) by ring.
        rewrite Hsh. exact (QltT_to_Qlt _ _ Heps1). }
    assert (Hgap : Qle (Qmult (Qmult (u n) (u n)) (1 # 2))
                       (Qinv (1 - u n) - exp_partial n (u n))).
    { assert (Hg1 : Qle 0 (Qinv (1 - u n) - geom_partial n (u n))).
      { apply (proj1 (Qle_minus_iff (geom_partial n (u n)) (Qinv (1 - u n)))).
        apply QleT'_to_Qle. apply (geom_partial_le_inv n (u n)).
        - apply Qle_to_QleT'. apply (Qlt_le_weak 0 (u n)). exact Hun0.
        - apply Qlt_to_QltT. exact Hun1. }
      assert (Hg2 : Qle (Qmult (Qmult (u n) (u n)) (1 # 2)) (geom_partial n (u n) - exp_partial n (u n))).
      { apply QleT'_to_Qle. apply (geom_minus_exp_ge_sq n (u n) Hn2). apply Qle_to_QleT'. apply (Qlt_le_weak 0 (u n)). exact Hun0. }
      assert (Hre : Qinv (1 - u n) - exp_partial n (u n) ==
                    (Qinv (1 - u n) - geom_partial n (u n)) + (geom_partial n (u n) - exp_partial n (u n))) by ring.
      rewrite Hre.
      apply (Qle_trans _ (geom_partial n (u n) - exp_partial n (u n)) _).
      + exact Hg2.
      + apply (Qle_trans _ (Qplus 0 (geom_partial n (u n) - exp_partial n (u n))) _).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        * apply (Qplus_le_compat 0 (Qinv (1 - u n) - geom_partial n (u n))
                                 (geom_partial n (u n) - exp_partial n (u n))
                                 (geom_partial n (u n) - exp_partial n (u n))).
          -- exact Hg1.
          -- apply Qle_refl. }
    apply (Qlt_le_trans _ (Qmult (Qmult (u n) (u n)) (1 # 2)) _).
    + unfold eps'.
      apply (Qmult_lt_compat_r (Qmult eps0 eps0) (Qmult (u n) (u n)) (1 # 2)).
      * change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
      * apply (Qlt_trans _ (Qmult eps0 (u n)) _).
        -- apply QltT_to_Qlt. apply (q_lt_mult_comm_r eps0 (u n) eps0). apply Qlt_to_QltT. exact Hun. exact Heps0.
        -- apply QltT_to_Qlt. apply (q_lt_mult_comm_r eps0 (u n) (u n)). apply Qlt_to_QltT. exact Hun. apply Qlt_to_QltT. exact Hun0.
    + exact Hgap.
Qed.

(* T3.3-(3) (the eps-margin form): |e^x − 1| ≤ |x|·e^{|x|} + eps.
   In the non-eps version the gap = |x|·e^{|x|} − |e^x − 1| vanishes at x = 0 and is positive for x ≠ 0,
   which needs the trichotomy to decide (at that boundary) — the eps-margin form closes it pointwise. *)
Lemma real_exp_abs_minus_one_eps : forall (x eps : Real), real_lt real_zero eps ->
  real_le (real_abs (real_plus (cauchy_real_exp x) (real_opp real_one)))
          (real_plus (real_mult (real_abs x) (cauchy_real_exp (real_abs x))) eps).
Proof.
  intros x eps Heps.
  destruct x as [u Hu].
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  unfold real_le.
  left.
  unfold real_lt.
  exists eps0. split.
  - exact Heps0.
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hepsn : QltT eps0 (projT1 eps n - 0)).
    { apply (HN0 n). exact Hn. }
    assert (Hepsn_le : Qle eps0 (projT1 eps n)).
    { apply (Qle_trans _ (projT1 eps n - 0) _).
      - apply (Qlt_le_weak _ _). apply QltT_to_Qlt. exact Hepsn.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                      (real_opp real_one)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                            (real_opp real_one) n)).
    rewrite (qeqT_imp_qeq _ _ (real_exp_proj (existT (fun s : Qseq => cauchy s) u Hu) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_abs (existT (fun s : Qseq => cauchy s) u Hu))
                                       (cauchy_real_exp (real_abs (existT (fun s : Qseq => cauchy s) u Hu))))
                            eps n)).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_abs (existT (fun s : Qseq => cauchy s) u Hu))
                            (cauchy_real_exp (real_abs (existT (fun s : Qseq => cauchy s) u Hu))) n)).
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj (existT (fun s : Qseq => cauchy s) u Hu) n)).
    rewrite (qeqT_imp_qeq _ _ (real_exp_proj (real_abs (existT (fun s : Qseq => cauchy s) u Hu)) n)).
    change (projT1 (real_abs (existT (fun s : Qseq => cauchy s) u Hu)) n) with (Qabs (u n)).
    assert (Hd : Qle 0 (Qmult (Qabs (u n)) (exp_partial n (Qabs (u n))) - Qabs (exp_partial n (u n) - 1))).
    { apply (proj1 (Qle_minus_iff (Qabs (exp_partial n (u n) - 1))
                                  (Qmult (Qabs (u n)) (exp_partial n (Qabs (u n)))))).
      apply QleT'_to_Qle. apply (exp_partial_abs_diff_le n (u n)). }
    assert (Hsh : (Qmult (Qabs (u n)) (exp_partial n (Qabs (u n))) + projT1 eps n) -
                  Qabs (exp_partial n (u n) - 1) ==
                  (Qmult (Qabs (u n)) (exp_partial n (Qabs (u n))) - Qabs (exp_partial n (u n) - 1)) +
                  projT1 eps n) by ring.
    rewrite Hsh.
    apply (Qlt_le_trans _ (projT1 eps n) _).
    + apply (Qlt_le_trans _ (projT1 eps n - 0) _).
      * apply QltT_to_Qlt. exact Hepsn.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ (projT1 eps n + 0) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ (Qplus (projT1 eps n)
                                  (Qmult (Qabs (u n)) (exp_partial n (Qabs (u n))) - Qabs (exp_partial n (u n) - 1))) _).
        { apply (Qplus_le_compat (projT1 eps n) (projT1 eps n) 0
                                 (Qmult (Qabs (u n)) (exp_partial n (Qabs (u n))) - Qabs (exp_partial n (u n) - 1))).
          { apply Qle_refl. }
          { exact Hd. } }
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
Qed.

(* Triple verification: Print Assumptions should report Closed under the global context. *)
End ExpInequalities.


(* ============================================================ *)
(* T2.3 quantitative KV eviction bound (incorporated).          *)
(* Review S2 response: the explicit quantitative connection of   *)
(* db_breaking with the temperature D, the energy bound E_max,   *)
(* and the Lipschitz constant L.                                 *)
(* Structure: P1 the exp_neg difference bound (global, assembled *)
(*   transitively from the real_exp_abs_minus_one_eps material of T3.3). *)
(*   Section RealKVQuantMain: B1 eviction to zero / B2 the structural *)
(*   decomposition (db == invZ·T·|b−b'|) / B3 the analytic bound *)
(*   (Lipschitz scaling + temperature boundedness + product absorption) *)
(*   / B4 the final bound theorem.                               *)
(* Discipline: purely constructive / Set layer / zero admissions / zero *)
(* classical axioms; the honest interface carries only instantiable *)
(* premises (energy_lipschitz / energy_lower / nonnegative symmetric kernel). *)
(* ============================================================ *)
(* ===== Tool 0: replacing the right side of real_le equivalently (the Or decomposition + real_lt_eq_lt). ===== *)
Lemma real_le_eq_r : forall (x y z : Real),
  real_le x y -> real_eq y z -> real_le x z.
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy as [Hlt | Heq].
  - left. apply (real_lt_eq_lt x y z Hlt Hyz).
  - right. apply (real_eq_trans x y z Heq Hyz).
Qed.

(* ===== Tool 1: e^{−u} == e^{−v}·e^{−(u−v)} (exp_neg_plus backwards + ring identities)
   Ring steps: v + (u − v) == u; −(v + (u−v)) == −v + −(u−v) (real_opp_plus);
   e^{a+b} == e^{a}·e^{b} (cauchy_real_exp_plus). *)
Lemma real_exp_neg_split : forall (u v : Real),
  real_eq (real_exp_neg u)
          (real_mult (real_exp_neg v) (real_exp_neg (real_plus u (real_opp v)))).
Proof.
  intros u v.
  assert (Hsum : real_eq (real_plus v (real_plus u (real_opp v))) u).
  {
    apply (real_eq_trans _ (real_plus (real_plus v u) (real_opp v)) _).
    - apply (real_plus_assoc v u (real_opp v)).
    - apply (real_eq_trans _ (real_plus (real_plus u v) (real_opp v)) _).
      + apply (RealSetoid.real_eq_plus_compat (real_plus v u) (real_opp v)
                                              (real_plus u v) (real_opp v)
                                              (real_plus_comm v u) (real_eq_refl (real_opp v))).
      + apply (real_eq_trans _ (real_plus u (real_plus v (real_opp v))) _).
        * apply real_eq_sym. apply (real_plus_assoc u v (real_opp v)).
        * apply (real_eq_trans _ (real_plus u real_zero) _).
          -- apply (RealSetoid.real_eq_plus_compat u (real_plus v (real_opp v))
                                                  u real_zero
                                                  (real_eq_refl u) (real_plus_opp v)).
          -- apply (real_plus_zero u).
  }
  unfold real_exp_neg.
  apply (real_eq_trans _ (cauchy_real_exp (real_opp (real_plus v (real_plus u (real_opp v))))) _).
  - apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_opp_compat u (real_plus v (real_plus u (real_opp v)))).
    apply real_eq_sym.
    exact Hsum.
  - apply (real_eq_trans _ (cauchy_real_exp
                              (real_plus (real_opp v)
                                         (real_opp (real_plus u (real_opp v))))) _).
    + apply cauchy_real_exp_wd.
      apply (real_opp_plus v (real_plus u (real_opp v))).
    + apply (real_eq_trans _ (real_mult (cauchy_real_exp (real_opp v))
                                        (cauchy_real_exp (real_opp (real_plus u (real_opp v))))) _).
      * exact (cauchy_real_exp_plus (real_opp v) (real_opp (real_plus u (real_opp v)))).
      * exact (real_eq_refl _).
Qed.

(* ===== Tool 2a: mult a (opp 1) == opp a (real_mult_opp_l + mult_one wd). ===== *)
Lemma real_mult_opp_one_l : forall (a : Real),
  real_eq (real_mult a (real_opp real_one)) (real_opp a).
Proof.
  intro a.
  apply (real_eq_trans _ (real_opp (real_mult a real_one)) _).
  - apply (real_mult_opp_l a real_one).
  - apply (RealSetoid.real_eq_opp_compat (real_mult a real_one) a).
    apply (real_mult_one a).
Qed.

(* ===== Tool 2: a·(c − 1) == a·c − a (distrib backwards + mult a (−1) == −a). ===== *)
Lemma real_mult_minus_one_distr : forall (a c : Real),
  real_eq (real_mult a (real_plus c (real_opp real_one)))
          (real_plus (real_mult a c) (real_opp a)).
Proof.
  intros a c.
  apply (real_eq_trans _ (real_plus (real_mult a c) (real_mult a (real_opp real_one))) _).
  - apply (real_distrib a c (real_opp real_one)).
  - apply (RealSetoid.real_eq_plus_compat (real_mult a c) (real_mult a (real_opp real_one))
                                          (real_mult a c) (real_opp a)
                                          (real_eq_refl _) (real_mult_opp_one_l a)).
Qed.

(* ===== Tool 3: |e^{−u} − e^{−v}| == e^{−v}·|e^{−(u−v)} − 1| (e^{−v} > 0). ===== *)
Lemma real_exp_neg_diff_abs : forall (u v : Real),
  real_eq (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
          (real_mult (real_exp_neg v)
                     (real_abs (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                          (real_opp real_one)))).
Proof.
  intros u v.
  pose proof (real_exp_neg_split u v) as Hsplit.
  (* Inner difference: e^{−u} − e^{−v} == e^{−v}·(c − 1), with c := e^{−(u−v)}. *)
  assert (Hfac : real_eq (real_plus (real_exp_neg u) (real_opp (real_exp_neg v)))
                         (real_mult (real_exp_neg v)
                                    (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                               (real_opp real_one)))).
  {
    apply (real_eq_trans _ (real_plus (real_mult (real_exp_neg v)
                                                 (real_exp_neg (real_plus u (real_opp v))))
                                      (real_opp (real_exp_neg v))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_exp_neg u) (real_opp (real_exp_neg v))
                                            (real_mult (real_exp_neg v)
                                                       (real_exp_neg (real_plus u (real_opp v))))
                                            (real_opp (real_exp_neg v))
                                            Hsplit (real_eq_refl _)).
    - apply real_eq_sym.
      apply (real_mult_minus_one_distr (real_exp_neg v)
                                       (real_exp_neg (real_plus u (real_opp v)))).
  }
  (* abs: |a·(c−1)| == |a·c − a|; first rewrite to |a·(c−1)|. *)
  apply (real_eq_trans _ (real_abs (real_mult (real_exp_neg v)
                                              (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                                         (real_opp real_one)))) _).
  - apply (real_abs_eq_compat (real_plus (real_exp_neg u) (real_opp (real_exp_neg v)))
                              (real_mult (real_exp_neg v)
                                         (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                                    (real_opp real_one)))
                              Hfac).
  - (* |a·(c−1)| == |a|·|c−1| == a·|c−1| (a = e^{−v} > 0) *)
    apply (real_eq_trans _ (real_mult (real_abs (real_exp_neg v))
                                      (real_abs (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                                           (real_opp real_one)))) _).
    + apply (real_abs_mult_req (real_exp_neg v)
                               (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                          (real_opp real_one))).
    + apply (RealSetoid.real_eq_mult_compat (real_abs (real_exp_neg v)) (real_abs (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                                                                             (real_opp real_one)))
                                            (real_exp_neg v) (real_abs (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                                                                   (real_opp real_one)))
                                            (real_abs_pos_req (real_exp_neg v)
                                                              (real_exp_neg_pos v))
                                            (real_eq_refl _)).
Qed.

(* ===== Tool 4: the |x| restatement of the inner bound |e^{x} − 1| ≤ |x|·e^{|x|} + eps
   (real_exp_abs_minus_one_eps at x := −(u−v), restated via abs_opp). ===== *)
Lemma real_exp_minus_one_abs_bound : forall (u v eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_plus (real_exp_neg (real_plus u (real_opp v)))
                               (real_opp real_one)))
          (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))
                     eps).
Proof.
  intros u v eps Heps.
  pose proof (real_exp_abs_minus_one_eps (real_opp (real_plus u (real_opp v))) eps Heps) as Hx.
  (* Hx : |e^{−(u−v)} − 1| ≤ |−(u−v)|·e^{|−(u−v)|} + eps (the same term after unfolding exp_neg on the left). *)
  assert (Hright : real_eq
    (real_plus (real_mult (real_abs (real_opp (real_plus u (real_opp v))))
                          (cauchy_real_exp (real_abs (real_opp (real_plus u (real_opp v)))))) eps)
    (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                          (cauchy_real_exp (real_abs (real_plus u (real_opp v))))) eps)).
  {
    assert (Hm : real_eq
      (real_mult (real_abs (real_opp (real_plus u (real_opp v))))
                 (cauchy_real_exp (real_abs (real_opp (real_plus u (real_opp v))))))
      (real_mult (real_abs (real_plus u (real_opp v)))
                 (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))).
    {
      apply (RealSetoid.real_eq_mult_compat
               (real_abs (real_opp (real_plus u (real_opp v))))
               (cauchy_real_exp (real_abs (real_opp (real_plus u (real_opp v)))))
               (real_abs (real_plus u (real_opp v)))
               (cauchy_real_exp (real_abs (real_plus u (real_opp v))))).
      - apply (real_abs_opp (real_plus u (real_opp v))).
      - apply cauchy_real_exp_wd.
        apply (real_abs_opp (real_plus u (real_opp v))).
    }
    exact (RealSetoid.real_eq_plus_compat
             (real_mult (real_abs (real_opp (real_plus u (real_opp v))))
                        (cauchy_real_exp (real_abs (real_opp (real_plus u (real_opp v))))))
             eps
             (real_mult (real_abs (real_plus u (real_opp v)))
                        (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))
             eps
             Hm (real_eq_refl eps)).
  }
  (* Left side: the same term as Hx after unfolding exp_neg. *)
  unfold real_exp_neg.
  exact (real_le_eq_r
           (real_abs (real_plus (cauchy_real_exp (real_opp (real_plus u (real_opp v))))
                                (real_opp real_one)))
           (real_plus (real_mult (real_abs (real_opp (real_plus u (real_opp v))))
                                 (cauchy_real_exp (real_abs (real_opp (real_plus u (real_opp v)))))) eps)
           (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                 (cauchy_real_exp (real_abs (real_plus u (real_opp v))))) eps)
           Hx Hright).
Qed.

(* ===== P1 main lemma: |e^{−u} − e^{−v}| ≤ e^{−v}·(|u−v|·e^{|u−v|} + eps). ===== *)
Lemma real_exp_neg_diff_bound : forall (u v eps : Real), real_lt real_zero eps ->
  real_le (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
          (real_mult (real_exp_neg v)
                     (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                           (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))
                                eps)).
Proof.
  intros u v eps Heps.
  (* Chain: |e^{−u}−e^{−v}| == e^{−v}·|c−1| ≤ e^{−v}·(|u−v|·e^{|u−v|} + eps). *)
  apply (real_le_trans
           (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
           (real_mult (real_exp_neg v)
                      (real_abs (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                           (real_opp real_one))))
           (real_mult (real_exp_neg v)
                      (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                            (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))
                                 eps))).
  - (* First segment: |…| == e^{−v}·|c−1|, so ≤ (the eq branch). *)
    exact (RealSetoid.real_eq_le _ _ (real_exp_neg_diff_abs u v)).
  - (* Second segment: e^{−v}·|c−1| ≤ e^{−v}·(|u−v|·e^{|u−v|} + eps) (order preserved by multiplying a positive factor). *)
    apply (real_le_mult_compat_r (real_exp_neg v)
                                 (real_abs (real_plus (real_exp_neg (real_plus u (real_opp v)))
                                                      (real_opp real_one)))
                                 (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                                       (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))
                                            eps)).
    + apply (RealSetoid.real_lt_le_iff_req real_zero (real_exp_neg v)).
      left. exact (real_exp_neg_pos v).
    + exact (real_exp_minus_one_abs_bound u v eps Heps).
Qed.
