(* ConstructiveWorld-Set — cross-entropy decomposition and the
   training-objective equivalence. *)

(** * UpReqTrainingEquiv: cross-entropy, its entropy-plus-KL
      decomposition, and the equivalence of cross-entropy and KL
      minimization.

    Mission.  Defines [real_cross_entropy] on the [Real] carrier, proves
      the decomposition [real_cross_entropy_decomp] (cross-entropy =
      entropy term + KL term) and the pointwise expansion
      [real_kl_term_expand], and establishes [real_training_equivalence]:
      for a fixed target [p], cross-entropy descent implies KL descent.

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp] of
      this development.

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name whose statement names are carried over
      verbatim (statement-face Set-carrier completion); the identity
      cross-entropy = entropy + KL divergence (a corollary of Gibbs'
      inequality) and the training-objective equivalence principle.

    Constructivity.  Every statement closes with [Qed]; no proof is left
      open; the proof bodies introduce no assumption beyond the statement
      premises.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqTrainingEquiv.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 000160bc]. *)

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

(* ------------------------------------------------------------ *)
(* Statement 0: the definition [real_cross_entropy].             *)

(*   [Id]-form counterpart: [cross_entropy] in                   *)
(*     [S04_RealExpLogConv]:                                     *)
(*     Definition cross_entropy (p q : S -> R) : R :=            *)

(*   The [Real]-carrier copy keeps the same list carrier: the    *)
(*   summation is [real_list_sum X _ l]; the only premise-face   *)
(*   difference is that [real_log] carries a positivity witness  *)
(*   (its definition face in [S07_RealSetoidExpLog]), so [Hq] is *)
(*   moved forward — the same position as [real_entropy_dist] in *)
(*   [UpReqTempDefs].                                            *)
(* ------------------------------------------------------------ *)
Definition real_cross_entropy
  (X : Type) (l : list X) (p q : X -> Real)
  (Hq : forall s : X, real_lt real_zero (q s)) : Real :=
  real_list_sum X (fun s => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l.

(* ------------------------------------------------------------ *)
(* Statement 1a: [(-x) + (x + y) == y] — the cancellation-chain  *)
(*   primitive, same family as the [Hin] block of                *)
(*   [real_kl_sum_decomp] in [S08_RealMainlineDPO], with the     *)
(*   [x] and [y] positions swapped on the opposite side.         *)
(* ------------------------------------------------------------ *)
Lemma real_plus_opp_cancel_mid :
  forall x y : Real,
  real_eq (real_plus (real_opp x) (real_plus x y)) y.
Proof.
  intros x y.
  apply (real_eq_trans _ (real_plus (real_plus (real_opp x) x) y) _).
  - exact (real_plus_assoc (real_opp x) x y).
  - apply (real_eq_trans _ (real_plus real_zero y) _).
    + exact (RealSetoid.real_eq_plus_compat
                (real_plus (real_opp x) x) y real_zero y
                (real_eq_trans _ (real_plus x (real_opp x)) _
                   (real_plus_comm (real_opp x) x) (real_plus_opp x))
                (real_eq_refl y)).
    + apply (real_eq_trans _ _ _ (real_plus_comm real_zero y) (real_plus_zero y)).
Qed.

(* ------------------------------------------------------------ *)
(* Statement 1b: [a + (b + (-a)) == b] — the [Real] copy of the  *)
(*   [Id]-carrier [minus_plus_cancel]; it finishes the           *)
(*   right-summand rewrite in the final step of the main         *)
(*   theorem.                                                    *)
(* ------------------------------------------------------------ *)
Lemma real_plus_minus_r_cancel :
  forall a b : Real,
  real_eq (real_plus a (real_plus b (real_opp a))) b.
Proof.
  intros a b.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) b)) _).
  - exact (RealSetoid.real_eq_plus_compat a (real_plus b (real_opp a))
              a (real_plus (real_opp a) b)
              (real_eq_refl a) (real_plus_comm b (real_opp a))).
  - apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) b) _).
    + exact (real_plus_assoc a (real_opp a) b).
    + apply (real_eq_trans _ (real_plus real_zero b) _).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_plus a (real_opp a)) b real_zero b
                  (real_plus_opp a) (real_eq_refl b)).
      * apply (real_eq_trans _ _ _ (real_plus_comm real_zero b) (real_plus_zero b)).
Qed.

(* ------------------------------------------------------------ *)
(* Statement 1c: two-sided rewrite of the difference carrier     *)
(*   [real_minus_r], whose definition unfolds in                 *)
(*   [S12_B5RecycleSF].                                          *)
(* ------------------------------------------------------------ *)
Lemma real_minus_r_compat :
  forall a b c d : Real,
  real_eq a c -> real_eq b d -> real_eq (real_minus_r a b) (real_minus_r c d).
Proof.
  intros a b c d Hac Hbd.
  unfold real_minus_r.
  exact (RealSetoid.real_eq_plus_compat a (real_opp b) c (real_opp d) Hac           (RealSetoid.real_eq_opp_compat b d Hbd)).
Qed.

(* ------------------------------------------------------------ *)
(* Statement 1d: cancelling a common summand — the               *)
(*   [real_minus_r] copy of the [Id]-carrier                     *)
(*   [minus_plus_common_local] in [S04_RealExpLogConv]:          *)
(*   [(A+B) - (A+C) == B - C].                                   *)
(* ------------------------------------------------------------ *)
Lemma real_minus_r_plus_common :
  forall A B C : Real,
  real_eq (real_minus_r (real_plus A B) (real_plus A C)) (real_minus_r B C).
Proof.
  intros A B C.
  apply (real_eq_trans
           _ (real_plus (real_plus A B) (real_plus (real_opp A) (real_opp C))) _).
  - exact (RealSetoid.real_eq_plus_compat
              (real_plus A B) (real_opp (real_plus A C))
              (real_plus A B) (real_plus (real_opp A) (real_opp C))
              (real_eq_refl (real_plus A B))
              (real_opp_plus A C)).
  - apply (real_eq_trans
             _ (real_plus (real_plus A (real_opp A)) (real_plus B (real_opp C))) _).
    + exact (real_plus_swap_mid A B (real_opp A) (real_opp C)).
    + apply (real_eq_trans _ (real_plus real_zero (real_plus B (real_opp C))) _).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_plus A (real_opp A)) (real_plus B (real_opp C))
                  real_zero (real_plus B (real_opp C))
                  (real_plus_opp A) (real_eq_refl (real_plus B (real_opp C)))).
      * apply (real_eq_trans _ _ _
                  (real_plus_comm real_zero (real_plus B (real_opp C)))
                  (real_plus_zero (real_plus B (real_opp C)))).
Qed.

(* ---------------------------------------------------------- *)



(* ---------------------------------------------------------- *)
Lemma real_log_inv_pos_opp :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hone : real_lt real_zero real_one) by exact real_one_pos_local.
  assert (Hsum : real_eq
                   (real_plus (real_log x Hx)
                              (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                   real_zero).
  { apply (real_eq_trans
             _ (real_log (real_mult x (real_inv_pos x Hx))
                         (real_mult_positive x (real_inv_pos x Hx) Hx
                            (real_inv_pos_pos x Hx))) _).
    - apply real_eq_sym.
      exact (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx)).
    - apply (real_eq_trans _ (real_log real_one Hone) _).
      + exact (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                  (real_mult_positive x (real_inv_pos x Hx) Hx
                     (real_inv_pos_pos x Hx)) Hone
                  (real_inv_pos_correct x Hx)).
      + exact (real_log_one Hone). }
  apply (real_eq_trans
           _ (real_plus (real_opp (real_log x Hx))
                        (real_plus (real_log x Hx)
                                   (real_log (real_inv_pos x Hx)
                                             (real_inv_pos_pos x Hx)))) _).
  - apply real_eq_sym.
    exact (real_plus_opp_cancel_mid (real_log x Hx)
             (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    + exact (RealSetoid.real_eq_plus_compat
                (real_opp (real_log x Hx))
                (real_plus (real_log x Hx)
                           (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                (real_opp (real_log x Hx)) real_zero
                (real_eq_refl (real_opp (real_log x Hx))) Hsum).
    + exact (real_plus_zero (real_opp (real_log x Hx))).
Qed.

(* ---------------------------------------------------------- *)
(* Statement 2b: the pointwise expansion of the KL term.         *)


(*   Chain: move the negation inward ([real_opp_plus] in         *)
(*   [S07_RealSetoidExpLog], [real_opp_opp] in                   *)
(*   [S08_RealMainlineDPO], and commutativity of the group),     *)
(*   then rewrite the multiplication side                        *)
(*   ([RealSetoid.real_eq_mult_compat]).                         *)
(* ---------------------------------------------------------- *)
Lemma real_kl_term_expand :
  forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult p (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  set (Hwit := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (Lp := real_log p Hp).
  set (Lq := real_log q Hq).
  assert (Hlog : real_eq
                   (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hwit))
                   (real_plus Lp (real_opp Lq))).
  { apply (real_eq_trans
             _ (real_opp (real_plus Lq
                                    (real_log (real_inv_pos p Hp)
                                              (real_inv_pos_pos p Hp)))) _).
    - exact (RealSetoid.real_eq_opp_compat
                (real_log (real_mult q (real_inv_pos p Hp)) Hwit)
                (real_plus Lq
                           (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp)))
                (real_log_mult q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))).
    - apply (real_eq_trans
               _ (real_opp (real_plus Lq (real_opp Lp))) _).
      + exact (RealSetoid.real_eq_opp_compat
                  (real_plus Lq
                             (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp)))
                  (real_plus Lq (real_opp Lp))
                  (RealSetoid.real_eq_plus_compat Lq
                     (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))
                     Lq (real_opp Lp)
                     (real_eq_refl Lq) (real_log_inv_pos_opp p Hp))).
      + apply (real_eq_trans
                 _ (real_plus (real_opp Lq) (real_opp (real_opp Lp))) _).
        * exact (real_opp_plus Lq (real_opp Lp)).
        * apply (real_eq_trans _ (real_plus (real_opp Lq) Lp) _).
          -- exact (RealSetoid.real_eq_plus_compat
                       (real_opp Lq) (real_opp (real_opp Lp))
                       (real_opp Lq) Lp
                       (real_eq_refl (real_opp Lq))
                       (real_opp_opp Lp)).
          -- exact (real_plus_comm (real_opp Lq) Lp). }
  exact (RealSetoid.real_eq_mult_compat p
           (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hwit))
           p (real_plus Lp (real_opp Lq))
           (real_eq_refl p) Hlog).
Qed.

(* ---------------------------------------------------------- *)
(* Statement 3: the decomposition [real_cross_entropy_decomp], a *)
(*   [real_eq] identity: [CE(p,q) == Ent(p) + sum kl_term(p,q)]. *)
(*   Cross-entropy = own entropy + relative entropy (the [Real]  *)
(*   copy of the [Id]-carrier [cross_entropy_decomp] in          *)
(*   [S04_RealExpLogConv]); the assembly follows the same family *)
(*   as [real_kl_sum_decomp] in [S08_RealMainlineDPO]: pointwise *)
(*   (the statement 1a cancellation chain plus [real_distrib]),  *)
(*   then extensionality, then additivity, then extensionality   *)
(*   onto the KL bridge.                                         *)
(* ---------------------------------------------------------- *)
Lemma real_cross_entropy_decomp :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_cross_entropy X l p q Hq)
          (real_plus
             (real_list_sum X
                (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
             (real_list_sum X
                (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq.
  assert (Hpt : forall s : X,
    real_eq (real_mult (p s) (real_opp (real_log (q s) (Hq s))))
            (real_plus (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                       (real_mult (p s)
                          (real_plus (real_log (p s) (Hp s))
                                     (real_opp (real_log (q s) (Hq s))))))).
  {
    intro s.
    assert (Ha : real_eq (real_opp (real_log (q s) (Hq s)))
                         (real_plus (real_opp (real_log (p s) (Hp s)))
                                    (real_plus (real_log (p s) (Hp s))
                                               (real_opp (real_log (q s) (Hq s)))))).
    { apply real_eq_sym.
      exact (real_plus_opp_cancel_mid (real_log (p s) (Hp s))
               (real_opp (real_log (q s) (Hq s)))). }
    apply (real_eq_trans
             _ (real_mult (p s)
                    (real_plus (real_opp (real_log (p s) (Hp s)))
                               (real_plus (real_log (p s) (Hp s))
                                          (real_opp (real_log (q s) (Hq s)))))) _).
    - exact (RealSetoid.real_eq_mult_compat (p s)
                (real_opp (real_log (q s) (Hq s))) (p s)
                (real_plus (real_opp (real_log (p s) (Hp s)))
                           (real_plus (real_log (p s) (Hp s))
                                      (real_opp (real_log (q s) (Hq s)))))
                (real_eq_refl (p s)) Ha).
    - exact (real_distrib (p s) (real_opp (real_log (p s) (Hp s)))
               (real_plus (real_log (p s) (Hp s)) (real_opp (real_log (q s) (Hq s))))).
  }
  unfold real_cross_entropy.
  apply (real_eq_trans _ (real_list_sum X
           (fun s => real_plus (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                               (real_mult (p s)
                                  (real_plus (real_log (p s) (Hp s))
                                             (real_opp (real_log (q s) (Hq s)))))) l) _).
  - exact (real_list_sum_ext X
             (fun s => real_mult (p s) (real_opp (real_log (q s) (Hq s))))
             (fun s => real_plus (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                                 (real_mult (p s)
                                    (real_plus (real_log (p s) (Hp s))
                                               (real_opp (real_log (q s) (Hq s))))))
             l Hpt).
  - apply (real_eq_trans _ (real_plus
               (real_list_sum X
                  (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
               (real_list_sum X
                  (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s))))) l)) _).
    + exact (real_list_sum_add X
               (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s))))
               (fun s => real_mult (p s)
                            (real_plus (real_log (p s) (Hp s))
                                       (real_opp (real_log (q s) (Hq s)))))
               l).
    + exact (RealSetoid.real_eq_plus_compat
               (real_list_sum X
                  (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
               (real_list_sum X
                  (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s))))) l)
               (real_list_sum X
                  (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
               (real_list_sum X
                  (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
               (real_eq_refl
                  (real_list_sum X
                     (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l))
               (real_list_sum_ext X
                  (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s)))))
                  (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                  l
                  (fun s => real_eq_sym _ _
                              (real_kl_term_expand (p s) (q s) (Hp s) (Hq s))))).
Qed.

(* ---------------------------------------------------------- *)
(* Statement 4 (the main statement): [real_training_equivalence] *)
(*   — Theorem 4.10 on the [Real] layer, the [real_le] form of   *)
(*   the same statement with no weakening: for fixed target [p], *)
(*   a drop in cross-entropy implies a drop in KL.  Assembly     *)
(*   chain (four ordered steps):                                 *)
(*   (1) nonnegativity of the difference: [0 <= CE1 - CE2] via   *)
(*     [real_le_minus_nonneg_aux] in [S13_NLiveAudit]; both [Or] *)
(*     branches are discharged constructively, with no           *)
(*     excluded-middle leakage;                                  *)
(*   (2) identity of the difference: [CE1 - CE2 == K1 - K2] —    *)
(*     the statement 3 decomposition, then statement 1c, then    *)
(*     statement 1d;                                             *)
(*   (3) transport along [RealSetoid.real_le_id_r] (in           *)
(*     [S07_RealSetoidExpLog]);                                  *)
(*   (4) finish: [K2 <= K2 + (K1 - K2) == K1] via                *)
(*     [real_le_plus_nonneg_r_aux] in [S13_NLiveAudit] plus      *)
(*     statement 1b.                                             *)
(* ---------------------------------------------------------- *)
Theorem real_training_equivalence :
  forall (X : Type) (l : list X) (p q1 q2 : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq1 : forall s : X, real_lt real_zero (q1 s))
    (Hq2 : forall s : X, real_lt real_zero (q2 s)),
  real_le (real_cross_entropy X l p q2 Hq2) (real_cross_entropy X l p q1 Hq1) ->
  real_le (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
          (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l).
Proof.
  intros X l p q1 q2 Hp Hq1 Hq2 Hce.
  (* (1) nonnegativity of the difference (the [real_minus_r] carrier unfolds definitionally to [real_plus b (real_opp a)]). *)
  assert (Hd0 : real_le real_zero
                  (real_minus_r (real_cross_entropy X l p q1 Hq1)
                                (real_cross_entropy X l p q2 Hq2)))
    by exact (real_le_minus_nonneg_aux
                (real_cross_entropy X l p q2 Hq2)
                (real_cross_entropy X l p q1 Hq1) Hce).
  (* (2) identity of the difference: [CE1 - CE2 == K1 - K2]. *)
  assert (Hdiff : real_eq
                    (real_minus_r (real_cross_entropy X l p q1 Hq1)
                                  (real_cross_entropy X l p q2 Hq2))
                    (real_minus_r
                       (real_list_sum X
                          (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                       (real_list_sum X
                          (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))).
  { apply (real_eq_trans
             _ (real_minus_r
                  (real_plus
                     (real_list_sum X
                        (fun s => real_mult (p s)
                                       (real_opp (real_log (p s) (Hp s)))) l)
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l))
                  (real_plus
                     (real_list_sum X
                        (fun s => real_mult (p s)
                                       (real_opp (real_log (p s) (Hp s)))) l)
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))) _).
    - exact (real_minus_r_compat
                (real_cross_entropy X l p q1 Hq1)
                (real_cross_entropy X l p q2 Hq2)
                (real_plus
                   (real_list_sum X
                      (fun s => real_mult (p s)
                                     (real_opp (real_log (p s) (Hp s)))) l)
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l))
                (real_plus
                   (real_list_sum X
                      (fun s => real_mult (p s)
                                     (real_opp (real_log (p s) (Hp s)))) l)
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))
                (real_cross_entropy_decomp X l p q1 Hp Hq1)
                (real_cross_entropy_decomp X l p q2 Hp Hq2)).
    - exact (real_minus_r_plus_common
                (real_list_sum X
                   (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
                (real_list_sum X
                   (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                (real_list_sum X
                   (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)). }
  (* (3) transport: [0 <= K1 - K2]. *)
  assert (Hd : real_le real_zero
                  (real_minus_r
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)))
    by exact (RealSetoid.real_le_id_r real_zero
                (real_minus_r (real_cross_entropy X l p q1 Hq1)
                              (real_cross_entropy X l p q2 Hq2))
                (real_minus_r
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))
                Hdiff Hd0).
  (* (4) finish: [K2 <= K2 + (K1 - K2) == K1]. *)
  apply (RealSetoid.real_le_id_r
           (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
           (real_plus
              (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
              (real_minus_r
                 (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                 (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)))
           (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)).
  - exact (real_plus_minus_r_cancel
             (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
             (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)).
  - exact (real_le_plus_nonneg_r_aux
             (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
             (real_minus_r
                (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))
             Hd).
Qed.

(* ============================================================ *)
(* Assumption audit: Print Assumptions on the main statements    *)
(*   and on the difference lemmas; each reports Closed.          *)
(* ============================================================ *)
Print Assumptions real_cross_entropy.
Print Assumptions real_cross_entropy_decomp.
Print Assumptions real_training_equivalence.

Print Assumptions real_minus_r_compat.
