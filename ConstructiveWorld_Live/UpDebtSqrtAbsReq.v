(* UpDebtSqrtAbsReq.v — abstract real_eq-layer square-root witness piece. *)
(* Mission. Section SqrtAbsReq carries req_sqrt_premise_le_intro (the
   real_le-introduction form of a square-geq-a premise),
   req_sqrt_witness_exists_abstract (square-root witness existence in sigT
   form), with two_abs / half_abs support pieces and the witness-form
   restatements req_sqrt_witness_exists_abstract_witness and
   req_sqrt_one_abstract. *)
(* Dependencies. S01_BaseRing .. S15_TailFEPUp plus UpReqAlgebra (sixteen
   modules of tree 109); interface import RealInterfaceEnhancedMod (S07). *)
(* References. The abstract-interface version of constructive square-root
   existence (Bishop-style constructivism). *)
(* Constructivity. Every piece is Qed-closed with zero admission words and no
   classical logic; the statement face is carried at the Set layer on the
   concrete Set-valued faces real_eq/real_lt/real_le (S02_CauchyComplete
   411/480/484) — order predicates and the equality are Set-valued, with
   zero Prop leakage. *)
(* Build. coqc -native-compiler no -q -Q . "" (the rocq c compile form;
   this toolchain exposes the coqc driver) compiled in place against the
   seat world of tree-109 sources; every launch passes the cpu_guard thermal
   wrapper with ulimit -s 65532. *)

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
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

Section SqrtAbsReq.

(* Tree-face adaptation (registered precedent: the same two lines in
   UpReqAlgebra; class declaration at S07_RealSetoidExpLog "Class
   RealInterfaceEnhancedSetoid"). In this tree the interface class is
   unparameterized: its carrier is the global Real and its sole registered
   instance is RealEnhancedReal. The source piece was written against the
   older parameterized-interface world, so the two Context lines
   (Context {R : Set} and Context {RIS : RealInterfaceEnhancedSetoid R}) are
   replaced by the notation below, and the Let bindings re-anchor to that
   instance. Statement-face re-anchor (registered precedent: the UpReqAlgebra
   real_eq face, tree-verified magic=0; diagnostic-seat E5): every bare
   projection token req/lt/le on the statement faces and the assert type
   faces is rewritten to the concrete faces real_eq/real_lt/real_le
   (S02_CauchyComplete 411/480/484), with statement names unchanged; the two
   order-field anchor Lets (Let lt / Let le) are removed as no longer needed.
   Proof bodies keep zero character changes. The projection-face statements
   were the Obj.magic source (CI probe magic=50); this concrete-face
   re-anchor clears them. *)
Notation R := Real.

Let zero := @zero RealEnhancedReal.
Let one := @one RealEnhancedReal.
Let plus := @plus RealEnhancedReal.
Let mult := @mult RealEnhancedReal.
Let inv_pos := @inv_pos RealEnhancedReal.
Let exp_neg := @exp_neg RealEnhancedReal.

(* two := 1 + 1; two > 0 (direct citation of the base piece req_two_pos). *)
Definition two_abs : R := plus one one.
Lemma two_abs_pos : real_lt zero two_abs.
Proof. exact req_two_pos. Qed.

(* half := inv(two); half + half == one (real_eq chain: inv_pos_correct
   + distrib + mult_one + req_plus_compat, five pure-term steps). *)
Definition half_abs : R := inv_pos two_abs two_abs_pos.
Lemma half_plus_half : real_eq (plus half_abs half_abs) one.
Proof.
  assert (Hd : real_eq (mult half_abs two_abs) one).
  { exact (req_trans (mult half_abs two_abs) (mult two_abs half_abs) one
             (mult_comm half_abs two_abs)
             (inv_pos_correct two_abs two_abs_pos)). }
  assert (Hsplit : real_eq (mult half_abs two_abs) (plus half_abs half_abs)).
  { apply (req_trans
              (mult half_abs (plus one one))
              (plus (mult half_abs one) (mult half_abs one))
              (plus half_abs half_abs)).
    - exact (distrib half_abs one one).
    - exact (req_plus_compat (mult half_abs one) half_abs
                             (mult half_abs one) half_abs
                             (mult_one half_abs) (mult_one half_abs)). }
  exact (req_trans (plus half_abs half_abs) (mult half_abs two_abs) one
           (req_sym (mult half_abs two_abs) (plus half_abs half_abs) Hsplit)
           Hd).
Qed.

(* ===== Piece 3: the Or premise is exactly the constructive content of real_le ===== *)
Lemma req_sqrt_premise_le_intro : forall d : R,
  Or (real_lt zero d) (real_eq zero d) -> real_le zero d.
Proof.
  intros d H. apply lt_le_iff. exact H.
Qed.

(* ===== Piece 4 (main theorem): the abstract real_eq-layer square-root witness ===== *)
(* d > 0: r := e^{-(half·log_inv d)}; real_le comes from exp_neg_pos, and
   r·r == d from exp_neg_plus(sym) + exp_neg_req_compat_setoid
   (using Hinner : half·L + half·L == L) + exp_neg_log_inv, three chains;
   d == 0: r := zero, where mult zero zero == zero is the interface field
   mult_zero. *)
Theorem req_sqrt_witness_exists_abstract :
  forall d : R,
  Or (real_lt zero d) (real_eq zero d) ->
  sigT (fun r : R => And (real_le zero r) (real_eq (mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - exists (exp_neg (mult half_abs (log_inv d Hdlt))).
    split.
    + exact (lt_le_iff zero (exp_neg (mult half_abs (log_inv d Hdlt)))
                        (inl (exp_neg_pos (mult half_abs (log_inv d Hdlt))))).
    + assert (Hinner : real_eq (plus (mult half_abs (log_inv d Hdlt))
                                 (mult half_abs (log_inv d Hdlt)))
                           (log_inv d Hdlt)).
      { apply (req_trans
                  (plus (mult half_abs (log_inv d Hdlt)) (mult half_abs (log_inv d Hdlt)))
                  (mult (plus half_abs half_abs) (log_inv d Hdlt))
                  (log_inv d Hdlt)).
        - exact (req_sym
                    (mult (plus half_abs half_abs) (log_inv d Hdlt))
                    (plus (mult half_abs (log_inv d Hdlt)) (mult half_abs (log_inv d Hdlt)))
                    (req_mult_plus_distr_r half_abs half_abs (log_inv d Hdlt))).
        - apply (req_trans
                    (mult (plus half_abs half_abs) (log_inv d Hdlt))
                    (mult one (log_inv d Hdlt))
                    (log_inv d Hdlt)).
          + exact (req_mult_compat (plus half_abs half_abs) one
                                   (log_inv d Hdlt) (log_inv d Hdlt)
                                   half_plus_half (req_refl (log_inv d Hdlt))).
          + exact (req_trans (mult one (log_inv d Hdlt))
                             (mult (log_inv d Hdlt) one)
                             (log_inv d Hdlt)
                             (mult_comm one (log_inv d Hdlt))
                             (mult_one (log_inv d Hdlt))). }
      exact (req_trans
              (mult (exp_neg (mult half_abs (log_inv d Hdlt)))
                    (exp_neg (mult half_abs (log_inv d Hdlt))))
              (exp_neg (plus (mult half_abs (log_inv d Hdlt))
                             (mult half_abs (log_inv d Hdlt))))
              d
              (req_sym
                  (exp_neg (plus (mult half_abs (log_inv d Hdlt))
                                 (mult half_abs (log_inv d Hdlt))))
                  (mult (exp_neg (mult half_abs (log_inv d Hdlt)))
                        (exp_neg (mult half_abs (log_inv d Hdlt))))
                  (exp_neg_plus (mult half_abs (log_inv d Hdlt))
                                (mult half_abs (log_inv d Hdlt))))
              (req_trans
                  (exp_neg (plus (mult half_abs (log_inv d Hdlt))
                                 (mult half_abs (log_inv d Hdlt))))
                  (exp_neg (log_inv d Hdlt))
                  d
                  (exp_neg_req_compat_setoid
                      (plus (mult half_abs (log_inv d Hdlt))
                            (mult half_abs (log_inv d Hdlt)))
                      (log_inv d Hdlt) Hinner)
                  (exp_neg_log_inv d Hdlt))).
  - exists zero.
    split.
    + apply le_refl.
    + exact (req_trans (mult zero zero) zero d (mult_zero zero) Hdeq).
Qed.

(* ===== Piece 5: witness-form restatement (same semantics as Piece 4,
   provided for downstream name-based consumption) ===== *)
Lemma req_sqrt_witness_exists_abstract_witness :
  forall d : R,
  Or (real_lt zero d) (real_eq zero d) ->
  sigT (fun r : R => And (real_le zero r) (real_eq (mult r r) d)).
Proof.
  intros d H.
  exact (req_sqrt_witness_exists_abstract d H).
Qed.

(* ===== Piece 6: instance — the abstract square root of 1 ===== *)
Lemma req_sqrt_one_abstract :
  sigT (fun r : R => And (real_le zero r) (real_eq (mult r r) one)).
Proof.
  exact (req_sqrt_witness_exists_abstract one (inl one_pos)).
Qed.

End SqrtAbsReq.
