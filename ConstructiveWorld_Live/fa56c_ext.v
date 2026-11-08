(* ConstructiveWorld-Set -- fa56c_ext: C-class slot supplies for the S04/S05
   language-model, temperature, and physical-prediction sections. *)

(** * fa56c_ext: engine-continued Id-carrier slot supplies.

    Mission.  Supplies for four premise slots on the engine exports
      [fa56_id_carrier]/[fa56b_ext]: the [default_token] slot (from
      the head element of a nonempty [vocab], with three companions);
      the [prediction_landauer] slot (the [E_min] piece and the
      Landauer upper bound [ln 2 <= 1] via the log tangent bound);
      [loss_structure_correlation] (a scaled [total_loss] with le/lt
      companions and an annealed specialization); and
      [max_entropy_production] (an [ExistsT] witness, a
      constant-weight specialization, the [noneq_loss] mirror).  New
      engine piece: [fa56c_le_mult_compat_l] (left-multiplication
      [le] compatibility).

    Dependencies.  Stdlib [Lists.List]; requires [S01_BaseRing],
      [fa56_id_carrier], [fa56b_ext].

    References.  ConstructiveWorld-Main, module [fa56c_ext]
      (statement names carried over verbatim).

    Constructivity.  Statement faces are Set-level ([lt]/[le]/[Id]/
      [Not]/[ExistsT], [ExistsT] [:= sigT]); purely constructive,
      no admits; tail [Print Assumptions] covers every statement.

    Build.  [coqc -native-compiler no -q -Q . "" fa56c_ext.v]
      compiles cleanly (exit 0). *)

Require Import S01_BaseRing.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa56cExt.

Context {RI : RealInterfaceEnhanced}.

Let R    := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let le   := @le RI.
Let lt   := @lt RI.
Let log  := @log RI.

(* ============ Engine key: left-multiplication le compatibility *)
(* The interface provides only the right-multiplication field      *)
(* [le_mult_compat] ([c] multiplied on the right); the slot XI     *)
(* upper-bound chain and the slot XIII dominance chain both need   *)
(* the left form - assembled by two [mult_comm] rearrangements,    *)
(* no new premises.                                                *)

Lemma fa56c_le_mult_compat_l :
  forall (a b c : R), lt zero c -> le a b -> le (mult c a) (mult c b).
Proof.
  intros a b c Hc H.
  exact (le_trans (mult c a) (mult a c) (mult c b)
           (le_id_r (mult c a) (mult c a) (mult a c)
              (mult_comm c a) (le_refl (mult c a)))
           (le_trans (mult a c) (mult b c) (mult c b)
              (le_mult_compat a b c Hc H)
              (le_id_l (mult b c) (mult c b) (mult c b)
                 (mult_comm b c) (le_refl (mult c b))))).
Qed.

(* Left-multiplication [lt] compatibility (same method; used by    *)
(* the strict version of slot XII).                                *)

Lemma fa56c_lt_mult_compat_l :
  forall (a b c : R), lt zero c -> lt a b -> lt (mult c a) (mult c b).
Proof.
  intros a b c Hc H.
  exact (lt_id_l (mult c a) (mult a c) (mult c b)
           (mult_comm c a)
           (lt_id_r (mult a c) (mult b c) (mult c b)
              (mult_comm b c) (lt_mult_compat a b c Hc H))).
Qed.

(* ============ Slot X: the S04:1590 default_token slot (LM       *)
(*   section) ============                                        *)
(* Slot statement: [Variable default_token : Token] (the          *)
(* [ArgminCorrectness] section, grouped with [vocab]/             *)
(* [vocab_nonempty]).  Realization: for a nonempty vocabulary the *)
(* default token is constructed from the head element of [vocab], *)
(* the nil branch being killed by the nonemptiness premise.       *)

Definition fa56c_default_token (Token : Set) (vocab : list Token)
                               (Hne : Not (Id vocab (@nil Token))) : Token :=
  match vocab as l return Not (Id l (@nil Token)) -> Token with
  | nil => fun H0 => match H0 (@id_refl (list Token) (@nil Token)) with end
  | w0 :: _ => fun _ => w0
  end Hne.

(* Head property: the default token of a cons vocabulary is its    *)
(* first element (definitional reduction).                         *)
Theorem fa56c_default_token_head :
  forall (Token : Set) (t0 : Token) (l : list Token)
         (Hne : Not (Id (t0 :: l) (@nil Token))),
    Id (fa56c_default_token Token (t0 :: l) Hne) t0.
Proof. intros Token t0 l Hne. reflexivity. Qed.

(* Singleton-vocabulary instance: the nonemptiness witness is      *)
(* supplied directly by the fa56b singleton piece.                 *)
Theorem fa56c_default_token_singleton :
  forall (Token : Set) (t0 : Token),
    Id (fa56c_default_token Token (t0 :: nil)
          (fa56b_singleton_nonempty Token t0)) t0.
Proof. intros Token t0. reflexivity. Qed.

(* Companion: consing the default token back keeps the vocabulary  *)
(* nonempty (using the fa56b discrimination core).                 *)
Theorem fa56c_default_token_cons_preserves_nonempty :
  forall (Token : Set) (vocab : list Token)
         (Hne : Not (Id vocab (@nil Token))),
    Not (Id (fa56c_default_token Token vocab Hne :: vocab) (@nil Token)).
Proof.
  intros Token vocab Hne H.
  exact (fa56b_cons_nil_id_contra Token
           (fa56c_default_token Token vocab Hne) vocab H).
Qed.

(* ============ Slot XI: the S05:5942-5944 Landauer slot (physical *)
(*   prediction section) ============                              *)
(* Slot statement: [prediction_landauer : Id E_min (mult k_B (mult *)
(* T_landauer (log (plus one one))))].  Assembly: the [E_min]      *)
(* definition piece plus the identical [Id] piece; the nontrivial  *)
(* companion is the Landauer upper bound [ln 2 <= 1] (the log      *)
(* tangent bound [log_le_linear], [two_pos], and minus ring        *)
(* pieces) lifted twice by the left-multiplication compatibility   *)
(* piece, giving [E_min <= k_B*T].                                 *)

Definition fa56c_E_min (k_B T_landauer : R) : R :=
  mult k_B (mult T_landauer (log (plus one one))).

Theorem fa56c_prediction_landauer :
  forall k_B T_landauer : R,
    Id (fa56c_E_min k_B T_landauer)
       (mult k_B (mult T_landauer (log (plus one one)))).
Proof. intros k_B T_landauer. reflexivity. Qed.

Theorem fa56c_landauer_upper_bound :
  forall k_B T_landauer : R,
    lt zero k_B -> lt zero T_landauer ->
    le (fa56c_E_min k_B T_landauer) (mult k_B T_landauer).
Proof.
  intros k_B T_landauer Hk HT. unfold fa56c_E_min.
  apply (le_id_r _ (mult k_B (mult T_landauer one))).
  - exact (id_cong (fun y => mult k_B y) (mult_one T_landauer)).
  - exact (fa56c_le_mult_compat_l
             (mult T_landauer (log (plus one one)))
             (mult T_landauer one) k_B Hk
             (fa56c_le_mult_compat_l (log (plus one one)) one
                T_landauer HT
                (le_id_r (log (plus one one))
                   (minus (plus one one) one) one
                   (minus_plus_cancel_r one one)
                   (log_le_linear (plus one one) two_pos)))).
Qed.

(* ============ Slot XII: the S05:6016-6019 loss_structure_       *)
(*   correlation slot ============                                *)
(* Slot statement: [forall epoch, le (grammar_error (model epoch)) *)
(* (grammar_error (model (succ epoch))) -> le (total_loss (model   *)
(* epoch)) (total_loss (model (succ epoch)))].  Realization: the   *)
(* [total_loss] assembly definition (positive scale [c]); the      *)
(* le/lt companions go through [le_mult_compat]/[lt_mult_compat];  *)
(* the annealed specialization takes [c := fa56_prob_neg_entropy]  *)
(* (using the fa56 positivity companion).                          *)

Definition fa56c_total_loss (Token : Set) (grammar_error : list Token -> R)
                            (c : R) (l : list Token) : R :=
  mult c (grammar_error l).

Theorem fa56c_loss_structure_correlation :
  forall (Token : Set) (model : nat -> list Token)
         (grammar_error : list Token -> R) (c : R),
    lt zero c ->
    forall epoch : nat,
      le (grammar_error (model epoch))
         (grammar_error (model (Nat.succ epoch))) ->
      le (fa56c_total_loss Token grammar_error c (model epoch))
         (fa56c_total_loss Token grammar_error c
            (model (Nat.succ epoch))).
Proof.
  intros Token model grammar_error c Hc epoch H.
  exact (le_trans (mult c (grammar_error (model epoch)))
                  (mult (grammar_error (model epoch)) c)
                  (mult c (grammar_error (model (Nat.succ epoch))))
           (le_id_r (mult c (grammar_error (model epoch)))
                    (mult c (grammar_error (model epoch)))
                    (mult (grammar_error (model epoch)) c)
              (mult_comm c (grammar_error (model epoch)))
              (le_refl (mult c (grammar_error (model epoch)))))
           (le_trans (mult (grammar_error (model epoch)) c)
                     (mult (grammar_error (model (Nat.succ epoch))) c)
                     (mult c (grammar_error (model (Nat.succ epoch))))
              (le_mult_compat (grammar_error (model epoch))
                              (grammar_error (model (Nat.succ epoch))) c Hc H)
              (le_id_l (mult (grammar_error (model (Nat.succ epoch))) c)
                       (mult c (grammar_error (model (Nat.succ epoch))))
                       (mult c (grammar_error (model (Nat.succ epoch))))
                 (mult_comm (grammar_error (model (Nat.succ epoch))) c)
                 (le_refl (mult c (grammar_error (model (Nat.succ epoch)))))))).
Qed.

(* Strict version: a strict decrease in grammar error gives a      *)
(* strict decrease in total loss.                                  *)
Theorem fa56c_loss_structure_strict :
  forall (Token : Set) (model : nat -> list Token)
         (grammar_error : list Token -> R) (c : R),
    lt zero c ->
    forall epoch : nat,
      lt (grammar_error (model epoch))
         (grammar_error (model (Nat.succ epoch))) ->
      lt (fa56c_total_loss Token grammar_error c (model epoch))
         (fa56c_total_loss Token grammar_error c
            (model (Nat.succ epoch))).
Proof.
  intros Token model grammar_error c Hc epoch H.
  exact (fa56c_lt_mult_compat_l _ _ _ Hc H).
Qed.

(* Annealed specialization: [c] is the fa56 fluctuation-scale      *)
(* piece (a temperature-carried negative scale); positivity from   *)
(* the fa56 piece.                                                 *)
Theorem fa56c_loss_structure_annealed :
  forall (Token : Set) (model : nat -> list Token)
         (grammar_error : list Token -> R) (k_B : R)
         (k_B_pos : lt zero k_B) (N : R) (epoch : nat),
    le (grammar_error (model epoch))
       (grammar_error (model (Nat.succ epoch))) ->
    le (fa56c_total_loss Token grammar_error
          (fa56_prob_neg_entropy k_B k_B_pos N) (model epoch))
       (fa56c_total_loss Token grammar_error
          (fa56_prob_neg_entropy k_B k_B_pos N)
          (model (Nat.succ epoch))).
Proof.
  intros Token model grammar_error k_B k_B_pos N epoch H.
  exact (le_trans (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                        (grammar_error (model epoch)))
                  (mult (grammar_error (model epoch))
                        (fa56_prob_neg_entropy k_B k_B_pos N))
                  (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                        (grammar_error (model (Nat.succ epoch))))
           (le_id_r (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                          (grammar_error (model epoch)))
                    (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                          (grammar_error (model epoch)))
                    (mult (grammar_error (model epoch))
                          (fa56_prob_neg_entropy k_B k_B_pos N))
              (mult_comm (fa56_prob_neg_entropy k_B k_B_pos N)
                         (grammar_error (model epoch)))
              (le_refl (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                             (grammar_error (model epoch)))))
           (le_trans (mult (grammar_error (model epoch))
                           (fa56_prob_neg_entropy k_B k_B_pos N))
                     (mult (grammar_error (model (Nat.succ epoch)))
                           (fa56_prob_neg_entropy k_B k_B_pos N))
                     (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                           (grammar_error (model (Nat.succ epoch))))
              (le_mult_compat (grammar_error (model epoch))
                              (grammar_error (model (Nat.succ epoch)))
                              (fa56_prob_neg_entropy k_B k_B_pos N)
                              (fa56_prob_neg_entropy_pos k_B k_B_pos N) H)
              (le_id_l (mult (grammar_error (model (Nat.succ epoch)))
                             (fa56_prob_neg_entropy k_B k_B_pos N))
                       (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                             (grammar_error (model (Nat.succ epoch))))
                       (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                             (grammar_error (model (Nat.succ epoch))))
                 (mult_comm (grammar_error (model (Nat.succ epoch)))
                            (fa56_prob_neg_entropy k_B k_B_pos N))
                 (le_refl (mult (fa56_prob_neg_entropy k_B k_B_pos N)
                                (grammar_error (model (Nat.succ epoch)))))))).
Qed.

(* ============ Slot XIII: the S05:5824-5827 max_entropy_         *)
(*   production slot ============                                 *)
(* Slot statement: [max_entropy_production : forall X, ExistsT     *)
(* (fun J : Flux => forall J' : Flux, le (entropy_production_rate  *)
(* J X) (entropy_production_rate J' X))].  Realization: the rate   *)
(* assembly definition (weight times potential), the [ExistsT]     *)
(* witness assembly (dominance premise in the signature, [existT   *)
(* J0] in one step), the constant-weight specialization            *)
(* (premise-free, closed by [le_refl]), and the [noneq_loss]       *)
(* mirror.                                                         *)

Definition fa56c_entropy_production_rate (Flux TD : Set) (w : Flux -> R)
                                         (theta : TD -> R) (J : Flux)
                                         (X : TD) : R :=
  mult (w J) (theta X).

(* Existence main piece: when [J0] is a weight-dominant flux, the  *)
(* maximal-production witness assembles directly by [existT].      *)
Theorem fa56c_max_entropy_production :
  forall (Flux TD : Set) (w : Flux -> R) (theta : TD -> R) (J0 : Flux)
         (X : TD),
    (forall J' : Flux, le (w J0) (w J')) ->
    lt zero (theta X) ->
    ExistsT (fun J : Flux => forall J' : Flux,
      le (fa56c_entropy_production_rate Flux TD w theta J X)
         (fa56c_entropy_production_rate Flux TD w theta J' X)).
Proof.
  intros Flux TD w theta J0 X Hdom Htheta.
  exact (existT _ J0
           (fun J' => le_mult_compat (w J0) (w J') (theta X) Htheta
                        (Hdom J'))).
Qed.

(* Constant-weight specialization: under the constant-one weight   *)
(* kernel any [J0] is a witness (weight dominance closes by        *)
(* [le_refl]).                                                     *)
Theorem fa56c_max_entropy_production_const :
  forall (Flux TD : Set) (theta : TD -> R) (J0 : Flux) (X : TD),
    ExistsT (fun J : Flux => forall J' : Flux,
      le (fa56c_entropy_production_rate Flux TD (fun _ => one) theta J X)
         (fa56c_entropy_production_rate Flux TD (fun _ => one) theta
            J' X)).
Proof.
  intros Flux TD theta J0 X.
  exact (existT _ J0 (fun J' => le_refl (mult one (theta X)))).
Qed.

(* [noneq_loss] mirror piece (isomorphic to the S05:5822           *)
(* [Definition noneq_loss]).                                       *)
Definition fa56c_noneq_loss (Flux TD : Set) (w : Flux -> R)
                            (theta : TD -> R) (J : Flux) (X : TD) : R :=
  opp (fa56c_entropy_production_rate Flux TD w theta J X).

Theorem fa56c_noneq_loss_mirror :
  forall (Flux TD : Set) (w : Flux -> R) (theta : TD -> R) (J : Flux)
         (X : TD),
    Id (fa56c_noneq_loss Flux TD w theta J X)
       (opp (mult (w J) (theta X))).
Proof. intros Flux TD w theta J X. reflexivity. Qed.

End Fa56cExt.

(* ============ Assumption-face closure report ============ *)

Print Assumptions fa56c_le_mult_compat_l.
Print Assumptions fa56c_lt_mult_compat_l.
Print Assumptions fa56c_default_token.
Print Assumptions fa56c_default_token_head.
Print Assumptions fa56c_default_token_singleton.
Print Assumptions fa56c_default_token_cons_preserves_nonempty.
Print Assumptions fa56c_prediction_landauer.
Print Assumptions fa56c_landauer_upper_bound.
Print Assumptions fa56c_loss_structure_correlation.
Print Assumptions fa56c_loss_structure_strict.
Print Assumptions fa56c_loss_structure_annealed.
Print Assumptions fa56c_max_entropy_production.
Print Assumptions fa56c_max_entropy_production_const.
Print Assumptions fa56c_noneq_loss_mirror.
