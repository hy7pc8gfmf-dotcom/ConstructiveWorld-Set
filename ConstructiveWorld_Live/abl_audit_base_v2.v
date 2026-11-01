(* ===================================================================== *)
(*  abl_audit_base_v2.v -- audit carrier expansion v2, form-A closure 2.   *)
(*  Mission.: certified-carrier module (Z report Sec.2 four-bay spec):     *)
(*        independent bare-run-face audit carrier for the true use sites   *)
(*        of the S06 single-step TV contraction main theorem and the S04   *)
(*        Boltzmann normalization main theorem, plus a tail-bay Print      *)
(*        Assumptions direct audit (cross-module type). Closes Z report    *)
(*        Sec.3.3 bare-run Top10 next ranks: Top3 attention_tv_contraction;*)
(*        Top4 boltzmann_normalized with boltzmann_dist_temp_normalized    *)
(*        (both names used in one row). New non-empty statements: (1)      *)
(*        abb_tv_contraction_twice (single-step contraction iterated       *)
(*        twice via preservation pair attention_step_normalized /          *)
(*        attention_step_nonneg; bound (1-d)^2 * TV(mu)); (2)              *)
(*        abb_boltzmann_pair_mass_two (total mass identity equals 2 of     *)
(*        the pointwise two-family Boltzmann sum, wrapping both            *)
(*        normalization facts via sum_over_S_add).                         *)
(*  Dependencies.: S01_BaseRing S02_CauchyComplete S03_QExp                *)
(*        S04_RealExpLogConv S05_AlignmentGRPO S06_DiffSamplingGibbs       *)
(*        (read-only -Q precompiled tree); tail Stdlib Extraction bay.     *)
(*  References.: Z report Sec.2 spec; family precedent                     *)
(*        abl_audit_base_v5 (registered in the Live tree).                 *)
(*  Constructivity.: zero admissible sentences, zero classical logic;      *)
(*        statement faces at the Set layer (Id/le/lt); explicit            *)
(*        id_trans/id_cong/exact proof chains, no tactic guessing. Tail:   *)
(*        six Print Assumptions checks + Separate Extraction exit bay.     *)
(*  Build.: <Live toolchain opam live>/bin/rocq c -native-compiler no      *)
(*        -Q vo_local_world_unified_0930 "" (exclusive pool                *)
(*        audit_base_v2/, gate cap 1, single file, no in-pool chain).      *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.

(* ============================================================ *)
(*  Verification note: both upstream main theorems are fully       *)
(*  parameterized once their Sections close (sum_pos_preserved,    *)
(*  D, D_pos, energy, transition, row-stochasticity, detailed      *)
(*  balance, delta, lower bound, arithmetic compatibility, sum     *)
(*  swap, abs compatibility); statements in this file were shaped  *)
(*  against verified live signatures and match the Z report text.  *)
(*  Top-level statements keep the Section + Context class-argument *)
(*  wrapping (checked: bare top-level class arguments leave evars  *)
(*  open).                                                         *)
(* ============================================================ *)

(* ============================================================ *)
(*  Sec.1 carrier statement bay, Top3 rank: two-fold iteration      *)
(*  composite corollary of the single-step TV contraction           *)
(*  (consumes S06.attention_tv_contraction + the preservation       *)
(*  pair)                                                           *)
(* ============================================================ *)

Section AbbTvTwice.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let minus := @minus RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Theorem abb_tv_contraction_twice :
  forall (sum_pos_preserved : forall f : S -> R,
                              (forall s : S, lt zero (f s)) ->
                              lt zero (sum_over_S f))
         (D : R) (D_pos : lt zero D) (energy : @logits RI SS)
         (transition : S -> S -> R),
       (forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one) ->
       (forall s s' : S,
        Id (mult (boltzmann_dist_attn sum_pos_preserved D D_pos energy s)
                  (transition s s'))
           (mult (boltzmann_dist_attn sum_pos_preserved D D_pos energy s')
                 (transition s' s))) ->
       forall delta : R,
       lt zero delta ->
       lt delta one ->
       (forall s s' : S,
        le (mult delta (boltzmann_dist_attn sum_pos_preserved D D_pos energy s'))
           (transition s s')) ->
       (forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d)) ->
       (forall f : S -> S -> R,
        Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
           (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s')))) ->
       (forall a : R, le zero a -> Id (abs a) a) ->
       forall mu : S -> R,
       Id (sum_over_S mu) one ->
       (forall s : S, le zero (mu s)) ->
       le (tv_dist (attention_step transition (attention_step transition mu))
                   (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
          (mult (minus one delta)
                (mult (minus one delta)
                      (tv_dist mu (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
Proof.
  intros sum_pos_preserved D D_pos energy transition
         Hrow Hdb delta Hd0 Hd1 Hmin Hltc Hswap Habs mu Hn Hnn.
  apply (le_trans _
          (mult (minus one delta)
                (tv_dist (attention_step transition mu)
                         (boltzmann_dist_attn sum_pos_preserved D D_pos energy))) _).
  - (* second step: contract step mu once more (norm/nonneg are *)
    (* supplied by the preservation pair) *)
    exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
             Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs
             (attention_step transition mu)
             (attention_step_normalized sum_pos_preserved D D_pos energy transition
                Hrow delta Hd1 Hltc Hswap mu Hn)
             (attention_step_nonneg sum_pos_preserved D D_pos energy transition delta
                Hd0 Hd1 Hmin Hltc mu Hn Hnn)).
  - (* first-step factor: (1-d) * TV(step mu) <= (1-d) * ((1-d) * TV mu) *)
    apply (le_mult_compat_r (minus one delta)
             (tv_dist (attention_step transition mu)
                      (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
             (mult (minus one delta)
                   (tv_dist mu (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
    + exact (lt_le_iff zero (minus one delta)
              (inl (one_minus_delta_pos delta Hd1 Hltc))).
    + exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
               Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs mu Hn Hnn).
Qed.

End AbbTvTwice.

(* ============================================================ *)
(*  Sec.2 carrier statement bay, Top4 rank: probability mass        *)
(*  wrapping of the two temperature families                        *)
(*  (consumes S04.boltzmann_normalized and                          *)
(*  boltzmann_dist_temp_normalized)                                 *)
(* ============================================================ *)

Section AbbPairMass.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let minus := @minus RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Theorem abb_boltzmann_pair_mass_two :
  forall (base_loss : S -> R)
         (D : R) (D_pos : lt zero D) (Z : R) (Z_pos : lt zero Z)
         (HZ : Id Z (sum_over_S (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
         (sum_pos : forall f : S -> R,
                      (forall s : S, lt zero (f s)) ->
                      lt zero (sum_over_S f))
         (Z_temp : R -> R)
         (Z_spec : forall (t : R) (Ht : lt zero t),
                     Id (Z_temp t)
                        (sum_over_S (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))))
         (t : R) (Ht : lt zero t),
       Id (sum_over_S (fun s : S =>
              plus (boltzmann_dist base_loss D D_pos Z Z_pos s)
                   (boltzmann_dist_temp base_loss sum_pos Z_temp Z_spec t Ht s)))
          (plus one one).
Proof.
  intros base_loss D D_pos Z Z_pos HZ sum_pos Z_temp Z_spec t Ht.
  exact (id_trans
          (* sum linearity splits the addition *)
          (sum_over_S_add (boltzmann_dist base_loss D D_pos Z Z_pos)
                          (boltzmann_dist_temp base_loss sum_pos Z_temp Z_spec t Ht))
          (* the two normalization facts slot in *)
          (id_trans
            (id_cong (fun x : R => plus x (sum_over_S (boltzmann_dist_temp base_loss sum_pos Z_temp Z_spec t Ht)))
                     (boltzmann_normalized base_loss D D_pos Z Z_pos HZ))
            (id_cong (fun y : R => plus one y)
                     (boltzmann_dist_temp_normalized base_loss sum_pos Z_temp Z_spec t Ht)))).
Qed.

End AbbPairMass.

(* ============================================================ *)
(*  Sec.3 tail bay: assumption audit (the two new statements +      *)
(*  four cross-module upstream statements)                          *)
(*  reading rule: all six lines must print                          *)
(*  "Closed under the global context"                               *)
(* ============================================================ *)

Print Assumptions abb_tv_contraction_twice.
Print Assumptions abb_boltzmann_pair_mass_two.
Print Assumptions S06_DiffSamplingGibbs.attention_tv_contraction.
Print Assumptions S06_DiffSamplingGibbs.attention_iterate_converges.
Print Assumptions S04_RealExpLogConv.boltzmann_normalized.
Print Assumptions S04_RealExpLogConv.boltzmann_dist_temp_normalized.

(* ============================================================ *)
(*  Sec.4 exit bay: the carrier doubles as an extraction port       *)
(*  (rule: zero Obj.magic)                                          *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abb_tv_contraction_twice abb_boltzmann_pair_mass_two.
