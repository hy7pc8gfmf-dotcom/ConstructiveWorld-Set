(* ConstructiveWorld-Set -- the Paper7-ablation squeeze statement families with instance forms. *)
(** * UpAblP7_LoHiSqueeze: the lo/hi squeeze statement families on the
    Paper7 ablation base, in two parallel series plus instance forms.

    Mission.  The [lhs_] family ([lhs_lo_lt_one_hi], [lhs_lo_lt_hi],
      [lhs_delta_star_bounded], [lhs_omd_bounded]); the independently
      re-proven [uahl_] family ([uahl_lo_lt_one_hi], [uahl_lo_lt_hi],
      [uahl_delta_star_bounded], [uahl_omd_bounded]); instance forms
      ([uahl_omd_bounded_one], [uahl_lo_lt_hi_one] at one/one;
      [uahl_omd_bounded_half] at lo := one half).

    Dependencies.  This development: [S01_BaseRing], [Paper7Ablation],
      [P7BoundedSoftmaxDeep]; no direct Stdlib requires.

    References.  Paper7Ablation.v ([p7a_lo_lt_one], [p7a_delta_star_pos],
      [p7a_omd_pos], [p7a_omd_lt_one]); P7BoundedSoftmaxDeep.v
      ([p7d_hi_gt_one]); S01_BaseRing.v ([inv_pos], [half_twice],
      [two_pos]); AttnDoeblin.bs_lo_lt_hi (:565 alignment); the same-name
      ConstructiveWorld-Main baseline; parallel copy ToyR_UpAblP7_LoHiSqueeze.v.

    Constructivity.  Every proof closed by [Qed]; axiom-free; no classical
      logic; statements Set-carried with no Prop leakage;
      [Print Assumptions] blocks at each section close.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpAblP7_LoHiSqueeze.v]. *)

(* The UahlStar section is textually identical (empty diff) to the same-named
   section of ToyR_UpAblP7_LoHiSqueeze.v; retiring the older parallel copy is a
   usage-face ruling made elsewhere; this note does not touch the statement face. *)
Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.

(* ================= §1 the lhs_lo_lt_one_hi family ================= *)
(* ################ Part 1: conjunction packaging, the squeeze corollary, δ* ∈ (0,1) (no DO) #### *)
(* Cross-reference -548: lo := expf(invT·oppΔ), hi := expf(invT·Δ). *)

Section LhsPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* Part (a): the conjunction packaging -- lt lo one ∧ lt one hi (Set-level
   And = prod).
   The left component uses [p7a_lo_lt_one] (the pruned form: the five
   arguments Delta/Delta_pos/expf/expf_zero/expf_mono_lt plus invT;
   [inv_pos_pos] discharges the premise lt zero invT by instantiation);
   the right component uses [p7d_hi_gt_one] (the universally quantified
   8-argument form, with the full temp face). *)
Theorem lhs_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* Part (b): the squeeze corollary -- lt lo hi (one [lt_trans] step, both
   components drawn from the conjunction packaging).
   The statement aligns with the base module AttnDoeblin.bs_lo_lt_hi:565
   with the same premise face (B-class certificate). *)
Theorem lhs_lo_lt_hi : lt lo hi.
Proof.
  assert (Hlo : lt lo one).
  { exact (fst lhs_lo_lt_one_hi). }
  assert (Hhi : lt one hi).
  { exact (snd lhs_lo_lt_one_hi). }
  exact (lt_trans lo one hi Hlo Hhi).
Qed.

(* Part (c): the full packaging of 0 < δ* < 1 (Set-level And).
   Left component: [p7a_delta_star_pos] (check signature
   forall lo, lt zero lo -> ...; the DO/temp faces are already pruned by
   the section exit, and lo_pos := expf_pos(invT·oppΔ) supplies it
   directly).
   Right component (a fresh derivation of δ* < 1): lo < 1 (left component
   of the conjunction packaging) and lo > 0 imply lo·lo < lo·1
   ([lt_mult_compat] preserves the strict order under right multiplication
   by lo) = lo ([mult_one], the right unit law, lowered through
   [lt_id_r]) < 1 (reusing lo < 1) -- joined by [lt_trans]. *)
Theorem lhs_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End LhsPair.

(* ############ Part 2: joining the κ := 1−δ* ∈ (0,1) premise package (DO section) ######## *)
(* p7a_omd_pos/p7a_omd_lt_one keep the DO argument after the section exit
   (the fa53 usage chain); their implicit argument cannot be recovered
   from the conclusion, so the fully applied form @ RI DO must be supplied
   (the P7A card's usage precedent). *)

Section LhsStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* Part (d): the full packaging of 0 < 1−δ* < 1 (the κ ∈ (0,1) premise
   package of paper §6.3).
   Left component: [p7a_omd_pos] applied to the right component of part (c)
   (δ* < 1 implies 0 < κ).
   Right component: [p7a_omd_lt_one] applied to lo_pos (0 < δ* implies
   κ < 1).
   The two post-section premises (the δ* < 1 premise and the lo_pos
   premise) are discharged by instantiation from part (c) of the previous
   section and from the expf_pos field certificate, respectively. *)
Theorem lhs_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End LhsStar.

(* ---- Print Assumptions self-check block (the G1 min-pa and G4 review
   record face; all names global after section exit) ---- *)
Print Assumptions lhs_lo_lt_one_hi.
Print Assumptions lhs_lo_lt_hi.
Print Assumptions lhs_delta_star_bounded.
Print Assumptions lhs_omd_bounded.
(* ================= §2 the uahl_lo_lt_one_hi family ================= *)
(* ############ Part 1: the conjunction lo<1∧1<hi, the squeeze lo<hi, δ*∈(0,1) (no decidable-order argument) ## *)
(* The section-variable face matches the LhsPair section of the source
   module (the temperature pair, the spread pair, and the four
   exponential-family fields). *)

Section UahlPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* uahl_lo_lt_one_hi (an independent re-proof of the source module's
   lhs_lo_lt_one_hi): the left component via [p7a_lo_lt_one], the right
   component via [p7d_hi_gt_one]; the positivity of invT is supplied by
   [inv_pos_pos]. *)
Theorem uahl_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* uahl_lo_lt_hi (an independent re-proof of the source module's
   lhs_lo_lt_hi): [lt_trans] composes the two steps, with both components
   taken from the two conjuncts of uahl_lo_lt_one_hi. *)
Theorem uahl_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst uahl_lo_lt_one_hi) (snd uahl_lo_lt_one_hi)).
Qed.

(* uahl_delta_star_bounded (an independent re-proof of the source module's
   lhs_delta_star_bounded): the left component by [p7a_delta_star_pos];
   the right component, δ* < 1, by an independent three-step chain:
   [lt_mult_compat], [lt_id_l] (through [mult_one]), and [lt_trans]. *)
Theorem uahl_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End UahlPair.

(* ############ Part 2: uahl_omd_bounded -- κ := 1−δ*∈(0,1) (section with a decidable-order argument) #### *)
(* The section-variable face matches the LhsStar section of the source
   module; the decidable-order implicit argument of
   p7a_omd_pos/p7a_omd_lt_one cannot be recovered from the conclusion, so
   they are applied fully and explicitly with @. *)

Section UahlStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* uahl_omd_bounded (an independent re-proof of the source module's
   lhs_omd_bounded): the left component applies @p7a_omd_pos with the
   δ* < 1 premise; the right component applies @p7a_omd_lt_one with
   0 < lo -- fully explicit application. *)
Theorem uahl_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End UahlStar.

(* ########## Part 3: instance form A -- uahl_omd_bounded/uahl_lo_lt_hi @ temperature := 1, spread := 1 ## *)
(* Both the temperature and the spread are taken as [one] ([one_pos]
   supplies the two positivity premises), invT := inv_pos one one_pos;
   the exponential family stays abstract (the repository has no concrete
   real-number instance). *)

Section UahlSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).

(* uahl_omd_bounded_one (the instance form of uahl_omd_bounded at
   temperature := 1 and spread := 1): [p7a_lo_lt_one] @ one/one supplies
   lo < 1, [expf_pos] supplies 0 < lo, and the δ* < 1 three-step chain is
   inlined -- fully explicit @ application. *)
Theorem uahl_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT
             (inv_pos_pos one one_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp one))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

(* uahl_lo_lt_hi_one (the instance form of uahl_lo_lt_hi at the same
   instance): [p7a_lo_lt_one] @ one/one supplies lo < 1 and
   [p7d_hi_gt_one] @ one/one supplies 1 < hi, composed by [lt_trans]. *)
Theorem uahl_lo_lt_hi_one :
  lt (expf (mult invT (opp one))) (expf (mult invT one)).
Proof.
  exact (lt_trans (expf (mult invT (opp one))) one (expf (mult invT one))           (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT              (inv_pos_pos one one_pos))           (p7d_hi_gt_one one one_pos one one_pos expf expf_pos expf_zero              expf_mono_lt)).
Qed.

End UahlSbInst.

(* ############ Part 4: instance form B -- uahl_omd_bounded @ lo := one half, abstract form ######## *)
(* lo := inv_pos (plus one one) two_pos (one half; [two_pos]/[inv_pos_pos]
   supply the positivity);
   the left component avoids the δ* < 1 detour and runs an independent
   chain: [half_twice] (half + half = 1, half² + half² = half) with
   [plus_positive] (half² > 0) and identity rearrangements, deriving
   0 < 1 − 1/4;
   the right component by @p7a_omd_lt_one. *)

Section UahlHalf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* uahl_omd_bounded_half (instance form B) *)
Theorem uahl_omd_bounded_half :
  And (lt zero (minus one half2)) (lt (minus one half2) one).
Proof.
  assert (Hhp : lt zero half).
  { exact (inv_pos_pos (plus one one) two_pos). }
  assert (Hh2p : lt zero half2).
  { exact (mult_positive half half Hhp Hhp). }
  assert (Hh2p2 : lt zero (plus half2 half2)).
  { exact (plus_positive half2 half2 Hh2p Hh2p). }
  assert (Hq : Id (plus half2 half2) half).
  { exact (half_twice half). }
  assert (Hone : Id (plus half half) one).
  { exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                    (half_twice one)). }
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans (id_sym Hone) (id_sym (id_cong (fun x => plus x x) Hq))). }
  assert (Gup : Id (plus (plus (plus half2 half2) (plus half2 half2))
                         (opp half2))
                   (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (plus_assoc (plus half2 half2) (plus half2 half2)
                       (opp half2)))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_trans (id_sym (plus_assoc half2 half2 (opp half2)))
                      (id_trans
                         (id_cong (fun w => plus half2 w)
                            (plus_comm half2 (opp half2)))
                         (plus_assoc half2 (opp half2) half2))))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_cong (fun w => plus w half2) (plus_opp half2)))
                (id_trans
                   (id_cong (fun x => plus (plus half2 half2) x)
                      (id_trans (plus_comm zero half2) (plus_zero half2)))
                   (id_sym (plus_assoc half2 half2 half2)))))). }
  assert (Gtotal : Id (minus one half2) (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_cong (fun w => plus w (opp half2)) (id_sym Hone2)))
             Gup). }
  split.
  - exact (lt_id_r zero (plus half2 (plus half2 half2)) (minus one half2)
             (id_sym Gtotal)
             (plus_positive half2 (plus half2 half2) Hh2p Hh2p2)).
  - exact (@p7a_omd_lt_one RI DO half Hhp).
Qed.

End UahlHalf.

(* ---- Closing block: per-theorem [Print Assumptions] audit of the assumption set ---- *)
Print Assumptions uahl_lo_lt_one_hi.
Print Assumptions uahl_lo_lt_hi.
Print Assumptions uahl_delta_star_bounded.
Print Assumptions uahl_omd_bounded.
Print Assumptions uahl_omd_bounded_one.
Print Assumptions uahl_lo_lt_hi_one.
Print Assumptions uahl_omd_bounded_half.
