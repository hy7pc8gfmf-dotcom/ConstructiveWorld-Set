(* ===================================================================== *)
(*  abl_audit_base_v4.v - audit-carrier expansion v4: chained composite   *)
(*  carrier file, S06 chain closure site (Z report Sec.4 candidate 1).    *)
(*  Mission.: the Z bare-face Top3 row (two names, one row) chained       *)
(*  composite closure. Two carriers, three chain theorems on one line:    *)
(*  (1) abd_tv_contraction_twice_orbit, orbit-point form of the           *)
(*  twice-iterated single-step TV contraction, tv(step(step w),           *)
(*  p_attn) <= (1-d)*(1-d)*tv(w, p_attn): the contraction main theorem    *)
(*  (attention_tv_contraction) fires twice along the orbit, mid-state     *)
(*  norm/nonneg supplied by the preservation pair                         *)
(*  (attention_step_normalized / attention_step_nonneg); (2)              *)
(*  abd_iterate_converges_via_twice: the composite fed again into the     *)
(*  convergence main theorem (attention_iterate_converges) - under one    *)
(*  witness N, n-step iterate TV distance < eps (convergence face) and    *)
(*  (2+n)-step iterate TV distance <= (1-d)*(1-d)*eps (composite face);   *)
(*  the Top4 row is covered by the v2 file, not re-supplied here.         *)
(*  Dependencies.: S01_BaseRing S02_CauchyComplete S03_QExp               *)
(*  S04_RealExpLogConv S05_AlignmentGRPO S06_DiffSamplingGibbs (read-only *)
(*  -Q precompiled tree); tail Stdlib Extraction bay.                     *)
(*  References.: abl_audit_base_v2, same-family in-tree precedent shape.  *)
(*  Constructivity.: zero admissible sentences, zero classical logic,     *)
(*  zero Prop-valued carriers: existence/witnesses at sigT (Set level),   *)
(*  conjunctions S01_BaseRing.And, comparisons all Id/le/lt (Set-typed);  *)
(*  the orbit payload keeps its (N <= n) premise slot (Prop premise       *)
(*  position, lawful), converted at both consumption sites by the         *)
(*  in-tree NatLe_lift bridge; proof bodies are explicit terms.           *)
(*  Build.: env.sh sourced, COQLIB/ROCQLIB unset, ulimit -s 65532, then   *)
(*  rocq c -native-compiler no -q -Q <world-dir> "" abl_audit_base_v4.v   *)
(*  (exclusive pool audit_base_v4/, gate cap 1, no in-pool chain).        *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.

(* ============================================================ *)
(*  Verification note: the five main signatures on the chain are   *)
(*  shaped against Check-measured live closed forms one by one -   *)
(*  attention_iterate_converges carries the Hltc/Hlec dual         *)
(*  arithmetic-compatibility premises and the Hdecay geometric      *)
(*  decay witness premise; attention_tv_contraction carries Hd1     *)
(*  but not Hd0; attention_step_normalized carries neither Hmin     *)
(*  nor Hdb. iterate is the S01-own Fixpoint (induction on n,       *)
(*  S-side = f (iterate f n' x)), so iterate f (2+n) x ==           *)
(*  f (f (iterate f n x)) holds definitionally and the composite    *)
(*  face's orbit reindexing closes by conversion checking. The      *)
(*  abd_ prefix has zero grep hits in the whole tree. Top-level     *)
(*  statements keep the Section + Context class-argument wrapping   *)
(*  and carry every former section entry as an explicit premise     *)
(*  (checked: bare top-level class arguments leave evars open;      *)
(*  same-family shape as abl_audit_base_v2).                        *)
(* ============================================================ *)

(* ============================================================ *)
(*  Sec.1 carrier statement bay, composite first half:              *)
(*  single-step TV contraction x the preservation pair              *)
(*  implies the twice-iterated composite (orbit-point general form) *)
(* ============================================================ *)

Section AbdTvTwiceOrbit.

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

(* Carrier 1: the twice-iterated composite (orbit-point general form).   *)
(* For any normalized nonneg w, the TV distance after two attention      *)
(* steps shrinks by the (1-d)^2 factor - the single-step contraction     *)
(* main theorem fires once along the mid-state (step w) and once along   *)
(* the start w, whose normalization/nonneg the preservation pair         *)
(* supplies.                                                             *)
Theorem abd_tv_contraction_twice_orbit :
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
       forall w : S -> R,
       Id (sum_over_S w) one ->
       (forall s : S, le zero (w s)) ->
       le (tv_dist (attention_step transition (attention_step transition w))
                   (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
          (mult (minus one delta)
                (mult (minus one delta)
                      (tv_dist w
                         (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
Proof.
  intros sum_pos_preserved D D_pos energy transition
         Hrow Hdb delta Hd0 Hd1 Hmin Hltc Hswap Habs w Hw1 Hw2.
  apply (le_trans _
          (mult (minus one delta)
                (tv_dist (attention_step transition w)
                         (boltzmann_dist_attn sum_pos_preserved D D_pos energy))) _).
  - (* second step: contract (step w) once more; the mid-state's *)
    (* normalization/nonneg are supplied by the preservation pair *)
    exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
             Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs
             (attention_step transition w)
             (attention_step_normalized sum_pos_preserved D D_pos energy transition
                Hrow delta Hd1 Hltc Hswap w Hw1)
             (attention_step_nonneg sum_pos_preserved D D_pos energy transition delta
                Hd0 Hd1 Hmin Hltc w Hw1 Hw2)).
  - (* first-step factor: 0 < 1-d feeds the le_mult_compat_r scaling *)
    apply (le_mult_compat_r (minus one delta)
             (tv_dist (attention_step transition w)
                      (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
             (mult (minus one delta)
                   (tv_dist w
                      (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
    + exact (lt_le_iff zero (minus one delta)
              (inl (one_minus_delta_pos delta Hd1 Hltc))).
    + exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
               Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs w Hw1 Hw2).
Qed.

(* ============================================================ *)
(*  Sec.2 carrier statement bay, composite second half:             *)
(*  the twice-iterated composite (carrier 1) fed again into the     *)
(*  convergence main theorem - the chained closure site             *)
(*  (uses attention_iterate_converges + the n-step preservation     *)
(*  pair iterate_attention_normalized / iterate_attention_nonneg)   *)
(* ============================================================ *)

(* Carrier 2: both faces under one shared witness N -                    *)
(*   convergence face: for n >= N, tv(iterate n mu0, p_attn) < eps       *)
(*   (the convergence main theorem's output slots in verbatim);          *)
(*   composite face: for n >= N, tv(iterate (2+n) mu0, p_attn)           *)
(*             <= (1-d)*(1-d)*eps - carrier 1 fires along the orbit      *)
(*   point w := iterate n mu0 (its normalization/nonneg supplied by the  *)
(*   n-step preservation pair), then two scaling rounds bring it to eps. *)
(*   Both proof faces are the chain of three theorems on one line.       *)
Theorem abd_iterate_converges_via_twice :
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
       forall (Hlec : forall a b c d : R,
                 le a b -> lt c d -> lt (plus a c) (plus b d))
              (Hdecay : forall a : R,
                          lt zero a ->
                          forall eps : R, lt zero eps ->
                          sigT (fun N : nat =>
                            lt (mult a (r_pow (minus one delta) N)) eps))
              (mu0 : S -> R),
       Id (sum_over_S mu0) one ->
       (forall s : S, le zero (mu0 s)) ->
       forall eps : R,
       lt zero eps ->
       lt zero (tv_dist mu0
                  (boltzmann_dist_attn sum_pos_preserved D D_pos energy)) ->
       sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
         S01_BaseRing.And
           (lt (tv_dist (iterate (attention_step transition) n mu0)
                        (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
               eps)
           (le (tv_dist (iterate (attention_step transition) (2 + n)%nat mu0)
                        (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
               (mult (minus one delta) (mult (minus one delta) eps)))).
Proof.
  intros sum_pos_preserved D D_pos energy transition
         Hrow Hdb delta Hd0 Hd1 Hmin Hltc Hswap Habs
         Hlec Hdecay mu0 Hn Hnn eps Heps Hinit.
  destruct (attention_iterate_converges sum_pos_preserved D D_pos energy transition
              Hrow Hdb delta Hd0 Hd1 Hmin Hltc Hlec Hswap Habs Hdecay
              mu0 Hn Hnn eps Heps Hinit) as [N0 HconvN].
  exists N0. intros n Hn0.
  split.
  - (* convergence face: the convergence main theorem's output slots in *)
    (* verbatim; NatLe_lift bridges the payload premise to NatLe form   *)
    exact (HconvN n (NatLe_lift N0 n Hn0)).
  - (* composite face: carrier 1 fires along the orbit point, then two  *)
    (* scaling rounds bring it down to eps                              *)
    apply (le_trans _
            (mult (minus one delta)
                  (mult (minus one delta)
                        (tv_dist (iterate (attention_step transition) n mu0)
                                 (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))) _).
    + exact (abd_tv_contraction_twice_orbit
               sum_pos_preserved D D_pos energy transition
               Hrow Hdb delta Hd0 Hd1 Hmin Hltc Hswap Habs
               (iterate (attention_step transition) n mu0)
               (iterate_attention_normalized sum_pos_preserved D D_pos energy transition
                  Hrow delta Hd1 Hltc Hswap mu0 n Hn)
               (iterate_attention_nonneg sum_pos_preserved D D_pos energy transition
                  Hrow delta Hd0 Hd1 Hmin Hltc Hswap mu0 n Hn Hnn)).
    + apply (le_mult_compat_r (minus one delta)
               (mult (minus one delta)
                     (tv_dist (iterate (attention_step transition) n mu0)
                              (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))
               (mult (minus one delta) eps)).
      * exact (lt_le_iff zero (minus one delta)
                  (inl (one_minus_delta_pos delta Hd1 Hltc))).
      * apply (le_mult_compat_r (minus one delta)
                 (tv_dist (iterate (attention_step transition) n mu0)
                          (boltzmann_dist_attn sum_pos_preserved D D_pos energy)) eps).
        -- exact (lt_le_iff zero (minus one delta)
                    (inl (one_minus_delta_pos delta Hd1 Hltc))).
        -- exact (lt_le_iff
                    (tv_dist (iterate (attention_step transition) n mu0)
                             (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
                    eps (inl (HconvN n (NatLe_lift N0 n Hn0)))).
Qed.

End AbdTvTwiceOrbit.

(* ============================================================ *)
(*  Sec.3 tail bay - assumption audit (six cross-file faces of the  *)
(*  chain + the self-audit of this file's two carriers).            *)
(*  Reading rule: all eight lines print                             *)
(*  "Closed under the global context".                              *)
(*  First 6 = the six faces of the S06 convergence chain (single-   *)
(*  step contraction / single-step preservation pair / convergence  *)
(*  main theorem / n-step preservation pair), whose prior direct    *)
(*  whole-tree audit count is 0 (the Top3 row); last 2 = the two    *)
(*  carriers of this file. Carrier 2's assumption face includes, by *)
(*  transitive dependency, the union of the assumption faces of     *)
(*  carrier 1 and the six chain faces (composite audit              *)
(*  monotonicity, Z report Sec.4 candidate 1).                      *)
(* ============================================================ *)

Print Assumptions S06_DiffSamplingGibbs.attention_tv_contraction.
Print Assumptions S06_DiffSamplingGibbs.attention_step_normalized.
Print Assumptions S06_DiffSamplingGibbs.attention_step_nonneg.
Print Assumptions S06_DiffSamplingGibbs.attention_iterate_converges.
Print Assumptions S06_DiffSamplingGibbs.iterate_attention_normalized.
Print Assumptions S06_DiffSamplingGibbs.iterate_attention_nonneg.
Print Assumptions abd_tv_contraction_twice_orbit.
Print Assumptions abd_iterate_converges_via_twice.

(* ============================================================ *)
(*  Sec.4 exit bay: the carriers double as extraction ports         *)
(*  (rule: the extraction face carries zero magic constants)        *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abd_tv_contraction_twice_orbit abd_iterate_converges_via_twice.
