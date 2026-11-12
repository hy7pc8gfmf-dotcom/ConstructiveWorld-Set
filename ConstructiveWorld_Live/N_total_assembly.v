(* ConstructiveWorld-Set -- N_total_of_eps synthesis: the single explicit
   budget function of route 2 (work order R2-WD, steps P1-P2).

    Mission.  Assemble the N=max synthesis over the three upstream packages
      with no new mathematics: N_budget_w_of_eps (w-side slot, max of Nlo,
      Nup, Nwd), N_total_of_eps (four-source data-carrying main product),
      and N_total_sound (proof-bridge lifting all six source certificates
      past the synthesized budget through Nat.max dispatch).  Statement
      faces: nat / sigT / QltT carriers, zero Prop statement faces.  The
      w-side premise faces (cos diagonal, window certificates) are explicit
      parameters matching the S10 consumption shape (S10:8780-8786); the
      real_eq diagonal certificate is assembly-stage material not claimed
      here.

    Dependencies.  atan_expl_rate (W-B: atan_N_of_eps, atan_N_expl_spec),
      WC_budget_family (W-C: Nlo_of, Nup_of, Nwd_of, Nzd_of, wc_*_spec),
      vertex_window (W-A: vertex_abs_le_1_5, vertex_abs_le_1_239),
      S01_BaseRing, S02_CauchyComplete, S10_KVQuantTrig, S11_TP3B5; Stdlib
      QArith.QArith, QArith.Qabs, Arith.Arith.

    References.  Work order R2-WD P1-P2; W-C order section 3 handover.

    Constructivity.  Zero axioms, zero admitted goals; every statement face
      is Set-carried; Prop occurs only at premise positions.  The soundness
      lemma ends in Defined: pure existT assembly over the certificates.

    Build.  coqc -native-compiler no -q -Q <sandbox> "" -Q <set_src_world> ""
      N_total_assembly.v -- Rocq 9.3.0; the sandbox world carries the
      set_src-generation S01..S14 chain plus the three upstream deliverables
      compiled in the same world. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import atan_expl_rate.
Require Import WC_budget_family.
Require Import vertex_window.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ============================================================ *)
(* Section 1  w-side budget synthesis (skeleton slot 4)             *)
(*                                                                *)
(*   Max of the three window-budget moduli: lower window (Nlo),    *)
(*   upper window (Nup), and the window-diagonal cos modulus       *)
(*   (Nwd, scaled to eps/8 per the W-C delivery semantics).  The   *)
(*   premise faces match the S10 consumption shape exactly.        *)
(* ============================================================ *)

Definition N_budget_w_of_eps (w : Real)
  (Hw0 : real_eq (cauchy_real_cos w) real_zero)
  (Hlow : real_lt (real_const (3#2)) w)
  (Hup : real_lt w (real_const (5#3)))
  (eps : Q) (Heps : Qlt 0 eps) : nat :=
  Nat.max (Nlo_of w Hlow) (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps)).

(* ============================================================ *)
(* Section 2  N=max synthesis (data-carrying main product)          *)
(*                                                                *)
(*   Four sources: the 1/5 band and the 1/239 band from W-B, the   *)
(*   cos_pi_half diagonal modulus Nzd from W-C, and the w-side     *)
(*   budget from Section 1.  Each source dominates: Nat.max on     *)
(*   the right keeps the synthesized budget above every source.    *)
(* ============================================================ *)

Definition N_total_of_eps (w : Real)
  (Hw0 : real_eq (cauchy_real_cos w) real_zero)
  (Hlow : real_lt (real_const (3#2)) w)
  (Hup : real_lt w (real_const (5#3)))
  (eps : Q) (Heps : Qlt 0 eps) : nat :=
  Nat.max (atan_N_of_eps (1#5) eps)
          (Nat.max (atan_N_of_eps (1#239) eps)
                   (Nat.max (Nzd_of eps Heps)
                            (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))).

(* ============================================================ *)
(* Section 3  Synthesis soundness (proof-bridge)                    *)
(*                                                                *)
(*   Four sources sound at their own moduli (atan_N_expl_spec on   *)
(*   both bands; the four wc_*_spec bridges) lift to the           *)
(*   synthesized budget: past N_total_of_eps every source          *)
(*   certificate holds simultaneously.  The conjunction of six     *)
(*   Set-sorted certificates is carried by a sigT chain (R8);      *)
(*   each certificate is discharged by max dispatch and direct     *)
(*   consumption of the upstream specification bridge.             *)
(* ============================================================ *)

Lemma N_total_sound : forall (w : Real)
  (Hw0 : real_eq (cauchy_real_cos w) real_zero)
  (Hlow : real_lt (real_const (3#2)) w)
  (Hup : real_lt w (real_const (5#3)))
  (eps : Q) (Heps : Qlt 0 eps) (m n : nat),
  (N_total_of_eps w Hw0 Hlow Hup eps Heps <= m)%nat -> (m <= n)%nat ->
  sigT (fun c1 : QltT (Qabs (arctan_partial n (1#5) - arctan_partial m (1#5))) eps =>
        sigT (fun c2 : QltT (Qabs (arctan_partial n (1#239) - arctan_partial m (1#239))) eps =>
        sigT (fun c3 : QltT (projT1 Hlow) (projT1 w n - projT1 (real_const (3#2)) n) =>
        sigT (fun c4 : QltT (projT1 Hup) (projT1 (real_const (5#3)) n - projT1 w n) =>
        sigT (fun c5 : QltT (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                           (eps / 8) =>
              QltT (Qabs (projT1 (cauchy_real_cos cos_pi_half) n
                          - projT1 real_zero n)) (eps / 8)))))).
Proof.
  intros w Hw0 Hlow Hup eps Heps m n HN Hmn.
  (* Max dispatch: every source modulus is at most the synthesized budget
     (Nat.le_max_l / Nat.le_max_r chains), and m >= budget with m <= n
     puts every index past its own source modulus.  All chains are written
     with explicit middle terms (no evar inference in nested le_trans). *)
  assert (H1 : (atan_N_of_eps (1#5) eps <= m)%nat)
    by exact (Nat.le_trans (atan_N_of_eps (1#5) eps)
                (N_total_of_eps w Hw0 Hlow Hup eps Heps) m
                (Nat.le_max_l (atan_N_of_eps (1#5) eps)
                   (Nat.max (atan_N_of_eps (1#239) eps)
                      (Nat.max (Nzd_of eps Heps)
                         (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))))
                HN).
  assert (H2 : (atan_N_of_eps (1#239) eps <= m)%nat)
    by exact (Nat.le_trans (atan_N_of_eps (1#239) eps)
                (Nat.max (atan_N_of_eps (1#239) eps)
                   (Nat.max (Nzd_of eps Heps)
                      (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))) m
                (Nat.le_max_l (atan_N_of_eps (1#239) eps)
                   (Nat.max (Nzd_of eps Heps)
                      (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)))
                (Nat.le_trans (Nat.max (atan_N_of_eps (1#239) eps)
                                (Nat.max (Nzd_of eps Heps)
                                   (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)))
                   (N_total_of_eps w Hw0 Hlow Hup eps Heps) m
                   (Nat.le_max_r (atan_N_of_eps (1#5) eps)
                      (Nat.max (atan_N_of_eps (1#239) eps)
                         (Nat.max (Nzd_of eps Heps)
                            (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))))
                   HN)).
  assert (Hw : (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps <= m)%nat)
    by exact (Nat.le_trans (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)
                (Nat.max (Nzd_of eps Heps)
                   (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)) m
                (Nat.le_max_r (Nzd_of eps Heps)
                   (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))
                (Nat.le_trans (Nat.max (Nzd_of eps Heps)
                                (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))
                   (Nat.max (atan_N_of_eps (1#239) eps)
                      (Nat.max (Nzd_of eps Heps)
                         (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))) m
                   (Nat.le_max_r (atan_N_of_eps (1#239) eps)
                      (Nat.max (Nzd_of eps Heps)
                         (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)))
                   (Nat.le_trans (Nat.max (atan_N_of_eps (1#239) eps)
                                   (Nat.max (Nzd_of eps Heps)
                                      (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)))
                      (N_total_of_eps w Hw0 Hlow Hup eps Heps) m
                      (Nat.le_max_r (atan_N_of_eps (1#5) eps)
                         (Nat.max (atan_N_of_eps (1#239) eps)
                            (Nat.max (Nzd_of eps Heps)
                               (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))))
                      HN))).
  assert (Hzd : (Nzd_of eps Heps <= m)%nat)
    by exact (Nat.le_trans (Nzd_of eps Heps)
                (Nat.max (Nzd_of eps Heps)
                   (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)) m
                (Nat.le_max_l (Nzd_of eps Heps)
                   (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))
                (Nat.le_trans (Nat.max (Nzd_of eps Heps)
                                (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))
                   (Nat.max (atan_N_of_eps (1#239) eps)
                      (Nat.max (Nzd_of eps Heps)
                         (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))) m
                   (Nat.le_max_r (atan_N_of_eps (1#239) eps)
                      (Nat.max (Nzd_of eps Heps)
                         (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)))
                   (Nat.le_trans (Nat.max (atan_N_of_eps (1#239) eps)
                                   (Nat.max (Nzd_of eps Heps)
                                      (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps)))
                      (N_total_of_eps w Hw0 Hlow Hup eps Heps) m
                      (Nat.le_max_r (atan_N_of_eps (1#5) eps)
                         (Nat.max (atan_N_of_eps (1#239) eps)
                            (Nat.max (Nzd_of eps Heps)
                               (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps))))
                      HN))).
  assert (Hlo : (Nlo_of w Hlow <= m)%nat)
    by exact (Nat.le_trans (Nlo_of w Hlow)
                (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps) m
                (Nat.le_max_l (Nlo_of w Hlow)
                   (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps)))
                Hw).
  assert (Hupn : (Nup_of w Hup <= m)%nat)
    by exact (Nat.le_trans (Nup_of w Hup)
                (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps)) m
                (Nat.le_max_l (Nup_of w Hup) (Nwd_of w Hw0 eps Heps))
                (Nat.le_trans (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps))
                   (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps) m
                   (Nat.le_max_r (Nlo_of w Hlow)
                      (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps)))
                   Hw)).
  assert (Hwd : (Nwd_of w Hw0 eps Heps <= m)%nat)
    by exact (Nat.le_trans (Nwd_of w Hw0 eps Heps)
                (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps)) m
                (Nat.le_max_r (Nup_of w Hup) (Nwd_of w Hw0 eps Heps))
                (Nat.le_trans (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps))
                   (N_budget_w_of_eps w Hw0 Hlow Hup eps Heps) m
                   (Nat.le_max_r (Nlo_of w Hlow)
                      (Nat.max (Nup_of w Hup) (Nwd_of w Hw0 eps Heps)))
                   Hw)).
  (* Index transport: the wc_*_spec bridges bind their tail at n, so every
     modulus bound is lifted from m to n through Hmn first. *)
  assert (Hzd_n : (Nzd_of eps Heps <= n)%nat)
    by exact (Nat.le_trans (Nzd_of eps Heps) m n Hzd Hmn).
  assert (Hlo_n : (Nlo_of w Hlow <= n)%nat)
    by exact (Nat.le_trans (Nlo_of w Hlow) m n Hlo Hmn).
  assert (Hup_n : (Nup_of w Hup <= n)%nat)
    by exact (Nat.le_trans (Nup_of w Hup) m n Hupn Hmn).
  assert (Hwd_n : (Nwd_of w Hw0 eps Heps <= n)%nat)
    by exact (Nat.le_trans (Nwd_of w Hw0 eps Heps) m n Hwd Hmn).
  (* Source 1/2: arctan bands via atan_N_expl_spec (its own slots take m
     then m <= n, so the raw bounds H1/H2 with Hmn are already shaped). *)
  exists (atan_N_expl_spec (1#5) eps vertex_abs_le_1_5 Heps m n H1 Hmn).
  exists (atan_N_expl_spec (1#239) eps vertex_abs_le_1_239 Heps m n H2 Hmn).
  (* Sources 3-6: the four wc specification bridges at n. *)
  exists (wc_Nlo_of_spec w Hlow n (NatLe_lift (Nlo_of w Hlow) n Hlo_n)).
  exists (wc_Nup_of_spec w Hup n (NatLe_lift (Nup_of w Hup) n Hup_n)).
  exists (wc_Nwd_of_spec w Hw0 eps Heps n Hwd_n).
  exact (wc_Nzd_of_spec eps Heps n Hzd_n).
Defined.

(* Assumption-face print anchors: every statement must report
   "Closed under the global context". *)
Print Assumptions N_budget_w_of_eps.
Print Assumptions N_total_of_eps.
Print Assumptions N_total_sound.
