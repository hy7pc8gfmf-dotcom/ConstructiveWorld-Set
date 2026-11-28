(* ========================================================================== *)
(* Module   : abl_tail_slot_upgrade                                          *)
(* Mission. : general cons-shape supply for six undersupplied tail slots.   *)
(*   (1) Nonempty decidable Id-face family: the boolean cons discriminator  *)
(*   cons_nonempty_bool over any Set carrier (nil reads false, cons reads   *)
(*   true), with its general pin (Id (cons_nonempty_bool (x :: rest))       *)
(*   true), the bool two-point instance, three named slot pins, a concrete  *)
(*   nat-list readout, and the cons-shape length-positivity consumption     *)
(*   instance (direct arithmetic route).  (2) Nonempty equality-face slot:  *)
(*   the same discriminator pin recarried on the Set-sorted leiblw_Id       *)
(*   window, with its named slot pin.  (3) A pair of distribution bridges   *)
(*   over a finite-sum interface: the energy-in-log and free-energy         *)
(*   Boltzmann identities restated verbatim on the migrated cwe_* carrier,  *)
(*   proved by direct reuse of the logc_* engines with positivity           *)
(*   certificates transcribed pointwise through sup_compat, plus the two    *)
(*   consumption theorems with bridge positions filled by these two         *)
(*   supplies.                                                              *)
(* Dependencies. : S01_BaseRing (Set-sorted Id, id_eq_SI), LW0LeibWindow    *)
(*   (leiblw_Id Set window), UpReqLogCompD (logc_* engines), Arch_Up_01     *)
(*   (kvev cons-branch arithmetic steps), Arch_PA_04 (SigMigrate cwe set),  *)
(*   Stdlib List; concrete Real faces and real_lt positivity faces by full  *)
(*   path (S02/S07/S08/S13).                                                *)
(* References. : P7BoundedSoftmaxDeep :161/:374; Arch_Up_01 :272/:327;      *)
(*   UpAblP2WByPass :111; Arch_PA_04 ReqFreeEnergyPilot :910-917 and        *)
(*   :1108-1110/:1147-1157; UpReqLogCompD engine lemmas.                    *)
(* Constructivity. : every statement face is Set-carried (S01 Id and        *)
(*   leiblw_Id Set-sorted; req/lt Set-valued at the concrete Real carrier): *)
(*   zero Prop statement faces, zero axioms, zero admits, zero classical    *)
(*   logic, no Prop component inside any Set carrier.  Cure record: the     *)
(*   five former Not-of-Id statements and the window form are recast as     *)
(*   decidable boolean pins on cons_nonempty_bool; the old                  *)
(*   constructor-conflict carrier cons_nonempty_case and its dependent      *)
(*   match family (unit vs Empty_set arms) — the one Obj.magic at the       *)
(*   extraction census — are removed.  The original Not-of-Id content       *)
(*   survives as in-body constructivity derivations at the Prop face (Id-   *)
(*   to-eq readout via id_eq_SI, constructor discrimination, nil arm of     *)
(*   the boolean dichotomy killed by the Id-face refutation), which         *)
(*   extraction erases; the Set-sorted Not premise of kvev_list_len_pos is  *)
(*   that same conflict face, so its cons-branch arithmetic steps are       *)
(*   reused directly.  Definitions and pins transparent (Defined); Qed      *)
(*   closures follow the in-tree Set-carried precedent (Group 3 unchanged). *)
(* Build. : rocq c -native-compiler no -q -Q <Set Live root> ""            *)
(*   abl_tail_slot_upgrade.v (single shot; r237 driver adds the verdict).   *)
(* ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
Require Import S01_BaseRing.
Require Import LW0LeibWindow.
Require Import UpReqLogCompD.
Require Import Arch_Up_01.
Require Import Arch_PA_04.

(* Concrete-carrier pins: every algebra face below is the global Real twin, *)
(* spelled by full path so no import order can split a face.                *)
Abbreviation R := S02_CauchyComplete.Real.
Abbreviation req := S02_CauchyComplete.real_eq.
Abbreviation req_refl := S02_CauchyComplete.real_eq_refl.
Abbreviation req_trans := S02_CauchyComplete.real_eq_trans.
Abbreviation zero := S02_CauchyComplete.real_zero.
Abbreviation real_one := S02_CauchyComplete.real_one.
Abbreviation plus := S02_CauchyComplete.real_plus.
Abbreviation mult := S02_CauchyComplete.real_mult.
Abbreviation opp := S02_CauchyComplete.real_opp.
Abbreviation lt := S02_CauchyComplete.real_lt.
Abbreviation log := S07_RealSetoidExpLog.real_log.
Abbreviation exp_neg := S07_RealSetoidExpLog.real_exp_neg.
Abbreviation exp_neg_pos := S07_RealSetoidExpLog.real_exp_neg_pos.
Abbreviation inv_pos := S03_QExp.real_inv_pos.
Abbreviation req_plus_compat :=
  S07_RealSetoidExpLog.RealSetoid.real_eq_plus_compat_adapt.
Abbreviation req_mult_compat :=
  S07_RealSetoidExpLog.RealSetoid.real_eq_mult_compat_adapt.
Abbreviation req_opp_compat :=
  S07_RealSetoidExpLog.RealSetoid.real_eq_opp_compat.
Abbreviation real_of_nat := S08_RealMainlineDPO.real_of_nat.

(* ============================================================ *)
(* Group 1: nonempty decidable Id-face family (the boolean cons             *)
(* discriminator, the general pin, the bool two-point instance, three       *)
(* slot pins, a concrete nat-list readout, and the length-positivity        *)
(* consumption instance).                                                   *)
(* ============================================================ *)

(* Boolean discriminator: nil reads false, a cons cell reads true.  This    *)
(* clean constructor match replaces the constructor-conflict carrier        *)
(* cons_nonempty_case, whose dependent match family (unit vs Empty_set      *)
(* arms) collapsed to Obj.magic under extraction.                           *)
Definition cons_nonempty_bool (T : Set) (l : list T) : bool :=
  match l with
  | nil => false
  | _ :: _ => true
  end.

(* General nonempty cons pin at the Id face.  Proof body: the original      *)
(* Not-of-Id face, preserved as an in-body constructivity derivation at     *)
(* the Prop face (Id-to-eq readout through id_eq_SI, then constructor       *)
(* discrimination), feeding the nil arm of the boolean dichotomy; the       *)
(* equation face then lifts to the Id face.  Every in-body step is          *)
(* Prop-sorted and extraction-erased, so the extracted body stays magic-    *)
(* free.                                                                    *)
Theorem cons_nil_id_contra : forall (T : Set) (x : T) (rest : list T),
  S01_BaseRing.Id (cons_nonempty_bool T (x :: rest)) true.
Proof.
  intros T x rest.
  (* in-body Not-of-Id content: a cons list is never nil at the Id face. *)
  assert (Hne : S01_BaseRing.Id (x :: rest) (@nil T) -> False).
  { intro Hlist.
    discriminate (S01_BaseRing.id_eq_SI (list T) (x :: rest) (@nil T) Hlist). }
  assert (Hgen : forall (l : list T),
    (S01_BaseRing.Id l (@nil T) -> False) -> cons_nonempty_bool T l = true).
  { intros l Hnil. destruct l as [| w ws].
    - exfalso. exact (Hnil (@S01_BaseRing.id_refl (list T) nil)).
    - reflexivity. }
  assert (Hb : cons_nonempty_bool T (x :: rest) = true)
    by (exact (Hgen (x :: rest) Hne)).
  exact (match Hb in (_ = z)
         return S01_BaseRing.Id (cons_nonempty_bool T (x :: rest)) z with
         | eq_refl => S01_BaseRing.id_refl
         end).
Defined.

(* Bool two-point instance. *)
Theorem bool_two_point_nonempty_id :
  S01_BaseRing.Id (cons_nonempty_bool bool (true :: false :: nil)) true.
Proof.
  exact (cons_nil_id_contra bool true (false :: nil)).
Defined.

(* Named slot pin: P7BoundedSoftmaxDeep :161. *)
Theorem p7b_deep_sec3_slot_nonempty :
  forall (T : Set) (x : T) (rest : list T),
    S01_BaseRing.Id (cons_nonempty_bool T (x :: rest)) true.
Proof.
  intros T x rest.
  exact (cons_nil_id_contra T x rest).
Defined.

(* Named slot pin: P7BoundedSoftmaxDeep :374. *)
Theorem p7b_deep_sec7_slot_nonempty :
  forall (T : Set) (x : T) (rest : list T),
    S01_BaseRing.Id (cons_nonempty_bool T (x :: rest)) true.
Proof.
  intros T x rest.
  exact (cons_nil_id_contra T x rest).
Defined.

(* Named slot pin: Arch_Up_01 :272 (states nonemptiness position). *)
Theorem archup_states_slot_nonempty :
  forall (T : Set) (x : T) (rest : list T),
    S01_BaseRing.Id (cons_nonempty_bool T (x :: rest)) true.
Proof.
  intros T x rest.
  exact (cons_nil_id_contra T x rest).
Defined.

(* Concrete singleton readout of the discriminator: the informative-bool    *)
(* witness face exercised by the extraction ladder driver (the cons cell    *)
(* headed by n; every reading is true).                                     *)
Definition cons_nonempty_bool_singleton (n : nat) : bool :=
  cons_nonempty_bool nat (n :: nil).

(* Consumption instance: length positivity of a nonempty cons list.  The    *)
(* Arch_Up_01 :327 root kvev_list_len_pos takes the Set-sorted Not premise  *)
(* (Id l nil -> Empty_set) — exactly the constructor-conflict face that     *)
(* casts to Obj.magic — so the instance reuses the root's own cons-branch   *)
(* arithmetic steps (one plus the rest tail, positivity compatibilities)    *)
(* instead, keeping the statement face and the extracted body magic-free.   *)
Theorem states_len_pos_cons :
  forall (T : Set) (x : T) (rest : list T),
    lt zero (real_of_nat (length (x :: rest))).
Proof.
  intros T x rest. cbn [length].
  apply (S02_CauchyComplete.real_lt_eq_lt zero
           (plus real_one (real_of_nat (length rest)))
           (real_of_nat (Datatypes.S (length rest)))).
  - apply (S02_CauchyComplete.real_eq_lt_lt zero
             (plus zero zero)
             (plus real_one (real_of_nat (length rest)))).
    + apply S02_CauchyComplete.real_eq_sym.
      apply S02_CauchyComplete.real_plus_zero.
    + apply S07_RealSetoidExpLog.real_lt_plus_compat_lt_le.
      * apply S07_RealSetoidExpLog.real_lt_zero_one.
      * apply S13_NLiveAudit.real_of_nat_nonneg_aux.
  - apply S02_CauchyComplete.real_eq_refl.
Defined.

(* ============================================================ *)
(* Group 2: nonempty equality-face slot, recarried on the Set-sorted        *)
(* leiblw_Id window: the window-face pin of the same discriminator, with    *)
(* its named slot pin.  The window-to-Id collapse bridge stays transparent  *)
(* and now serves the in-body window-face refutation.                       *)
(* ============================================================ *)

(* Set-carrier bridge: the leiblw window collapses to the Set-sorted Id. *)
Definition leiblw_to_id (A : Set) (x y : A)
    (H : LW0LeibWindow.leiblw_Id x y) : S01_BaseRing.Id x y :=
  match H in LW0LeibWindow.leiblw_Id _ a return S01_BaseRing.Id x a with
  | LW0LeibWindow.leiblw_id_intro _ => S01_BaseRing.id_refl
  end.

(* General nonempty cons form at the window face: the discriminator pin     *)
(* carried through the window.  Proof body: the original window-face        *)
(* Not-of-Id content, preserved as an in-body Prop-face derivation (window  *)
(* collapse to Id via leiblw_to_id, then id_eq_SI and constructor           *)
(* discrimination), feeding the nil arm of the window-face dichotomy; the   *)
(* equation face then lifts to the window pin face. *)
Theorem cons_nil_leiblw_contra : forall (T : Set) (x : T) (rest : list T),
  LW0LeibWindow.leiblw_Id (cons_nonempty_bool T (x :: rest)) true.
Proof.
  intros T x rest.
  assert (Hwne : LW0LeibWindow.leiblw_Id (x :: rest) (@nil T) -> False).
  { intro Hw.
    assert (Hid : S01_BaseRing.Id (x :: rest) (@nil T))
      by (exact (leiblw_to_id (list T) (x :: rest) (@nil T) Hw)).
    discriminate (S01_BaseRing.id_eq_SI (list T) (x :: rest) (@nil T) Hid). }
  assert (Hgen : forall (l : list T),
    (LW0LeibWindow.leiblw_Id l (@nil T) -> False) -> cons_nonempty_bool T l = true).
  { intros l Hnil. destruct l as [| w ws].
    - exfalso. exact (Hnil (LW0LeibWindow.leiblw_id_intro nil)).
    - reflexivity. }
  assert (Hb : cons_nonempty_bool T (x :: rest) = true)
    by (exact (Hgen (x :: rest) Hwne)).
  exact (match Hb in (_ = z)
         return LW0LeibWindow.leiblw_Id (cons_nonempty_bool T (x :: rest)) z with
         | eq_refl => LW0LeibWindow.leiblw_id_intro (cons_nonempty_bool T (x :: rest))
         end).
Defined.

(* Named slot pin: UpAblP2WByPass :111 (enum0 nonemptiness position). *)
Theorem p2w_enum_slot_nonempty :
  forall (T : Set) (x : T) (rest : list T),
    LW0LeibWindow.leiblw_Id (cons_nonempty_bool T (x :: rest)) true.
Proof.
  intros T x rest.
  exact (cons_nil_leiblw_contra T x rest).
Defined.

(* ============================================================ *)
(* Group 3: distribution-bridge pair over a finite-sum interface at the     *)
(* concrete Real carrier.  Section premises mirror the logc_* engine and    *)
(* SigMigrate slot positions so the supplies instantiate both verbatim.     *)
(* ============================================================ *)

Section DistributionBridgeSupply.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis fep_partition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Hypothesis sup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis sup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* Migrated distribution pair, with explicit type annotations. *)
Definition boltz_dist (s : S) : R :=
  SigMigrate.cwe_boltzmann_dist S base_loss D D_pos Z Z_pos s.
Definition boltz_dist_pos : SigMigrate.cwe_positive_dist S boltz_dist :=
  SigMigrate.req_boltzmann_positive S base_loss D D_pos Z Z_pos.
Definition boltz_free_energy : R :=
  SigMigrate.cwe_free_energy S sumf base_loss D
    (SigMigrate.cwe_boltzmann_dist S base_loss D D_pos Z Z_pos)
    (SigMigrate.req_boltzmann_positive S base_loss D D_pos Z Z_pos).

(* Supply 1: energy-in-log identity on the migrated carrier, proved by the *)
(* logc engine plus the pointwise positivity transcription through        *)
(* sup_compat (the two certificates convert definitionally).              *)
Theorem energy_in_log_boltzmann_slot :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (boltz_dist s) (boltz_dist_pos s))
                           (log Z Z_pos)))).
Proof.
  intro s.
  apply (req_trans (base_loss s)
           (opp (mult D (plus (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                  (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                              (log Z Z_pos))))
           (opp (mult D (plus (log (boltz_dist s) (boltz_dist_pos s))
                              (log Z Z_pos))))).
  - exact (logc_energy_in_log_boltzmann S base_loss D D_pos Z Z_pos
             sup_compat sup_log_exp_neg s).
  - exact (req_opp_compat
             (mult D (plus (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                           (log Z Z_pos)))
             (mult D (plus (log (boltz_dist s) (boltz_dist_pos s))
                           (log Z Z_pos)))
             (req_mult_compat D D
                (plus (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                           (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                      (log Z Z_pos))
                (plus (log (boltz_dist s) (boltz_dist_pos s)) (log Z Z_pos))
                (req_refl D)
                (req_plus_compat
                   (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                        (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                   (log (boltz_dist s) (boltz_dist_pos s))
                   (log Z Z_pos) (log Z Z_pos)
                   (sup_compat (logc_boltz S base_loss D D_pos Z Z_pos s)
                               (boltz_dist s)
                               (logc_boltz_pos S base_loss D D_pos Z Z_pos s)
                               (boltz_dist_pos s)
                               (req_refl (logc_boltz S base_loss D D_pos Z Z_pos s)))
                   (req_refl (log Z Z_pos))))).
Qed.

(* Supply 2: free-energy identity on the migrated carrier, proved by the  *)
(* logc engine plus the definitional conversion of the two carriers via   *)
(* the sum-extensionality premise.                                        *)
Theorem free_energy_boltzmann_slot :
  req boltz_free_energy (mult (opp D) (log Z Z_pos)).
Proof.
  apply (req_trans boltz_free_energy
           (logc_fe S sumf base_loss D
              (logc_boltz S base_loss D D_pos Z Z_pos)
              (logc_boltz_pos S base_loss D D_pos Z Z_pos))
           (mult (opp D) (log Z Z_pos))).
  - exact (req_plus_compat
             (sumf (fun s : S => mult (boltz_dist s) (base_loss s)))
             (sumf (fun s : S => mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                                      (base_loss s)))
             (mult D (sumf (fun s : S => mult (boltz_dist s)
                                      (log (boltz_dist s) (boltz_dist_pos s)))))
             (mult D (sumf (fun s : S =>
                       mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                            (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                 (logc_boltz_pos S base_loss D D_pos Z Z_pos s)))))
             (req_refl (sumf (fun s : S => mult (boltz_dist s) (base_loss s))))
             (req_mult_compat D D
                (sumf (fun s : S => mult (boltz_dist s)
                                  (log (boltz_dist s) (boltz_dist_pos s))))
                (sumf (fun s : S =>
                          mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                               (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                    (logc_boltz_pos S base_loss D D_pos Z Z_pos s))))
                (req_refl D)
                (sum_ext
                   (fun s : S => mult (boltz_dist s)
                                  (log (boltz_dist s) (boltz_dist_pos s)))
                   (fun s : S =>
                      mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                           (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                (logc_boltz_pos S base_loss D D_pos Z Z_pos s)))
                   (fun s : S =>
                      req_mult_compat (boltz_dist s)
                        (logc_boltz S base_loss D D_pos Z Z_pos s)
                        (log (boltz_dist s) (boltz_dist_pos s))
                        (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                             (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                        (req_refl (boltz_dist s))
                        (sup_compat (boltz_dist s)
                          (logc_boltz S base_loss D D_pos Z Z_pos s)
                          (boltz_dist_pos s)
                          (logc_boltz_pos S base_loss D D_pos Z Z_pos s)
                          (req_refl (boltz_dist s))))))).
  - exact (logc_free_energy_boltzmann S sumf sum_ext sum_add sum_linear
             base_loss D D_pos Z Z_pos fep_partition sup_compat
             sup_log_exp_neg).
Qed.

(* Consumption 1: p-weighted energy decomposition with the bridge position *)
(* filled by Supply 1.                                                    *)
Theorem p_times_energy_decomp_filled :
  forall (p : S -> R) (s : S),
    req (mult (p s) (base_loss s))
        (plus (opp (mult D (mult (p s) (log (boltz_dist s) (boltz_dist_pos s)))))
              (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  exact (SigMigrate.req_p_times_energy_decomp S base_loss D D_pos Z Z_pos
           (fun s0 : S => energy_in_log_boltzmann_slot s0) p s).
Qed.

(* Consumption 2: free-energy KL decomposition with both bridge positions *)
(* filled by Supplies 1 and 2.                                            *)
Theorem free_energy_kl_decomp_filled :
  forall (p : S -> R) (Hp : SigMigrate.cwe_normalized S sumf p)
    (p0 : SigMigrate.cwe_positive_dist S p),
    req (SigMigrate.cwe_free_energy S sumf base_loss D p p0)
        (plus boltz_free_energy
              (mult D (sumf (fun s : S =>
                mult (p s) (SigMigrate.rminus (log (p s) (p0 s))
                                              (log (boltz_dist s)
                                                   (boltz_dist_pos s))))))).
Proof.
  intros p Hp p0.
  exact (SigMigrate.req_free_energy_kl_decomp S sumf sum_ext sum_add sum_linear
           base_loss D D_pos Z Z_pos
           (fun s0 : S => energy_in_log_boltzmann_slot s0)
           free_energy_boltzmann_slot p Hp p0).
Qed.

End DistributionBridgeSupply.

(* ============================================================ *)
(* Face-preserving spot checks.                                             *)
(* ============================================================ *)

Check cons_nil_id_contra.
Check bool_two_point_nonempty_id.
Check cons_nil_leiblw_contra.
Check states_len_pos_cons.
Check energy_in_log_boltzmann_slot.
Check free_energy_boltzmann_slot.
Check p_times_energy_decomp_filled.
Check free_energy_kl_decomp_filled.

(* ============================================================ *)
(* Assumption audit: one line per theorem of this piece.                    *)
(* ============================================================ *)

Print Assumptions cons_nil_id_contra.
Print Assumptions bool_two_point_nonempty_id.
Print Assumptions p7b_deep_sec3_slot_nonempty.
Print Assumptions p7b_deep_sec7_slot_nonempty.
Print Assumptions archup_states_slot_nonempty.
Print Assumptions states_len_pos_cons.
Print Assumptions cons_nil_leiblw_contra.
Print Assumptions p2w_enum_slot_nonempty.
Print Assumptions energy_in_log_boltzmann_slot.
Print Assumptions free_energy_boltzmann_slot.
Print Assumptions p_times_energy_decomp_filled.
Print Assumptions free_energy_kl_decomp_filled.
