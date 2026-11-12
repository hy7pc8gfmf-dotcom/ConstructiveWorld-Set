(* =====================================================================
   WC_budget_family.v -- budget-side four-modulus witness function family.

   Mission. Route-2 order R2-WC: the budget-side moduli (Nlo/Nup/Nwd/Nzd)
   of the S10 destruct chain (S10_KVQuantTrig:8623-8626) as nat-valued
   data-carrying functions, assembled by direct projection from the
   supplied certificate values; D.14 weak-execution caliber (default):
   N is a certificate function, computability awaits Defined-ization.

   Statements. probe-3 canonical landing (cos_eq_zero_diag_bound_expl,
   cos_diag_N_of, probe3_eps8_pos with Defined ender, face unchanged,
   cos_pi_half_eps8_N_inst2); frozen family names Nlo_of / Nup_of /
   Nwd_of / Nzd_of (positivity premise Qlt 0 eps added where
   cos_diag_N_of demands it); bridges wc_eps8_pos / wc_q8_pos / wc_*_spec.

   Dependencies. S01_BaseRing, S02_CauchyComplete, S10_KVQuantTrig,
   Stdlib QArith/Arith.  References. base_local snapshot (Rocq 9.3.0):
   real_eq S02:399, real_lt S02:468, QltT S02:48, cos_pi_half S10:8403,
   real_cos_pi_half_zero S10:8425 (Qed), real_lt_lower_pt S10:8569 (Qed),
   real_lt_upper_pt S10:8590 (Qed); precedent route2_prerun_20261106/
   probe3_diag_defined.v (p3_run4).

   Constructivity. Set-carried, definitions transparent, zero new Prop
   statements (Prop-sorted bridges carry Qed; Set-sorted faces Defined);
   wc_nzd_inst8_decl is stuck by the Qed certificate real_cos_pi_half_zero
   (gate7 declaration: N is a certificate function; computability awaits
   certificate-chain Defined-ization).

   Build. coqc -native-compiler no -q -Q <sandbox> "" WC_budget_family.v
   ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S10_KVQuantTrig.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

Opaque Qred.

(* ==== Section 1: probe-3 minimal slice, canonical landing ==== *)

(* Explicit-witness recast of the S10 diagonal bound: the certificate Hw
   is consumed directly (existT assembly), so N is computable whenever
   the supplied certificate value is Defined. *)
Definition cos_eq_zero_diag_bound_expl (w : Real)
  (Hw : real_eq (cauchy_real_cos w) real_zero) (delta : Q) (Hdelta : Qlt 0 delta) :
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    QltT (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) delta) :=
  existT _ (projT1 (Hw delta (Qlt_to_QltT 0 delta Hdelta)))
    (fun n Hn => projT2 (Hw delta (Qlt_to_QltT 0 delta Hdelta)) n (NatLe_lift _ _ Hn)).

(* Modulus-extraction face: N := first projection of the certificate
   application at delta. *)
Definition cos_diag_N_of (w : Real) (Hw : real_eq (cauchy_real_cos w) real_zero)
  (delta : Q) (Hdelta : Qlt 0 delta) : nat :=
  projT1 (Hw delta (Qlt_to_QltT 0 delta Hdelta)).

(* Closed positivity witness for the eps/8 single branch. *)
Lemma probe3_eps8_pos : QltT 0 (1#8).
Proof. reflexivity. Defined.

(* Closed instance at cos_pi_half with eps = 1/8, consumed at a value
   position. *)
Definition cos_pi_half_eps8_N_inst2 : nat :=
  cos_diag_N_of cos_pi_half real_cos_pi_half_zero (1#8)
    (QltT_to_Qlt 0 (1#8) probe3_eps8_pos).

(* ==== Section 2: eps/8 positivity bridge ==== *)

Lemma wc_eps8_pos : forall eps : Q, Qlt 0 eps -> Qlt 0 (eps / 8).
Proof.
  intros eps Heps.
  apply (Qlt_shift_div_l 0 eps 8).
  - change (Qlt 0 8). compute. reflexivity.
  - simpl. exact Heps.
Qed.

(* ==== Section 3: four-modulus budget-witness family ==== *)

(* Lower window modulus: exactly the modulus the S10 consumption at
   S10:8623 obtains from real_lt_lower_pt, read off the real_lt witness
   structure (margin, positivity, modulus, pointwise tail). *)
Definition Nlo_of (w : Real) (Hlow : real_lt (real_const (3#2)) w) : nat :=
  projT1 (snd (projT2 Hlow)).

(* Upper window modulus, same assembly for the upper certificate. *)
Definition Nup_of (w : Real) (Hup : real_lt w (real_const (5#3))) : nat :=
  projT1 (snd (projT2 Hup)).

(* Window-diagonal modulus at an arbitrary zero point w, scaled to
   eps/8 as in the S10 consumption at S10:8625. *)
Definition Nwd_of (w : Real) (Hw0 : real_eq (cauchy_real_cos w) real_zero)
  (eps : Q) (Heps : Qlt 0 eps) : nat :=
  cos_diag_N_of w Hw0 (eps / 8) (wc_eps8_pos eps Heps).

(* Window-diagonal modulus at the canonical zero point cos_pi_half,
   scaled to eps/8 as in the S10 consumption at S10:8626.  Stuck unless
   a Defined certificate replaces the library Qed face. *)
Definition Nzd_of (eps : Q) (Heps : Qlt 0 eps) : nat :=
  cos_diag_N_of cos_pi_half real_cos_pi_half_zero (eps / 8)
    (wc_eps8_pos eps Heps).

(* ==== Section 4: contract bridges for the W-D synthesis ==== *)

(* Each bridge restates the certificate tail at the projected modulus,
   so the budget inequality of W-D composes without reopening Qed
   certificates. *)
Lemma wc_Nlo_of_spec : forall (w : Real) (Hlow : real_lt (real_const (3#2)) w)
  (n : nat), NatLe (Nlo_of w Hlow) n ->
  QltT (projT1 Hlow) (projT1 w n - projT1 (real_const (3#2)) n).
Proof. intros w Hlow n Hn. exact (projT2 (snd (projT2 Hlow)) n Hn). Defined.

Lemma wc_Nup_of_spec : forall (w : Real) (Hup : real_lt w (real_const (5#3)))
  (n : nat), NatLe (Nup_of w Hup) n ->
  QltT (projT1 Hup) (projT1 (real_const (5#3)) n - projT1 w n).
Proof. intros w Hup n Hn. exact (projT2 (snd (projT2 Hup)) n Hn). Defined.

Lemma wc_Nwd_of_spec : forall (w : Real)
  (Hw0 : real_eq (cauchy_real_cos w) real_zero) (eps : Q) (Heps : Qlt 0 eps)
  (n : nat), (Nwd_of w Hw0 eps Heps <= n)%nat ->
  QltT (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) (eps / 8).
Proof. intros w Hw0 eps Heps n Hn.
  exact (projT2 (Hw0 (eps / 8) (Qlt_to_QltT 0 (eps / 8) (wc_eps8_pos eps Heps)))
           n (NatLe_lift _ _ Hn)). Defined.

Lemma wc_Nzd_of_spec : forall (eps : Q) (Heps : Qlt 0 eps) (n : nat),
  (Nzd_of eps Heps <= n)%nat ->
  QltT (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
       (eps / 8).
Proof. intros eps Heps n Hn.
  exact (projT2 (real_cos_pi_half_zero (eps / 8)
           (Qlt_to_QltT 0 (eps / 8) (wc_eps8_pos eps Heps)))
           n (NatLe_lift _ _ Hn)). Defined.

(* ==== Section 5: closed-term computable instances (4b face) ==== *)

(* A closed window point strictly inside (3/2, 5/3): the constant
   sequence 8/5.  Both window certificates are explicit real_lt
   witnesses with margin 1/20 and modulus 0; the constant sequence
   makes every tail bound a closed rational comparison (the window
   gaps are 1/10 and 1/15, both above 1/20). *)
Lemma wc_q20_pos : QltT 0 (1#20).
Proof. reflexivity. Defined.

Lemma wc_tail_85 : forall n : nat, NatLe 0%nat n ->
  QltT (1#20) (projT1 (real_const (8#5)) n - projT1 (real_const (3#2)) n).
Proof. intros n Hn. cbn [projT1 real_const]. reflexivity. Defined.

Lemma wc_tail_53 : forall n : nat, NatLe 0%nat n ->
  QltT (1#20) (projT1 (real_const (5#3)) n - projT1 (real_const (8#5)) n).
Proof. intros n Hn. cbn [projT1 real_const]. reflexivity. Defined.

Definition wc_hlow_85 : real_lt (real_const (3#2)) (real_const (8#5)) :=
  existT _ (1#20) (wc_q20_pos, existT _ 0%nat wc_tail_85).

Definition wc_hup_21 : real_lt (real_const (8#5)) (real_const (5#3)) :=
  existT _ (1#20) (wc_q20_pos, existT _ 0%nat wc_tail_53).

(* Value-position instances: concrete nats out of Defined certificates. *)
Definition wc_nlo_inst8 : nat := Nlo_of (real_const (8#5)) wc_hlow_85.
Definition wc_nup_inst8 : nat := Nup_of (real_const (8#5)) wc_hup_21.

(* The canonical Nzd instance: the certificate is the library Qed face
   real_cos_pi_half_zero, so the value is stuck by construction -- the
   declared weak-execution-caliber observation face. *)
Lemma wc_q8_pos : Qlt 0 (1#8).
Proof. compute. reflexivity. Qed.

Definition wc_nzd_inst8_decl : nat := Nzd_of (1#8) wc_q8_pos.
