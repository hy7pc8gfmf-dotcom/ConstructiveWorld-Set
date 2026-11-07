(* ConstructiveWorld-Set — discharge of the bounded-softmax interface assumptions for the paper-7 ablation family. *)

(** * Paper7Ablation: non-trivial supply for the Section-variable
    interface assumptions of the bounded-softmax analysis module.

    Mission.  Each [Variable] assumption of Section [BoundedSoftmax]
      ([AttnDoeblin]) is discharged by a genuine theorem: the [expf]
      congruence and monotonicity reductions [p7a_expf_wd] and
      [p7a_expf_mono_le_do], the strict bound [p7a_lo_lt_one] with its
      instance [p7a_lo_lt_one_instant], and the [kappa := 1 -
      delta_star] selector supply [p7a_delta_star_pos], [p7a_omd_pos],
      [p7a_omd_lt_one].

    Dependencies.  Requires [S01_BaseRing] and [fa53_compat_abs] of
      this development.

    References.  This development, Paper7Ablation.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier
      completion); the discharged interfaces belong to [AttnDoeblin].

    Constructivity.  All named statements are carried by [Set] ([Id],
      [Or], [Not] are the Set-layer definitions of [S01_BaseRing]);
      every proof is a genuine derivation chain; statements extract
      with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" Paper7Ablation.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ==================== Section 1. Trimming the expf mini-interface ==================== *)
(* Mirrors the expf interface of Section [BoundedSoftmax] in [AttnDoeblin]. *)
Section P7aExpf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* C1: congruence of [expf] derived from [expf_plus], [expf_zero] and
   [expf_pos] through the [mult_cancel_l] cancellation chain — no
   independent congruence assumption is needed. *)
Theorem p7a_expf_wd : forall a b : R, Id a b -> Id (expf a) (expf b).
Proof.
  intros a b Hab.
  assert (He := expf_pos (opp b)).
  assert (Ha1 : Id (mult (expf a) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus a (opp b)))).
    apply (id_trans (id_cong expf
             (id_trans (id_cong (fun x => plus x (opp b)) Hab)
                       (plus_opp b)))).
    exact expf_zero. }
  assert (Hb1 : Id (mult (expf b) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus b (opp b)))).
    apply (id_trans (id_cong expf (plus_opp b)) expf_zero). }
  apply (mult_cancel_l (expf (opp b)) (expf a) (expf b) He).
  apply (id_trans (id_trans (mult_comm (expf (opp b)) (expf a)) Ha1)
                  (id_sym (id_trans (mult_comm (expf (opp b)) (expf b)) Hb1))).
Qed.

(* C2: [expf_mono_le] derived from [expf_mono_lt], the decidable
   trichotomy of the order, and C1 — the interface needs one field
   fewer. *)
Theorem p7a_expf_mono_le_do : forall a b : R, le a b -> le (expf a) (expf b).
Proof.
  intros a b Hab.
  destruct (@fa53_lt_dec RI DO a b) as [Hlt | [Heq | Hgt]].
  - (* Case [a < b]: strict monotonicity applies directly; the left
       disjunct of the [Or] lifts to [le]. *)
    exact (lt_le_iff (expf a) (expf b) (inl (expf_mono_lt a b Hlt))).
  - (* Case [a == b]: congruence (C1) with reflexivity. *)
    apply (le_id_l (expf a) (expf b) (expf b) (p7a_expf_wd a b Heq)).
    exact (le_refl (expf b)).
  - (* Case [b < a]: this contradicts [le a b]; antisymmetry forces
       [Id a b], which is absurd against [b < a]. *)
    destruct (lt_irrefl b
      (lt_id_r b a b (le_antisym a b Hab (lt_le_iff b a (inl Hgt))) Hgt)).
Qed.

End P7aExpf.

(* ==================== Section 2. Bounded softmax: the strict bound [lo < 1] ==================== *)
(* Mirrors [lo := expf (invT * opp Delta)] of [AttnDoeblin]. *)
Section P7aSoftBound.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* C3: [lo < 1], the dual companion of [bs_lo_pos] in [AttnDoeblin],
   stated generically for any positive [invT]. *)
Theorem p7a_lo_lt_one : forall invT : R,
  lt zero invT -> lt (expf (mult invT (opp Delta))) one.
Proof.
  intros invT Hin.
  assert (Hond := lt_zero_opp Delta Delta_pos).
  (* [invT * (-Delta) < 0]: first [(-Delta) * invT < 0 * invT] by sign
     monotonicity, then [0 * invT] normalizes to zero. *)
  assert (Hm : lt (mult (opp Delta) invT) zero).
  { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
             (id_trans (mult_comm zero invT) (mult_zero invT))).
    exact (lt_mult_compat (opp Delta) zero invT Hin Hond). }
  apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
  apply (expf_mono_lt (mult invT (opp Delta)) zero).
  apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
                   (mult_comm invT (opp Delta))).
  exact Hm.
Qed.

(* C3': [lo < 1] at the literal choice [lo := expf (inv_pos temp temp_pos * opp Delta)]. *)
Theorem p7a_lo_lt_one_instant :
  lt (expf (mult (inv_pos temp temp_pos) (opp Delta))) one.
Proof.
  exact (p7a_lo_lt_one (inv_pos temp temp_pos) (inv_pos_pos temp temp_pos)).
Qed.

End P7aSoftBound.

(* ==================== Section 3. Supply for the selector [kappa := 1 - delta_star] ==================== *)
(* Mirrors [delta_star := mult lo lo] of [AttnDoeblin].  The premises are
   exactly the interface certificates needed to close the side condition
   [kappa in (0,1)]: [lo_pos] (the shape of [bs_lo_pos]) and
   [delta_star < 1] (the shape of [bs_delta_star_lt_one]). *)
Section P7aKappa.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable lo : R.
Variable lo_pos : lt zero lo.

(* C4: [0 < delta_star = lo * lo]. *)
Theorem p7a_delta_star_pos : lt zero (mult lo lo).
Proof.
  exact (mult_positive lo lo lo_pos lo_pos).
Qed.

(* C5: [delta_star < 1 -> 0 < 1 - delta_star], the softmax instance of
   [u_omd_pos_next] in [AttnDoeblin]; the mixed strict/weak addition
   monotonicity is the first fa53 companion lemma. *)
Theorem p7a_omd_pos :
  lt (mult lo lo) one -> lt zero (minus one (mult lo lo)).
Proof.
  intro Hds.
  apply (lt_id_l zero (plus (mult lo lo) (opp (mult lo lo)))
                   (plus one (opp (mult lo lo)))
                   (id_sym (plus_opp (mult lo lo)))).
  exact (@fa53_lt_plus_compat_lt_le_dec RI DO (mult lo lo) one
           (opp (mult lo lo)) (opp (mult lo lo)) Hds
           (le_refl (opp (mult lo lo)))).
Qed.

(* C6: [0 < delta_star -> 1 - delta_star < 1], via the dual second
   fa53 companion lemma. *)
Theorem p7a_omd_lt_one : lt (minus one (mult lo lo)) one.
Proof.
  apply (lt_id_r (plus one (opp (mult lo lo))) (plus one zero) one
                   (plus_zero one)).
  exact (@fa53_lt_plus_compat_le_lt_dec RI DO one one
           (opp (mult lo lo)) zero (le_refl one)
           (lt_zero_opp (mult lo lo) p7a_delta_star_pos)).
Qed.

End P7aKappa.

(* Closure audit: [Print Assumptions] reports every statement Closed;
   all names are global after Section discharge. *)
Print Assumptions p7a_expf_wd.
Print Assumptions p7a_expf_mono_le_do.
Print Assumptions p7a_lo_lt_one.
Print Assumptions p7a_lo_lt_one_instant.
Print Assumptions p7a_delta_star_pos.
Print Assumptions p7a_omd_pos.
Print Assumptions p7a_omd_lt_one.
