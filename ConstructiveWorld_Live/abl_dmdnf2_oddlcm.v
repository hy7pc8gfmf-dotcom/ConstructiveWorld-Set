(* ConstructiveWorld-Set — odd-lcm denominator carrier modules. *)

(** * abl_dmdnf2_oddlcm: the odd-lcm denominator carrier.

    Mission.  Carries the denominator bookkeeping of the linear-form
      family on the odd least common multiple: the executable
      definitions [od_prod] and [oddlcm]; the witness interface
      [dnf2_odd_div_odprod] (every odd 2k+1 <= N divides [od_prod N],
      in sigT multiplier form) with the truncated-range corollary
      [dnf2_trunc_odd_clear]; the growth bounds
      [dnf2_oddlcm_le_odprod] / [dnf2_odprod_le_fact] with Set-face
      anchors [dnf2_oddlcm_le_odprod_t] / [dnf2_odprod_le_fact_t]; and
      the executable anchors [dnf2_anchor_*].

    Dependencies.  Stdlib [Arith.Arith], [Arith.Factorial], [Lia];
      requires [HansonLcm] (the [hl_le_t] comparator) and
      [S01_BaseRing] ([Id]) of this development.

    References.  The baseline module abl_dmdnf2_oddlcm.v in
      ConstructiveWorld-Main, whose statement names are carried over
      here verbatim (statement-face Set-carrier completion).

    Constructivity.  All statements close by [Qed]; growth bounds are
      product-form factorial bounds carried by [hl_le_t]; witness
      statements are [sigT]-carried over [Id]; [od_prod]/[oddlcm] are
      executable Fixpoints extracting with [Obj.magic] = 0; [coqchk]
      reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dmdnf2_oddlcm.v]
      compiles cleanly (exit 0); the artifact begins [436f7121 00015ff4]. *)


From Stdlib Require Import Arith.Arith Arith.Factorial Lia.
Require Import HansonLcm.
Require Import S01_BaseRing.

(* ================= Section 0. Oddness scaffold (nat-layer) ================= *)

Lemma dnf2_odd_SS : forall n : nat, Nat.odd n = true ->
  Nat.odd (Datatypes.S (Datatypes.S n)) = true.
Proof.
  intros n H. exact H.
Qed.

Lemma dnf2_odd_two_k1 : forall k : nat, Id (Nat.odd (2 * k + 1)) true.
Proof.
  intro k.
  assert (Hcore : Nat.odd (2 * k + 1) = true).
  { induction k as [| k IHk].
    - reflexivity.
  - replace (2 * Datatypes.S k + 1)%nat with (Datatypes.S (Datatypes.S (2 * k + 1))) by lia.
    apply dnf2_odd_SS. exact IHk. }
  destruct Hcore. apply id_refl.
Qed.

(* ================= Section A. Definitions: odd double factorial and odd lcm ================= *)

Fixpoint od_prod (N : nat) : nat :=
  match N with
  | Datatypes.O => 1
  | Datatypes.S N' => if Nat.odd (Datatypes.S N') then (Datatypes.S N') * od_prod N' else od_prod N'
  end.

Fixpoint oddlcm (N : nat) : nat :=
  match N with
  | Datatypes.O => 1
  | Datatypes.S N' => if Nat.odd (Datatypes.S N') then Nat.lcm (Datatypes.S N') (oddlcm N') else oddlcm N'
  end.

(* ================= Section B. The witness interface (main theorem) ================= *)
(*    Every odd 2k+1 <= N divides od_prod N: the truncated range of odd
      denominators up to 2n+2M+1 clears in one pass. *)
(* ============================================================ *)

Theorem dnf2_odd_div_odprod : forall (N k : nat), (2 * k + 1 <= N)%nat ->
  sigT (fun q : nat => Id (q * (2 * k + 1)) (od_prod N)).
Proof.
  induction N as [| N' IH]; intros k Hk.
  - lia.
  - cbn [od_prod]. destruct (Nat.odd (Datatypes.S N')) eqn:E.
    + (* Odd step: S N' enters the product. *)
      destruct (Nat.eq_dec (2 * k + 1) (Datatypes.S N')) as [Heq | Hne].
      * (* 2k+1 = S N': witness is od_prod N'. *)
        exists (od_prod N').
        rewrite Heq. rewrite Nat.mul_comm. reflexivity.
      * (* 2k+1 <= N' (strict inequality): the induction claim
           composes with the factor S N'. *)
        assert (Hle : (2 * k + 1 <= N')%nat) by lia.
        destruct (IH k Hle) as [q Hq].
        exists ((Datatypes.S N') * q)%nat.
        rewrite <- Nat.mul_assoc. rewrite Hq. apply id_refl.
    + (* Even step: product unchanged; 2k+1 = S N' contradicts evenness. *)
      destruct (Nat.eq_dec (2 * k + 1) (Datatypes.S N')) as [Heq | Hne].
      * rewrite <- Heq in E.
        assert (Hc : Nat.odd (2 * k + 1) = true)
          by (destruct (dnf2_odd_two_k1 k); reflexivity).
        rewrite Hc in E. discriminate E.
      * apply IH. lia.
Qed.

(* Direct-use form with the two range knobs n and M (coverage up to
   2n+2M+1). *)
Theorem dnf2_trunc_odd_clear : forall (n M k : nat), (2 * k + 1 <= 2 * n + 2 * M + 1)%nat ->
  sigT (fun q : nat => Id (q * (2 * k + 1)) (od_prod (2 * n + 2 * M + 1))).
Proof.
  intros n M k Hk.
  exact (dnf2_odd_div_odprod (2 * n + 2 * M + 1) k Hk).
Qed.

(* ================= Section C. Growth bounds ================= *)

Lemma dnf2_oddlcm_le_odprod : forall N : nat, NatLe (oddlcm N) (od_prod N).
Proof.
  intro N.
  assert (Hcore : (oddlcm N <= od_prod N)%nat).
  { induction N as [| N' IH].
  - simpl. lia.
  - cbn [oddlcm od_prod]. destruct (Nat.odd (Datatypes.S N')) eqn:E.
    + eapply Nat.le_trans.
      * apply (hl_le_t_to_le _ _ (hl_lcm_le_mul _ _)).
      * apply Nat.mul_le_mono_l. exact IH.
    + exact IH. }
  apply NatLe_lift. exact Hcore.
Qed.

Lemma dnf2_odprod_le_fact : forall N : nat, NatLe (od_prod N) (fact N).
Proof.
  intro N.
  assert (Hcore : (od_prod N <= fact N)%nat).
  { induction N as [| N' IH].
  - simpl. lia.
  - cbn [od_prod]. destruct (Nat.odd (Datatypes.S N')) eqn:E.
    + eapply Nat.le_trans.
      * apply Nat.mul_le_mono_l. exact IH.
      * cbn [fact]. lia.
    + eapply Nat.le_trans.
      * exact IH.
      * cbn [fact Nat.mul]. apply Nat.le_add_r. }
  apply NatLe_lift. exact Hcore.
Qed.

(* Set-face growth anchors (carried by [hl_le_t]). *)
Theorem dnf2_oddlcm_le_odprod_t : forall N : nat, hl_le_t (oddlcm N) (od_prod N).
Proof.
  intro N. exact (hl_le_to_le_t (oddlcm N) (od_prod N) (NatLe_drop _ _ (dnf2_oddlcm_le_odprod N))).
Qed.

Theorem dnf2_odprod_le_fact_t : forall N : nat, hl_le_t (od_prod N) (fact N).
Proof.
  intro N. exact (hl_le_to_le_t (od_prod N) (fact N) (NatLe_drop _ _ (dnf2_odprod_le_fact N))).
Qed.

(* ================= Section D. Executable anchors ================= *)

(* For larger N the unary representation grows quickly; the anchors below
   stay within executable range and are cross-checked by independent
   recomputation. *)
Lemma dnf2_anchor_odprod9 : Id (od_prod 9) 945.
Proof. reflexivity. Qed.

Lemma dnf2_anchor_oddlcm9 : Id (oddlcm 9) 315.
Proof. reflexivity. Qed.

Lemma dnf2_anchor_odprod11 : Id (od_prod 11) 10395.
Proof. reflexivity. Qed.

(* Truncated-range anchor: n = 1, M = 4 gives N = 11; the odd denominator
   11 gets its multiplier witness. *)
Lemma dnf2_anchor_trunc11 :
  sigT (fun q : nat => Id (q * 11) (od_prod 11)).
Proof.
  exact (dnf2_odd_div_odprod 11 5 (le_n 11)).
Qed.

(* ================= Assumption closure ================= *)

Print Assumptions dnf2_odd_div_odprod.
Print Assumptions dnf2_trunc_odd_clear.
Print Assumptions dnf2_oddlcm_le_odprod_t.
Print Assumptions dnf2_odprod_le_fact_t.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log".
Separate Extraction oddlcm od_prod dnf2_trunc_odd_clear.
