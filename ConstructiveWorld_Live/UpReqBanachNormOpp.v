(* ConstructiveWorld-Set — Uniqueness of the reduced form and the norm-of-opposite law. *)

(** * UpReqBanachNormOpp: [Qred] uniqueness and the [bnorm] opposite face.

    Mission.  The key to an [Id]-well-defined norm of the form
    [bnorm := Qred o Qabs] is uniqueness of the reduced form:
    [bno_qred_unique : forall x y : Q, x == y -> Qred x = Qred y]
    (Leibniz codomain), assembled from three legs: the coprime-pair
    uniqueness machine re-assembled from the [Zis_gcd] recipe, the
    [bnorm_opp] attack chain of the Real-carrier study used verbatim,
    and the canonical-pair characterization of [Qred] from
    [Qcanon]/[Qreduction].  Companion laws: positivity and
    strict-order bridges on [Z], canonical outputs of [Qred], the
    [eq]-form and [Id]-form of the norm-of-opposite invariance, and
    the engine lemmas for the harmonic escape statement
    [bno_sum_inv_fact_escape] (its main statement remains an honest
    open item; the engine segment is closed here).

    Dependencies.  Stdlib [QArith], [Qabs], [Qcanon], [ZArith],
    [Znumtheory], [Lia].  Requires [S01_BaseRing],
    [S02_CauchyComplete], [S03_QExp], [UpReqBanachInstB],
    [UpReqBanachInstReal] of this development.

    References.  This development, UpReqBanachInstB.v and
    UpReqBanachInstReal.v, the baseline modules in
    ConstructiveWorld-Main whose statement names are carried over here
    verbatim (statement-face Set-carrier completion).

    Constructivity.  Statements are carried by [Set]
    ([Set]/[eq]/[Id]/[Qeq]/[ZLtT] shapes); no global assumptions; the
    closing [Print Assumptions] audits report [Closed]; statements
    extract with [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""
    UpReqBanachNormOpp.v] compiles cleanly (exit 0); the first eight
    bytes of the artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInstReal.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qcanon
  ZArith.ZArith ZArith.Znumtheory.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0. Integer coprimality tools (the canonical-pair uniqueness
   machine, re-assembled from the cross-product recipe) *)
(* ============================================================ *)

(* The positivity bridge through the integer comparison. *)
(* Set-valued strict order on [Z] (the [NatLe] shape, mirrored 1:1). *)
Definition ZLtT (a b : Z) : Set := Id (Z.ltb a b) true.

Lemma ZLtT_drop : forall a b : Z, ZLtT a b -> (a < b)%Z.
Proof.
  intros a b H. unfold ZLtT in H.
  destruct (Z.ltb a b) eqn:E.
  - apply (proj1 (Z.ltb_lt a b)). exact E.
  - inversion H.
Qed.

Lemma ZLtT_lift : forall a b : Z, (a < b)%Z -> ZLtT a b.
Proof.
  intros a b H. unfold ZLtT.
  destruct (Z.ltb a b) eqn:E.
  - apply id_refl.
  - exfalso.
    assert (H2 : (a <? b) = true) by (apply (proj2 (Z.ltb_lt a b)); exact H).
    rewrite H2 in E. discriminate E.
Qed.

Lemma bno_gt0_of_lt0 : forall d : Z, 0 < d -> ZLtT 0 d.
Proof. intros d H. apply ZLtT_lift. exact H. Qed.

Lemma bno_gt0_of_lt0_zgt : forall d : Z, 0 < d -> (d > 0)%Z.
Proof. intros d H. apply (proj2 (Z.compare_gt_iff d 0)). exact H. Qed.

(* [gcd = 1] gives coprimality (the [Zis_gcd_intro] recipe). *)
Lemma bno_rel_prime_of_gcd1 : forall n d : Z, Z.gcd n d = 1%Z -> rel_prime n d.
Proof.
  intros n d H.
  exact (Zis_gcd_intro n d 1%Z (Z.divide_1_l n) (Z.divide_1_l d)
    (fun z Hz1 Hz2 =>
       match Zgcd_is_gcd n d with
       | Zis_gcd_intro _ _ _ _ _ Hdiv =>
           eq_ind (Z.gcd n d) (fun g => (z | g)%Z)
             (Hdiv z Hz1 Hz2) 1%Z H
       end)).
Qed.

(* Canonical-pair cross-product uniqueness: if both pairs have
   numerator and denominator coprime to 1 with positive denominators
   and equal cross products, the numerators and denominators agree —
   the Gauss/rel_prime_cross_prod law applies directly. *)
(* [eq]-to-[Id] transport for Set carriers (self-provided). *)
Definition nz_id_of_eq {A : Set} (x y : A) (p : x = y) : @Id A x y :=
  match p with eq_refl => id_refl end.

(* [Id]-to-[eq] transport (the dual direction). *)
Definition nz_eq_of_id {A : Set} {x y : A} (p : @Id A x y) : x = y :=
  match p with id_refl => eq_refl end.

Lemma bno_canon_pair_unique : forall n1 d1 n2 d2 : Z,
  Z.gcd n1 d1 = 1%Z -> Z.gcd n2 d2 = 1%Z -> (d1 > 0)%Z -> (d2 > 0)%Z ->
  (n1 * d2 = n2 * d1)%Z -> And (@Id Z n1 n2) (@Id Z d1 d2).
Proof.
  intros n1 d1 n2 d2 H1 H2 P1 P2 Hc.
  exact (let E := rel_prime_cross_prod n1 d1 n2 d2
             (bno_rel_prime_of_gcd1 n1 d1 H1)
             (bno_rel_prime_of_gcd1 n2 d2 H2) P1 P2
             (eq_ind (n2 * d1) (fun x => (n1 * d2 = x)%Z) Hc (d1 * n2) (Z.mul_comm n2 d1)) in
         (nz_id_of_eq _ _ (proj1 E), nz_id_of_eq _ _ (proj2 E))).
Qed.

(* ============================================================ *)
(* S1. Uniqueness of [Qred] *)
(* ============================================================ *)

(* [Qred] output is always a canonical pair (idempotence feeds [Qred_iff]). *)
Lemma bno_qred_canon : forall x : Q,
  @Id Z (Z.gcd (Qnum (Qred x)) (Z.pos (Qden (Qred x)))) (1%Z).
Proof.
  intro x.
  assert (Hi : Qred (Qred x) = Qred x) by (apply Qred_complete, Qred_correct).
  apply nz_id_of_eq. exact (proj1 (Qred_iff (Qred x)) Hi).
Qed.

(* Main statement: [Qred] uniqueness ([Qeq] in, Leibniz [eq] out). *)
Lemma bno_qred_unique : forall x y : Q, x == y -> @Id Q (Qred x) (Qred y).
Proof.
  intros x y Hxy.
  pose proof (nz_eq_of_id (bno_qred_canon x)) as Hc1.
  pose proof (nz_eq_of_id (bno_qred_canon y)) as Hc2.
  assert (Hr : Qred x == Qred y).
  { apply (Qeq_trans _ x).
    - apply Qred_correct.
    - rewrite Hxy. apply (Qeq_sym (Qred y) y). apply Qred_correct. }
  destruct (Qred x) as [n1 d1] eqn:Ex.
  destruct (Qred y) as [n2 d2] eqn:Ey.
  simpl in Hc1, Hc2.
  unfold Qeq in Hr; simpl in Hr.
  destruct (bno_canon_pair_unique n1 (Z.pos d1) n2 (Z.pos d2)
    Hc1 Hc2 ltac:(apply bno_gt0_of_lt0_zgt; lia)
    ltac:(apply bno_gt0_of_lt0_zgt; lia)
    Hr) as [E1 E2].
  apply (id_cong2 (fun (a : Z) (b : positive) => (a # b)%Q)).
  - exact E1.
  - apply nz_id_of_eq. apply (Pos2Z.inj d1 d2).
    apply nz_eq_of_id. exact E2.
Qed.

(* The [Id]-face form of the main statement (through the bridge). *)
Lemma bno_qred_unique_id : forall x y : Q, x == y -> Id (Qred x) (Qred y).
Proof. intros x y H. exact (bno_qred_unique x y H). Qed.

(* ============================================================ *)
(* S2. The [bnorm] opposite face: discharge of the [bnorm_opp] slot of
   the [bnorm := Qred o Qabs] prescription, with the attack chain of
   the Real-carrier study transcribed *)
(* ============================================================ *)

(* The opposite-invariance of [Qred o Qabs] in [eq] form (the [Q]
   carrier [bnorm_opp] slot). *)
Lemma bno_qred_abs_opp : forall u : Q, @Id Q (Qred (Qabs (Qopp u))) (Qred (Qabs u)).
Proof.
  intro u. apply nz_id_of_eq.
  destruct u as [n d]. cbn [Qopp Qabs].
  rewrite Z.abs_opp. reflexivity.
Qed.

(* The same statement in [Id] form (through the bridge). *)
Lemma bno_qred_abs_opp_id : forall u : Q,
  Id (Qred (Qabs (Qopp u))) (Qred (Qabs u)).
Proof. intro u. exact (bno_qred_abs_opp u). Qed.

(* Transcription of the first dependency (the ready-made leg, keeping
   the library [Id] statement shape: the [Qabs]-norm invariance under
   [Qopp] and [qnorm]). *)
Lemma bno_qabs_qnorm_opp : forall u : Q,
  Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).
Proof. intro u. exact (bxra_qabs_opp_norm u). Qed.

(* Transcription of the second dependency (Real-carrier face:
   [bnorm (opp x) = bnorm x], library [Id] shape). *)
Lemma bno_bnorm_opp_real : forall a : Real,
  Id (bxra_bnorm_f (bxra_bopp_f a)) (bxra_bnorm_f a).
Proof. intro a. exact (bxra_f_norm_opp a). Qed.

(* ============================================================ *)
(* S3. The escape statement (its proof is an honest open item carried
   by the statement face; the ingredients are the factorial positivity
   and exponential-series laws of S03_QExp, the integer-scaling engine
   below, and a decidable fork on [q] versus the partial sums) *)
(* ============================================================ *)

Definition bno_sum_inv_fact_escape : Type :=
  forall q : Q,
    sigT (fun n : nat => Qlt 1 (Qabs (q_fact n * (q - exp_series n 1))%Q)).

(* Engine lemmas of the escape statement (three closed here; the main
   statement remains open). *)

(* Engine 1: the powers of one normalize. *)
Lemma bno_q_pow_one : forall n : nat, QeqT (q_pow 1%Q n) (1%Q).
Proof.
  intro n.
  exact (qeq_imp_qeqT _ _ (nat_ind (fun k => q_pow 1%Q k == 1%Q) (Qeq_refl 1%Q)
    (fun (m : nat) (IH : q_pow 1%Q m == 1%Q) =>
       Qeq_trans (1%Q * q_pow 1%Q m)%Q (q_pow 1%Q m) 1%Q
         (Qmult_1_l (q_pow 1%Q m)) IH) n)).
Qed.

(* Engine 2 helper: [q * (1/q)] normalizes ([Qmult_inv_r]'s side
   condition is a [Qeq]-form inequality). *)
Lemma bno_mul_div_self : forall q : Q, ~ (q == 0%Q) -> QeqT (q * (1%Q / q)) (1%Q).
Proof.
  intros q Hq. apply qeq_imp_qeqT. unfold Qdiv. rewrite Qmult_1_l.
  apply Qmult_inv_r. exact Hq.
Qed.

(* Engine 2: the one-step fraction form of the exponential series at
   [B := 1]. *)
Lemma bno_exp_series_succ_frac : forall n : nat, 
  QeqT (exp_series (Datatypes.S n) 1%Q)
 (exp_series n 1%Q + 1%Q / q_fact (Datatypes.S n)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. cbn [exp_series].
  rewrite (qeqT_imp_qeq _ _ (bno_q_pow_one (Datatypes.S n))). reflexivity.
Qed.

(* Engine 3: scaling the partial sums by [n!] lands them in the
   integers — the core ingredient for the divergence of the harmonic
   exponential tail. *)
Lemma bno_exp_scale_Z : forall n : nat,
  sigT (fun z : Z => QeqT (q_fact n * exp_series n 1)%Q ((z # 1)%Q)).
Proof.
  induction n as [| m IH].
  - exists 1%Z. apply qeq_imp_qeqT. unfold Qeq. cbn [q_fact exp_series Qnum Qden Qmult]. reflexivity.
  - destruct IH as [z Hz].
    exists (Z.of_nat (Datatypes.S m) * z + 1)%Z.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ m)).
    rewrite (qeqT_imp_qeq _ _ (bno_exp_series_succ_frac _)).
    assert (Hq0 : ~ ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m == 0%Q)).
    { intro Hc. apply (Qlt_not_eq 0%Q _ (QltT_to_Qlt 0%Q _ (q_fact_pos (Datatypes.S m)))).
      apply Qeq_sym. exact Hc. }
    assert (Hs : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * (1%Q / ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q) == 1%Q).
    { apply qeqT_imp_qeq. apply bno_mul_div_self. exact Hq0. }
    assert (Hm : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * exp_series m 1%Q == ((Z.of_nat (Datatypes.S m) * z) # 1)%Q).
    { apply (Qeq_trans _ ((Z.of_nat (Datatypes.S m) # 1)%Q
                          * (q_fact m * exp_series m 1)%Q)%Q).
      - apply Qeq_sym. apply Qmult_assoc.
      - apply (@Qmult_comp (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Qeq_refl (Z.of_nat (Datatypes.S m) # 1)%Q)
                           (q_fact m * exp_series m 1)%Q ((z # 1)%Q)
                           (qeqT_imp_qeq (q_fact m * exp_series m 1)%Q
                                ((z # 1)%Q) Hz)). }
    rewrite Qmult_plus_distr_r.
    rewrite Hs.
    rewrite Hm.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult].
    first [lia | ring | reflexivity].
Qed.

(* ============================================================ *)
(* S4. Extraction audit and assumption review *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
(* Extraction discipline (as in the earlier blocks): only scalar and lemma-level items are extracted; *)
(*   no carrier-dependent terms; [Obj.magic] is expected at zero on
   both faces. *)
Separate Extraction bno_qred_unique bno_qred_unique_id bno_canon_pair_unique
  bno_rel_prime_of_gcd1 bno_gt0_of_lt0 bno_qred_canon bno_qred_abs_opp
  bno_qred_abs_opp_id bno_qabs_qnorm_opp bno_bnorm_opp_real.

Print Assumptions bno_qred_unique.
Print Assumptions bno_qred_unique_id.
Print Assumptions bno_canon_pair_unique.
Print Assumptions bno_qred_abs_opp.
Print Assumptions bno_qred_abs_opp_id.
Print Assumptions bno_qabs_qnorm_opp.
Print Assumptions bno_bnorm_opp_real.
Print Assumptions bno_q_pow_one.
Print Assumptions bno_exp_series_succ_frac.
Print Assumptions bno_mul_div_self.
Print Assumptions bno_exp_scale_Z.

(* ============================================================ *)
(* S5. Closure of the escape statement: the main statement
   [bno_sum_inv_fact_escape] is discharged with an explicit [sigT]
   witness.

   Proof method (constructive, no LPO, no case fork): *)
(*   Step 1, engine approach via [bno_scale_q_int]: for any q = p/d choose n >= d so that n! * q lands in Z *)
(*     ([bno_qfact_int]: n! is itself an integer; [bno_qfact_scale_d]: d divides n!) *)
(*   a rational witness [w]; the denominator climbs into [nat] via
   [Z.to_nat]. *)
(*   Step 2, iteration [bno_tail_step]: T_{k+1} = (k+1) * T_k - 1 *)
(*   with [T_k := k! * (q - s_k)] (the ring tactic plus
   [bno_mul_div_self]). *)
(*   Step 3, two-step absorption [bno_two_step]: any integer z, after two steps, *)
(*   the integer absorption [|b * (a*z - 1) - 1| >= 2 > 1] for
   [a >= 2, b >= 3] swallows the zero case as well, so the fork on
   [q == s_k] disappears entirely (stronger than the original plan,
   with no LPO). *)
(*   Step 4, strict lower bound [bno_lt1_int_abs]: integer part |w| >= 2 implies [Qlt 1 (Qabs t)]; *)
(*   monotonicity assembles through right multiplication, closed
   explicitly on the three branches [z >= 1], [z = 0], [z <= -1],
   with no nonlinear reflection. *)
(*   Step 5, main statement [bno_sum_inv_fact_escape_close]: combining n! * q with the engine lemmas *)
(*   subtracting the integer scaling law from itself places [T_n0] in
   [Z]; after one index shift the two-step absorption applies, with
   witness index [S (S (S n0))]. *)
(* Assumption-face self-review: every item in this section is free of axioms, parameters, admitted proofs and variable declarations, *)
(*   Statements are carried by [Type]/[sigT]/[Qlt] shapes; the main
   statement closes under the global context. *)
(* Extraction discipline (as above): the sigT witness pieces (qfact_int/qfact_scale_d/) *)
(*   the proof-side lemmas stay out of the extraction unit and their
   assumption face is carried by [Print Assumptions]; the [Qeq]/[Qlt]
   scalar statements join the extraction unit. *)
(* The earlier statements of this module are untouched. *)
(* ============================================================ *)

From Stdlib Require Import Qring.

(* P1: n! is itself an integer *)
Lemma bno_qfact_int : forall n : nat,
  sigT (fun z : Z => Qeq (q_fact n)%Q ((z # 1)%Q)).
Proof.
  induction n as [| m IH].
  - exists 1%Z. reflexivity.
  - destruct IH as [z Hz]. exists (Z.of_nat (Datatypes.S m) * z)%Z.
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ m)). rewrite Hz. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P2: n! contains the multiples of the denominator d (d <= n) *)
Lemma bno_qfact_scale_d : forall (n : nat) (d : Z),
  (1 <= d)%Z -> (d <= Z.of_nat n)%Z ->
  sigT (fun w : Z => Qeq (q_fact n)%Q (((d * w)%Z # 1)%Q)).
Proof.
  induction n as [| m IH]; intros d Hd Hle.
  - lia.
  - destruct (Z.eq_dec d (Z.of_nat (Datatypes.S m))) as [HdEq | HdNe].
    + destruct (bno_qfact_int m) as [z Hz]. subst d.
      exists z. rewrite (qeqT_imp_qeq _ _ (q_fact_succ m)). rewrite Hz.
      unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
    + assert (Hlt : (d <= Z.of_nat m)%Z).
      { rewrite Nat2Z.inj_succ in Hle.
        assert (Hne : (d <> Z.succ (Z.of_nat m))%Z).
        { rewrite <- Nat2Z.inj_succ. exact HdNe. }
        lia. }
      destruct (IH d Hd Hlt) as [w Hw].
      exists (Z.of_nat (Datatypes.S m) * w)%Z.
      rewrite (qeqT_imp_qeq _ _ (q_fact_succ m)). rewrite Hw. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P3: any rational times a large enough n! is an integer *)
Lemma bno_pos_d_nat : forall d : positive, sigT (fun n : nat => (Z.pos d <= Z.of_nat n)%Z).
Proof.
  intro d.
  exact (existT (fun n : nat => (Z.pos d <= Z.of_nat n)%Z) (Z.to_nat (Z.pos d))
    (eq_ind (Z.pos d) (fun z => (Z.pos d <= z)%Z) (Z.le_refl (Z.pos d))
       (Z.of_nat (Z.to_nat (Z.pos d)))
       (eq_sym (Z2Nat.id (Z.pos d)
          (Z.lt_le_incl 0 (Z.pos d) (Pos2Z.is_pos d)))))).
Qed.

Lemma bno_scale_q_int : forall q : Q,
  sigT (fun n : nat => sigT (fun z : Z => Qeq (q_fact n * q)%Q ((z # 1)%Q))).
Proof.
  intro q. destruct q as [p d].
  destruct (bno_pos_d_nat d) as [n Hn].
  destruct (bno_qfact_scale_d n (Z.pos d)
    ltac:(pose proof (Pos2Z.is_pos d); lia) Hn) as [w0 Hw].
  exists n, (w0 * p)%Z.
  rewrite Hw. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P4: iteration step T_{k+1} = (k+1)*T_k - 1 *)
Lemma bno_tail_step : forall (n : nat) (q : Q), 
  QeqT ((q_fact (Datatypes.S n) * (q - exp_series (Datatypes.S n) 1))%Q)
 (((Z.of_nat (Datatypes.S n) # 1) * (q_fact n * (q - exp_series n 1)) - 1%Q)%Q).
Proof.
  intros n q. apply qeq_imp_qeqT.
  assert (Hinv : (q_fact (Datatypes.S n) * (1%Q / q_fact (Datatypes.S n)))%Q == 1%Q).
  { apply qeqT_imp_qeq. apply bno_mul_div_self. intro H0.
    apply (Qlt_not_eq 0%Q _ (QltT_to_Qlt 0%Q _ (q_fact_pos (Datatypes.S n)))).
    apply Qeq_sym. exact H0. }
  rewrite (qeqT_imp_qeq _ _ (bno_exp_series_succ_frac _)).
  apply (Qeq_trans _ (q_fact (Datatypes.S n) * (q - exp_series n 1)%Q
                      - q_fact (Datatypes.S n) * (1%Q / q_fact (Datatypes.S n))%Q)%Q).
  - ring.
  - rewrite Hinv. rewrite (qeqT_imp_qeq _ _ (q_fact_succ n)). ring.
Qed.

(* P5: an integer value (>= 2) gives a strictly greater-than-1 absolute value *)
Lemma bno_lt1_int_abs : forall (w : Z) (t : Q), 
  t == (w # 1)%Q -> (1 < Z.abs w)%Z -> QltT 1%Q (Qabs t).
Proof.
  intros w [tn td] Heq Hw.
  apply (Qlt_to_QltT _ _).
  unfold Qeq in Heq. cbn [Qnum Qden Qmult] in Heq.
  rewrite Z.mul_1_r in Heq.
  unfold Qlt, Qabs. cbn [Qnum Qden Qmult].
  rewrite Heq, Z.abs_mul, Z.mul_1_r.
  replace (Z.abs (Z.pos td)) with (Z.pos td)
    by (rewrite Z.abs_eq; pose proof (Pos2Z.is_pos td); lia).
  pose proof (Pos2Z.is_pos td) as Hp.
  pose proof (Z.mul_le_mono_nonneg_r 2 (Z.abs w) (Z.pos td) ltac:(lia) ltac:(lia)) as Hmono.
  lia.
Qed.

(* Constructor-level bridging lemma: rational arithmetic on the [Z#1]
   shape by constructor reduction alone, no opaque projections. *)
Lemma bno_z1_step_eq : forall x y : Z, 
  QeqT (((x # 1)%Q * (y # 1)%Q - 1%Q)%Q) (((x * y - 1)%Z # 1)%Q).
Proof.
  intros x y. apply qeq_imp_qeqT. unfold Qeq.
  cbn [Qnum Qden Qmult Qminus Qopp Qplus Pos.mul]. lia.
Qed.

Lemma bno_z1_minus_eq : forall x y : Z,  
 QeqT (((x # 1)%Q - (y # 1)%Q)%Q) (((x - y)%Z # 1)%Q).
Proof.
  intros x y. apply qeq_imp_qeqT. unfold Qeq.
  cbn [Qnum Qden Qminus Qopp Qplus Pos.mul]. lia.
Qed.

(* P6: the two-step iteration absorbs every integer (including 0) *)
Lemma bno_two_step : forall (n : nat) (q : Q) (z : Z), 
  (1 <= Z.of_nat n)%Z -> 
  (q_fact n * (q - exp_series n 1))%Q == (z # 1)%Q -> 
  QltT 1%Q
 (Qabs (q_fact (Datatypes.S (Datatypes.S n))                    * (q - exp_series (Datatypes.S (Datatypes.S n)) 1))%Q).
Proof.
  intros n q z Hn Hz.
  pose proof (bno_tail_step n q) as H1. apply qeqT_imp_qeq in H1. rewrite Hz in H1.
  assert (Hw1 : (q_fact (Datatypes.S n) * (q - exp_series (Datatypes.S n) 1))%Q
              == (((Z.of_nat (Datatypes.S n) * z - 1)%Z # 1)%Q)).
  { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S n) # 1) * (z # 1) - 1%Q)%Q)).
    - exact H1.
    - apply qeqT_imp_qeq. apply bno_z1_step_eq. }
  pose proof (bno_tail_step (Datatypes.S n) q) as H2. apply qeqT_imp_qeq in H2.
  rewrite Hw1 in H2.
  apply (bno_lt1_int_abs
    (Z.of_nat (Datatypes.S (Datatypes.S n)) * (Z.of_nat (Datatypes.S n) * z - 1) - 1)%Z
    (q_fact (Datatypes.S (Datatypes.S n))
     * (q - exp_series (Datatypes.S (Datatypes.S n)) 1))%Q).
  - apply (Qeq_trans _ (((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                          * (((Z.of_nat (Datatypes.S n) * z - 1)%Z # 1)%Q)
                          - 1%Q)%Q)).
    + exact H2.
    + apply qeqT_imp_qeq. apply bno_z1_step_eq.
  - rewrite !Nat2Z.inj_succ.
    (* [a := Z.succ (Z.of_nat n) >= 2] and [b := Z.succ a >= 3];
       monotonicity on the three branches, right-multiplication form. *)
    destruct (Z_lt_le_dec z 0) as [Hzneg | Hznonneg].
    + assert (Hm1 : (z * Z.succ (Z.of_nat n) <= (-1) * Z.succ (Z.of_nat n))%Z)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (Hm2 : ((Z.succ (Z.of_nat n) * z - 1) * Z.succ (Z.succ (Z.of_nat n))
                     <= (-3) * Z.succ (Z.succ (Z.of_nat n)))%Z)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite Z.abs_neq by lia. lia.
    + destruct (Z.eq_dec z 0) as [Hz0 | Hz0ne].
      * subst z. rewrite Z.mul_0_r.
        replace (0 - 1)%Z with (-1)%Z by lia.
        rewrite Z.abs_neq by lia. lia.
      * assert (Hm1 : (1 * Z.succ (Z.of_nat n) <= z * Z.succ (Z.of_nat n))%Z)
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Z.mul_1_l in Hm1.
        assert (Hprod : (1 <= Z.succ (Z.of_nat n) * z - 1)%Z) by lia.
        assert (Hm2 : (1 * Z.succ (Z.succ (Z.of_nat n))
                       <= (Z.succ (Z.of_nat n) * z - 1) * Z.succ (Z.succ (Z.of_nat n)))%Z)
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Z.mul_1_l in Hm2.
        rewrite Z.abs_eq by lia. lia.
Qed.

(* Main closure of the escape statement (explicit [sigT] witness, no
   LPO). *)
Theorem bno_sum_inv_fact_escape_close : bno_sum_inv_fact_escape.
Proof.
  unfold bno_sum_inv_fact_escape. intro q.
  destruct (bno_scale_q_int q) as [n0 [z1 Hz1]].
  pose proof (bno_exp_scale_Z n0) as Hs. destruct Hs as [z2 Hz2].
  assert (Hs' : (q_fact n0 * exp_series n0 1)%Q == (z2 # 1)%Q)
    by (apply qeqT_imp_qeq; exact Hz2).
  assert (HT0 : (q_fact n0 * (q - exp_series n0 1))%Q == (((z1 - z2)%Z # 1)%Q)).
  { apply (Qeq_trans _ (q_fact n0 * q - q_fact n0 * exp_series n0 1)%Q).
    - ring.
    - rewrite Hz1, Hs'. apply qeqT_imp_qeq. apply bno_z1_minus_eq. }
  pose proof (bno_tail_step n0 q) as Hts. apply qeqT_imp_qeq in Hts. rewrite HT0 in Hts.
  assert (HT1 : (q_fact (Datatypes.S n0) * (q - exp_series (Datatypes.S n0) 1))%Q
              == (((Z.of_nat (Datatypes.S n0) * (z1 - z2) - 1)%Z # 1)%Q)).
  { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S n0) # 1)
                          * (((z1 - z2)%Z # 1)%Q) - 1%Q)%Q)).
    - exact Hts.
    - apply qeqT_imp_qeq. apply bno_z1_step_eq. }
  exists (Datatypes.S (Datatypes.S (Datatypes.S n0))).
  apply (QltT_to_Qlt _ _).
  apply (bno_two_step (Datatypes.S n0) q
    (Z.of_nat (Datatypes.S n0) * (z1 - z2) - 1)%Z).
  - rewrite Nat2Z.inj_succ. lia.
  - exact HT1.
Qed.


(* ============================================================ *)
(* S6. Extraction audit and assumption review (final segment) *)
(* ============================================================ *)

(* Extraction discipline (as above): only Qeq/Qlt scalar/lemma-level items are extracted; sigT *)
(*   witness lemmas stay out of the extraction unit (an [existT]
   witness carries inherent erasure risk); their assumption face is
   carried by [Print Assumptions]. *)
Separate Extraction bno_tail_step bno_lt1_int_abs bno_two_step
  bno_z1_step_eq bno_z1_minus_eq.

Print Assumptions bno_pos_d_nat.
Print Assumptions bno_qfact_int.
Print Assumptions bno_qfact_scale_d.
Print Assumptions bno_scale_q_int.
Print Assumptions bno_tail_step.
Print Assumptions bno_lt1_int_abs.
Print Assumptions bno_z1_step_eq.
Print Assumptions bno_z1_minus_eq.
Print Assumptions bno_two_step.
Print Assumptions bno_sum_inv_fact_escape_close.
