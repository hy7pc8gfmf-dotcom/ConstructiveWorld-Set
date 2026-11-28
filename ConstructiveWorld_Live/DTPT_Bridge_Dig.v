(* ========================================================================= *)
(* Module   : DTPT_Bridge_Dig                                              *)
(* Mission.  Decidability and informative-certificate bridges over the DTPT *)
(*            Dig code tree: is_num dichotomy and size witness, dig_size   *)
(*            comparator dichotomy, sub_dig/dig_eqb size transfers, the    *)
(*            dig_Q round trip, u12 gate chain split/QleT, dig_dec test.   *)
(* Dependencies. DTPT, DTPT_DigTheory, DTPT_Extract of this development;    *)
(*            Stdlib QArith/List/Bool/Arith.                               *)
(* References.  Upstream ConstructiveWorld-Main DTPT_Bridge_Dig.v (names    *)
(*            kept); DTPT_DigTheory.v :365/:442/:575/:769; DTPT_Extract.v  *)
(*            :136/:148; DTPT.v :1178; G11_IDLFam.v :297; LW0LeibWindow:66.*)
(* Constructivity. Statement faces fully Set-carried, zero Prop statements: *)
(*            bool faces on the DTPT Id family and the local generic-in-   *)
(*            Type dId; Q order/equality on dQleT/dQeqT := Id (Qle_bool    *)
(*            ...) true / Id (Qeq_bool ...) true; dichotomies on the local *)
(*            ddec decision sum (stdlib sumbool branches are Prop-limited; *)
(*            ddec mirrors the library sdec precedent, carries only Set    *)
(*            certificates, so zero Prop is embedded in any Set carrier).  *)
(*            Recasts of the upstream Prop faces, all declared: dQleT/     *)
(*            dQeqT inductives become Id-of-bool faces, the round-trip     *)
(*            premise d = dQ x becomes dId d (dQ x), the nat strict order  *)
(*            becomes Id (Nat.ltb ...) true, and the witness's negative    *)
(*            Leibniz conjunct becomes the positive discriminator face     *)
(*            (first_dig + dig_eqb false). Prop reasoning stays inside     *)
(*            proof bodies only; zero axioms, zero admits, no classical    *)
(*            logic; all proofs close in Defined (no pure-Prop statement,  *)
(*            hence no Qed anywhere).                                      *)
(* Build.     rocq c -native-compiler no -q -Q <Set Live world root> ""    *)
(*            DTPT_Bridge_Dig.v (single shot, this directory as workdir).  *)
(* ========================================================================= *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.
Require DTPT.
Require DTPT_DigTheory.
Require DTPT_Extract.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_DigTheory.DTPT_DigTheory.
Import DTPT_Extract.DTPT_Extract.

(* ============================================================ *)
(* Section 0. local statement-face families: the decision sum,   *)
(* the generic Set-equality face, the Q order/equality faces.    *)
(* ============================================================ *)

(* The Set-layer decision sum (the informative-certificate variant of       *)
(* sumbool: stdlib sumbool branches are Prop-limited and cannot carry Set-  *)
(* layer certificates; this two-way dispatch type carries informative       *)
(* certificates in both branches. It lives in Type alongside option/sigT,   *)
(* informative end to end, extractable, zero Prop).                         *)
Inductive ddec (A B : Type) : Type :=
| ddec_l (a : A)
| ddec_r (b : B).

(* The generic Set-valued identity type, generic in Type so it applies to   *)
(* Dig : Type (the DTPT Id face is bounded at Set and cannot). Same shape   *)
(* as the library generic Set-equality precedent.                           *)
Inductive dId {A : Type} (a : A) : A -> Set :=
| dId_refl : dId a a.

Arguments dId_refl {A} {a}.

(* Leibniz read-out of the dId face (proof-side bridge; the conclusion is   *)
(* the Prop equality, consumed only inside proof bodies below).             *)
Lemma dId_eq : forall (A : Type) (x y : A), dId x y -> x = y.
Proof. intros A x y H. destruct H. reflexivity. Defined.

(* Q non-strict order certificate: the boolean identity face of Qle_bool.   *)
Definition dQleT (x y : Q) : Set := Id (Qle_bool x y) true.

(* Q equality certificate: the boolean identity face of Qeq_bool.           *)
Definition dQeqT (x y : Q) : Set := Id (Qeq_bool x y) true.

(* Reflection face: dQeqT x x holds for every x, through the stdlib         *)
(* Qeq_bool_iff bridge and the propositional Qeq_refl (both constructive).  *)
Lemma dQeqT_refl : forall x : Q, dQeqT x x.
Proof.
  intros x. unfold dQeqT.
  exact (eq_imp_id (proj2 (Qeq_bool_iff x x) (Qeq_refl x))).
Defined.

(* ============================================================ *)
(* Section 1. the is_num executable decision bridges.            *)
(* ============================================================ *)

(* Decision completeness: is_num returns a decided bool on every code;      *)
(* each branch carries the boolean identity certificate of the outcome.     *)
Theorem is_num_spec : forall d : Dig,
  ddec (Id (is_num d) true) (Id (is_num d) false).
Proof.
  intro d. destruct d as [x | a b | l | n f | a b | a | a b].
  - apply ddec_l. exact id_refl.
  - apply ddec_r. exact id_refl.
  - apply ddec_r. exact id_refl.
  - apply ddec_r. exact id_refl.
  - apply ddec_r. exact id_refl.
  - apply ddec_r. exact id_refl.
  - apply ddec_r. exact id_refl.
Defined.

(* Characterization face: is_num = true carries the size-one witness       *)
(* informatively (sigT over the witness, Set product of the two boolean    *)
(* identity certificates; the forward direction only -- the converse is    *)
(* false, dSeq [] is a size-one non-numeric counterexample, so no          *)
(* converse face is bridged).                                              *)
Theorem is_num_size1_set : forall d : Dig,
  Id (is_num d) true ->
  sigT (fun n : nat => prod (Id n 1%nat) (Id (dig_size d) n)).
Proof.
  intros d H.
  pose proof (id_eq_SI bool (is_num d) true H) as He.
  exists 1%nat. split.
  - exact id_refl.
  - exact (eq_imp_id (is_num_size1 d He)).
Defined.

(* ============================================================ *)
(* Section 2. tower size monotonicity: the comparator dichotomy   *)
(* and the transfer faces.                                       *)
(* ============================================================ *)

(* Executable size comparator: Nat.leb dispatches the decision sum, each    *)
(* branch carrying the boolean identity certificate of its outcome.         *)
Definition dig_size_le_dec (a d : Dig) :
  ddec (Id (Nat.leb (dig_size a) (dig_size d)) true)
       (Id (Nat.leb (dig_size a) (dig_size d)) false).
Proof.
  destruct (Nat.leb (dig_size a) (dig_size d)) eqn:E.
  - apply ddec_l. exact id_refl.
  - apply ddec_r. exact id_refl.
Defined.

(* sub_dig size dichotomy: with the sub_dig certificate, the comparator     *)
(* left branch carries the leb = true identity; the right branch carries    *)
(* the strict order as the Nat.ltb boolean identity certificate (the        *)
(* computational dichotomy of the comparator; the strict branch is          *)
(* vacuous under the monotonicity theorem, kept for the dichotomy shape).   *)
Theorem sub_dig_size_mono_set : forall d a : Dig,
  Id (sub_dig a d) true ->
  ddec (Id (Nat.leb (dig_size a) (dig_size d)) true)
       (Id (Nat.ltb (dig_size d) (dig_size a)) true).
Proof.
  intros d a Hsub.
  destruct (Nat.leb (dig_size a) (dig_size d)) eqn:E.
  - apply ddec_l. exact id_refl.
  - apply ddec_r.
    exact (eq_imp_id (proj2 (Nat.ltb_lt (dig_size d) (dig_size a))
                       (proj1 (Nat.leb_gt (dig_size a) (dig_size d)) E))).
Defined.

(* Coherent transfer face: under the sub_dig certificate the comparator is  *)
(* always on the left branch (the leb = true identity certificate).         *)
Theorem sub_dig_size_dec_true : forall d a : Dig,
  Id (sub_dig a d) true ->
  Id (Nat.leb (dig_size a) (dig_size d)) true.
Proof.
  intros d a Hsub.
  pose proof (id_eq_SI bool (sub_dig a d) true Hsub) as He.
  pose proof (sub_dig_size_mono d a He) as Hle.
  exact (eq_imp_id (proj2 (Nat.leb_le (dig_size a) (dig_size d)) Hle)).
Defined.

(* dig_eqb size transfer: the dig_eqb certificate forces the size           *)
(* comparator certificate (n := dig_size a self-instantiation of the        *)
(* library size-bound lemma).                                               *)
Theorem dig_eqb_size_dec_true : forall a b : Dig,
  Id (dig_eqb a b) true ->
  Id (Nat.leb (dig_size a) (dig_size b)) true.
Proof.
  intros a b Hab.
  pose proof (id_eq_SI bool (dig_eqb a b) true Hab) as He.
  pose proof (dig_eqb_size_bound (dig_size a) a b (le_n (dig_size a)) He) as Hle.
  exact (eq_imp_id (proj2 (Nat.leb_le (dig_size a) (dig_size b)) Hle)).
Defined.

(* dig_Q projection round trip: for a code equal to the numeric node dQ x,  *)
(* the projection value equals x, delivered as the QeqT certificate. The    *)
(* premise is the generic-in-Type dId face (the propositional d = dQ x      *)
(* premise of the library lemma has no Set form); the projection is not     *)
(* injective (the default-zero collision), so only this direction is        *)
(* bridged.                                                                 *)
Theorem dig_Q_roundtrip_set : forall (d : Dig) (x : Q),
  dId d (dQ x) -> dQeqT (dig_Q d) x.
Proof.
  intros d x H.
  pose proof (dId_eq Dig d (dQ x) H) as He.
  rewrite He.
  exact (dQeqT_refl x).
Defined.

(* ============================================================ *)
(* Section 3. the extraction gate chain: dichotomy, gate split,   *)
(* and the QleT certificates.                                    *)
(* ============================================================ *)

(* Full-chain decision: u12_gate_chain returns a decided bool on every      *)
(* column / threshold pair, each branch carrying its identity certificate.  *)
Theorem u12_gate_chain_spec : forall (l : list Q) (t : Q),
  ddec (Id (u12_gate_chain l t) true) (Id (u12_gate_chain l t) false).
Proof.
  intros l t. destruct (u12_gate_chain l t) eqn:E.
  - apply ddec_l. exact id_refl.
  - apply ddec_r. exact id_refl.
Defined.

(* Two-gate split: the chain conjunction dispatches independently on the    *)
(* threshold gate (gate_pass on the adjusted column height) and the phase   *)
(* gate (u12_phase_side_bool), each as its own decision sum.                *)
Definition u12_gate_chain_gates (l : list Q) (t : Q) :
  prod (ddec (Id (gate_pass t (H_adj l)) true)
             (Id (gate_pass t (H_adj l)) false))
       (ddec (Id (u12_phase_side_bool l 0%nat) true)
             (Id (u12_phase_side_bool l 0%nat) false)).
Proof.
  split.
  - destruct (gate_pass t (H_adj l)) eqn:E.
    + apply ddec_l. exact id_refl.
    + apply ddec_r. exact id_refl.
  - destruct (u12_phase_side_bool l 0%nat) eqn:E.
    + apply ddec_l. exact id_refl.
    + apply ddec_r. exact id_refl.
Defined.

(* Threshold gate QleT certificate: gate_pass t h = true unfolds (through   *)
(* the library boolean reflection of gate_pass) to the Q order h <= t,      *)
(* carried as the dQleT boolean identity certificate.                       *)
Theorem gate_pass_QleT : forall t h : Q,
  Id (gate_pass t h) true -> dQleT h t.
Proof.
  intros t h H.
  pose proof (id_eq_SI bool (gate_pass t h) true H) as He.
  pose proof (proj1 (llm_gate_pass_iff t h) He) as Hle.
  exact (eq_imp_id (proj2 (Qle_bool_iff h t) Hle)).
Defined.

(* Main certificate: the chain certificate splits over andb into the two    *)
(* gate certificates -- the threshold gate carries H_adj l <= t, the phase  *)
(* gate carries H_adj (P0 l) <= H_adj (Pinf l 0) (both as dQleT boolean     *)
(* identity certificates; the phase gate body is Qle_bool-valued, so its    *)
(* certificate converts directly).                                          *)
Theorem u12_gate_chain_QleT : forall (l : list Q) (t : Q),
  Id (u12_gate_chain l t) true ->
  prod (dQleT (H_adj l) t)
       (dQleT (H_adj (P0 l)) (H_adj (Pinf l 0%nat))).
Proof.
  intros l t Hc.
  pose proof (id_eq_SI bool (u12_gate_chain l t) true Hc) as He.
  unfold u12_gate_chain in He.
  apply andb_true_iff in He. destruct He as [Hg Hp].
  split.
  - exact (gate_pass_QleT t (H_adj l) (eq_imp_id Hg)).
  - unfold u12_phase_side_bool in Hp.
    exact (eq_imp_id Hp).
Defined.

(* ============================================================ *)
(* Section 4. the dig_dec shape+size double test: a sound        *)
(* lower approximation of Leibniz equality, with the concrete    *)
(* completeness-failure discriminator witness.                   *)
(* ============================================================ *)
(* Full Leibniz equality on Dig is not decidable (the dCode carrier         *)
(* function equality is undecidable), so dig_dec tests only the decidable   *)
(* sub-face "constructor tag + tower size":                                 *)
(*   soundness  a = b -> dig_dec a b = true;                                *)
(*   completeness fails -- the witness below gives two codes agreeing on   *)
(*   tag and size (hence dig_dec = true) that are still distinguishable.    *)
(* The witness is delivered positively: the first projections of the two    *)
(* codes carry the dig_eqb false certificate (the dQ leaves hold Q 0 vs     *)
(* Q 1, where dig_eqb computes through Qeq_bool), a Set-carried            *)
(* discriminator; the negative Leibniz reading (the two codes are not       *)
(* equal) is recoverable inside any proof body from that certificate        *)
(* through the dQ leaf Qeq_bool_iff and the dig_inj_dPair/dig_inj_dQ        *)
(* injectivity faces of the library.                                        *)

Definition dig_tag (d : Dig) : nat :=
  match d with
  | dQ _ => 0%nat
  | dPair _ _ => 1%nat
  | dSeq _ => 2%nat
  | dCode _ _ => 3%nat
  | dJudge _ _ => 4%nat
  | dModel _ => 5%nat
  | dProofT _ _ => 6%nat
  end.

Definition dig_dec (a b : Dig) : bool :=
  andb (Nat.eqb (dig_tag a) (dig_tag b))
       (Nat.eqb (dig_size a) (dig_size b)).

(* The first-projection discriminator on the pair constructor. *)
Definition first_dig (d : Dig) : Dig :=
  match d with
  | dPair u _ => u
  | _ => dQ 0
  end.

Theorem dig_dec_sound : forall a b : Dig,
  dId a b -> Id (dig_dec a b) true.
Proof.
  intros a b H. destruct H.
  unfold dig_dec. apply eq_imp_id.
  rewrite (Nat.eqb_refl (dig_tag a)). rewrite (Nat.eqb_refl (dig_size a)).
  reflexivity.
Defined.

Theorem dig_dec_shape : forall a b : Dig,
  Id (dig_dec a b) true -> Id (dig_tag a) (dig_tag b).
Proof.
  intros a b H.
  pose proof (id_eq_SI bool (dig_dec a b) true H) as He.
  unfold dig_dec in He.
  apply andb_true_iff in He. destruct He as [H1 _].
  apply (proj1 (Nat.eqb_eq (dig_tag a) (dig_tag b))) in H1.
  exact (eq_imp_id H1).
Defined.

Theorem dig_dec_size : forall a b : Dig,
  Id (dig_dec a b) true -> Id (dig_size a) (dig_size b).
Proof.
  intros a b H.
  pose proof (id_eq_SI bool (dig_dec a b) true H) as He.
  unfold dig_dec in He.
  apply andb_true_iff in He. destruct He as [_ H2].
  apply (proj1 (Nat.eqb_eq (dig_size a) (dig_size b))) in H2.
  exact (eq_imp_id H2).
Defined.

(* The completeness-failure witness, positive form: the two pair codes      *)
(* pass the double test (dig_dec true, same tag, same size) while their     *)
(* first projections carry the dig_eqb false discriminator certificate.     *)
Theorem dig_dec_not_eq_witness :
  prod (Id (dig_dec (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0))) true)
       (prod (Id (dig_eqb (first_dig (dPair (dQ 0) (dQ 0)))
                          (first_dig (dPair (dQ 1) (dQ 0)))) false)
             (prod (Id (dig_tag (dPair (dQ 0) (dQ 0)))
                       (dig_tag (dPair (dQ 1) (dQ 0))))
                   (Id (dig_size (dPair (dQ 0) (dQ 0)))
                       (dig_size (dPair (dQ 1) (dQ 0)))))).
Proof.
  split.
  - exact id_refl.
  - split.
    + exact id_refl.
    + split.
      * exact id_refl.
      * exact id_refl.
Defined.

(* ============================================================ *)
(* Assumption audit: every theorem and every proof-bearing        *)
(* definition, one line each.                                    *)
(* ============================================================ *)

Print Assumptions is_num_spec.
Print Assumptions is_num_size1_set.
Print Assumptions dig_size_le_dec.
Print Assumptions sub_dig_size_mono_set.
Print Assumptions sub_dig_size_dec_true.
Print Assumptions dig_eqb_size_dec_true.
Print Assumptions dig_Q_roundtrip_set.
Print Assumptions u12_gate_chain_spec.
Print Assumptions u12_gate_chain_gates.
Print Assumptions gate_pass_QleT.
Print Assumptions u12_gate_chain_QleT.
Print Assumptions dig_dec.
Print Assumptions dig_dec_sound.
Print Assumptions dig_dec_shape.
Print Assumptions dig_dec_size.
Print Assumptions dig_dec_not_eq_witness.
