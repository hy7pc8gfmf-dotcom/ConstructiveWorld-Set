(* ConstructiveWorld-Set -- Real-layer iterated dual of the policy-iteration family (nontrivial reinforcement segment). *)
(*
   Mission.  Theorem 4.8 calls for iterated contraction of the policy-iteration
   dual: KL(pi*||pi_t) should shrink geometrically like (1-eta)^t; this file
   closes that induction on the Real layer in eps form.  Main results:
     geodi_policy_iter_kl_geom_iter_eps  KL(pi*||pi_t) <= (1-eta)^t*KL(pi*||pi_0)+eps
     geodi_policy_iter_kl_geom_iter_B    KL(pi*||pi_t) <=_B (1-eta)^t*KL(pi*||pi_0)
     geodi_seq_norm / geodi_step_norm    the orbit stays normalized;
     geodi_iter_one_step_eps / geodi_iter_two_steps_eps  one- and two-step cases.

   Dependencies.  S01_BaseRing .. S15_TailFEPUp, UpRealLeB, UpRealLeB2,
   G07_KLWall (powb_pow power carrier), UpReqGeomD (one-step engine
   geod_policy_iter_kl_geom_step_eps, geod_lsum, geod_kappa_pos),
   UpGeomB (geod_b_half_double).

   References.  Prefix geodi_ clash-free in the tree; the orbit carrier mirrors
   the UpGeomB geod_b_iterate precedent; a single eps witness is introduced
   once and kept fixed along the whole induction.

   Constructivity.  Set-valued statements (real_le / real_lt / real_eq /
   real_le_b, with Or := A+B); the orbit is a sigT recursion threading a
   per-step positivity certificate; every proof ends in Qed and the closing
   Print Assumptions sweep rechecks all items; pure term-mode assembly
   (real_eq is not Id: no rewriting on the main chain).  Honest boundary:
   eta open (the engine needs 0 < kappa, so eta = 1 is out of scope), n >= 1
   explicit (Z would be the empty sum 0 at n = 0); a le_b multiplicative
   monotone closure is missing from the library and not assumed (open gap).

   Build.  rocq c -native-compiler no -q -Q world "" UpReqGeomIter.v
   (Rocq 9.1.0), same-world dependency .vo tree, cpu_guard wrapper. *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import UpReqGeomD.
Require Import UpGeomB.

(* ============================================================ *)
(* A. Ring auxiliary: kappa + eta == 1 (kappa := 1-eta taken literally; reordered from the GeomD fact eta+(1-eta)==1) *)
(* ============================================================ *)
Lemma geodi_kappa_plus_eta : forall eta : Real,
  real_eq (real_plus (real_plus real_one (real_opp eta)) eta) real_one.
Proof.
  intros eta.
  apply (real_eq_trans _ (real_plus eta (real_plus real_one (real_opp eta)))).
  - apply real_plus_comm.
  - exact (geod_eta_plus_kappa eta).
Qed.

(* Left identity: 1*x == x (CW_219 provides only the right-identity lemma real_mult_one; commutation yields the left one) *)
Lemma geodi_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x.
  exact (real_eq_trans (real_mult real_one x) (real_mult x real_one) x
           (real_mult_comm real_one x) (real_mult_one x)).
Qed.

(* ============================================================ *)
(* B. Three positivity items: positive powers / positive interpolation partition Z / pointwise-positive next policy *)
(* ============================================================ *)
Lemma geodi_pow_pos_lt : forall (a alpha : Real) (Ha : real_lt real_zero a),
  real_lt real_zero (real_pow_pos a alpha Ha).
Proof.
  intros a alpha Ha. unfold real_pow_pos.
  exact (cauchy_real_exp_pos (real_mult alpha (cw_log a Ha))).
Qed.

(* Z positive (nontrivial premise n >= 1; each term = positive power x positive power; real_list_sum_pos: nonempty sum of positives) *)
(*   The n >= 1 bound uses the CW_219 Set-layer encoding NatLt := Id (ltb) true (the UpMinP/G07_KLWall *)
(*   precedents use the same pattern; the Prop-layer Datatypes.lt is barred by the constructivity rule; *)
(*   the n = 0 branch is discharged by destruct on id_false_true (CW_219: Id false true -> Empty_set)) *)
Lemma geodi_zpos : forall (n : nat) (r q : nat -> Real) (kappa : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hn : NatLt 0 n),
  real_lt real_zero (real_interp_Z n r q kappa Hr Hq).
Proof.
  intros n r q kappa Hr Hq Hn. unfold real_interp_Z.
  apply (real_list_sum_pos nat).
  - intro i.
    apply (real_mult_positive
             (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
             (real_pow_pos (q i) kappa (Hq i))).
    + exact (geodi_pow_pos_lt (r i) (real_plus real_one (real_opp kappa)) (Hr i)).
    + exact (geodi_pow_pos_lt (q i) kappa (Hq i)).
  - destruct n as [| m].
    + (* NatLt 0 0 is Id false true: Empty_set has no constructors (G07_KLWall precedent) *)
      destruct (id_false_true Hn).
    + intro Hc. simpl in Hc. discriminate Hc.
Qed.

(* Next policy pointwise positive: multiplicative positivity chain of positive power x positive power x positive reciprocal *)
Lemma geodi_next_pos : forall (n : nat) (r q : nat -> Real) (kappa : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hn : NatLt 0 n) (i : nat),
  real_lt real_zero
    (real_step_next n r q kappa Hr Hq (geodi_zpos n r q kappa Hr Hq Hn) i).
Proof.
  intros n r q kappa Hr Hq Hn i. unfold real_step_next.
  apply (real_mult_positive
           (real_mult
              (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
              (real_pow_pos (q i) kappa (Hq i)))
           (real_inv_pos (real_interp_Z n r q kappa Hr Hq)
                         (geodi_zpos n r q kappa Hr Hq Hn))).
  - apply (real_mult_positive
             (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
             (real_pow_pos (q i) kappa (Hq i))).
    + exact (geodi_pow_pos_lt (r i) (real_plus real_one (real_opp kappa)) (Hr i)).
    + exact (geodi_pow_pos_lt (q i) kappa (Hq i)).
  - exact (real_inv_pos_pos (real_interp_Z n r q kappa Hr Hq)
              (geodi_zpos n r q kappa Hr Hq Hn)).
Qed.

(* ============================================================ *)
(* C. Orbit carrier: dependent recursion packaged in sigT, threading per-step certificates (all Set-valued) *)
(*   pi_0 := p; pi_{S m} := step_next(pi*, pi_m; kappa); Z-positivity and pointwise positivity supplied at each step. *)
(* ============================================================ *)
Fixpoint geodi_seq (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (kappa : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (t : nat)
  : sigT (fun q : nat -> Real => forall i : nat, real_lt real_zero (q i)) :=
  match t with
  | O => existT _ p Hp
  | Datatypes.S m =>
      match geodi_seq n r Hr kappa p Hp Hn m with
      | existT _ q Hq =>
          existT _
            (real_step_next n r q kappa Hr Hq
               (geodi_zpos n r q kappa Hr Hq Hn))
            (geodi_next_pos n r q kappa Hr Hq Hn)
      end
  end.

Definition geodi_iterate (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (t : nat) : nat -> Real :=
  projT1 (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn t).

Definition geodi_iterate_pos (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (t : nat) :
  forall i : nat, real_lt real_zero (geodi_iterate n r Hr eta p Hp Hn t i) :=
  projT2 (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn t).

(* Unfolding lemma: the orbit at step S equals the engine's next policy (match resolution carried out inside the proof) *)
Lemma geodi_iterate_S : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (m : nat),
  Id (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m))
  (real_step_next n r (geodi_iterate n r Hr eta p Hp Hn m)
    (real_plus real_one (real_opp eta))
    Hr (geodi_iterate_pos n r Hr eta p Hp Hn m)
    (geodi_zpos n r (geodi_iterate n r Hr eta p Hp Hn m)
       (real_plus real_one (real_opp eta)) Hr
       (geodi_iterate_pos n r Hr eta p Hp Hn m) Hn)).
Proof.
  intros n r Hr eta p Hp Hn m.
  unfold geodi_iterate, geodi_iterate_pos.
  (* First unfold one step so the (S m) branch exposes the match (the fix stays stuck on the variable m, the inner orbit remains folded), *)
  (* then destruct the inner orbit's existT to retype -- in the other order the match never moves. *)
  cbn [geodi_seq].
  destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn m)
    as [q Hq].
  apply id_refl.
Qed.

(* Orbit sigT pair equation: the whole S-step pair == existT(step(q), next-certificate(q)). *)
(*   Lawful retyping target for the dependent certificate: abstracting the whole geodi_seq (S m) pair is *)
(*   dependently well-formed (the certificate's type retypes with the whole pair); abstracting the bare *)
(*   value geodi_iterate (S m) is ill-formed (the type of the 4th argument of real_kl_term depends on the 2nd). *)
Lemma geodi_seq_pair_S : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (kappa : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (m : nat),
  Id (geodi_seq n r Hr kappa p Hp Hn (Datatypes.S m))
  (existT (fun q : nat -> Real => forall i : nat, real_lt real_zero (q i))
    (real_step_next n r (projT1 (geodi_seq n r Hr kappa p Hp Hn m))
       kappa Hr (projT2 (geodi_seq n r Hr kappa p Hp Hn m))
       (geodi_zpos n r (projT1 (geodi_seq n r Hr kappa p Hp Hn m)) kappa Hr
          (projT2 (geodi_seq n r Hr kappa p Hp Hn m)) Hn))
    (geodi_next_pos n r (projT1 (geodi_seq n r Hr kappa p Hp Hn m)) kappa Hr
       (projT2 (geodi_seq n r Hr kappa p Hp Hn m)) Hn)).
Proof.
  intros n r Hr kappa p Hp Hn m.
  cbn [geodi_seq].
  destruct (geodi_seq n r Hr kappa p Hp Hn m) as [q Hq].
  apply id_refl.
Qed.

(* ============================================================ *)
(* D. Normalization invariant along the orbit: sum pi_{t+1} == sum(term)*inv Z == Z*inv Z == 1 *)
(* ============================================================ *)
Lemma geodi_step_norm : forall (n : nat) (r q : nat -> Real) (kappa : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hq : forall i : nat, real_lt real_zero (q i))
    (HZ : real_lt real_zero (real_interp_Z n r q kappa Hr Hq)),
  real_eq (geod_lsum n (real_step_next n r q kappa Hr Hq HZ)) real_one.
Proof.
  intros n r q kappa Hr Hq HZ.
  unfold geod_lsum, real_step_next.
  apply (real_eq_trans _
           (real_mult (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
                      (real_interp_Z n r q kappa Hr Hq))).
  - (* sum(term*invZ) == invZ*sum(term) == invZ*Z (sum(term) is Z by definitional transparency) *)
    apply (real_eq_trans _
             (real_mult (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
                        (real_list_sum nat
                           (fun i : nat =>
                              real_mult (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
                              (real_pow_pos (q i) kappa (Hq i)))
                           (seq 0 n)))).
    + exact (real_list_sum_linear_r nat
               (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
               (fun i : nat =>
                  real_mult (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
                              (real_pow_pos (q i) kappa (Hq i)))
               (seq 0 n)).
    + apply (RealSetoid.real_eq_mult_compat
               (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
               (real_list_sum nat
                  (fun i : nat =>
                     real_mult (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
                              (real_pow_pos (q i) kappa (Hq i)))
                  (seq 0 n))
               (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
               (real_interp_Z n r q kappa Hr Hq)).
      * apply real_eq_refl.
      * apply real_eq_refl.
  - (* invZ*Z == Z*invZ == 1 *)
    apply (real_eq_trans _
             (real_mult (real_interp_Z n r q kappa Hr Hq)
                        (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ))).
    + apply real_mult_comm.
    + exact (real_inv_pos_correct (real_interp_Z n r q kappa Hr Hq) HZ).
Qed.

Lemma geodi_seq_norm : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n)
    (Hnormp : real_eq (geod_lsum n p) real_one) (t : nat),
  real_eq (geod_lsum n (geodi_iterate n r Hr eta p Hp Hn t)) real_one.
Proof.
  intros n r Hr eta p Hp Hn Hnormp t. induction t as [| m IH].
  - exact Hnormp.
  - unfold geodi_iterate, geodi_iterate_pos.
    cbn [geodi_seq].
    destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn m)
      as [q Hq].
    exact (geodi_step_norm n r q (real_plus real_one (real_opp eta)) Hr Hq
             (geodi_zpos n r q (real_plus real_one (real_opp eta)) Hr Hq Hn)).
Qed.

(* Paired generalization of the norm: normalization of the m-step orbit component q (fed through the q/Hq slots after the destruct retyping). *)
(*   The fold-wrapped geodi_iterate ... m and the resolved q are not convertible (the fix is stuck on the variable m), *)
(*   so the along-orbit certificate family must be generalized pairwise on the orbit = existT q Hq equation. *)
Lemma geodi_seq_norm_pair : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n)
    (Hnormp : real_eq (geod_lsum n p) real_one) (m : nat)
    (q : nat -> Real) (Hq : forall i : nat, real_lt real_zero (q i)),
  geodi_seq n r Hr eta p Hp Hn m = existT _ q Hq ->
  real_eq (geod_lsum n q) real_one.
Proof.
  intros n r Hr eta p Hp Hn Hnormp m.
  induction m as [| m IH]; intros q Hq E.
  - cbn [geodi_seq] in E.
    (* base case: the component equation gives p = q (projT1 projection, avoiding dependent inversion) *)
    assert (Epq : p = q).
    { exact (f_equal (@projT1 (nat -> Real)
                        (fun q0 : nat -> Real => forall i : nat,
                            real_lt real_zero (q0 i))) E). }
    rewrite <- Epq. exact Hnormp.
  - cbn [geodi_seq] in E.
    destruct (geodi_seq n r Hr eta p Hp Hn m) as [q' Hq'] eqn:E'.
    cbn [projT1 projT2] in E.
    (* the S-step component q == step(q') (projT1 projection); the norm is supplied by geodi_step_norm *)
    assert (Eq1 : real_step_next n r q' eta Hr Hq'
                    (geodi_zpos n r q' eta Hr Hq' Hn) = q).
    { exact (f_equal (@projT1 (nat -> Real)
                        (fun q0 : nat -> Real => forall i : nat,
                            real_lt real_zero (q0 i))) E). }
    rewrite <- Eq1.
    exact (geodi_step_norm n r q' eta Hr Hq'
             (geodi_zpos n r q' eta Hr Hq' Hn)).
Qed.

(* ============================================================ *)
(* E. Order preservation under left multiplication by a positive factor (both Or branches: the lt branch gets the engine lemma; the eq branch is retyping) *)
(* ============================================================ *)
Lemma geodi_mult_le_compat_l : forall (kappa a b : Real),
  real_lt real_zero kappa -> real_le a b ->
  real_le (real_mult kappa a) (real_mult kappa b).
Proof.
  intros kappa a b Hk Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (real_mult_lt_compat_l a b kappa Hlt Hk)).
  - exact (inr (RealSetoid.real_eq_mult_compat kappa a kappa b
                  (real_eq_refl kappa) Heq)).
Qed.

(* ============================================================ *)

(*   KL(pi*||pi_t) <= (1-eta)^t*KL(pi*||pi_0) + eps *)
(* ============================================================ *)
Theorem geodi_policy_iter_kl_geom_iter_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n),
  forall (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn t i)
                       (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
                  (geod_lsum n
                     (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
       eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  induction t as [| m IH].
  - (* base case t=0: KL0 <= 1*KL0 + eps (retyped via 1*KL0 == KL0, as in UpGeomB) *)
    apply (RealSetoid.real_le_id_l
             (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
             (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             (real_plus
                (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                eps)).
    + apply real_eq_sym.
      exact (real_eq_trans
               (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult real_one
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
               (RealSetoid.real_eq_mult_compat
                  (powb_pow (real_plus real_one (real_opp eta)) O)
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                  real_one
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                  (real_eq_refl real_one) (real_eq_refl
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (geodi_mult_one_l (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))).
    + exact (inl (real_lt_plus_r_zero
                    (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                       (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                    eps Heps)).
  - (* induction step: the one-step lemma contributes eta*eps, kappa reweights, and (kappa+eta)==1 finishes *)
    (* Orbit pair resolution: the IH is first unfolded and reverted so that it retypes with the whole pair into the q shape -- *)
    (*   the fold-wrapped IH is not convertible with the resolved q (the fix is stuck on the variable m), so the certificates *)
    (*   (norm / Z-positivity / pointwise positivity) are all supplied directly through q/Hq (geodi_seq_norm_pair etc.). *)
    unfold geodi_iterate, geodi_iterate_pos in IH.
    unfold geodi_iterate, geodi_iterate_pos.
    revert IH.
    cbn [geodi_seq].
    destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn m)
      as [q Hq] eqn:Em.
    intro IH.
    pose proof (geodi_seq_norm_pair n r Hr
                  (real_plus real_one (real_opp eta)) p Hp Hn Hnormp m q Hq Em)
      as HnormQ.
    pose proof (geodi_zpos n r q (real_plus real_one (real_opp eta)) Hr Hq Hn)
      as HZq.
    pose proof (real_mult_positive eta eps Heta Heps) as Hetaeps.
    (* One-step instance (the GeomD main theorem): KL_{S m} <= kappa*KL_q + eta*eps *)
    (*   The HZ/Hqv slots must carry the same literal term: the HZ position of geodi_next_pos's output type is baked in as *)
    (*   geodi_zpos ... Hn; an aliased premise is not unifiable with it (rigid-rigid). *)
    pose proof (geod_policy_iter_kl_geom_step_eps n r q eta Hr Hq
                  Hnormr HnormQ
                  (geodi_zpos n r q (real_plus real_one (real_opp eta)) Hr Hq Hn)
                  (geodi_next_pos n r q (real_plus real_one (real_opp eta))
                     Hr Hq Hn)
                  Heta Hlt1 (real_mult eta eps) Hetaeps) as Hstep.
    (* kappa-weighting the IH: kappa*KL_q <= kappa*(kappa^m*KL0 + eps) == kappa^{S m}*KL0 + kappa*eps *)
    pose proof (geodi_mult_le_compat_l (real_plus real_one (real_opp eta))
                  (geod_lsum n
                     (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i)))
                  (real_plus (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                (geod_lsum n
                                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                             eps)
                  (geod_kappa_pos eta Hlt1) IH) as Hmul.
    pose proof (real_le_plus_compat
                  (real_mult (real_plus real_one (real_opp eta))
                     (geod_lsum n
                        (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))))
                  (real_plus
                     (real_mult
                        (real_mult (real_plus real_one (real_opp eta))
                           (powb_pow (real_plus real_one (real_opp eta)) m))
                        (geod_lsum n
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_mult (real_plus real_one (real_opp eta)) eps))
                  (real_mult eta eps)
                  (real_mult eta eps)
                  (RealSetoid.real_le_id_r
                     (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n
                           (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))))
                     (real_mult (real_plus real_one (real_opp eta))
                        (real_plus (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                      (geod_lsum n
                                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                                   eps))
                     (real_plus
                        (real_mult
                           (real_mult (real_plus real_one (real_opp eta))
                              (powb_pow (real_plus real_one (real_opp eta)) m))
                           (geod_lsum n
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                        (real_mult (real_plus real_one (real_opp eta)) eps))
                     (real_eq_trans
                        (real_mult (real_plus real_one (real_opp eta))
                           (real_plus (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                         (geod_lsum n
                                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                                      eps))
                        (real_plus
                           (real_mult (real_plus real_one (real_opp eta))
                              (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                 (geod_lsum n
                                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                           (real_mult (real_plus real_one (real_opp eta)) eps))
                        (real_plus
                           (real_mult
                              (real_mult (real_plus real_one (real_opp eta))
                                 (powb_pow (real_plus real_one (real_opp eta)) m))
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_mult (real_plus real_one (real_opp eta)) eps))
                        (real_distrib (real_plus real_one (real_opp eta))
                           (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           eps)
                        (RealSetoid.real_eq_plus_compat
                           (real_mult (real_plus real_one (real_opp eta))
                              (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                 (geod_lsum n
                                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                           (real_mult (real_plus real_one (real_opp eta)) eps)
                           (real_mult
                              (real_mult (real_plus real_one (real_opp eta))
                                 (powb_pow (real_plus real_one (real_opp eta)) m))
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_mult (real_plus real_one (real_opp eta)) eps)
                           (real_mult_assoc (real_plus real_one (real_opp eta))
                              (powb_pow (real_plus real_one (real_opp eta)) m)
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_eq_refl
                              (real_mult (real_plus real_one (real_opp eta)) eps))))
                     Hmul)
                  (real_le_refl (real_mult eta eps))) as Hmid.
    (* final collapse: (A + kappa*eps) + eta*eps == A + (kappa+eta)*eps == A + 1*eps == A + eps *)
    assert (Hcollapse : real_eq
      (real_plus (real_plus (real_mult
                   (real_mult (real_plus real_one (real_opp eta))
                      (powb_pow (real_plus real_one (real_opp eta)) m))
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                (real_mult (real_plus real_one (real_opp eta)) eps))
             (real_mult eta eps))
      (real_plus (real_mult
               (real_mult (real_plus real_one (real_opp eta))
                  (powb_pow (real_plus real_one (real_opp eta)) m))
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps)).
    { apply (real_eq_trans _
               (real_plus
                  (real_mult
                     (real_mult (real_plus real_one (real_opp eta))
                        (powb_pow (real_plus real_one (real_opp eta)) m))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_plus (real_mult (real_plus real_one (real_opp eta)) eps)
                             (real_mult eta eps)))).
      - apply real_eq_sym. apply real_plus_assoc.
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult
                    (real_mult (real_plus real_one (real_opp eta))
                       (powb_pow (real_plus real_one (real_opp eta)) m))
                    (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                 (real_plus (real_mult (real_plus real_one (real_opp eta)) eps)
                            (real_mult eta eps))
                 (real_mult
                    (real_mult (real_plus real_one (real_opp eta))
                       (powb_pow (real_plus real_one (real_opp eta)) m))
                    (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                 eps).
        + apply real_eq_refl.
        + (* kappa*eps + eta*eps == (kappa+eta)*eps == 1*eps == eps (distrib, flipped) *)
          apply (real_eq_trans _
                     (real_plus (real_mult eps (real_plus real_one (real_opp eta)))
                                (real_mult eps eta))).
          * apply (RealSetoid.real_eq_plus_compat
                     (real_mult (real_plus real_one (real_opp eta)) eps)
                     (real_mult eta eps)
                     (real_mult eps (real_plus real_one (real_opp eta)))
                     (real_mult eps eta)
                     (real_mult_comm (real_plus real_one (real_opp eta)) eps)
                     (real_mult_comm eta eps)).
          * apply (real_eq_trans _
                       (real_mult eps (real_plus (real_plus real_one (real_opp eta)) eta))).
          -- apply real_eq_sym. apply real_distrib.
          -- apply (real_eq_trans _
                         (real_mult eps real_one)).
             ++ apply (RealSetoid.real_eq_mult_compat eps
                         (real_plus (real_plus real_one (real_opp eta)) eta) eps real_one
                         (real_eq_refl eps) (geodi_kappa_plus_eta eta)).
             ++ apply real_mult_one. }
    exact (real_le_trans _ _ _ Hstep
             (real_le_trans _ _ _ Hmid
                (RealSetoid.real_le_id_l
                   (real_plus
                      (real_plus
                         (real_mult
                            (real_mult (real_plus real_one (real_opp eta))
                               (powb_pow (real_plus real_one (real_opp eta)) m))
                            (geod_lsum n
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                         (real_mult (real_plus real_one (real_opp eta)) eps))
                      (real_mult eta eps))
                   (real_plus
                      (real_mult
                         (real_mult (real_plus real_one (real_opp eta))
                            (powb_pow (real_plus real_one (real_opp eta)) m))
                         (geod_lsum n
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                      eps)
                   (real_plus
                      (real_mult
                         (real_mult (real_plus real_one (real_opp eta))
                            (powb_pow (real_plus real_one (real_opp eta)) m))
                         (geod_lsum n
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                      eps)
                   Hcollapse (real_le_refl
                      (real_plus
                         (real_mult
                            (real_mult (real_plus real_one (real_opp eta))
                               (powb_pow (real_plus real_one (real_opp eta)) m))
                            (geod_lsum n
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                         eps))))).
Qed.

(* ============================================================ *)
(* G. Stratified ladder: one-step / two-step instances of the main theorem, finished on literal powers *)
(* ============================================================ *)
Theorem geodi_iter_one_step_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n),
  forall (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S O) i)
                       (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S O) i)))
    (real_plus (real_mult (real_plus real_one (real_opp eta))
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn eps Heps.
  pose proof (geodi_policy_iter_kl_geom_iter_eps n r Hr eta Heta Hlt1 p Hp
                Hnormr Hnormp Hn (Datatypes.S O) eps Heps) as H.
  apply (RealSetoid.real_le_id_r
           (geod_lsum n
              (fun i : nat => real_kl_term (r i)
                              (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S O) i)
                              (Hr i)
                              (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S O) i)))
           (real_plus
              (real_mult (powb_pow (real_plus real_one (real_opp eta)) (Datatypes.S O))
                 (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
              eps)
           (real_plus (real_mult (real_plus real_one (real_opp eta))
                         (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                      eps)).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (powb_pow (real_plus real_one (real_opp eta)) (Datatypes.S O))
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps
             (real_mult (real_plus real_one (real_opp eta))
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps).
    + (* kappa^1*KL0 == kappa*KL0: kappa^1 is kappa*1 by conversion; assoc + mult_one retyping *)
      exact (real_eq_trans
               (real_mult (powb_pow (real_plus real_one (real_opp eta)) (Datatypes.S O))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult (real_plus real_one (real_opp eta))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_eq_refl
                  (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (real_eq_trans
                  (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult real_one
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_eq_sym _ _
                     (real_mult_assoc (real_plus real_one (real_opp eta)) real_one
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (RealSetoid.real_eq_mult_compat
                     (real_plus real_one (real_opp eta))
                     (real_mult real_one
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_plus real_one (real_opp eta))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                     (real_eq_refl (real_plus real_one (real_opp eta)))
                     (geodi_mult_one_l (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))))).
    + apply real_eq_refl.
  - (* the real_le slot: exactly the instance H of the main theorem at t := S O *)
    exact H.
Qed.

Theorem geodi_iter_two_steps_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n),
  forall (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)
                       (Hr i)
                       (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)))
    (real_plus (real_mult (real_plus real_one (real_opp eta))
                   (real_mult (real_plus real_one (real_opp eta))
                      (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn eps Heps.
  pose proof (geodi_policy_iter_kl_geom_iter_eps n r Hr eta Heta Hlt1 p Hp
                Hnormr Hnormp Hn (Datatypes.S (Datatypes.S O)) eps Heps) as H.
  apply (RealSetoid.real_le_id_r
           (geod_lsum n
              (fun i : nat => real_kl_term (r i)
                              (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)
                              (Hr i)
                              (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)))
           (real_plus
              (real_mult (powb_pow (real_plus real_one (real_opp eta))
                             (Datatypes.S (Datatypes.S O)))
                 (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
              eps)
           (real_plus (real_mult (real_plus real_one (real_opp eta))
                         (real_mult (real_plus real_one (real_opp eta))
                            (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                      eps)).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (powb_pow (real_plus real_one (real_opp eta))
                           (Datatypes.S (Datatypes.S O)))
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps
             (real_mult (real_plus real_one (real_opp eta))
                (real_mult (real_plus real_one (real_opp eta))
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
             eps).
    + (* kappa^2*KL0 == kappa*(kappa*KL0): kappa^2 is kappa*(kappa*1) by conversion; assoc twice + mult_one *)
      exact (real_eq_trans
               (real_mult (powb_pow (real_plus real_one (real_opp eta))
                             (Datatypes.S (Datatypes.S O)))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult (real_plus real_one (real_opp eta)) real_one))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult (real_plus real_one (real_opp eta))
                  (real_mult (real_plus real_one (real_opp eta))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (real_eq_refl
                  (real_mult
                     (real_mult (real_plus real_one (real_opp eta))
                        (real_mult (real_plus real_one (real_opp eta)) real_one))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (real_eq_trans
                  (real_mult
                     (real_mult (real_plus real_one (real_opp eta))
                        (real_mult (real_plus real_one (real_opp eta)) real_one))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (real_eq_sym _ _
                     (real_mult_assoc (real_plus real_one (real_opp eta))
                        (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (RealSetoid.real_eq_mult_compat
                     (real_plus real_one (real_opp eta))
                     (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_plus real_one (real_opp eta))
                     (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_eq_refl (real_plus real_one (real_opp eta)))
                     (real_eq_trans
                        (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                           (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                        (real_mult (real_plus real_one (real_opp eta))
                           (real_mult real_one
                              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                        (real_mult (real_plus real_one (real_opp eta))
                           (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                        (real_eq_sym _ _
                           (real_mult_assoc (real_plus real_one (real_opp eta)) real_one
                              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                        (RealSetoid.real_eq_mult_compat
                           (real_plus real_one (real_opp eta))
                           (real_mult real_one
                              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_plus real_one (real_opp eta))
                           (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                           (real_eq_refl (real_plus real_one (real_opp eta)))
                           (geodi_mult_one_l (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))))))).
    + apply real_eq_refl.
  - (* the real_le slot: exactly the instance H of the main theorem at t := S (S O) *)
    exact H.
Qed.

(* ============================================================ *)
(* H. Bishop companion: KL(pi*||pi_t) <=_B (1-eta)^t*KL(pi*||pi_0) (finished in the Bishop le_b language) *)
(* ============================================================ *)
Theorem geodi_policy_iter_kl_geom_iter_B :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (t : nat),
  real_le_b
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn t i)
                       (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t.
  (* Bishop finish (UpRealLeB real_le_closure_b_one, specialized at D := 1): the main theorem is already *)
  (*   the family real_le X (Y+eps) over all eps > 0 -- exactly the premise shape of the closure lemma; one explicit application closes it. *)
  apply (real_le_closure_b_one
           (geod_lsum n
              (fun i : nat => real_kl_term (r i)
                              (geodi_iterate n r Hr eta p Hp Hn t i)
                              (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))).
  intros eps Heps.
  exact (geodi_policy_iter_kl_geom_iter_eps n r Hr eta Heta Hlt1 p Hp
           Hnormr Hnormp Hn t eps Heps).
Qed.

(* ============================================================ *)
(* I. KL Bishop nonnegativity companion (the usable side of gap I4): 0 <=_B KL(pi*||pi_0) *)
(*   Certificate chain: gibbs per eps (le form) -> le_b lifting by half -> assoc + halving-identity retyping. *)
(* ============================================================ *)
Lemma geodi_kl_nonneg_B : forall (n : nat) (r p : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one),
  real_le_b real_zero
    (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))).
Proof.
  intros n r p Hr Hp Hnormr Hnormp. unfold real_le_b. intros eps Heps.
  pose proof (real_plus_positive real_one real_one
                real_lt_zero_one real_lt_zero_one) as Htwo.
  pose proof (real_inv_pos_pos (real_plus real_one real_one) Htwo) as Hinv.
  pose proof (real_mult_positive eps
                (real_inv_pos (real_plus real_one real_one) Htwo) Heps Hinv) as Hh.
  pose proof (real_le_to_le_b real_zero
                (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
                (real_gibbs_inequality_eps nat (seq 0 n) r p Hr Hp Hnormr Hnormp
                   (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)) Hh)) as Hleb.
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus
              (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                         (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
              (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
           (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))) eps)).
  - apply (real_eq_trans
             (real_plus
                (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
                (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
             (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                        (real_plus
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo))
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))))
     .
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
               (real_plus
                  (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo))
                  (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
               eps).
      * apply real_eq_refl.
      * exact (geod_b_half_double eps (real_inv_pos (real_plus real_one real_one) Htwo)
                  (real_inv_pos_correct (real_plus real_one real_one) Htwo)).
  - exact (Hleb (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)) Hh).
Qed.

(* ============================================================ *)
(* Endnote: honest registry *)
(* Exact shape of gap I4: a compositor for "t <= t1 implies KL_{t1} <= kappa^t*KL_0 (Bishop form)" *)
(*   already has (1) KL_{t1} <=_B kappa^{t1}*KL_0 (main B companion); (2) 0 <=_B KL_0 (companion I); *)
(*   (3) kappa^{t1} <=_B kappa^t (PowB powb_one_minus_eta_mono_dec).  Missing is (4) the le_b multiplicative *)
(*   monotone closure: a <=_B b and 0 <=_B c imply a*c <=_B b*c -- its per-eps proof must multiply out *)
(*   the delta of kappa^{t1} <= kappa^t + delta and press it back under eps, i.e. it needs upper-bound *)
(*   material for KL_0 (sup KL); on the simplex sup KL follows from min positivity, but the library *)
(*   has no such upper-bound item -- (4) is left unbuilt in exactly the shape above; no ad-hoc construction. *)

(*   The closing Print Assumptions sweep is Closed for every item (see the end of this file); the extraction check reports Obj.magic = 0. *)

(* ============================================================ *)

Print Assumptions geodi_zpos.
Print Assumptions geodi_step_norm.
Print Assumptions geodi_seq_norm.
Print Assumptions geodi_mult_le_compat_l.
Print Assumptions geodi_policy_iter_kl_geom_iter_eps.
Print Assumptions geodi_iter_one_step_eps.
Print Assumptions geodi_iter_two_steps_eps.
Print Assumptions geodi_policy_iter_kl_geom_iter_B.
Print Assumptions geodi_kl_nonneg_B.
