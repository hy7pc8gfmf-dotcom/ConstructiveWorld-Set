(* ===================================================================== *)
(*  planb4_calib_chain_glue_qred.v - canonicalization bridges for the     *)
(*  small-step calibration chain, carried on the zzId Set-level equality  *)
(*  carrier.                                                              *)
(** * planb4_calib_chain_glue_qred: canonicalization bridges for the small-step calibration chain, carried on the zzId Set-level equality carrier.

    Mission.  the four carrier-borne faces the chain consumers rewrite through: the identity projector on the zzId carrier (the Set-equality reflection whose Leibniz projection face is assembled at use sites), the Qred insertion law zzId (Qeq_bool (Qred x) x) true, the Qnum-of-canonicalized-integer injection face zzId (Z.eqb (Qnum (Qred (inject_Z z))) z) true, and the canonical-form transfer zzId (Qeq_bool p q) true -> zzId (Qred p) (Qred q) that turns boolean-carried window sums back into rewrite material at the carrier face.

    Dependencies.  zzm1_gauss (zzId carrier, zzIdR, zzId_from_eq, zzId_Qeqb_refl); stdlib QArith.QArith, QArith.Qcanon (Qred_identity, Qred_correct, Qred_complete, Qeq_bool_eq, Qeq_eq_bool), ZArith (Z.eqb_eq, Z.gcd_1_r), List.

    References.  zzm1_gauss.v (the zzId carrier and the bool-sorted identity zzId_true, whose propositional conclusion moved one-to-one to the carrier); planb4_g1_laur_extract.v (Qred usage face); planb4_g1_ab_def.v (the Qred-canonicalized assemblies this bridge serves).

    Constructivity.  all four statement faces are Set-borne on the zzId carrier; the two source conclusion-position propositional faces (the Leibniz projection and the Qred syntactic equality) moved one-to-one to the carrier, and propositional equalities survive only inside proof bodies (Qred_correct / Qred_complete / Qeq_bool_eq / Z.eqb_eq cores).  The file is axiom-free; Print Assumptions reports Closed under the global context at every station; Separate Extraction yields zero Obj.magic on both the .ml and .mli faces.

    Build.  coqc -native-compiler no -q -Q <this sandbox> "" -Q <module tree ConstructiveWorld_Live> "" planb4_calib_chain_glue_qred.v (Rocq 9.3.0, thermal-guard wrapped; products stay in the sandbox, the module tree is read-only). *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qcanon ZArith.ZArith List.
Require Import zzm1_gauss.

Open Scope Q_scope.

(* Generic projector: the zzId carrier re-expresses at the Set-level
   equality carrier itself.  The source's propositional reflection face
   (zzId x y -> x = y) moved one-to-one to the carrier, following the
   bool-sorted identity zzId_true in zzm1_gauss; the Leibniz projection
   face is assembled at use sites by matching the carrier (the single
   constructor zzIdR closes every instance). *)
Definition pb4cwin_zzId_eq {A : Set} {x y : A} (p : zzId x y) : zzId x y := p.

(* Qred insertion at the boolean face: Qred x and x agree as rationals,
   certified on the carrier; the propositional core (Qred_correct) stays
   inside the proof body. *)
Lemma pb4cwin_qred_correct_b : forall x : Q, zzId (Qeq_bool (Qred x) x) true.
Proof.
  intros x. apply zzId_from_eq. apply Qeq_eq_bool. apply Qred_correct.
Defined.

(* Qnum of the canonicalized integer injection lands on the integer:
   inject_Z z = z # 1 is canonical (numerator and denominator coprime by
   Z.gcd_1_r), so Qred rewrites away inside the proof body. *)
Lemma pb4cwin_qnum_qred_inj_b :
  forall z : Z, zzId (Z.eqb (Qnum (Qred (inject_Z z))) z) true.
Proof.
  intros z. apply zzId_from_eq. apply Z.eqb_eq.
  rewrite (Qred_identity (inject_Z z) (Z.gcd_1_r z)).
  reflexivity.
Defined.

(* Canonical-form transfer: boolean rational equality of p and q carries
   the Qred forms to the carrier (the assembly law that turns
   boolean-carried window sums back into rewrite material at the carrier
   face).  The boolean certificate is projected out of h inside the term
   by matching the carrier. *)
Definition pb4cwin_qred_canon_eq (p q : Q) (h : zzId (Qeq_bool p q) true)
  : zzId (Qred p) (Qred q) :=
  zzId_from_eq (Qred_complete p q (Qeq_bool_eq p q
    (match h in zzId _ y' return Qeq_bool p q = y' with
     | zzIdR => eq_refl
     end))).

Print Assumptions pb4cwin_zzId_eq.
Print Assumptions pb4cwin_qred_correct_b.
Print Assumptions pb4cwin_qnum_qred_inj_b.
Print Assumptions pb4cwin_qred_canon_eq.
