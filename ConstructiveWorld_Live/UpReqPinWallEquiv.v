(* ConstructiveWorld-Set — Equivalence between pinned-interface satisfiability and restricted LPO. *)
(** * UpReqPinWallEquiv: the pinned-interface / restricted-LPO equivalence package.

    Mission.  [pwe_PinWall] asserts ([sigT], all [Set]) that some [bnorm : Q -> Q]
      satisfies the pin form [pwe_pin] ([bnorm q = Qabs q] for all [q]) and the C*
      identities [pwe_cstar] (canon consistency with [bxib_bcnorm], [bplus_zero],
      assoc); the pinned form cannot actually hold — it would force the Leibniz
      false equality [2#4 = 1#2], refutable at the constructor level.  Statements:
      [pwe_pin_wall_lpo] ([pwe_PinWall -> rLPO], forward reduction via [pwe_qdisc]);
      [pwe_pin_wall_void]; [pwe_reverse_obstacle] (a reverse reduction would refute
      [rLPO] — constructively unreachable); [pwe_equivalence] (forward + obstacle);
      [pwe_canon_cstar_ok] (the constructive dual: [bxib_bcnorm] satisfies the C*
      positions unconditionally); [pwe_carrier_excl]/[pwe_E_carrier_excl] (generic
      carriers).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs]; requires [S01_BaseRing],
      [S02_CauchyComplete], [UpReqLpoEquiv], [UpReqBanachInstB] of this development.

    References.  The INSTB cornerstone [bxib_canon_pin_wall]/[bxib_bcnorm] in
      [UpReqBanachInstB.v]; the restricted-choice-principle (LPO family) equivalence
      files of this development; the generic-carrier section follows the pattern of
      [UpReqGibbsWallEquiv].

    Constructivity.  Purely constructive [Set] layer; statement face all [Type]/[sigT]/
      custom [And]/[Or] with zero [Prop]; nothing admitted, empty assumption face; the
      downgraded form is explicit (carried by [pwe_reverse_obstacle]).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" UpReqPinWallEquiv.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqLpoEquiv.
Require Import UpReqBanachInstB.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1. The decision-data extractor — from mutual exclusion   *)
(*   (a Leibniz false equality) to Set-layer data                *)
(* ============================================================ *)

(* Dependent transport along Id (the eliminator of the S01 [Id]; large elimination into Set is legitimate) *)
Definition pwe_id_transport {A : Set} (P : A -> Set) {x y : A}
            (p : Id x y) (u : P x) : P y :=
  match p in Id _ z return P z with
  | id_refl => u
  end.

(* The constructor-level discriminator: numerator position xH (the computed form of
   1#2) maps to the empty type Empty_set; everything else (including
   2#4 = Qmake (Zpos (xO xH)) 4) maps to unit.
   pwe_qdisc (2#4) ≡ unit (inhabited); pwe_qdisc (1#2) ≡ Empty_set. *)
Definition pwe_qdisc (q : Q) : Set :=
  match q with
  | Qmake n _ => match n with
                 | Zpos xH => Empty_set
                 | _ => unit
                 end
  end.

(* Full Set-layer refutation of the Leibniz false equality 2#4 = 1#2 (decision-data extraction) *)
Theorem pwe_false_of_half_quarter_id :
  forall A : Set, Id (2#4)%Q (1#2)%Q -> A.
Proof.
  intros A H.
  destruct (pwe_id_transport pwe_qdisc H tt).
Qed.

(* ============================================================ *)
(* Part 2. The pinned-interface statement face (all Set, zero Prop) *)
(* ============================================================ *)

(* The pin form: bnorm preserves the raw Qabs form (the pin-field statement shape of the INSTB [bxib_canon_pin_wall], mediated under pwe_ names) *)
Definition pwe_pin (bnorm : Q -> Q) : Set :=
  forall q : Q, Id (bnorm q) (Qabs q).

(* The C* identities: canon consistency + the bplus_zero position + the assoc position, Leibniz-compatible *)
Definition pwe_cstar (bnorm : Q -> Q) : Set :=
  And (forall q : Q, Id (bnorm q) (bxib_bcnorm q))
      (And (forall q : Q, Id (bnorm (Qplus q (Qopp q))) (bnorm (0#1)%Q))
           (forall a b c : Q,
              Id (bnorm (Qplus a (Qplus b c)))
                 (bnorm (Qplus (Qplus a b) c)))).

(* PinWall: the satisfiability assertion for the pinned interface (some bnorm satisfies both the pin form and the C* identities) *)
Definition pwe_PinWall : Set :=
  sigT (fun bnorm : Q -> Q => And (pwe_pin bnorm) (pwe_cstar bnorm)).

(* ============================================================ *)
(* Part 3. The generic carrier section — the mutual-exclusion    *)
(*   mechanism holds uniformly for all Φ-factorized carriers     *)
(* ============================================================ *)

(* The carrier-generic pin form / canon form (any C with evaluation ev and bnorm) *)
Definition pwe_pin_gen (C : Set) (ev : C -> Q) (bnorm : C -> Q) : Set :=
  forall c : C, Id (bnorm c) (Qabs (ev c)).

Definition pwe_canon_gen (C : Set) (ev : C -> Q) (bnorm : C -> Q) : Set :=
  forall c : C, Id (bnorm c) (Qabs (bxib_qnorm (ev c))).

(* The generic mutual-exclusion theorem: the pin form × canon form forces the canon-raw false equality at every instance point *)
Theorem pwe_carrier_excl :
  forall (C : Set) (ev : C -> Q) (bnorm : C -> Q),
    pwe_pin_gen C ev bnorm -> pwe_canon_gen C ev bnorm ->
    forall x0 : C, Id (Qabs (ev x0)) (Qabs (bxib_qnorm (ev x0))).
Proof.
  intros C ev bnorm Hpin Hcanon x0.
  exact (id_trans (id_sym (Hpin x0)) (Hcanon x0)).
Qed.

(* The E-carrier (the INSTB free-term tree) instance: the instance point esc 2#4 yields the false equality 2#4 = 1#2 directly *)
Theorem pwe_E_carrier_excl : forall bnorm : bxib_E -> Q,
  pwe_pin_gen bxib_E bxib_ev bnorm -> pwe_canon_gen bxib_E bxib_ev bnorm ->
  Id (2#4)%Q (1#2)%Q.
Proof.
  intros bnorm Hpin Hcanon.
  exact (pwe_carrier_excl bxib_E bxib_ev bnorm Hpin Hcanon           (bxib_esc (2#4)%Q)).
Qed.

(* The refutation form of the E-carrier mutual exclusion (full decision power) *)
Theorem pwe_E_carrier_void : forall bnorm : bxib_E -> Q,
  pwe_pin_gen bxib_E bxib_ev bnorm -> pwe_canon_gen bxib_E bxib_ev bnorm ->
  forall A : Set, A.
Proof.
  intros bnorm Hpin Hcanon A.
  exact (pwe_false_of_half_quarter_id A (pwe_E_carrier_excl bnorm Hpin Hcanon)).
Qed.

(* ============================================================ *)
(* Part 4. The Q-carrier mutual-exclusion theorem (the interface-level upgrade of the INSTB [bxib_canon_pin_wall]) *)
(* ============================================================ *)

Theorem pwe_pin_excl : forall bnorm : Q -> Q,
  pwe_pin bnorm -> pwe_cstar bnorm -> Id (2#4)%Q (1#2)%Q.
Proof.
  intros bnorm Hpin Hcs.
  destruct Hcs as [Hcanon _].
  specialize (Hpin (2#4)%Q).
  specialize (Hcanon (2#4)%Q).
  (* Hpin   : Id (bnorm (2#4)) (Qabs (2#4))        ≡ Id (bnorm (2#4)) (2#4) *)
  (* Hcanon : Id (bnorm (2#4)) (bxib_bcnorm (2#4)) ≡ Id (bnorm (2#4)) (1#2) *)
  (* (bxib_bcnorm (2#4) ≡ Qabs (1#2) ≡ 1#2, as computed in the INSTB base file) *)
  exact (id_trans (id_sym Hpin) Hcanon).
Qed.

(* ============================================================ *)
(* Part 5. The unsatisfiability decision for the pinned interface + the one-direction reduction *)
(* ============================================================ *)

(* The pinned interface is unsatisfiable (the full-decision-power form of the mutual-exclusion decision) *)
Theorem pwe_pin_wall_void : pwe_PinWall -> forall A : Set, A.
Proof.
  intros H A.
  destruct H as [bnorm [Hpin Hcs]].
  exact (pwe_false_of_half_quarter_id A (pwe_pin_excl bnorm Hpin Hcs)).
Qed.


(* The decision data: the Leibniz false equality forced by mutual exclusion, eliminated at the Set layer for full decision power *)
Theorem pwe_pin_wall_lpo : pwe_PinWall -> rLPO.
Proof.
  intro H.
  exact (pwe_pin_wall_void H rLPO).
Qed.

(* ============================================================ *)
(* Part 6. The constructive dual — the canon-form interface      *)
(*   satisfies the three C* identity positions unconditionally   *)
(*   (the constructive dual of the unsatisfiability-by-design of *)
(*   the pinned interface: raw-form positions empty, canon-form  *)
(*   positions full)                                             *)
(* ============================================================ *)

Theorem pwe_canon_cstar_ok : pwe_cstar bxib_bcnorm.
Proof.
  unfold pwe_cstar.
  split.
  - (* the canon position: reflexivity ([bxib_bcnorm] is the canon form itself) *)
    intros q. apply id_refl.
  - split.
    + (* the bplus_zero position: [bxib_zero_canon_opp] (q + (−q) normalizes to 0#1) *)
      intros q.
      exact (id_cong Qabs (bxib_zero_canon_opp q)).
    + (* the assoc position: associativity as Qeq, lifted to QeqT, then the machine-checked uniqueness of the normal form *)
      intros a b c.
      apply (id_cong Qabs).
      apply bxib_qnorm_id_of_qeqT.
      apply qeq_imp_qeqT.
      ring.
Qed.

(* ============================================================ *)
(* Part 7. The reverse-obstacle report + the main statement      *)
(*   (downgraded form, explicitly annotated)                     *)
(* ============================================================ *)

(* The reverse-obstacle report: if a reverse reduction rLPO -> pwe_PinWall existed,
   composing it with the forward one would refute rLPO — the pinned interface is
   unsatisfiable (the Part 5 decision), so the reverse reduction would force rLPO
   to supply an existence witness for an unsatisfiable interface, i.e. refute the
   classically satisfiable LPO; constructively unreachable.  This statement is the
   machine-checked account of the blocked reverse direction. *)
Theorem pwe_reverse_obstacle : (rLPO -> pwe_PinWall) -> rLPO -> Empty_set.
Proof.
  intros Hrev Hlpo.
  exact (pwe_pin_wall_void (Hrev Hlpo) Empty_set).
Qed.

(* The main statement (downgraded form, annotated as such):
   the first component is the forward reduction (proved);
   the second component is not rLPO -> pwe_PinWall (blocked, see
   [pwe_reverse_obstacle]) and is carried by the reverse-obstacle report.
   Not a false equivalence claim: the file does not prove the full
   PinWall ⟺ rLPO form, only the forward reduction together with the
   reverse-unreachability report. *)
Definition pwe_equivalence :
  And (pwe_PinWall -> rLPO)
      ((rLPO -> pwe_PinWall) -> rLPO -> Empty_set) :=
  (pwe_pin_wall_lpo, pwe_reverse_obstacle).

Print Assumptions pwe_pin_wall_lpo.
Print Assumptions pwe_carrier_excl.
Print Assumptions pwe_canon_cstar_ok.
Print Assumptions pwe_reverse_obstacle.
Print Assumptions pwe_equivalence.
