(* ConstructiveWorld-Set — Realization package for interface premise slots of the G02/UpFirewall/UpGRPO/G04/UpDPOLip families. *)
(** * fa57_ext: realizations for interface premise slots over the fa5x carrier supplies.

    Mission.  Realizes interface premise statements as named [Set]-carried terms:
      [fa57_sum_carrier_realizes] (G02_Debt L165-175 abstract-carrier package via the
      list fold [fa51_sumd]) and [fa57_sumd_mult_const_r]; [fa57_lt_minus_nonneg] and
      [fa57_minus_lt_strict] (the UpFirewall L104 slot, both directions);
      [fa57_nat_to_R_pos] and [fa57_grpo_G_pos] (UpGRPO L66 positivity chain);
      [fa57_two_pos], [fa57_half_pos], [fa57_half_plus_half] and the two-point uniform
      package [fa57_W2p_uniform_two_realized] (G04_ProjFam W2'); [fa57_dpolip_Z_realizer] (UpDPOLip Z_align slots).

    Dependencies.  Stdlib [Lists.List] (with [ListNotations]); requires [S01_BaseRing]
      (the [RealInterfaceEnhanced] interface), [fa51_sumpos_id], [fa53_compat_abs],
      [fa56_id_carrier], [fa56b_ext] of this development.  No other file is modified;
      the [fa57_] names are new to this development.

    References.  The realized statements follow the slot faces of [G02_Debt.v]
      (L165-175), [UpFirewall.v] (L104), [UpGRPO.v] (L66; the locally redeclared
      carrier is isomorphic to L51-65), [G04_ProjFam.v] (L175-181/394-400), and
      [UpDPOLip] (L372-373); the supplies [fa51_sumd], [fa51_sumd_nonnil_pos],
      [fa56b_sumd_cong], [fa56_sumd_mult_const], [fa53_lt_plus_translate_r], and
      [fa51_Z_align]/[fa51_Z_align_pos] are consumed unchanged.

    Constructivity.  Nothing admitted; the statement face is entirely [Set]-layer
      ([Id]/[lt]/[le]/[Or]/[And]/[sigT], [And] the S01 L66 product); proofs close by
      direct [exact] reference to the supplies and short identity chains; the closing
      [Print Assumptions] block is expected [Closed] throughout.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" fa57_ext.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]. *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa53_compat_abs.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa57Ext.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
(* Usage position of the fa53 family: the one-sided strict translation family needs
   the decidable-order extension (precedent [AbsLeId.v]: feed [DO] with all arguments
   explicit via [@]); after discharge, [DO] enters only the signatures of the two
   cluster-2 lemmas — the honest discharged form of the UpFirewall L104 and
   UpEntropyGain L86 slots. *)
Context {DO : DecidableOrder RI}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

(* ==================== Cluster 1: one-shot realization package for the G02 L165-175 carrier slots ==================== *)
(* The slot statements (the abstract-carrier-parameterized section at G02_Debt.v
   L169/172/174): pos_preserved — pointwise positive implies positive sum; ext —
   pointwise equal implies equal sums; linear — the sum of (a·f) equals a·(sum f).
   This package supplies the sigT witness: a list fold ([fa51_sumd]). *)

Theorem fa57_sum_carrier_realizes :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    sigT (fun sumf : (X -> R) -> R =>
            And (forall f : X -> R,
                   (forall x : X, lt zero (f x)) -> lt zero (sumf f))
                (And (forall f g : X -> R,
                        (forall x : X, Id (f x) (g x)) -> Id (sumf f) (sumf g))
                     (forall (a : R) (f : X -> R),
                        Id (sumf (fun x => mult a (f x)))
                           (mult a (sumf f))))).
Proof.
  intros X enum Hne.
  exact (existT _                (fun f => fa51_sumd X f enum)                ((fun f Hf => fa51_sumd_nonnil_pos X f enum Hne Hf),                 ((fun f g Hpt => fa56b_sumd_cong X f g enum Hpt),                  (fun a f => fa56_sumd_mult_const X a f enum)))).
Qed.

(* ---- Right-factor linearity (the [fun x => mult (f x) a] variant of G02 L174):
        a three-step Id chain — swap ([fa56b]) × const ([fa56]) × comm. ---- *)
Lemma fa57_sumd_mult_const_r :
  forall (X : Set) (a : R) (f : X -> R) (l : list X),
    Id (fa51_sumd X (fun x => mult (f x) a) l)
       (mult (fa51_sumd X f l) a).
Proof.
  intros X a f l.
  exact (id_trans (fa56b_sumd_cong X (fun x => mult (f x) a)                                    (fun x => mult a (f x)) l                                    (fun x => mult_comm (f x) a))                  (id_trans (fa56_sumd_mult_const X a f l)                            (mult_comm a (fa51_sumd X f l)))).
Qed.

(* ==================== Cluster 2: the UpFirewall L104 lt_minus_nonneg slot ==================== *)
(* The slot statement: lt a b implies lt zero (minus b a) (minus is definitionally
   plus with opp).  Forward direction: put a + (opp a) == zero in place, then the
   fa53 one-sided strict translation. *)

Lemma fa57_lt_minus_nonneg :
  forall a b : R, lt a b -> lt zero (minus b a).
Proof.
  intros a b Hab.
  exact (lt_id_l zero (plus a (opp a)) (plus b (opp a))           (id_sym (plus_opp a))           (@fa53_lt_plus_translate_r RI DO a b (opp a) Hab)).
Qed.

(* Reverse direction (the strict counterpart of G01 L685 [le_of_minus_nonneg]):
   translate back from zero via the assoc/opp/zero identity channels. *)
Lemma fa57_minus_lt_strict :
  forall a b : R, lt zero (minus b a) -> lt a b.
Proof.
  intros a b H.
  apply (lt_id_l a (plus zero a) b
           (id_trans (id_sym (plus_zero a)) (id_sym (plus_comm zero a)))).
  apply (lt_id_r (plus zero a) (plus (plus b (opp a)) a) b).
  - exact (id_trans (id_sym (plus_assoc b (opp a) a))
                    (id_trans (id_cong (fun w => plus b w)
                                       (id_trans (plus_comm (opp a) a)
                                                 (plus_opp a)))
                              (plus_zero b))).
  - exact (@fa53_lt_plus_translate_r RI DO zero (plus b (opp a)) a H).
Qed.

(* ==================== Cluster 3: the UpGRPO L66 G_pos realization chain ==================== *)
(* The slot: G := nat_to_R_g (length group_enum) with G_pos : lt zero G originally a
   section Variable.  Realization: the cover (a universal InT witness) at any point
   g0 forces the enumeration nonempty (the nil branch is killed by the zero
   constructors of InT), length is definitionally S k, and the positivity induction
   lemma applies.  The carrier is redeclared locally because section parameters are
   not exported; UpGRPO.v L51-65 is isomorphic — recursion at the S position by
   plus one, induction via plus_positive/one_pos. *)

Fixpoint fa57_nat_to_R (k : nat) : R :=
  match k with
  | O => zero
  | Datatypes.S m => plus one (fa57_nat_to_R m)
  end.

Lemma fa57_nat_to_R_pos :
  forall k : nat, lt zero (fa57_nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - exact (lt_id_r zero one (plus one zero) (id_sym (plus_zero one)) one_pos).
  - exact (plus_positive one (fa57_nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

Theorem fa57_grpo_G_pos :
  forall (Group : Set) (group_enum : list Group),
    (forall i : Group, InT i group_enum) ->
    forall g0 : Group,
      lt zero (fa57_nat_to_R (Datatypes.length group_enum)).
Proof.
  intros Group group_enum cover g0.
  (* induction on the InT derivation itself: both constructors are cons-shaped, so
     the nil branch never enters the proof term (the same method as G04
     [projp_single_le_sum]; this avoids the empty match that extraction would wrap
     in a magic cast). *)
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
Qed.

(* ==================== Cluster 4: the G04 W2' two-point uniform projection family ==================== *)
(* All faces of the G04_ProjFam.v L175-181/394-400 slots (I/f/idx/f_norm/f_pos/
   P_witness) are realized by the two-point uniform instance: I := bool,
   idx := [true; false], f ≡ half, P ≡ true.  The half normalization chain:
   half+half == half·1+half·1 == half·two == one (a four-step chain through
   distrib, mult_one, mult_comm, inv_pos_correct). *)

Definition fa57_two : R := plus one one.

Lemma fa57_two_pos : lt zero fa57_two.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

Definition fa57_half : R := inv_pos fa57_two fa57_two_pos.

Lemma fa57_half_pos : lt zero fa57_half.
Proof.
  exact (inv_pos_pos fa57_two fa57_two_pos).
Qed.

Lemma fa57_half_plus_half : Id (plus fa57_half fa57_half) one.
Proof.
  exact (id_trans (id_cong2 plus (id_sym (mult_one fa57_half))                                (id_sym (mult_one fa57_half)))                  (id_trans (id_sym (distrib fa57_half one one))                            (id_trans (mult_comm fa57_half fa57_two)                                      (inv_pos_correct fa57_two fa57_two_pos)))).
Qed.

(* ---- The W2' seven-slot realization package (the norm/pos/witness slots; the structural slots are discharged by the type face itself) ---- *)
Theorem fa57_W2p_uniform_two_realized :
  And (Id (fa51_sumd bool (fun _ : bool => fa57_half) [true; false]) one)
      (And (forall i : bool, lt zero ((fun _ : bool => fa57_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  split.
  - exact (id_trans (id_cong (fun w : R => plus fa57_half w)
                             (plus_zero fa57_half))
                    fa57_half_plus_half).
  - split.
    + exact (fun _ => fa57_half_pos).
    + exact (existT (fun i : bool =>
                       And (Id ((fun _ : bool => true) i) true)
                           (InT i [true; false]))
                    true (id_refl, @InT_here bool true [false])).
Qed.

(* ==================== Cluster 5: loading the UpDPOLip L372-373 Z_align slots ==================== *)
(* The slots: Z_align : Real (bare) and Z_align_pos : lt zero Z_align (carrying its
   own positivity).  Loading: the [fa51_Z_align] realizer feeds both slots at once;
   instantiating with this realizer inside the UpDPOLip section discharges both. *)

Definition fa57_dpolip_Z_realizer :
  forall (X : Set) (enum : list X) (reward : X -> R) (beta : R)
         (beta_pos : lt zero beta) (pi_ref : X -> R),
    (forall s : X, lt zero (pi_ref s)) ->
    Not (Id enum nil) ->
    sigT (fun Z : R => And (Id Z (fa51_Z_align X enum reward beta beta_pos pi_ref))
                           (lt zero Z)).
Proof.
  intros X enum reward beta beta_pos pi_ref Href Hne.
  exact (existT _
                (fa51_Z_align X enum reward beta beta_pos pi_ref)
                (id_refl,
                 fa51_Z_align_pos X enum reward beta beta_pos pi_ref Href Hne)).
Qed.

End Fa57Ext.

(* ============ Assumption-face closure audit ============ *)

Print Assumptions fa57_sum_carrier_realizes.
Print Assumptions fa57_sumd_mult_const_r.
Print Assumptions fa57_lt_minus_nonneg.
Print Assumptions fa57_minus_lt_strict.
Print Assumptions fa57_grpo_G_pos.
Print Assumptions fa57_W2p_uniform_two_realized.
Print Assumptions fa57_dpolip_Z_realizer.
