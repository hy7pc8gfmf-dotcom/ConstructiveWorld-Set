(* ConstructiveWorld-Set -- DTPT evidence-enum supply: five instance-domain
   realizations of DTPT_Truth statement-premise slots. *)

(** * abl_dtpt_yellow_supply: one supply theorem per premise slot.

    Mission.  Five supply theorems ([tdy_]-prefixed), each realizing a
      [DTPT_Truth] statement premise on a decidable instance domain
      (direct-supply form: derivations consume only exported content):
      [tdy_qlist_Qeq_complete_h1] (a [Forall2 Qeq] certificate over
      single-point lists), [tdy_ev_cong_eqb_complete_h1] (an [ev_cong]
      certificate at the diagonal [evNum 0%Q]), and the three
      enumeration-membership instances [tdy_ev_enum_size_bound_h1],
      [tdy_ev_enum_pair_member_h1], [tdy_ev_enum_pair_member_h2].
      Three [Check] demonstrations feed them into the host
      completeness faces.

    Dependencies.  Stdlib [QArith.QArith], [List], [Bool], [Arith];
      requires [DTPT], [DTPT_Truth].

    References.  ConstructiveWorld-Main, module
      [abl_dtpt_yellow_supply] (statement names carried over verbatim).

    Constructivity.  Whole file [Qed]-closed, no admits, no axioms,
      no section variables; purely Set-level carriers, all inherited
      from the host (no new data carriers); statement faces carry no
      negation, disjunction, existential, or classical logic; nat
      literals as [Datatypes.S]/[O]/[Nat.sub], Q literals as [0%Q].

    Build.  [coqc -native-compiler no -q -Q . ""
      abl_dtpt_yellow_supply.v] compiles cleanly (exit 0). *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_Truth.
Import DTPT_Truth.DTPT_Truth.

(* Slot for [qlist_Qeq_complete] (premise 1, [Forall2 Qeq l1 l2]):  *)
(* pointwise certificate assembly over the single-point cons/nil    *)
(* lists, with the [Qeq] premise supplied explicitly over the       *)
(* set-equality domain (no Leibniz face involved).                  *)
Theorem tdy_qlist_Qeq_complete_h1 : forall q1 q2 : Q,
  q1 == q2 -> Forall2 Qeq (q1 :: nil) (q2 :: nil).
Proof.
  intros q1 q2 H. constructor.
  - exact H.
  - constructor.
Qed.

(* Slot for [ev_cong_eqb_complete] (premise 1, [ev_cong a b]):      *)
(* constructor certificate by [ev_cong_num] with [Qeq_refl] at the  *)
(* diagonal of the same record shape; the Leibniz-direction         *)
(* counterexample face [ev_eqb_leibniz_gap] does not block this     *)
(* set-equality certificate.                                        *)
Theorem tdy_ev_cong_eqb_complete_h1 : ev_cong (evNum 0%Q) (evNum 0%Q).
Proof.
  apply ev_cong_num. apply Qeq_refl.
Qed.

(* Slot for [ev_enum_size_bound] (premise 1, [In e (ev_enum n)]):   *)
(* enumeration-membership instance with the leaf witness [evNum     *)
(* 0%Q] at budget layer 1 (supplied by the host [ev_enum_num_0] at  *)
(* [n := O]).                                                       *)
Theorem tdy_ev_enum_size_bound_h1 :
  In (evNum 0%Q) (ev_enum (Datatypes.S O)).
Proof.
  exact (ev_enum_num_0 Datatypes.O).
Qed.

(* Slot for [ev_enum_pair_member] (premise 1, [In a (ev_enum n)]):  *)
(* enumeration-membership instance with [evSeq nil] at budget       *)
(* layer 2 (supplied by the host [ev_enum_seq_nil] at [n := S O]).  *)
Theorem tdy_ev_enum_pair_member_h1 :
  In (evSeq nil) (ev_enum (Datatypes.S (Datatypes.S O))).
Proof.
  exact (ev_enum_seq_nil (Datatypes.S Datatypes.O)).
Qed.

(* Slot for [ev_enum_pair_member] (premise 2, [In b (ev_enum (n -   *)
(* ev_size a))]): budget-difference membership instance with        *)
(* [a := evNum 0%Q], [n := 2], [b := evNum 0%Q]; [ev_size] of the   *)
(* [evNum] leaf is [S O] and [Nat.sub 2 (S O)] reduces by           *)
(* definition to budget layer 1 (supplied by [ev_enum_num_0] at     *)
(* [n := O], up to conversion).                                     *)
Theorem tdy_ev_enum_pair_member_h2 :
  In (evNum 0%Q)
     (ev_enum (Nat.sub (Datatypes.S (Datatypes.S O))
                       (ev_size (evNum 0%Q)))).
Proof.
  exact (ev_enum_num_0 Datatypes.O).
Qed.

(* ========== Use demonstrations (Check face: verified at compile *)
(*   time, no new names introduced) ========== *)
(* Demonstration 1 (the slot supply feeds the qlist_Qeq_complete   *)
(* completeness face): the Forall2 certificate inputs, and the     *)
(* decider returns true.                                           *)
Check (qlist_Qeq_complete (0%Q :: nil) (0%Q :: nil)
         (tdy_qlist_Qeq_complete_h1 0%Q 0%Q (Qeq_refl 0%Q))).
(* Demonstration 2 (the slot supply feeds the ev_cong_eqb_complete *)
(* completeness face): the ev_cong certificate inputs, and the     *)
(* decider returns true.                                           *)
Check (ev_cong_eqb_complete (evNum 0%Q) (evNum 0%Q)
         tdy_ev_cong_eqb_complete_h1).
(* Demonstration 3 (the two slot supplies feed the host shape-    *)
(* level generation rule ev_enum_pair_member): the concatenated   *)
(* element [evPair (evSeq nil) (evNum 0%Q)] registers at budget   *)
(* layer 3 ([a := evSeq nil] of size 1, budget difference         *)
(* 2 - 1 = 1; the right component's budget layer is definitionally *)
(* equal to the slot-36 supply statement, up to conversion).      *)
Check (ev_enum_pair_member (Datatypes.S (Datatypes.S O)) (evSeq nil)
         (evNum 0%Q) tdy_ev_enum_pair_member_h1
         tdy_ev_enum_pair_member_h2).

(* ========== Assumption self-audit (the five supply theorems    *)
(*   printed one by one) ========== *)
Print Assumptions tdy_qlist_Qeq_complete_h1.
Print Assumptions tdy_ev_cong_eqb_complete_h1.
Print Assumptions tdy_ev_enum_size_bound_h1.
Print Assumptions tdy_ev_enum_pair_member_h1.
Print Assumptions tdy_ev_enum_pair_member_h2.
