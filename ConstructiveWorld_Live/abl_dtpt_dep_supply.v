(* ConstructiveWorld-Set — residual bounded-guard supplies for the DTPT bridge dependency slots. *)

(** * abl_dtpt_dep_supply: supplies for the premise slots of DTPT_Bridge_Dep.

    Mission.  Two supplies for the bounded-guard premise slot
      [forall x : Q, In x l -> Qabs x <= B] of [DTPT_Bridge_Dep]:
      [tbd_dep_HB_wit_002], the guard at the closed witness list
      [[0;0;2]] with the tight bound B := 2 (the same witness column as
      the [dtr_] sorted-witness supplies), and [tbd_dep_HB_P0_single],
      the computation law on [P0 [a]] = [[a]] with the canonical bound
      B := [Qabs a]. The host's other three slots ([SortedQ l],
      [l <> []], (lam1 <= lam2)%Q at 0/1) are [dtr_]-supplied and reused.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List];
      requires [S02_CauchyComplete] (the [QleT'] carrier) and [DTPT]
      (definitions [P0], [xq_Qle_bool_le]) of this development, read-only.

    References.  DTPT.v (the host definitions) and the baseline module of
      the same name in ConstructiveWorld-Main (statement names verbatim).

    Constructivity.  Both supplies close by [Qed] via closed [Q]
      comparisons ([vm_compute] on [Qle_bool]) and discrimination on the
      [In] membership; no new data carriers, no section variables, no
      classical logic; [Q] literals scoped with [%Q]; the two
      [Print Assumptions] audits report Closed.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      abl_dtpt_dep_supply.v] compiles cleanly (exit 0); the first eight
      bytes of the artifact are [436f7121 000160bc]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
Import ListNotations.

Require Import S02_CauchyComplete.
Require DTPT.
Import DTPT.DTPT.

Open Scope Q_scope.

(* ========== Supplies for the bounded-guard premise slot (instance-domain and computation-law forms) ========== *)

(* Supply 1 (closed-instance form): the bounded guard on the witness list
   [0;0;2] — the same column as the sorted-witness supplies (sorted_wit_002 /
   dtr_c2_sorted_wit_002), so the slot-2 supplies range over the same domain.
   Proof shape: the In disjunction is expanded element by element and, after
   substitution, [Qabs] is decided on closed values (Qle_bool reflection, the
   same recipe as the host). B := 2 is the exact supremum of the column (the
   element 2 occurs in it), so the bound is tight. *)
Theorem tbd_dep_HB_wit_002 : forall x : Q, In x [0; 0; 2] -> QleT' (Qabs x) 2%Q.
Proof.
  intros x Hx.
  destruct (Q_dec x 0%Q) as [Hx0 | Hx0].
  - subst x. vm_compute. reflexivity.
  - destruct (Q_dec x 2%Q) as [Hx2 | Hx2].
    + subst x. vm_compute. reflexivity.
    + exfalso. simpl in Hx.
      * destruct Hx as [He | [He | [He | HF]]].
        -- congruence.
        -- congruence.
        -- congruence.
        -- exact HF.
Qed.

(* Supply 2 (computation-law form): the fully applied family on the
   single-element P0 domain — the insertion sort computes P0 [a] = [a] (the
   insert step on an empty list is purely constructive), and the element is
   unique, so [Qabs a] is the exact bound (B := Qabs a, the canonical bound
   term). Sharing the P0 closed domain with the slot-2/slot-3 supplies, the
   three guards can be applied together over one domain. *)
Theorem tbd_dep_HB_P0_single : forall a y : Q,
  In y (P0 [a]) -> QleT' (Qabs y) (Qabs a).
Proof.
  intros a y Hy.
  assert (E : P0 [a] = [a]) by reflexivity.
  rewrite E in Hy. simpl in Hy.
  destruct (Q_dec y a) as [Hya | Hne].
  - subst y. apply Qle_to_QleT'. apply Qle_refl.
  - exfalso. destruct Hy as [Heq | HF].
    + congruence.
    + exact HF.
Qed.

(* ========== assumption audit (Print Assumptions per statement) ========== *)
Print Assumptions tbd_dep_HB_wit_002.
Print Assumptions tbd_dep_HB_P0_single.
