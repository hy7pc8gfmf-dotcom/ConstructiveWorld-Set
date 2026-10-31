(* Mission. Formalization of the statement faces of this file's 4 theorems
   (prefix uabt10_). Dependencies. S01_BaseRing, S02_CauchyComplete,
   S07_RealSetoidExpLog (the Require face below; all read-only use, zero
   change to the tree). References. ablation source real_weak_trich@
   S07_RealSetoidExpLog.v (green piece, closed by Qed); S04_RealExpLogConv.v
   L1388 weak_trich slot judged W (trichotomy wall = rLPO family) versus the
   source note L1386-87 "Real-layer real_weak_trich supplied already, not
   LPO". Constructivity. zero acknowledgment-style statements (mechanically
   checked); statement faces all Set-layer (real_lt/real_eq : Real -> Real
   -> Set measured; Not at the S01 base layer); axiom face zero additions.
   Build. coqc -native-compiler no -q -Q . "". *)
(* Slot coverage account: the slot form forall x y, Not (lt x y) ->
   Not (lt y x) -> Id x y is covered slot-whole by the green piece under the
   instantiation map R:=Real, lt:=real_lt, Id:=real_eq -- position by
   position: binders x y same; premise 1 Not (lt x y) <-> Not (real_lt x y)
   same position; premise 2 Not (lt y x) <-> Not (real_lt y x) same position;
   conclusion Id x y <-> real_eq x y. The abstract interface face (R/lt/Id
   without decoders) keeps the W annotation; the instantiated supply face
   flips to N. *)
(* Piece inventory and grading: 1 uabt10_weak_trich_real <- slot-form Real
   instantiation resolution, direct supply, grade N1 zero construction (the
   library already holds the equivalent piece at the S07:5719-class
   coordinate; this file is the flip-registration form). 2 uabt10_eq_not_lt_l
   and 3 uabt10_eq_not_lt_r <- reverse compactness leftward/rightward (id_l
   canal, symmetric form), grade N2 finite elimination chain, three steps
   real_eq_sym -> real_lt_id_r/l -> real_lt_irrefl. 4 uabt10_weak_trich_iff
   <- biconditional wrapper, slot form <=> real_eq (Set-layer prod product),
   grade N2 assembly; no piece is T (whole-library grep: zero hits).
   Per-piece Print Assumptions at the tail (G2 all-Closed gauge). *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.

(* Piece 1 <- S04_RealExpLogConv.v L1388 slot form (verbatim instantiation
   R:=Real, lt:=real_lt, Id:=real_eq). *)
Theorem uabt10_weak_trich_real : forall x y : Real,
  Not (real_lt x y) -> Not (real_lt y x) -> real_eq x y.
Proof.
  exact real_weak_trich.
Qed.

(* Piece 2 <- reverse compactness (leftward): equality eliminates
   same-direction lt (real_lt_id_r: eq b c -> lt a b -> lt a c, take c:=a). *)
Theorem uabt10_eq_not_lt_l : forall x y : Real,
  real_eq x y -> Not (real_lt x y).
Proof.
  intros x y Hxy Hlt.
  exact (real_lt_irrefl x
          (RealSetoid.real_lt_id_r x y x (real_eq_sym x y Hxy) Hlt)).
Qed.

(* Piece 3 <- reverse compactness (rightward): equality eliminates
   opposite-direction lt (real_lt_id_l: eq a b -> lt b c -> lt a c, take
   c:=a). *)
Theorem uabt10_eq_not_lt_r : forall x y : Real,
  real_eq x y -> Not (real_lt y x).
Proof.
  intros x y Hxy Hyx.
  exact (real_lt_irrefl x (RealSetoid.real_lt_id_l x y x Hxy Hyx)).
Qed.

(* Piece 4 <- biconditional wrapper: weak trichotomy slot form <=>
   setoid equality (Set-layer prod product). *)
Theorem uabt10_weak_trich_iff : forall x y : Real,
  prod
    (Not (real_lt x y) -> Not (real_lt y x) -> real_eq x y)
    (real_eq x y -> prod (Not (real_lt x y)) (Not (real_lt y x))).
Proof.
  intros x y.
  split.
  - exact (uabt10_weak_trich_real x y).
  - intros H.
    split.
    + exact (uabt10_eq_not_lt_l x y H).
    + exact (uabt10_eq_not_lt_r x y H).
Qed.

(* Tail audit port: per-piece Print Assumptions (G2 all-Closed gauge). *)
Print Assumptions uabt10_weak_trich_real.
Print Assumptions uabt10_eq_not_lt_l.
Print Assumptions uabt10_eq_not_lt_r.
Print Assumptions uabt10_weak_trich_iff.
