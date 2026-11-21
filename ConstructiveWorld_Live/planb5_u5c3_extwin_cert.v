(** * planb5_u5c3_extwin_cert: extension-window A/B cross bites.

    Mission.  The per-point cross certificate of the general-n A/B
      assembly at n = 44, in the litdef cross-multiplication form
      [Qeq_bool (exp * L * sign * r_snapshot) (anchor)]: the pipeline
      r/s snapshot values (Z literals, kb41m_rs_snapshot_20261112.json)
      against the rebuilt single-source anchors; a wrong snapshot
      computes to false.  The rebuilt n = 56 / 64 values conflict with
      an independent 460-digit Machin-pi recomputation (two conflicting
      witness values, neither declared), so only the doubly verified
      point n = 44 is asserted; 45..55, 57..64, 65..1347 carry no
      claim, and the calib domain excludes all three points.

    Dependencies.  planb4_g1_ab_def (the planb4_ab_exp / planb4_ab_L /
      planb4_ab_sign channels); planb3_g1_calib (planb3_g1_dom); the
      Set-layer identity carrier [Id] defined locally in this file.

    References.  KB41m beta0 pre-survey receipt supplement 6 (|Rhat|_hi
      exponents -125.34 / -159.68 / -178.90); the ZZ2020 Prop 1
      assembly (2^(-5n/2+2) L_n I_n in Z + Z pi).

    Constructivity.  Set-carrier: every verdict is carried by the
      Set-layer [Id] on a boolean verdict (Qeq_bool / planb3_g1_dom),
      not by a proposition - zero Prop statement face.  Each bite
      closes by one small-integer vm_compute step (the giant-term
      reduction of [planb4_abqA n] never terminates at n >= 8) and is
      transparent ([Defined]) so verdicts extract as data;
      admission-free and postulate-free.

    Build.  coqc -native-compiler no -q -Q . "" planb5_u5c3_extwin_cert.v (Rocq 9.3.0, serial single lane under cpu_guard_v3). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.

(* ================================================================ *)
(* Section 1. The Set-layer statement carrier.                       *)
(* ================================================================ *)

(* The Set-layer identity type over a decidable verdict: [Id x y] is    *)
(* inhabited exactly when [x] and [y] are convertible elements of the   *)
(* Set [A].  Each verdict below is stated as the data [Id verdict       *)
(* expected] rather than as a proposition, so the verdicts extract as   *)
(* computable content (the certificate-module statement-carrier face).  *)
Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

(* ================================================================ *)
(* Section 2. The extension-window cross bites (n = 44).             *)
(* One Qeq_bool cross-multiplication face per channel: the in-tree   *)
(* exp/L/sign definitions times the pipeline's internal r/s channel  *)
(* snapshot (Z literals from kb41m_rs_snapshot_20261112) must equal  *)
(* the rebuilt single-source anchor.  n = 44 is the only doubly      *)
(* verified point (independent Machin -125.3355 vs receipt -125.34,  *)
(* delta 0.0045).  Small-integer arithmetic only; the giant-term     *)
(* reduction form is not used.                                       *)
(* ================================================================ *)

Lemma planb5_ext_A_44 :
  Id (Qeq_bool (planb4_ab_exp 44 * inject_Z (planb4_ab_L 44)
      * inject_Z (planb4_ab_sign 44)
      * inject_Z (-17545533289124070670616905700395653654224401868563345277693392653649161786724860692729299608637207202891087053923615584730299882208355256477907838466973275771625400436763336653552173956280971742799586287067888949341715991881393443180963029609086976)%Z
      / inject_Z (15346144494172535825501455131028779402768044548349646823875)%Z)
      (inject_Z 22609249443517065326730524672222971139740359111382579347265754575004671993461901853384416766782692596045207624429359081530101354062646361128499523029089709989146125764883782483690897799478899760050131649331224952015159296%Z)) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.

Lemma planb5_ext_B_44 :
  Id (Qeq_bool (planb4_ab_exp 44 * inject_Z (planb4_ab_L 44)
      * inject_Z (planb4_ab_sign 44)
      * inject_Z (363929631081981549690549204999197006408907739587470555424302824807952638390580207065288770564572814236656934867553306533048280084435564378965911740685104282013134304224213533276784813932544)%Z
      / inject_Z 1%Z)
      (inject_Z (-7196747617066849641395044252287707900357657332554179848655982765193550893378537337014724660256508088907095948818919585133102098127620044242316061925741402104447482293400828526919868824079369324017839893248043059298848000)%Z)) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.

(* n = 56 / 64: retracted by the honest contraction - the rebuilt     *)
(* anchors conflict with the independent Machin recomputation by      *)
(* +825 / +980 bits; two conflicting witnesses, no claim here.        *)

(* ================================================================ *)
(* Section 3. Domain honesty.  The extension points sit outside the  *)
(* frozen 1..40 calib domain.  The n = 44 claim is carried by        *)
(* Section 2's cross bites against the doubly-verified anchor; the   *)
(* points 45..55, 56, 57..64 and 65..1347 carry no claim anywhere:   *)
(* 45..55 were never computed (the KB41m 43-point window), 56/64     *)
(* were retracted (two conflicting witness values).  The pipeline    *)
(* computes everywhere, but this face asserts only at n = 44.        *)
(* ================================================================ *)

Lemma planb5_ext_dom_44 : Id (planb3_g1_dom 44) false.
Proof. vm_compute. exact (@id_refl bool false). Defined.

Lemma planb5_ext_dom_56 : Id (planb3_g1_dom 56) false.
Proof. vm_compute. exact (@id_refl bool false). Defined.

Lemma planb5_ext_dom_64 : Id (planb3_g1_dom 64) false.
Proof. vm_compute. exact (@id_refl bool false). Defined.

(* ================================================================ *)
(* Section 4. Assumption audit (5 faces).                            *)
(* ================================================================ *)

Print Assumptions planb5_ext_A_44.
Print Assumptions planb5_ext_B_44.
Print Assumptions planb5_ext_dom_44.
Print Assumptions planb5_ext_dom_56.
Print Assumptions planb5_ext_dom_64.
