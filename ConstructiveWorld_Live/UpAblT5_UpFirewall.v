(* ========================================================================== *)
(*  UpAblT5_UpFirewall.v - strictly antitone positive-inverse slot piece.     *)
(* ========================================================================== *)
(*  Mission. The theorem face below is the inventoried slot statement,        *)
(*  verbatim: for a b with 0 < a and 0 < b (strict order lt, Set-carried),    *)
(*  a < b implies lt (inv_pos b Hb) (inv_pos a Ha) - strict antitony.        *)
(*  Dependencies. The in-file Require surface (S01_BaseRing, InvPosLtCompat); *)
(*  no more Require. The supply theorem ipl_inv_pos_lt_compat                *)
(*  (InvPosLtCompat.v) is reused directly at the abstract interface layer.   *)
(*  References. Statement face matches ipl_inv_pos_lt_compat of               *)
(*  InvPosLtCompat.v argument by argument (same premise order, same          *)
(*  conclusion); projection aliases unpack interface fields as local Lets.   *)
(*  Constructivity. Zero acknowledgment-style statements (mechanically        *)
(*  checked by the end-of-file audit print); statement faces all             *)
(*  Set-carried (lt/Id); purely constructive closure; no additions to the    *)
(*  assumption surface; original tree untouched; abl_ prefix guard.          *)
(*  Build. rocq c -native-compiler no -Q . ""                                *)
(* ========================================================================== *)

Require Import S01_BaseRing.
Require Import InvPosLtCompat.

Section AblUpFirewall.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

Theorem abl_UpFirewall_inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

End AblUpFirewall.

(* ---- End-of-file audit print ---- *)
Print Assumptions abl_UpFirewall_inv_pos_lt_compat.
