(* ========================================================================== *)
(*  InvPosLtCompat.v - strictly antitone positive-inverse slot piece.         *)
(* ========================================================================== *)
(*  Mission. Discharge the honest-interface strict slot inv_pos_lt_compat at *)
(*  the abstract layer: forall a b : R, lt zero a -> lt zero b -> lt a b ->   *)
(*  lt (inv_pos b Hb) (inv_pos a Ha) - the positive inverse is strictly       *)
(*  antitone (a rising temperature strictly lowers 1/t), the core order slot  *)
(*  of strictly monotone temperature chains. The interface already carries    *)
(*  the non-strict field inv_pos_le_compat (S01_BaseRing); the strict version *)
(*  previously existed only at the concrete Real layer                        *)
(*  (real_inv_pos_lt_contra, S07_RealSetoidExpLog); this piece fills the gap. *)
(*  Dependencies. The in-file Require surface: S01_BaseRing; no more Require. *)
(*  Closure principle. Pure order-algebraic chain, no decidable-order        *)
(*  extension in the dependency surface:                                      *)
(*    inv b == (inv a * a) * inv b < (inv a * b) * inv b == inv a             *)
(*  via one-sided strict left multiplication (the lt_mult_compat field is    *)
(*  the right-multiplication form; two mult_comm channels), right           *)
(*  multiplication by inv b (positivity from inv_pos_pos), the left channel  *)
(*  (inv a*a) == one (mult_comm + inv_pos_correct, folded by mult_comm +    *)
(*  mult_one), the right channel (inv a*b)*inv b == inv a (mult_assoc +     *)
(*  inv_pos_correct + mult_one), and two-sided closure by lt_id_l/lt_id_r.  *)
(*  References. The concrete Real-layer counterpart real_inv_pos_lt_contra  *)
(*  (S07_RealSetoidExpLog) stays in place and is not consumed here.          *)
(*  Constructivity. Purely constructive; statement faces all Set-carried     *)
(*  (lt/Id; Not is the S01_BaseRing Empty_set-function form); non-trivial    *)
(*  genuine proof (the four-segment field chain); ipl_ prefix guards against *)
(*  name clashes library-wide; end-of-file Print Assumptions block.          *)
(*  Build. coqc -native-compiler no -q -Q . "".                              *)
(* ========================================================================== *)

Require Import S01_BaseRing.

Section InvPosLtCompat.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* Projection aliases (unpack interface fields as local Lets). *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

(* ---- Support: one-sided strict left multiplication (new form: the        ---- *)
(* ---- lt_mult_compat field is the right-multiplication form; strict left ---- *)
(* ---- multiplication was missing at the interface layer; the isomorphic  ---- *)
(* ---- channel-translation method supplies it                             ---- *)
Lemma ipl_lt_mult_compat_l :
  forall a b c : R, lt zero c -> lt a b -> lt (mult c a) (mult c b).
Proof.
  intros a b c Hc Hab.
  apply (lt_id_r (mult c a) (mult b c) (mult c b) (mult_comm b c)).
  apply (lt_id_l (mult c a) (mult a c) (mult b c) (mult_comm c a)).
  exact (lt_mult_compat a b c Hc Hab).
Qed.

(* ---- Main piece: strictly antitone positive inverse ----
   inv b == (inv a*a)*inv b < (inv a*b)*inv b == inv a. *)
Theorem ipl_inv_pos_lt_compat :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  (* middle term strict: inv a*a < inv a*b (left multiplication by the      *)
  (* positive inv a), then right-multiply the whole by the positive inv b   *)
  (* (chained-genuine-proof shape). *)
  assert (Hmid : lt (mult (inv_pos a Ha) a) (mult (inv_pos a Ha) b)).
  { exact (ipl_lt_mult_compat_l a b (inv_pos a Ha) (inv_pos_pos a Ha) Hab). }
  assert (Hstep : lt (mult (mult (inv_pos a Ha) a) (inv_pos b Hb))
                     (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))).
  { exact (lt_mult_compat (mult (inv_pos a Ha) a) (mult (inv_pos a Ha) b)
                          (inv_pos b Hb) (inv_pos_pos b Hb) Hmid). }
  (* left channel: X := (inv a*a)*inv b == inv b ((inv a*a) == one + one    *)
  (* left-multiplication fold-back) *)
  assert (Hl : Id (mult (mult (inv_pos a Ha) a) (inv_pos b Hb))
                  (inv_pos b Hb)).
  { exact (id_trans
             (id_cong (fun w => mult w (inv_pos b Hb))
                      (id_trans (mult_comm (inv_pos a Ha) a)
                                (inv_pos_correct a Ha)))
             (id_trans (mult_comm one (inv_pos b Hb))
                       (mult_one (inv_pos b Hb)))). }
  (* right channel: Y := (inv a*b)*inv b == inv a (assoc regrouping +       *)
  (* inv b*inv b == one + mult_one right-multiplication fold-back) *)
  assert (Hr : Id (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))
                  (inv_pos a Ha)).
  { exact (id_trans (id_sym (mult_assoc (inv_pos a Ha) b (inv_pos b Hb)))
                    (id_trans (id_cong (fun w => mult (inv_pos a Ha) w)
                                       (inv_pos_correct b Hb))
                              (mult_one (inv_pos a Ha)))). }
  (* two-sided conversion closure *)
  exact (lt_id_r (inv_pos b Hb)
                 (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))
                 (inv_pos a Ha) Hr
                 (lt_id_l (inv_pos b Hb)
                          (mult (mult (inv_pos a Ha) a) (inv_pos b Hb))
                          (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))
                          (id_sym Hl) Hstep)).
Qed.

(* ---- Cross-check form: re-feed anchor whose statement is verbatim equal  ---- *)
(* ---- to the inventoried interface slot statement                        ---- *)
Corollary ipl_upfirewall_102_shape :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  exact (fun a b Ha Hb Hab => ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

(* ---- Dual form: strictly monotone positive inverse (the                  ---- *)
(* ---- lt (inv a) (inv b) direction, the sibling-slot-family               ---- *)
(* ---- real_inv_pos_lt shape; from the main piece by the two-sided         ---- *)
(* ---- lt_id conversions                                                  ---- *)
Lemma ipl_lt_inv_pos_mono :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt b a -> lt (inv_pos a Ha) (inv_pos b Hb).
Proof.
  intros a b Ha Hb Hba.
  exact (ipl_inv_pos_lt_compat b a Hb Ha Hba).
Qed.

(* ---- le-version compatibility check: the main piece implies the         ---- *)
(* ---- interface field inv_pos_le_compat of the same shape (strict        ---- *)
(* ---- implies non-strict, via the lt_le_iff field channel; no conflict   ---- *)
(* ---- with the S01_BaseRing field                                       ---- *)
Corollary ipl_inv_pos_le_of_lt :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt a b -> le (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (lt_le_iff (inv_pos b Hb) (inv_pos a Ha)
           (inl (ipl_inv_pos_lt_compat a b Ha Hb Hab))).
Qed.

End InvPosLtCompat.

(* ---- End-of-file audit print ---- *)
Print Assumptions ipl_lt_mult_compat_l.
Print Assumptions ipl_inv_pos_lt_compat.
Print Assumptions ipl_upfirewall_102_shape.
Print Assumptions ipl_lt_inv_pos_mono.
Print Assumptions ipl_inv_pos_le_of_lt.
