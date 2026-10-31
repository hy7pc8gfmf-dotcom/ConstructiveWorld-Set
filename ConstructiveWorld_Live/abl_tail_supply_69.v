(* ========================================================================= *)
(*  abl_tail_supply_69.v -- DO-free order-preservation boundary-record piece. *)
(*  Mission. Two supply theorems were requested ("DO-free bs_abs" and         *)
(*    "bs_lpc", the lt_plus_compat_lt_le shape).  The present-state audit     *)
(*    concludes both are unprovable over the abstract ordered-field           *)
(*    interface; per the loud-failure clause (fail loudly, never silently     *)
(*    downgrade, never placeholder) this piece registers the two slots as     *)
(*    true premises and ships only the two DO-free non-strict BOUNDARY        *)
(*    forms; the full evidence chain, wall shapes and the anti-inflation      *)
(*    declaration live in the evidence record below.                          *)
(*  Dependencies. S01_BaseRing single item (abstract interface class and      *)
(*    fields; fa53-style minimal dependency face; existing pieces            *)
(*    untouched).  Zero Require fa53_compat_abs: its body carries a          *)
(*    DecidableOrder premise, reuse is forbidden by the mission text, and    *)
(*    no proof body below references its names.                              *)
(*  References. Branch-splitting recipe original = S07_RealSetoidExpLog.v    *)
(*    6154-6159 (concrete layer); abstract with-DO originals =               *)
(*    fa53_compat_abs.v 103-118 and 141-152; section-four broadcast          *)
(*    precedent = UpAblP2WByPass.v 611-634; non-strict composition           *)
(*    ingredients = S01_BaseRing class fields lt_le_iff (S01 172) plus       *)
(*    le_plus_compat (S01 233).                                              *)
(*  Constructivity. Both theorems close by Qed via intros + exact over the   *)
(*    class fields lt_le_iff and le_plus_compat; statement carriers are      *)
(*    Set-formed (lt / le / Id are Set-valued; zero Prop leakage); the       *)
(*    piece is axiom-free with no suspended premises and no classical        *)
(*    logic; Print Assumptions must report Closed under the global           *)
(*    context; the trailing extraction probe is judged by Obj.magic zero.    *)
(*  Build. rocq c -native-compiler no -q -Q . "" abl_tail_supply_69.v        *)
(*    (single flat -Q root; dependencies present as .vo beside the piece;    *)
(*    stack limit preset 65532).                                             *)

Require Import S01_BaseRing.
From Stdlib Require Import Extraction.

(* ========================= evidence record =============================== *)
(*                                                                            *)
(* Require face: S01_BaseRing single item; the use face of this piece is the  *)
(* abstract interface class fields (the fa53-style minimal dependency face);  *)
(* existing pieces are untouched.                                             *)
(*                                                                            *)
(* (1) Recipe provenance: the branch-splitting recipe (unfold the le          *)
(*     definition face; destruct the premise into lt / eq branches; lt branch *)
(*     via the class field lt_plus_compat; eq branch via congruence plus      *)
(*     translation lemmas) is verbatim-isomorphic to real_lt_plus_compat_lt_le*)
(*     at S07_RealSetoidExpLog.v 6154-6159.  That recipe is feasible only at  *)
(*     the concrete Real layer: real_le is the transparent Or(lt, eq)         *)
(*     definition (S02_CauchyComplete.v 472), real_lt the transparent eps-form*)
(*     definition (S02 468), and the concrete translation lemma               *)
(*     real_lt_plus_translate (S07 6116) opens precisely by unfolding the     *)
(*     eps form of real_lt for the same-shape split.                          *)
(*                                                                            *)
(* (2) Slot layer: the family slots live in abstract interface projection     *)
(*     sections (P7BoundedSoftmaxDeep.v 153-176 section three;                *)
(*     Arch_Up_01.v 763-798 FirewallLoop and 1139-1176 EntropyGainQuant),     *)
(*     where le := @le RI and the statements draw on abstract class fields:   *)
(*     le is an opaque field (S01_BaseRing.v 152-153) and the whole class     *)
(*     offers only the one-way lt_le_iff (S01 172) into le, with no le        *)
(*     decomposition field; the recipe's first step (destruct the le          *)
(*     premise) is unwritable at the abstract layer.                          *)
(*                                                                            *)
(* (3) Translation wall: the eq branch of the recipe needs one-sided strict   *)
(*     translation, not derivable inside pure fields.  fa53's own header      *)
(*     concedes that the two family statements are not directly derivable     *)
(*     inside RealInterfaceEnhanced pure fields (missing one-sided strict     *)
(*     translation); UpAblT2b_fa53_lpc_broadcast.v honestly registers that    *)
(*     mixed order preservation fails on an abstract R; S08_RealMainlineDPO   *)
(*     2269 notes the linear-order property is instantiable (a concrete-layer *)
(*     fact); Arch_Up_01 FirewallLoop keeps lt_minus_nonneg as a section      *)
(*     interface premise (never a class field), and at the four use sites     *)
(*     (Arch_Up_01 822 / 1004 / 1233 / 1522) the le argument is always       *)
(*     le_refl -- the use face needs exactly the underivable one-sided        *)
(*     translation itself.                                                    *)
(*                                                                            *)
(* (4) In-service precedent face: every in-library supply of this family      *)
(*     carries a DecidableOrder premise -- fa53_compat_abs.v 109 / 147        *)
(*     (abstract layer, with DO); AbsLeId.v 47 (with DO, all-argument form);  *)
(*     UpAblT1b_AttnDoeblin.v 158-176 (section with DO);                      *)
(*     UpAblT-13_UpEntropyGainReq.v 35 / 75 / 115 / 155 (section with DO);    *)
(*     UpAblP2WByPass.v 611-634 (section-four broadcast with DO).  The        *)
(*     DO-free version is absent from the library not by oversight but        *)
(*     because it is unprovable at the abstract layer.                        *)
(*                                                                            *)
(* (5) Machine three-arm comparison (probe_dofree69.v, a self-consuming pool  *)
(*     probe piece, with its log _log/probe_dofree69.log): arm A = abstract   *)
(*     RI with DO -- the fa53 two pieces hold in the slot statement shape;    *)
(*     arm B = abstract RI without DO -- the in-section destruct of the le /  *)
(*     lt premises Fails on both branches (machine transcript); arm C =       *)
(*     concrete layer -- the same-shape split is definitional, and the        *)
(*     consequences of the S07 6135 / 6154 recipe hold in the library.        *)
(*                                                                            *)
(* Downstream linkage: the two lt_plus_compat_lt_le slots of Arch_Up_01       *)
(*   (797-798 / 1175-1176) reclassify as true premises following this         *)
(*   verdict (the same ruling family as the LPO precedent); no supply file    *)
(*   is issued for them; the two P7BoundedSoftmaxDeep slots (175-176) share   *)
(*   the verdict.                                                             *)
(*                                                                            *)
(* Wall shapes (registry three-element form):                                 *)
(*   shape one (bs_abs slot):  forall (RI : RealInterfaceEnhanced)            *)
(*     (a : @R RI), @le RI (@zero RI) a -> Id (@abs RI a).                    *)
(*   shape two (bs_lpc slot): forall (RI : RealInterfaceEnhanced)             *)
(*     (a b c d : @R RI), @lt RI a b -> @le RI c d ->                         *)
(*     @lt RI (@plus RI a c) (@plus RI b d).                                  *)
(*   Defense coordinates: P7BoundedSoftmaxDeep.v 175-176; Arch_Up_01.v        *)
(*     797-798 and 1175-1176.                                                 *)
(*   Adjacent proven pieces: fa53_compat_abs.v 109 / 147 (abstract with DO);  *)
(*     AbsLeId.v 47; UpAblT2b_fa53_lpc_broadcast.v 57-107 (with DO thin       *)
(*     strict-chain broadcast, eight sections eleven slots);                  *)
(*     S07_RealSetoidExpLog.v 6135 / 6154 (DO-free concrete layer -- the      *)
(*     true landing layer of the branch-splitting recipe).                    *)
(*   This piece's boundary forms: tsp_f8_lt_le_mixed_plus_le and              *)
(*     tsp_f8_le_lt_mixed_plus_le (abstract layer, DO-free, non-strict).      *)
(*                                                                            *)
(* Anti-inflation declaration: the two theorems below are comparison          *)
(*   boundary forms, not slot supplies -- their statements differ from the    *)
(*   two mission slots (conclusion position le, not lt; the Id (abs a) a      *)
(*   slot is not covered either), so they can feed no slot and count in no    *)
(*   slot-resolution account.  Their purpose: machine-fix the DO-free         *)
(*   reachable boundary -- the lt_le_iff lifting plus the le_plus_compat      *)
(*   combination closes the non-strict conclusion, and the strictness gap     *)
(*   is exactly the translation wall.                                         *)
(* ========================================================================== *)

(* ============================================================ *)
(* Boundary-form region: the two nearest-reachable DO-free        *)
(*   non-strict forms (anti-inflation declaration above:          *)
(*   not slot supplies, feed no slot, count in no account).       *)
(* ============================================================ *)

Section TspF8Boundary.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* Boundary form one: the non-strict shape of lt + le mixed additive order
   preservation.  Proof path: the class field lt_le_iff (S01 172 class field,
   inl lifting) raises lt a b into le a b, then the class field
   le_plus_compat composes the two steps.  The strictness gap is the
   one-sided strict translation wall (registered in the evidence record),
   unreachable without DO -- this is exactly the boundary of this form. *)
Theorem tsp_f8_lt_le_mixed_plus_le :
  forall a b c d : R, lt a b -> le c d -> le (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_plus_compat a b c d (lt_le_iff a b (inl Hab)) Hcd).
Qed.

(* Boundary form two: the non-strict shape of le + lt mixed additive order
   preservation (dual slot direction, same direction as fa53 piece two). *)
Theorem tsp_f8_le_lt_mixed_plus_le :
  forall a b c d : R, le a b -> lt c d -> le (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_plus_compat a b c d Hab (lt_le_iff c d (inl Hcd))).
Qed.

End TspF8Boundary.

(* ============================================================ *)
(* Final audit: per-piece assumption-face audit + extraction      *)
(*   probe.  Name list 2 = Qed count 2 = output statement count   *)
(*   2, zero delta; the extraction criterion is Obj.magic count   *)
(*   0; if nonzero, register honestly by segment (in-pool         *)
(*   precedent caliber), never report a false pass.               *)
(* ============================================================ *)
Print Assumptions tsp_f8_lt_le_mixed_plus_le.
Print Assumptions tsp_f8_le_lt_mixed_plus_le.

Recursive Extraction tsp_f8_lt_le_mixed_plus_le tsp_f8_le_lt_mixed_plus_le.
