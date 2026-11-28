(* ========================================================================= *)
(* Module   : UpAblA2_LoInflation                                           *)
(* Mission. Low-inflation law for the mixing-time selector: with ub(lo) :=  *)
(*   TV0 * inv(lo^2 * budget) the four-fold identity ub(lo/2) = 4 * ub(lo)  *)
(*   holds exactly at the Id level, so halving lo quadruples the explicit   *)
(*   bound on the selector step count. Part A: abstract engine -- the       *)
(*   halving law (lo/2)^2 * 4 = lo^2, the four-fold law, the                *)
(*   two-configuration budget + dominance theorem, antitonicity of the      *)
(*   k-bound in lo. Part B: attention instantiation on the bounded-logits   *)
(*   softmax kernel, lo := expf(invT * (-Delta)), delta* := lo * lo         *)
(*   (upper-bound side only; the TV lower-bound direction stays open).      *)
(* Dependencies. S01_BaseRing; S04_RealExpLogConv (r_pow);                  *)
(*   S06_DiffSamplingGibbs (tv_dist); AttnDoeblin (BoundedSoftmax family,   *)
(*   inv_pos_mult_distr, u_titer); UpReqUMixSelect (ums_pow_tail,           *)
(*   ums_scale, ums_le_plus_r, ums_mult_one_l); Stdlib List.                *)
(* References. AttnDoeblin.v BoundedSoftmax section (lo/delta* forms,       *)
(*   bs_delta_star_lt_one); UpReqUMixSelect.v ums_pow_tail (Arch input      *)
(*   TV0 * inv(w * budget) consumed verbatim, so projT1 of the result is    *)
(*   the selector step count under the same witness); honest-interface      *)
(*   Variables as in AttnDoeblin/UpReqUMixSelect; no new interface slots.   *)
(* Constructivity. Statement faces fully Set-carried: quantifiers over     *)
(*   R/nat, comparisons via the Set-valued lt/le interface fields,          *)
(*   existentials as sigT witnesses under the Set-level And; the only       *)
(*   sigT-embedded predicate forms are those Set fields and the Set         *)
(*   identity Id, mirroring existing library faces; zero Prop statement,    *)
(*   zero classical logic, zero axioms. All results end Defined             *)
(*   (extraction-transparent); no Qed bridge, no Constructivity exception. *)
(* Build. rocq c -native-compiler no -q -Q <Set Live root> ""            *)
(*   UpAblA2_LoInflation.v  (workdir: this sandbox directory).            *)
(* ========================================================================= *)

From Stdlib Require Import List.
Require Import AttnDoeblin.
Require Import UpReqUMixSelect.
Require Import S01_BaseRing.
Require Import S04_RealExpLogConv.
Require Import S06_DiffSamplingGibbs.

(* ################ Part A: the abstract lo-inflation engine ################ *)

Section LoInflation.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let one := @one RI.
Let zero := @zero RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.

(* Honest interface: mixed lt+le additive order compatibility (the          *)
(*   same-name slot consumed by ums_pow_tail); declared explicitly here     *)
(*   and not lifted out of the section.                                     *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ---- Fixed faces: TV0 / budget ---- *)
Variable TV0 : R.
Variable Htv0 : le zero TV0.
Variable budget : R.
Variable Hbudget : lt zero budget.

(* ---- Inflation coefficient: lo (= expf(-Delta/T) in the attention instance) ---- *)
Variable lo : R.
Variable Hlo0 : lt zero lo.
Variable Hds1 : lt (mult lo lo) one.   (* delta* < 1: Doeblin certificate *)

(* Arch premise (selector actual form: le premise + nat-scale ums_scale shape) *)
Variable Harch : forall x : R, le zero x ->
  sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one)).

(* ---- Scaling constants: two / four and their inverses ---- *)
Let two := plus one one.
Let Htwo0 : lt zero two := plus_positive one one one_pos one_pos.
Let inv2 := inv_pos two Htwo0.
Let four := plus two two.
Let Hfour0 : lt zero four := plus_positive two two Htwo0 Htwo0.
Let inv4 := inv_pos four Hfour0.

(* ---- Two configurations: lo and lo/2;                                    *)
(*      delta* := lo^2 and delta*_2 := (lo/2)^2 = delta*/4 ---- *)
Let lo_half := mult lo inv2.
Let ds := mult lo lo.
Let ds2 := mult lo_half lo_half.
Let kap := minus one ds.
Let kap2 := minus one ds2.

(* ---- Arch inputs of the two configurations = explicit selector k-bounds ---- *)
Let Hds0 : lt zero ds := mult_positive lo lo Hlo0 Hlo0.
Let Hwb : lt zero (mult ds budget) :=
  mult_positive ds budget Hds0 Hbudget.
Let ub := mult TV0 (inv_pos (mult ds budget) Hwb).
Let Hlohalf0 : lt zero lo_half :=
  mult_positive lo inv2 Hlo0 (inv_pos_pos two Htwo0).
Let Hds2_0 : lt zero ds2 := mult_positive lo_half lo_half Hlohalf0 Hlohalf0.
Let Hwb2 : lt zero (mult ds2 budget) :=
  mult_positive ds2 budget Hds2_0 Hbudget.
Let ub2 := mult TV0 (inv_pos (mult ds2 budget) Hwb2).

(* ---------- Elementary order facts ---------- *)

(* 1 <= 4 (via 1 <= 2 <= 4) *)
Lemma loi_le_one_four : le one four.
Proof.
  apply (le_trans one (plus one one) four).
  - exact (ums_le_plus_r one one (lt_le_iff zero one (inl one_pos))).
  - exact (ums_le_plus_r two two
             (le_id_l zero (plus zero zero) two
                (id_sym (plus_zero zero))
                (le_plus_compat zero one zero one
                   (lt_le_iff zero one (inl one_pos))
                   (lt_le_iff zero one (inl one_pos))))).
Defined.

(* ---------- Ring identities (interface-level id chains; no ring tactic) ---------- *)

(* 2 * inv2 == 1 *)
Lemma loi_inv2_two : Id (mult two inv2) one.
Proof.
  exact (inv_pos_correct two Htwo0).
Defined.

(* inv2 * four == two (= 4/2) *)
Lemma loi_inv2_four_two : Id (mult inv2 four) two.
Proof.
  apply (id_trans (mult_comm inv2 four)).
  apply (id_trans (mult_plus_distr_r two two inv2)).
  apply (id_trans (id_cong2 plus
             (inv_pos_correct two Htwo0)
             (inv_pos_correct two Htwo0))).
  exact (id_refl : Id (plus one one) two).
Defined.

(* Inverse extensionality: a == b (both positive) implies inv a == inv b *)
Lemma loi_inv_wd : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  Id a b -> Id (inv_pos a Ha) (inv_pos b Hb).
Proof.
  intros a b Ha Hb Hab.
  apply (mult_cancel_l b (inv_pos a Ha) (inv_pos b Hb) Hb).
  exact (id_trans
           (id_trans
              (id_cong (fun x => mult x (inv_pos a Ha)) (id_sym Hab))
              (inv_pos_correct a Ha))
           (id_sym (inv_pos_correct b Hb))).
Defined.

(* ---------- (1) delta* halving law: (lo/2)^2 * 4 == lo^2 ---------- *)
Lemma loi_ds2_scale : Id (mult four ds2) ds.
Proof.
  assert (H1 : Id (mult four lo_half) (mult lo two)).
  { exact (id_trans (mult_assoc four lo inv2)
           (id_trans
              (id_cong2 mult (mult_comm four lo) (id_refl : Id inv2 inv2))
           (id_trans (id_sym (mult_assoc lo four inv2))
           (id_cong (fun x => mult lo x)
              (id_trans (mult_comm four inv2) loi_inv2_four_two))))). }
  assert (H2 : Id (mult four (mult lo_half lo_half))
                  (mult (mult four lo_half) lo_half)).
  { exact (mult_assoc four lo_half lo_half). }
  assert (H3 : Id (mult (mult four lo_half) lo_half)
                  (mult (mult lo two) lo_half)).
  { exact (id_cong2 mult H1 (id_refl : Id lo_half lo_half)). }
  assert (H4 : Id (mult (mult lo two) lo_half)
                  (mult (mult (mult lo two) lo) inv2)).
  { exact (mult_assoc (mult lo two) lo inv2). }
  assert (H5 : Id (mult (mult (mult lo two) lo) inv2)
                  (mult (mult (mult lo lo) two) inv2)).
  { exact (id_trans
             (id_cong2 mult (id_sym (mult_assoc lo two lo))
                             (id_refl : Id inv2 inv2))
             (id_cong2 mult
                (id_trans (id_cong (fun x => mult lo x) (mult_comm two lo))
                          (mult_assoc lo lo two))
                (id_refl : Id inv2 inv2))). }
  assert (H6 : Id (mult (mult (mult lo lo) two) inv2) ds).
  { exact (id_trans (id_sym (mult_assoc (mult lo lo) two inv2))
           (id_trans (id_cong (fun x => mult (mult lo lo) x) loi_inv2_two)
                     (mult_one (mult lo lo)))). }
  exact (id_trans (id_trans (id_trans H2 H3) H4) (id_trans H5 H6)).
Defined.

(* (lo/2)^2 <= lo^2 (via four >= 1 and (1)) *)
Lemma loi_ds2_le_ds : le ds2 ds.
Proof.
  apply (le_trans ds2 (mult ds2 one) ds).
  - exact (le_id_r ds2 ds2 (mult ds2 one)
             (id_sym (mult_one ds2)) (le_refl ds2)).
  - apply (le_trans (mult ds2 one) (mult ds2 four) ds).
    + exact (le_mult_compat_r ds2 one four
               (lt_le_iff zero ds2 (inl Hds2_0)) (loi_le_one_four)).
    + exact (le_id_l (mult ds2 four) ds ds
               (id_trans (mult_comm ds2 four) loi_ds2_scale) (le_refl ds)).
Defined.

(* delta*_2 = (lo/2)^2 < 1 (kappa_2 certificate) *)
Lemma loi_ds2_lt_one : lt ds2 one.
Proof.
  exact (le_lt_trans ds2 ds one loi_ds2_le_ds Hds1).
Defined.


(* ---------- (2) The core four-fold law: ub(lo/2) == 4 * ub(lo) ---------- *)
Lemma loi_ub2_quad : Id ub2 (mult four ub).
Proof.
  assert (Hsplit : Id (mult ds budget) (mult four (mult ds2 budget))).
  { exact (id_trans (id_cong2 mult (id_sym loi_ds2_scale)
                                   (id_refl : Id budget budget))
                    (id_sym (mult_assoc four ds2 budget))). }
  assert (Hbinv : Id (inv_pos (mult ds budget) Hwb)
                     (mult inv4 (inv_pos (mult ds2 budget) Hwb2))).
  { exact (id_trans
             (loi_inv_wd (mult ds budget)
                         (mult four (mult ds2 budget))
                         Hwb
                         (mult_positive four (mult ds2 budget)
                            Hfour0 Hwb2)
                         Hsplit)
             (inv_pos_mult_distr four (mult ds2 budget)
                                 Hfour0 Hwb2)). }
  assert (Hub' : Id ub (mult inv4 ub2)).
  { exact (id_trans (id_cong (fun x => mult TV0 x) Hbinv)
           (id_trans (mult_assoc TV0 inv4
                        (inv_pos (mult ds2 budget) Hwb2))
           (id_trans
              (id_cong2 mult (mult_comm TV0 inv4)
                        (id_refl : Id (inv_pos (mult ds2 budget) Hwb2)
                                      (inv_pos (mult ds2 budget) Hwb2)))
              (id_sym (mult_assoc inv4 TV0
                         (inv_pos (mult ds2 budget) Hwb2)))))). }
  assert (Hfin : Id (mult four (mult inv4 ub2)) ub2).
  { exact (id_trans (mult_assoc four inv4 ub2)
           (id_trans (id_cong2 mult
                        (inv_pos_correct four Hfour0)
                        (id_refl : Id ub2 ub2))
                     (ums_mult_one_l ub2))). }
  exact (id_sym (id_trans (id_cong (fun x => mult four x) Hub') Hfin)).
Defined.

(* ---------- (3) Main theorem: the inflation law ---------- *)
(* k1 realizes kappa^k1 * TV0 < budget (kappa := 1 - lo^2); k2 realizes      *)
(* kappa_2^k2 * TV0 < budget (kappa_2 := 1 - (lo/2)^2); and                  *)
(* k2 > 4 * ub(lo) = 4 * TV0/(lo^2 * budget): with TV0/budget fixed,         *)
(* halving lo exactly quadruples the explicit upper bound on the k the       *)
(* selector needs.                                                           *)
Theorem loi_lo_inflation :
  sigT (fun k1 : nat =>
    sigT (fun k2 : nat =>
      And (lt (mult (r_pow kap k1) TV0) budget)
        (And (lt (mult (r_pow kap2 k2) TV0) budget)
             (lt (mult four ub) (ums_scale k2 one))))).
Proof.
  assert (Hub : le zero ub).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult ds budget) Hwb))
             (mult TV0 (inv_pos (mult ds budget) Hwb))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult ds budget) Hwb))
                (mult_zero (inv_pos (mult ds budget) Hwb))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult ds budget) Hwb)
                (lt_le_iff zero (inv_pos (mult ds budget) Hwb)
                             (inl (inv_pos_pos (mult ds budget) Hwb)))
                Htv0)). }
  assert (Hub2 : le zero ub2).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult ds2 budget) Hwb2))
             (mult TV0 (inv_pos (mult ds2 budget) Hwb2))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult ds2 budget) Hwb2))
                (mult_zero (inv_pos (mult ds2 budget) Hwb2))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult ds2 budget) Hwb2)
                (lt_le_iff zero (inv_pos (mult ds2 budget) Hwb2)
                             (inl (inv_pos_pos (mult ds2 budget) Hwb2)))
                Htv0)). }
  destruct (Harch ub Hub) as [N1 HN1].
  destruct (Harch ub2 Hub2) as [N2 HN2].
  destruct (ums_pow_tail lt_plus_compat_lt_le kap TV0 budget ds N1 Hwb
              Hds0 Hds1
              (id_refl : Id kap (minus one ds)) Htv0
              (lt_le_iff zero budget (inl Hbudget)) HN1) as [k1 Hk1].
  pose (Hp2 := ums_pow_tail lt_plus_compat_lt_le kap2 TV0 budget ds2 N2 Hwb2
                 Hds2_0 loi_ds2_lt_one
                 (id_refl : Id kap2 (minus one ds2)) Htv0
                 (lt_le_iff zero budget (inl Hbudget)) HN2).
  exists k1. exists (projT1 Hp2). split.
  - exact Hk1.
  - split.
    + exact (projT2 Hp2).
    + exact (lt_id_l (mult four ub) ub2 (ums_scale (projT1 Hp2) one)
               (id_sym loi_ub2_quad) HN2).
Defined.

(* ---------- (4) Antitonicity of the k-bound ---------- *)
(* lo^2 <= lo'^2 implies ub(lo') <= ub(lo): the weaker the Doeblin constant  *)
(* (the smaller lo), the larger the explicit upper bound on the required k   *)
(* -- the monotone quantitative onset law.                                   *)
Lemma loi_ub_antitone :
  forall (lo' : R) (Htv0s : lt zero TV0)
         (Hlo2b : lt zero (mult (mult lo' lo') budget)),
  le ds (mult lo' lo') ->
  le (mult TV0 (inv_pos (mult (mult lo' lo') budget) Hlo2b)) ub.
Proof.
  intros lo' Htv0s Hlo2b Hle.
  assert (Hdsb_le : le (mult ds budget) (mult (mult lo' lo') budget)).
  { exact (le_mult_compat ds (mult lo' lo') budget Hbudget Hle). }
  assert (Hinv : le (inv_pos (mult (mult lo' lo') budget) Hlo2b)
                    (inv_pos (mult ds budget) Hwb)).
  { exact (inv_pos_le_compat (mult ds budget)
                             (mult (mult lo' lo') budget)
                             Hwb Hlo2b Hdsb_le). }
  exact (le_id_l
           (mult TV0 (inv_pos (mult (mult lo' lo') budget) Hlo2b))
           (mult (inv_pos (mult (mult lo' lo') budget) Hlo2b) TV0)
           ub
           (mult_comm TV0 (inv_pos (mult (mult lo' lo') budget) Hlo2b))
           (le_id_r
              (mult (inv_pos (mult (mult lo' lo') budget) Hlo2b) TV0)
              (mult (inv_pos (mult ds budget) Hwb) TV0)
              ub
              (mult_comm (inv_pos (mult ds budget) Hwb) TV0)
              (le_mult_compat
                 (inv_pos (mult (mult lo' lo') budget) Hlo2b)
                 (inv_pos (mult ds budget) Hwb)
                 TV0 Htv0s Hinv))).
Defined.

End LoInflation.

(* ################ Part B: the attention instantiation ################
   The BoundedSoftmax interface family is re-instantiated with named
   variables; lo := expf(invT * (-Delta)) and delta* := lo * lo (exact,
   loss-free, as in AttnDoeblin). *)

Section LoInflationAttn.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @tv_dist RI SS SO.

(* ---- BoundedSoftmax interface family (mirrors AttnDoeblin item by item) ---- *)
Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> Id (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S -> R, Id (sum_over_S g) (bs_list_sum g enum).

(* ---- Core instance (named re-instantiation) ---- *)
Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let amt_kernel : S -> S -> R :=
  bs_kernel enum enum_nonempty temp temp_pos Delta z z_lb expf expf_pos
            expf_mono_le sum_eq_list.

(* ---- Scaling constants and the two configurations (same shape as Part A) ---- *)
Let two := plus one one.
Let Htwo0 : lt zero two := plus_positive one one one_pos one_pos.
Let inv2 := inv_pos two Htwo0.
Let four := plus two two.
Let Hfour0 : lt zero four := plus_positive two two Htwo0 Htwo0.
Let lo_half_star := mult lo inv2.

Let Hlo0 : lt zero lo := expf_pos (mult invT (opp Delta)).
Let ds_star_pos : lt zero delta_star := mult_positive lo lo Hlo0 Hlo0.
Let Hlohalf0 : lt zero lo_half_star :=
  mult_positive lo inv2 Hlo0 (inv_pos_pos two Htwo0).
Let Hds2s0 : lt zero (mult lo_half_star lo_half_star) :=
  mult_positive lo_half_star lo_half_star Hlohalf0 Hlohalf0.

(* delta* < 1 (via bs_delta_star_lt_one) *)
Lemma loi_attn_ds_lt_one : lt delta_star one.
Proof.
  exact (bs_delta_star_lt_one temp temp_pos Delta Delta_pos expf expf_pos
           expf_zero expf_plus expf_mono_lt).
Defined.

(* ---------- (6) The TV-form inflation law on the attention kernel (main theorem) ---------- *)
(* Under one and the same Arch witness the selector returns k with           *)
(*   TV(T^k mu, T^k nu) < budget   and   k > TV0/(delta* * budget)           *)
(* (the dominance leg).                                                      *)
Theorem loi_attention_inflation :
  forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  forall (budget : R) (Hbudget : lt zero budget),
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    And (lt (tv (@u_titer RI SS SO amt_kernel k mu)
                (@u_titer RI SS SO amt_kernel k nu)) budget)
        (lt (mult (tv mu nu)
                  (inv_pos (mult delta_star budget)
                     (mult_positive delta_star budget ds_star_pos Hbudget)))
            (ums_scale k one))).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch.
  assert (Htvnn : le zero (tv mu nu)) by exact (tv_dist_nonneg mu nu).
  pose (HwbA := mult_positive delta_star budget ds_star_pos Hbudget).
  assert (Hub : le zero (mult (tv mu nu)
                          (inv_pos (mult delta_star budget) HwbA))).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult delta_star budget) HwbA))
             (mult (tv mu nu) (inv_pos (mult delta_star budget) HwbA))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult delta_star budget) HwbA))
                (mult_zero (inv_pos (mult delta_star budget) HwbA))))
             (le_mult_compat_weak zero (tv mu nu)
                (inv_pos (mult delta_star budget) HwbA)
                (lt_le_iff zero (inv_pos (mult delta_star budget) HwbA)
                             (inl (inv_pos_pos (mult delta_star budget)
                                    HwbA)))
                Htvnn)). }
  destruct (Harch (mult (tv mu nu)
                     (inv_pos (mult delta_star budget) HwbA)) Hub) as [N HN].
  pose (Hp := ums_pow_tail bs_lpc (minus one delta_star) (tv mu nu) budget
                 delta_star N HwbA ds_star_pos loi_attn_ds_lt_one
                 (id_refl : Id (minus one delta_star)
                               (minus one delta_star))
                 Htvnn (lt_le_iff zero budget (inl Hbudget)) HN).
  exists (projT1 Hp). split.
  - apply (le_lt_trans _
             (mult (r_pow (minus one delta_star) (projT1 Hp)) (tv mu nu))
             budget).
    + exact (bounded_softmax_tv_iter enum enum_nonempty temp temp_pos
               Delta Delta_pos z z_lb z_ub expf expf_pos expf_zero
               expf_plus expf_mono_lt expf_mono_le bs_swap bs_abs bs_lpc
               sum_eq_list (projT1 Hp) mu nu Hmu Hnu).
    + exact (projT2 Hp).
  - exact HN.
Defined.

(* ---------- (7) The exact four-fold law on the attention kernel ---------- *)
(* With TV0 := tv mu nu and budget fixed: ub(lo/2) == 4 * ub(lo) (Id).       *)
Theorem loi_attention_halving_quad :
  forall (mu nu : S -> R) (budget : R) (Hbudget : lt zero budget),
  Id (mult (tv mu nu)
         (inv_pos (mult (mult lo_half_star lo_half_star) budget)
                  (mult_positive (mult lo_half_star lo_half_star) budget
                     Hds2s0 Hbudget)))
     (mult four
        (mult (tv mu nu)
           (inv_pos (mult delta_star budget)
              (mult_positive delta_star budget ds_star_pos Hbudget)))).
Proof.
  intros mu nu budget Hbudget.
  exact (loi_ub2_quad (tv mu nu) budget Hbudget lo Hlo0).
Defined.

(* ---------- (8) The Part A main theorem fully instantiated at the attention TV0/lo ---------- *)
Theorem loi_attention_inflation_half :
  forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  forall (budget : R) (Hbudget : lt zero budget),
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
  sigT (fun k1 : nat =>
    sigT (fun k2 : nat =>
      And (lt (mult (r_pow (minus one delta_star) k1) (tv mu nu)) budget)
        (And (lt (mult (r_pow (minus one (mult lo_half_star lo_half_star)) k2)
                     (tv mu nu)) budget)
             (lt (mult four
                    (mult (tv mu nu)
                       (inv_pos (mult delta_star budget)
                          (mult_positive delta_star budget ds_star_pos
                             Hbudget))))
                 (ums_scale k2 one))))).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch.
  exact (loi_lo_inflation bs_lpc (tv mu nu) (tv_dist_nonneg mu nu)
           budget Hbudget lo Hlo0 loi_attn_ds_lt_one Harch).
Defined.

End LoInflationAttn.

(* ============================================================ *)
(* Assumption audit (one line per theorem; all expected Closed)  *)
(* ============================================================ *)

Print Assumptions loi_ds2_scale.
Print Assumptions loi_ub2_quad.
Print Assumptions loi_lo_inflation.
Print Assumptions loi_ub_antitone.
Print Assumptions loi_attention_inflation.
Print Assumptions loi_attention_halving_quad.
Print Assumptions loi_attention_inflation_half.
