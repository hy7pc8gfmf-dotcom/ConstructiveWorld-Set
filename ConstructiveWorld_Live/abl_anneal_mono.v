(* ==========================================================================)
   abl_anneal_mono
   Mission. Static annealing preamble on the attention temperature
     face (checklist A2): delta*(T) := exp(-2*Delta/T) is monotone in
     positive temperature T; the factor rate(T) := 1 - delta*(T) is
     antitone in T; budget transport closes constructively: k steps
     of the static bound rate(T)^k * TV0 <= budget at the cold end T
     witness the same bound at every warm end T' >= T (le form and
     sigT form).  A Part 2 mirror restates the core over a free expf
     interface, slot-compatible with the host softmax instance
     (lo := expf(invT * (-Delta)), delta* := lo*lo).
   Dependencies. S01_BaseRing (RealInterfaceEnhanced: the exp_neg_*
     monotone field family, inv_pos_le_compat, the positivity and
     multiplication fields, the le/lt core lemmas, the Id core
     id_sym/id_trans/id_cong/opp_mult_l); S04_RealExpLogConv
     (Fixpoint r_pow, RI-generic).
   References. Attention temperature face A2, open item 4; host
     anchor AttnDoeblin BoundedSoftmax (delta* := lo*lo =
     exp(-2*Delta/T)); S01 temp_factor_antitone is the orthogonal
     fixed-T face (here Delta is fixed and T varies).
   Constructivity. Statement faces are Set-carried (interface le/lt
     predicates, sigT existence, no or/exists/Not carriers); proofs
     are term-mode assemblies (two nat inductions use induction/
     simpl, zero rewrite); monotonicity data come from
     instance-supplied interface fields; every proof ends in Qed.
   Build. rocq c -native-compiler no -q -Q . "" abl_anneal_mono.v
     (Rocq 9.1 toolchain, thermal-guard wrapped; world = the
     S01_BaseRing and S04_RealExpLogConv .vo pool in this directory).
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S04_RealExpLogConv.

(* ============================================================ *)
(* Part 1. The fixed-Delta face: temperature-monotone core of        *)
(*   delta*(T) := exp(-2*Delta/T) and the step-budget transport.     *)
(*   The temperature carrier T follows the host convention: the      *)
(*   abstract R layer of RealInterfaceEnhanced (same Section         *)
(*   variable discipline as AttnDoeblin BoundedSoftmax).             *)
(* ============================================================ *)

Section AnmAnnealMono.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.

Variable Delta : R.
Variable Delta_pos : lt zero Delta.

(* Explicit c := 2*Delta: doubling of the logit diameter (bs_lo_hi_eq algebra face). *)
Definition anm_two_Delta : R := plus Delta Delta.

(* delta*(T) := exp(-2*Delta/T): the Doeblin contraction rate
   (minorization gap).  Value-wise the same object as the AttnDoeblin
   anchor delta_star := lo*lo = exp(-2*Delta/T): carried directly by
   exp_neg, with the monotonicity datum supplied by the interface
   field exp_neg_le_decr, same standing as the host expf_mono_le
   field. *)
Definition anm_dst (T : R) (HT : lt zero T) : R :=
  exp_neg (mult anm_two_Delta (inv_pos T HT)).

(* Contraction factor rate(T) := 1 - delta*(T): the per-step multiplier of the iterated TV bound. *)
Definition anm_rate (T : R) (HT : lt zero T) : R :=
  minus one (anm_dst T HT).

(* Certificates that 2*Delta is > 0 and >= 0. *)
Lemma anm_two_Delta_pos : lt zero anm_two_Delta.
Proof. exact (plus_positive Delta Delta Delta_pos Delta_pos). Qed.

Lemma anm_two_Delta_nonneg : le zero anm_two_Delta.
Proof. exact (lt_le_iff zero anm_two_Delta (inl anm_two_Delta_pos)). Qed.

(* Reciprocal antitone in positive temperature (direct drop of the inv_pos_le_compat
   interface field; zero Qinv positions, the BH pitfall is untouched). *)
Lemma anm_inv_antitone : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> le (inv_pos T' HT') (inv_pos T HT).
Proof.
  intros T T' HT HT' Hle.
  exact (inv_pos_le_compat T T' HT HT' Hle).
Qed.

(* ===== ANM-1 core: delta*(T) is monotone in T (temperature down
   => delta* down). =====
   Chain: T <= T' => 1/T' <= 1/T (reciprocal antitone) => 2*Delta/T'
   <= 2*Delta/T (multiplication by a nonnegative factor) =>
   exp(-2*Delta/T) <= exp(-2*Delta/T') (exp_neg_le_decr antitone).
   Nontrivial: the negative-exponent turn passes through two levels,
   reciprocal antitone and exp antitone; first item of checklist A2. *)
Theorem anm_dst_mono : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> le (anm_dst T HT) (anm_dst T' HT').
Proof.
  intros T T' HT HT' Hle. unfold anm_dst.
  exact (exp_neg_le_decr (mult anm_two_Delta (inv_pos T' HT'))
                         (mult anm_two_Delta (inv_pos T HT))
           (le_mult_compat_r anm_two_Delta (inv_pos T' HT') (inv_pos T HT)
              anm_two_Delta_nonneg (anm_inv_antitone T T' HT HT' Hle))).
Qed.

(* Positivity of delta* (exp is strictly positive). *)
Lemma anm_dst_pos : forall (T : R) (HT : lt zero T), lt zero (anm_dst T HT).
Proof.
  intros T HT. unfold anm_dst.
  exact (exp_neg_pos (mult anm_two_Delta (inv_pos T HT))).
Qed.

(* The exponential argument 2*Delta/T is strictly positive. *)
Lemma anm_exp_arg_pos : forall (T : R) (HT : lt zero T),
  lt zero (mult anm_two_Delta (inv_pos T HT)).
Proof.
  intros T HT.
  exact (mult_positive anm_two_Delta (inv_pos T HT)
           anm_two_Delta_pos (inv_pos_pos T HT)).
Qed.

(* delta* < 1: exp(-x) < exp(0) = 1 for x > 0 (strict exp_neg_decr plus exp_neg_zero). *)
Lemma anm_dst_lt_one : forall (T : R) (HT : lt zero T), lt (anm_dst T HT) one.
Proof.
  intros T HT. unfold anm_dst.
  exact (lt_id_r (exp_neg (mult anm_two_Delta (inv_pos T HT)))
                 (exp_neg zero) one exp_neg_zero
           (exp_neg_decr zero (mult anm_two_Delta (inv_pos T HT))
              (anm_exp_arg_pos T HT))).
Qed.

Lemma anm_dst_le_one : forall (T : R) (HT : lt zero T), le (anm_dst T HT) one.
Proof.
  intros T HT.
  exact (lt_le_iff (anm_dst T HT) one (inl (anm_dst_lt_one T HT))).
Qed.

(* rate(T) = 1 - delta*(T) >= 0: from delta* <= 1 via the opp
   antitone plus additive weak compatibility.  Note: the strict form
   0 < rate would need a strict-from-weak additive generator, a
   structural wall registered in the S04 wall family (same class as
   RW-MIX); the static face of this file needs only the weak form,
   so the wall is not used. *)
Lemma anm_rate_nonneg : forall (T : R) (HT : lt zero T), le zero (anm_rate T HT).
Proof.
  intros T HT. unfold anm_rate, minus.
  exact (le_id_l zero (plus one (opp one)) (plus one (opp (anm_dst T HT)))
           (id_sym (plus_opp one))
           (le_plus_compat one one (opp one) (opp (anm_dst T HT))
              (le_refl one)
              (opp_le_compat (anm_dst T HT) one (anm_dst_le_one T HT)))).
Qed.

(* ===== ANM-2: rate is antitone in T. =====
   T <= T' => delta*(T) <= delta*(T') (ANM-1) => 1 - delta*(T') <=
   1 - delta*(T): the warm end has the smaller contraction factor
   (contracts faster); temperature up => the static face of the step
   demand goes down. *)
Theorem anm_rate_antitone : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> le (anm_rate T' HT') (anm_rate T HT).
Proof.
  intros T T' HT HT' Hle. unfold anm_rate, minus.
  exact (le_plus_compat one one (opp (anm_dst T' HT')) (opp (anm_dst T HT))
           (le_refl one)
           (opp_le_compat (anm_dst T HT) (anm_dst T' HT')
              (anm_dst_mono T T' HT HT' Hle))).
Qed.

(* Powers are nonnegative (0 <= r => (r)^n >= 0; S04 r_pow convention, weak form self-contained, wall-free). *)
Lemma anm_rpow_nonneg : forall (r : R), le zero r ->
  forall n : nat, le zero (r_pow r n).
Proof.
  intros r Hr n. induction n as [| m IH].
  - simpl. exact (lt_le_iff zero one (inl one_pos)).
  - simpl.
    exact (le_id_l zero (mult r zero) (mult r (r_pow r m))
             (id_sym (mult_zero r))
             (le_mult_compat_r r zero (r_pow r m) Hr IH)).
Qed.

(* ===== ANM-3: powers are monotone (0 <= r <= s => r^n <= s^n).
   ===== Two-leg transitivity: left multiplication compatibility
   (le_mult_compat_r) plus right weak compatibility
   (le_mult_compat_weak, nonnegative multiplier in the third slot);
   a single induction. *)
Lemma anm_rpow_mono : forall (r s : R), le zero r -> le r s ->
  forall n : nat, le (r_pow r n) (r_pow s n).
Proof.
  intros r s Hr Hrs n. induction n as [| m IH].
  - simpl. exact (le_refl one).
  - simpl.
    exact (le_trans (mult r (r_pow r m)) (mult r (r_pow s m))
                    (mult s (r_pow s m))
              (le_mult_compat_r r (r_pow r m) (r_pow s m) Hr IH)
              (le_mult_compat_weak r s (r_pow s m)
                 (anm_rpow_nonneg s (le_trans zero r s Hr Hrs) m) Hrs)).
Qed.

(* ===== ANM-4: the contraction-factor power is antitone in T.
   ===== T <= T' => rate(T')^k <= rate(T)^k: at equal step counts
   the warm end gives the tighter TV bound. *)
Theorem anm_rate_pow_antitone : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> forall k : nat,
  le (r_pow (anm_rate T' HT') k) (r_pow (anm_rate T HT) k).
Proof.
  intros T T' HT HT' Hle k.
  exact (anm_rpow_mono (anm_rate T' HT') (anm_rate T HT)
                       (anm_rate_nonneg T' HT')
                       (anm_rate_antitone T T' HT HT' Hle) k).
Qed.

(* ===== ANM-5 linking piece, static step face (budget transport).
   ===== If the k-step static bound at the cold end T closes the
   budget, the same k closes it at every warm end T' >= T.  Chain:
   rate(T')^k <= rate(T)^k (ANM-4) => order kept when multiplying by
   TV0 (>= 0) => transitivity.  Reading: along the cooling direction
   (T down) delta* goes down and rate goes up, so the original budget
   fails: the static preorder says temperature down => steps up.
   Along the warming direction the budget is conserved: the static
   antitone face of k in T. *)
Theorem anm_budget_transport : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> forall (TV0 budget : R), le zero TV0 -> forall k : nat,
  le (mult (r_pow (anm_rate T HT) k) TV0) budget ->
  le (mult (r_pow (anm_rate T' HT') k) TV0) budget.
Proof.
  intros T T' HT HT' Hle TV0 budget HTV0 k Hk.
  exact (le_trans (mult (r_pow (anm_rate T' HT') k) TV0)
                  (mult (r_pow (anm_rate T HT) k) TV0) budget
            (le_id_l (mult (r_pow (anm_rate T' HT') k) TV0)
                     (mult TV0 (r_pow (anm_rate T' HT') k))
                     (mult (r_pow (anm_rate T HT) k) TV0)
               (mult_comm (r_pow (anm_rate T' HT') k) TV0)
               (le_id_r (mult TV0 (r_pow (anm_rate T' HT') k))
                        (mult TV0 (r_pow (anm_rate T HT) k))
                        (mult (r_pow (anm_rate T HT) k) TV0)
                  (mult_comm TV0 (r_pow (anm_rate T HT) k))
                  (le_mult_compat_r TV0 (r_pow (anm_rate T' HT') k)
                                    (r_pow (anm_rate T HT) k) HTV0
                     (anm_rate_pow_antitone T T' HT HT' Hle k))))
            Hk).
Qed.

(* ===== ANM-6 sigT form (the "there is a monotone upper bound k"
   shape, the constructive closure planned by open item 4 of the A2
   section report). =====
   A cold-end witness of k steps closing the budget yields a warm-end
   witness with the same k: Set-level existential transport with zero
   use of any k_select chooser. *)
Theorem anm_budget_transport_sigT : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> forall (TV0 budget : R), le zero TV0 ->
  sigT (fun k : nat => le (mult (r_pow (anm_rate T HT) k) TV0) budget) ->
  sigT (fun k : nat => le (mult (r_pow (anm_rate T' HT') k) TV0) budget).
Proof.
  intros T T' HT HT' Hle TV0 budget HTV0 Hwit. destruct Hwit as [k Hk].
  exact (existT (fun k : nat => le (mult (r_pow (anm_rate T' HT') k) TV0) budget)
                k (anm_budget_transport T T' HT HT' Hle TV0 budget HTV0 k Hk)).
Qed.

End AnmAnnealMono.

(* ============================================================ *)
(* Part 2. Slot-for-slot mirror over the host expf interface: the    *)
(*   AttnDoeblin drop-in twin.  anm_e_lo(T) := expf(invT * (-Delta)) *)
(*   is lo with T as an explicit argument, matching the host lo :=   *)
(*   expf(mult invT (opp Delta)); anm_e_dst(T) := lo*lo matches the  *)
(*   host delta_star shape.  Instantiating T := temp and supplying   *)
(*   the five expf fields slot by slot yields literally the host     *)
(*   bs_delta_star (the match is a single substitution).             *)
(* ============================================================ *)

Section AnmExpfMirror.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.

Variable Delta : R.
Variable Delta_pos : lt zero Delta.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).

(* lo with T as an explicit argument: exp(-Delta/T) (host slot-for-slot:
   mult invT (opp Delta), argument order preserved). *)
Definition anm_e_lo (T : R) (HT : lt zero T) : R :=
  expf (mult (inv_pos T HT) (opp Delta)).

(* delta* := lo*lo (the host delta_star shape). *)
Definition anm_e_dst (T : R) (HT : lt zero T) : R :=
  mult (anm_e_lo T HT) (anm_e_lo T HT).

Lemma anm_e_lo_pos : forall (T : R) (HT : lt zero T), lt zero (anm_e_lo T HT).
Proof.
  intros T HT. exact (expf_pos (mult (inv_pos T HT) (opp Delta))).
Qed.

(* Turn identity: invT * (-Delta) = -(Delta * invT) (one hop opp_mult_l plus one hop mult_comm). *)
Lemma anm_e_lo_idform : forall (T : R) (HT : lt zero T),
  Id (mult (inv_pos T HT) (opp Delta)) (opp (mult Delta (inv_pos T HT))).
Proof.
  intros T HT.
  exact (id_trans (opp_mult_l (inv_pos T HT) Delta)
                  (id_cong opp (mult_comm (inv_pos T HT) Delta))).
Qed.

(* ===== ANM-7: lo(T) = exp(-Delta/T) is monotone in T (the expf
   version of the anchor-shaped core). =====
   Chain: reciprocal antitone => Delta/T' <= Delta/T (multiply by the
   positive Delta) => opp turn => invT*(-Delta) <= invT'*(-Delta) =>
   expf_mono_le.  The negative-factor turn is carried by
   opp_le_compat plus Id reasoning steps. *)
Theorem anm_e_lo_mono : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> le (anm_e_lo T HT) (anm_e_lo T' HT').
Proof.
  intros T T' HT HT' Hle. unfold anm_e_lo.
  exact (expf_mono_le (mult (inv_pos T HT) (opp Delta))
                      (mult (inv_pos T' HT') (opp Delta))
           (le_id_l (mult (inv_pos T HT) (opp Delta))
                    (opp (mult Delta (inv_pos T HT)))
                    (mult (inv_pos T' HT') (opp Delta))
              (anm_e_lo_idform T HT)
              (le_id_r (opp (mult Delta (inv_pos T HT)))
                       (opp (mult Delta (inv_pos T' HT')))
                       (mult (inv_pos T' HT') (opp Delta))
                 (id_sym (anm_e_lo_idform T' HT'))
                 (opp_le_compat (mult Delta (inv_pos T' HT'))
                                (mult Delta (inv_pos T HT))
                   (le_mult_compat_r Delta (inv_pos T' HT') (inv_pos T HT)
                      (lt_le_iff zero Delta (inl Delta_pos))
                      (anm_inv_antitone T T' HT HT' Hle)))))).
Qed.

(* ===== ANM-8: delta* := lo*lo is monotone in T (the monotone piece in the host delta_star shape). ===== *)
Theorem anm_e_dst_mono : forall (T T' : R) (HT : lt zero T) (HT' : lt zero T'),
  le T T' -> le (anm_e_dst T HT) (anm_e_dst T' HT').
Proof.
  intros T T' HT HT' Hle. unfold anm_e_dst.
  exact (le_trans (mult (anm_e_lo T HT) (anm_e_lo T HT))
                  (mult (anm_e_lo T HT) (anm_e_lo T' HT'))
                  (mult (anm_e_lo T' HT') (anm_e_lo T' HT'))
            (le_mult_compat_r (anm_e_lo T HT) (anm_e_lo T HT)
                              (anm_e_lo T' HT')
               (lt_le_iff zero (anm_e_lo T HT) (inl (anm_e_lo_pos T HT)))
               (anm_e_lo_mono T T' HT HT' Hle))
            (le_id_l (mult (anm_e_lo T HT) (anm_e_lo T' HT'))
                     (mult (anm_e_lo T' HT') (anm_e_lo T HT))
                     (mult (anm_e_lo T' HT') (anm_e_lo T' HT'))
               (mult_comm (anm_e_lo T HT) (anm_e_lo T' HT'))
               (le_mult_compat_r (anm_e_lo T' HT') (anm_e_lo T HT)
                                 (anm_e_lo T' HT')
                  (lt_le_iff zero (anm_e_lo T' HT')
                                (inl (anm_e_lo_pos T' HT')))
                  (anm_e_lo_mono T T' HT HT' Hle)))).
Qed.

End AnmExpfMirror.

(* ============================================================ *)
(* Audit block (per-station Print Assumptions; expected all Closed:  *)
(*   zero new assumptions).                                          *)
(* ============================================================ *)

Print Assumptions anm_inv_antitone.
Print Assumptions anm_dst_mono.
Print Assumptions anm_dst_pos.
Print Assumptions anm_exp_arg_pos.
Print Assumptions anm_dst_lt_one.
Print Assumptions anm_dst_le_one.
Print Assumptions anm_rate_nonneg.
Print Assumptions anm_rate_antitone.
Print Assumptions anm_rpow_nonneg.
Print Assumptions anm_rpow_mono.
Print Assumptions anm_rate_pow_antitone.
Print Assumptions anm_budget_transport.
Print Assumptions anm_budget_transport_sigT.
Print Assumptions anm_e_lo_pos.
Print Assumptions anm_e_lo_idform.
Print Assumptions anm_e_lo_mono.
Print Assumptions anm_e_dst_mono.

(* ============================================================ *)
(* Red-line forensics block (four items, item by item).              *)
(* 1. Zero Prop carriers at Set level: every statement predicate is  *)
(*    the Set-valued le/lt of RealInterface; existence uses sigT     *)
(*    (ANM-6); no or/exists/Not carrier statements (the custom S01   *)
(*    Set-level Or appears only as an inl proof entrance).           *)
(* 2. Nontriviality: ANM-1 negative-exponent two-level turn chain    *)
(*    (reciprocal antitone x exp antitone); ANM-5/6 power antitone x *)
(*    budget transport chain; ANM-7 negative-factor multiplication   *)
(*    turn via Id reasoning steps: all are multi-leg constructions,  *)
(*    not restatements of library pieces (S01 temp_factor_antitone   *)
(*    is the fixed-T loss-comparison axis; this file is the          *)
(*    fixed-Delta temperature axis: orthogonal).                     *)
(* 3. Extractability: statements are all Set-typed, zero Obj.magic,  *)
(*    zero vm_compute; the disjunctive face is all Closed (the       *)
(*    seventeen Print Assumptions stations above).                   *)
(* 4. Zero assumptions, zero admission literals: the full admission  *)
(*    and classical-logic word list greps clean; every PA station is *)
(*    Closed under the global context.                               *)
(* ============================================================ *)
