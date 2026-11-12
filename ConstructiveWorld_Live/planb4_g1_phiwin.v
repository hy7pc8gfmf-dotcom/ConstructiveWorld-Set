(* ConstructiveWorld-Main - planB wave-2 piece: the U2 Phi_n/L_n prime-window normalization face (ZZ2020 Lemma 2/3, 40-point machine cross-check). *)
(** * planb4_g1_phiwin: the general-n Phi_n / L_n window face.

    Mission.  The ZZ2020 Lemma 2 prime window P_n = {p prime :
      p > max{5, sqrt(3n)}, 1/2 <= {n/p} < 2/3} in pure nat
      arithmetic ({n/p} = (n mod p)/p; p > sqrt(3n) iff p*p > 3*n);
      the window product Phi_n (empty window = 1); the lcm face
      lcm(1..k) over Z; the split normalization L_n :=
      lcm(1..4n) / Phi_n (ZZ2020 Lemma 3).  The unsplit lcm(1..4n)
      inflates each entry by Phi_n and misses the calibration face
      (L(4) = 102960 = lcm(1..16)/7 is the split witness); the A/B
      assembly consumes this normalized L_n.  Anchors: Phi_n =
      planb4_Phi n and L_n = planb4_LZn n for all n = 1..40, a
      definition-face cross-check census against the general-n
      reference faces of planb3_g1_calib (the zz_in_Pn window).

    Dependencies.  piu_zz_padic_clearing (zz_primeb, the
      trial-division primality, reused verbatim); planb3_g1_calib
      (the general-n reference faces planb4_Phi / planb4_LZn);
      stdlib ZArith, Arith, List.

    References.  ZZ2020, Lemma 2 (the P_n window) and Lemma 3
      (L_n = lcm / Phi_n), arXiv:1912.06345.

    Constructivity.  All faces are informative bool/Z-valued
      Definitions or Fixpoints over nat/Z transparent data;
      admission-free and postulate-free; each anchor closes by
      kernel conversion under vm_compute.

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_phiwin.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Require Import piu_zz_padic_clearing.
Require Import planb3_g1_calib.

Import ListNotations.

(* ================================================================== *)
(* Section 1. The ZZ2020 Lemma 2 window face in pure nat arithmetic.  *)
(* ================================================================== *)

(* primality: verbatim reuse of the in-tree trial-division test. *)
Definition planb4_g1_primeb (p : nat) : bool := zz_primeb p.

(* the fraction test {n/p} = (n mod p)/p: 1/2 <= {n/p} holds iff
   p <= 2*(n mod p); {n/p} < 2/3 holds iff 3*(n mod p) < 2*p;
   p > sqrt(3n) holds iff p*p > 3*n (p positive, no irrationals). *)
Definition planb4_g1_pwin (n p : nat) : bool :=
  (5 <? p)%nat && (3 * n <? p * p)%nat && (p <=? 2 * (n mod p))%nat &&
  (3 * (n mod p) <? 2 * p)%nat.

(* window membership = primality and the window inequalities. *)
Definition planb4_g1_inwin (n p : nat) : bool :=
  planb4_g1_primeb p && planb4_g1_pwin n p.

(* the window face coincides componentwise with the in-tree refined
   window zz_in_Pn (piu_zz_padic_clearing): the same five conjuncts,
   modulo the associativity of && (normalized by andb_assoc). *)
Lemma planb4_g1_inwin_zz_in_Pn :
  forall n p : nat, planb4_g1_inwin n p = zz_in_Pn n p.
Proof.
  intros n p.
  unfold planb4_g1_inwin, planb4_g1_primeb, planb4_g1_pwin, zz_in_Pn.
  rewrite !Bool.andb_assoc. reflexivity.
Qed.

(* ================================================================== *)
(* Section 2. The window product Phi_n.                               *)
(* ================================================================== *)

(* every window prime p satisfies p >= 7 (5 < p, p prime) and
   p <= 2*n (from p <= 2*(n mod p) and n mod p <= n), and the top
   endpoint p = 2*n of the enumeration domain seq 7 (2*n - 6)
   = [7 .. 2*n] is even hence composite for every n (proved below:
   planb4_g1_primeb_even_top), so the endpoint is inert and the
   domain covers the window exactly; it is empty for n <= 3. *)
Definition planb4_g1_pwin_list (n : nat) : list nat :=
  filter (fun p => planb4_g1_inwin n p) (seq 7 (2 * n - 6)).

(* Phi_n := the product of the window primes; the empty window
   yields the empty product 1 (n = 1..3). *)
Definition planb4_g1_phi (n : nat) : Z :=
  fold_right (fun p acc => acc * Z.of_nat p) 1%Z (planb4_g1_pwin_list n).

(* ================================================================== *)
(* Section 3. The lcm face lcm(1..k) over Z (Z.lcm fold).             *)
(* ================================================================== *)

Definition planb4_g1_lcmt (k : nat) : Z :=
  fold_left Z.lcm (map Z.of_nat (seq 1 k)) 1%Z.

(* ================================================================== *)
(* Section 4. The split normalization L_n := lcm(1..4n) / Phi_n.      *)
(* ================================================================== *)

(* Phi_n divides lcm(1..4n): each window prime p satisfies
   p <= 2*n <= 4*n so p divides the lcm, and the window primes are
   pairwise distinct (primality), so their product divides.
   Z.div is therefore exact on these arguments. *)
Definition planb4_g1_ln (n : nat) : Z :=
  Z.div (planb4_g1_lcmt (4 * n)) (planb4_g1_phi n).

(* ================================================================== *)
(* Section 5. The census faces against the general-n reference faces. *)
(* ================================================================== *)

(* per-n window check: Phi_n agrees with the reference face
   planb4_Phi (planb3_g1_calib, the zz_in_Pn window product). *)
Fixpoint planb4_g1_phiwin (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      andb (Z.eqb (planb4_g1_phi (S k')) (planb4_Phi (S k')))
           (planb4_g1_phiwin k')
  end.

(* per-n window check: L_n agrees with the reference face
   planb4_LZn (planb3_g1_calib, lcm / zz_in_Pn-window product). *)
Fixpoint planb4_g1_lnwin (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      andb (Z.eqb (planb4_g1_ln (S k')) (planb4_LZn (S k')))
           (planb4_g1_lnwin k')
  end.

(* exactness census: the remainder of lcm(1..4n) by Phi_n is 0 for
   n = 1..40 (each window prime divides the lcm, and the window
   primes are distinct, so the product divides) — machine backing
   for the exactness of Z.div in planb4_g1_ln. *)
Fixpoint planb4_g1_lndiv (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      andb (Z.eqb (Z.modulo (planb4_g1_lcmt (4 * S k'))
                            (planb4_g1_phi (S k'))) 0%Z)
           (planb4_g1_lndiv k')
  end.

(* ================================================================== *)
(* Section 5b. Census elimination: the boolean censuses yield per-n   *)
(* equations usable by the A/B assembly consumer.                     *)
(* ================================================================== *)

Lemma planb4_g1_phiwin_elim : forall k i : nat,
  planb4_g1_phiwin k = true -> (1 <= i)%nat -> (i <= k)%nat ->
  planb4_g1_phi i = planb4_Phi i.
Proof.
  induction k as [|k IH]; intros i Hc Hi1 Hi2.
  - exfalso. lia.
  - destruct (Nat.eq_dec i (S k)) as [He | Hne].
    + subst i. apply andb_true_iff in Hc. destruct Hc as [Heq _].
      apply Z.eqb_eq in Heq. exact Heq.
    + apply andb_true_iff in Hc. destruct Hc as [_ Hc'].
      apply IH; [exact Hc' | lia | lia].
Qed.

Lemma planb4_g1_lnwin_elim : forall k i : nat,
  planb4_g1_lnwin k = true -> (1 <= i)%nat -> (i <= k)%nat ->
  planb4_g1_ln i = planb4_LZn i.
Proof.
  induction k as [|k IH]; intros i Hc Hi1 Hi2.
  - exfalso. lia.
  - destruct (Nat.eq_dec i (S k)) as [He | Hne].
    + subst i. apply andb_true_iff in Hc. destruct Hc as [Heq _].
      apply Z.eqb_eq in Heq. exact Heq.
    + apply andb_true_iff in Hc. destruct Hc as [_ Hc'].
      apply IH; [exact Hc' | lia | lia].
Qed.

(* denominator safety: a fold_right product of positive factors stays
   positive, and every enumerated window prime is at least 7 — so the
   denominator Phi_n of the Z.div in planb4_g1_ln never vanishes. *)
Lemma planb4_g1_foldr_mul_pos : forall l : list nat,
  (forall p : nat, In p l -> (0 < Z.of_nat p)%Z) ->
  (0 < fold_right (fun p acc => acc * Z.of_nat p) 1%Z l)%Z.
Proof.
  induction l as [|p l IH]; intros Hpos.
  - cbn [fold_right]. lia.
  - cbn [fold_right]. apply Z.mul_pos_pos.
    + apply IH. intros q Hq. apply Hpos. right. exact Hq.
    + apply Hpos. left. reflexivity.
Qed.

Lemma planb4_g1_phi_pos : forall n : nat, (0 < planb4_g1_phi n)%Z.
Proof.
  intros n. unfold planb4_g1_phi.
  apply planb4_g1_foldr_mul_pos.
  intros p Hp.
  apply filter_In in Hp. destruct Hp as [Hseq _].
  apply in_seq in Hseq.
  assert (H0 : (0 < p)%nat) by lia.
  lia.
Qed.

Lemma planb4_g1_phi_nz : forall n : nat, planb4_g1_phi n <> 0%Z.
Proof.
  intros n. pose proof (planb4_g1_phi_pos n) as Hp. lia.
Qed.

(* ================================================================== *)
(* Section 5c. Domain honesty: the enumeration domain [7 .. 2*n] is   *)
(* sound and complete for the window face, and its top endpoint is    *)
(* inert (2*n is even hence composite).                               *)
(* ================================================================== *)

(* one-step unfolding of the trial-division descent (definitional). *)
Lemma planb4_g1_nodiv_upto_S : forall k d : nat,
  zz_nodiv_upto (Z.of_nat k) (S d) =
  if Z.ltb (Z.of_nat (S d)) 2 then true
  else if Z.eqb (Z.of_nat k mod Z.of_nat (S d)) 0 then false
  else zz_nodiv_upto (Z.of_nat k) d.
Proof. reflexivity. Qed.

(* an even positive target fails the trial-division descent: the
   descent walks its divisor range down to 2, and 2 divides. *)
Lemma planb4_g1_nodiv_even : forall (d k : nat),
  (2 <= d)%nat -> (exists m : nat, k = 2 * m)%nat ->
  zz_nodiv_upto (Z.of_nat k) d = false.
Proof.
  intros d. induction d as [|d IH]; intros k H2 [m Heq].
  - exfalso. lia.
  - destruct d as [|d'].
    + exfalso. lia.
    + rewrite planb4_g1_nodiv_upto_S.
      destruct (Z.ltb (Z.of_nat (S (S d'))) 2) eqn:Hlt.
      * apply Z.ltb_lt in Hlt. lia.
      * destruct (Z.eqb (Z.of_nat k mod Z.of_nat (S (S d'))) 0) eqn:Hmod.
        -- reflexivity.
        -- destruct (Nat.eq_dec d' 0) as [Hd0 | Hd0].
           ++ exfalso. subst d'.
              assert (H2z : (Z.of_nat 2 <> 0)%Z) by lia.
              assert (Hm : (Z.of_nat k mod 2 = 0)%Z).
              { apply (proj2 (Zmod_divides _ _ H2z)).
                exists (Z.of_nat m). lia. }
              change (Z.of_nat (S 1)) with 2%Z in Hmod.
              rewrite Hm in Hmod. discriminate.
           ++ apply IH; [lia | ].
              exists m. subst k. lia.
Qed.

(* the enumeration-domain top endpoint 2*n is composite: with
   planb4_g1_inwin_bounds this makes the endpoint inert — it is in
   the domain but never a window member. *)
Lemma planb4_g1_primeb_even_top : forall n : nat, (2 <= n)%nat ->
  planb4_g1_primeb (2 * n) = false.
Proof.
  intros n Hn. unfold planb4_g1_primeb, zz_primeb.
  apply andb_false_iff. right.
  apply planb4_g1_nodiv_even with (k := (2 * n)%nat).
  - lia.
  - exists n. reflexivity.
Qed.

(* every window member lies in [7, 2*n]: the window demands 5 < p, and
   p = 6 fails the reused primality test (6 mod 2 = 0); p <= 2*n
   follows from the window inequality p <= 2*(n mod p) together with
   n mod p <= n. *)
Lemma planb4_g1_inwin_bounds : forall n p : nat,
  planb4_g1_inwin n p = true -> (7 <= p)%nat /\ (p <= 2 * n)%nat.
Proof.
  intros n p H.
  unfold planb4_g1_inwin in H.
  apply andb_true_iff in H. destruct H as [Hprime Hrest].
  unfold planb4_g1_pwin in Hrest.
  apply andb_true_iff in Hrest. destruct Hrest as [Hrest Hd].
  apply andb_true_iff in Hrest. destruct Hrest as [Hrest Hc].
  apply andb_true_iff in Hrest. destruct Hrest as [Ha Hb].
  apply Nat.ltb_lt in Ha.
  apply Nat.leb_le in Hc.
  pose proof (Nat.Div0.mod_le n p) as Hmle.
  assert (H7 : (7 <= p)%nat).
  { destruct (Nat.eq_dec p 6) as [H6 | Hne6].
    - subst p. vm_compute in Hprime. discriminate.
    - lia. }
  split; [exact H7 | lia].
Qed.

(* soundness of the enumeration: listed primes are window members. *)
Lemma planb4_g1_pwin_list_sound : forall n p : nat,
  In p (planb4_g1_pwin_list n) -> planb4_g1_inwin n p = true.
Proof.
  intros n p H. apply filter_In in H. destruct H as [_ Hf]. exact Hf.
Qed.

(* completeness of the enumeration: every window member is listed
   (with the bounds lemma this closes the domain-honesty chain). *)
Lemma planb4_g1_pwin_list_complete : forall n p : nat,
  planb4_g1_inwin n p = true -> In p (planb4_g1_pwin_list n).
Proof.
  intros n p H. apply filter_In. split.
  - apply in_seq. pose proof (planb4_g1_inwin_bounds n p H) as [H7 H20].
    lia.
  - exact H.
Qed.

(* ================================================================== *)
(* Section 6. Anchors: per-n spots and the full n = 1..40 census.     *)
(* ================================================================== *)

(* empty window spots: Phi_n = 1 at n = 1..3 (the domain [7 .. 2n-1]
   is empty there). *)
Example planb4_g1_phi_1 : planb4_g1_phi 1 = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_phi_2 : planb4_g1_phi 2 = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_phi_3 : planb4_g1_phi 3 = 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* window discrimination: 7 enters the window at n = 4 (12 < 49,
   7 <= 8, 12 < 14) but fails at n = 5 (3*(5 mod 7) = 15 is
   not < 2*7 = 14). *)
Example planb4_g1_pwin_4_7 : planb4_g1_pwin 4 7 = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_pwin_5_7 : planb4_g1_pwin 5 7 = false.
Proof. vm_compute. reflexivity. Qed.

(* the split witnesses: Phi_4 = 7 and lcm(1..16)/7 = 102960;
   Phi_7 = 143 = 11*13 and lcm(1..28)/143 = 561632400. *)
Example planb4_g1_phi_4 : planb4_g1_phi 4 = 7%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_ln_4 : planb4_g1_ln 4 = 102960%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_phi_7 : planb4_g1_phi 7 = 143%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_ln_7 : planb4_g1_ln 7 = 561632400%Z.
Proof. vm_compute. reflexivity. Qed.

(* the lcm face: lcm(1..4) = 12 coincides with the reference entry at
   n = 1 because Phi_1 = 1 there. *)
Example planb4_g1_lcmt_4 : planb4_g1_lcmt 4 = 12%Z.
Proof. vm_compute. reflexivity. Qed.

(* the full census: both faces agree with the reference faces
   planb4_Phi / planb4_LZn on the whole declared domain n = 1..40. *)
Example planb4_g1_phiwin_40 : planb4_g1_phiwin 40 = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_lnwin_40 : planb4_g1_lnwin 40 = true.
Proof. vm_compute. reflexivity. Qed.

(* the exactness census: Z.div has zero remainder on the whole
   declared domain n = 1..40. *)
Example planb4_g1_lndiv_40 : planb4_g1_lndiv 40 = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 6b. Normalization discrimination: the split against the    *)
(* unsplit lcm face.                                                  *)
(* ================================================================== *)

(* at n = 1 the window is empty (Phi_1 = 1), so the split is vacuous
   and L_1 coincides with the raw lcm(1..4). *)
Example planb4_g1_ln_1_eq_lcmt_4 :
  planb4_g1_ln 1 = planb4_g1_lcmt 4.
Proof. vm_compute. reflexivity. Qed.

(* the unsplit face at n = 4: lcm(1..16) = 720720. *)
Example planb4_g1_lcmt_16 : planb4_g1_lcmt 16 = 720720%Z.
Proof. vm_compute. reflexivity. Qed.

(* from n = 4 on the split is active: the unsplit lcm inflates the
   calibration entry by Phi_n (720720 = 102960 * 7), so consuming
   the unsplit lcm instead of L_n would miss the calibration face. *)
Example planb4_g1_ln_4_neq_lcmt_16 :
  Z.eqb (planb4_g1_ln 4) (planb4_g1_lcmt 16) = false.
Proof. vm_compute. reflexivity. Qed.

(* the window list itself: empty at n <= 3; exactly [7] at the
   activation point n = 4; [17; 19] at n = 10 (Phi_10 = 323 =
   17 * 19). *)
Example planb4_g1_pwin_list_3 : planb4_g1_pwin_list 3 = []%nat.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_pwin_list_4 : planb4_g1_pwin_list 4 = [7]%nat.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_pwin_list_10 : planb4_g1_pwin_list 10 = [17; 19]%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 7. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_g1_primeb.
Print Assumptions planb4_g1_pwin.
Print Assumptions planb4_g1_inwin_zz_in_Pn.
Print Assumptions planb4_g1_pwin_list.
Print Assumptions planb4_g1_phi.
Print Assumptions planb4_g1_lcmt.
Print Assumptions planb4_g1_ln.
Print Assumptions planb4_g1_phi_4.
Print Assumptions planb4_g1_ln_4.
Print Assumptions planb4_g1_phi_7.
Print Assumptions planb4_g1_ln_7.
Print Assumptions planb4_g1_phiwin_40.
Print Assumptions planb4_g1_lnwin_40.
Print Assumptions planb4_g1_ln_1_eq_lcmt_4.
Print Assumptions planb4_g1_lcmt_16.
Print Assumptions planb4_g1_ln_4_neq_lcmt_16.
Print Assumptions planb4_g1_lndiv_40.
Print Assumptions planb4_g1_phiwin_elim.
Print Assumptions planb4_g1_lnwin_elim.
Print Assumptions planb4_g1_foldr_mul_pos.
Print Assumptions planb4_g1_phi_pos.
Print Assumptions planb4_g1_phi_nz.
Print Assumptions planb4_g1_pwin_list_3.
Print Assumptions planb4_g1_pwin_list_4.
Print Assumptions planb4_g1_pwin_list_10.
Print Assumptions planb4_g1_inwin_bounds.
Print Assumptions planb4_g1_pwin_list_sound.
Print Assumptions planb4_g1_pwin_list_complete.
Print Assumptions planb4_g1_nodiv_upto_S.
Print Assumptions planb4_g1_nodiv_even.
Print Assumptions planb4_g1_primeb_even_top.
