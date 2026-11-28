(* =================================================================== *)
(* Module  : abl_prop_carrier                                          *)
(* Mission. Decision companions for pairwise coprimality of nat lists: *)
(*   the boolean pair scanner plm_pw_cop_bool over all ordered pairs,  *)
(*   diagonal included (the host also asks gcd x x = 1; repeats are    *)
(*   excluded) with sound and complete bridges; the negation flag      *)
(*   plm_pairwise_coprime_neg with its refutation bridge; the two-arm  *)
(*   Set carrier plm_pw_cop_sb and decision plm_pairwise_coprime_sb    *)
(*   (certificate or refutation data) with mirror; the closed          *)
(*   corollaries plm_coprime_prod_dvd_closed, plm_prime_gcd_1_closed,  *)
(*   the plm-side readout plm_prime_sb with mirror. List nonemptiness  *)
(*   is already supplied by abl_redischarge_sumd_inst, not restated.   *)
(* Dependencies. Stdlib (Arith.Arith, List, Bool); S01_BaseRing (Id,   *)
(*   id_refl, id_eq_SI); abl_Pr_core_01 (pr_prime family, pr_eq_id);   *)
(*   abl_Pr_lcmdecomp_04; abl_redischarge_pr01_sb.                     *)
(* References. abl_Pr_lcmdecomp_04; abl_redischarge_pr01_sb; stdlib    *)
(*   forallb, Nat.eqb_eq, Nat.eq_dec, Nat.gcd_comm, andb_true_intro.   *)
(* Constructivity. Statement faces are Set-carried: equations by Id,   *)
(*   negation by boolean flags or refutation data A -> Empty_set; no   *)
(*   Prop-typed definition and no sumbool on the statement face; the   *)
(*   closed carriers follow the landed precedent forms: the two-arm    *)
(*   Set carrier holds the divide certificate face as a constructor    *)
(*   argument; the option-bool sigT has all-Set arms, the gcd arm      *)
(*   carried by Id. Data statements end in Defined; Qed only on pure   *)
(*   Prop bridges (forallb elim/intro, completeness, the two mirrors); *)
(*   vm_compute is confined to concrete numeric pins. Axioms: none;    *)
(*   one Print Assumptions per statement closes it.                    *)
(* Build. rocq c -native-compiler no -q -Q <world root> ""             *)
(*   abl_prop_carrier.v, single shot, with the five dep .vo nearby.    *)
(* =================================================================== *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Import ListNotations.
Require Import S01_BaseRing (Id, id_refl, id_eq_SI, NatLe_drop, NatLe_lift).
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_redischarge_pr01_sb.

(* ---- Sec.0  Transparent replications of landed data faces ---- *)

(* Two landed lemmas with informative (Id-face) conclusions end Qed   *)
(* in their home modules; consuming their sealed terms at data        *)
(* positions would cast at the extraction face. The two replication  *)
(* lemmas below re-derive the same facts transparently (Defined),    *)
(* consuming only stdlib facts and transparent bridges, so every     *)
(* data position in this module stays cast-free. No signature of a   *)
(* landed module changes. *)

(* Transparent replication of pr_dvd_mod0 (abl_Pr_core_01): a divide *)
(* fact with divisor >= 1 lands the modulus on zero. *)
Lemma pr_dvd_mod0_open : forall d n : nat,
  1 <= d -> Nat.divide d n -> Id (n mod d) 0.
Proof.
  intros d n Hd Hdvd.
  assert (Hcore : n mod d = 0).
  { destruct Hdvd as [z Hz].
    destruct (Nat.Div0.mod_divides n d) as [_ Hbwd].
    apply Hbwd. exists z. rewrite Hz. apply Nat.mul_comm. }
  destruct Hcore. apply id_refl.
Defined.

(* Transparent replication of plm_prime_gcd_1 (abl_Pr_lcmdecomp_04):  *)
(* distinct primes are coprime, delivered as the identity face on    *)
(* the gcd. Case analysis on the gcd value; the coprime-but-divides  *)
(* contradictions come from the primality faces of p and q. *)
Lemma plm_prime_gcd_1_open : forall p q : nat,
  pr_prime p -> pr_prime q -> (p = q -> False) -> Id (Nat.gcd p q) 1.
Proof.
  intros p q Hpp Hqq Hne.
  pose proof (fst Hpp) as Hp2. pose proof (snd Hpp) as Hpd.
  pose proof (fst Hqq) as Hq2. pose proof (snd Hqq) as Hqd.
  pose proof (NatLe_drop _ _ Hp2) as Hp2'.
  pose proof (NatLe_drop _ _ Hq2) as Hq2'.
  assert (Hgp : Nat.divide (Nat.gcd p q) p) by apply Nat.gcd_divide_l.
  assert (Hgq : Nat.divide (Nat.gcd p q) q) by apply Nat.gcd_divide_r.
  assert (Hlep : Nat.gcd p q <= p) by (apply Nat.divide_pos_le; [lia | exact Hgp]).
  assert (Hleq : Nat.gcd p q <= q) by (apply Nat.divide_pos_le; [lia | exact Hgq]).
  remember (Nat.gcd p q) as g eqn:Eg.
  destruct g as [| [| g'']].
  - exfalso. apply Nat.divide_0_l in Hgp. lia.
  - apply id_refl.
  - exfalso.
    destruct (Nat.eq_dec p q) as [Epq|Npq].
    + apply Hne. exact Epq.
    + destruct (Nat.eq_dec (S (S g'')) p) as [Egp|Ngp].
      * rewrite Egp in Hgq.
        assert (Hpq_lt : p < q).
        { destruct (le_lt_dec q p) as [Hqle|Hlt2].
          - exfalso. apply Npq. lia.
          - exact Hlt2. }
        exfalso.
        assert (Hqf : Id (Nat.eqb (q mod p) 0) false)
          by (apply (Hqd p Hp2); [apply NatLe_lift; exact Hpq_lt]).
        assert (Hqfe : Nat.eqb (q mod p) 0 = false)
          by (exact (match Hqf in (Id _ z) return (Nat.eqb (q mod p) 0 = z)
                     with id_refl => eq_refl end)).
        assert (Hp1 : 1 <= p) by lia.
        pose proof (pr_dvd_mod0_open p q Hp1 Hgq) as Hmod0.
        assert (Hqe : q mod p = 0)
          by (exact (match Hmod0 in (Id _ z) return (q mod p = z)
                     with id_refl => eq_refl end)).
        rewrite Hqe in Hqfe. simpl in Hqfe. discriminate.
      * exfalso.
        assert (Hgf : Id (Nat.eqb (p mod (S (S g''))) 0) false)
          by (apply (Hpd (S (S g''))); [apply NatLe_lift; lia | apply NatLe_lift; lia]).
        assert (Hgfe : Nat.eqb (p mod (S (S g''))) 0 = false)
          by (exact (match Hgf in (Id _ z) return (Nat.eqb (p mod (S (S g''))) 0 = z)
                     with id_refl => eq_refl end)).
        assert (Hg1 : 1 <= S (S g'')) by lia.
        pose proof (pr_dvd_mod0_open (S (S g'')) p Hg1 Hgp) as Hmod0.
        assert (Hmode : p mod (S (S g'')) = 0)
          by (exact (match Hmod0 in (Id _ z) return (p mod (S (S g'')) = z)
                     with id_refl => eq_refl end)).
        rewrite Hmode in Hgfe. simpl in Hgfe. discriminate.
Defined.

(* ---- Sec.1  forallb / In bridges (proof-face helpers) ---- *)

Lemma plm_forallb_in_elim : forall (f : nat -> bool) (l : list nat),
  forallb f l = true -> forall y : nat, In y l -> f y = true.
Proof.
  intros f l. induction l as [| x t IH]; simpl; intros Hb y Hy.
  - destruct Hy.
  - apply andb_prop in Hb. destruct Hb as [Hx Ht].
    destruct Hy as [Hy | Hy].
    + rewrite <- Hy. exact Hx.
    + exact (IH Ht y Hy).
Qed.

Lemma plm_forallb_in_intro : forall (f : nat -> bool) (l : list nat),
  (forall y : nat, In y l -> f y = true) -> forallb f l = true.
Proof.
  intros f l. induction l as [| x t IH]; simpl; intros H.
  - reflexivity.
  - apply andb_true_intro. split.
    + apply H. apply in_eq.
    + apply IH. intros y Hy. apply H. apply in_cons. exact Hy.
Qed.

(* ---- Sec.2  The boolean pair scanner and its two bridges ---- *)

(* All ordered pairs of the list, the diagonal pair included: the host *)
(* definition asks gcd x y = 1 for every pair with x = y allowed, so    *)
(* repeated elements are excluded, and the scanner checks them too. *)
Fixpoint plm_pw_cop_bool (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: t =>
      forallb (fun y => Nat.eqb (Nat.gcd x y) 1) (x :: t) && plm_pw_cop_bool t
  end.

(* Soundness: a true reading yields the pairwise-coprimality certificate. *)
Lemma plm_pw_cop_bool_sound : forall l : list nat,
  plm_pw_cop_bool l = true -> plm_pairwise_coprime l.
Proof.
  intros l. induction l as [| x t IH]; intros Hbool a b Ha Hbin.
  - simpl in Ha. destruct Ha.
  - change (plm_pw_cop_bool (x :: t))
      with (forallb (fun y => Nat.eqb (Nat.gcd x y) 1) (x :: t)
            && plm_pw_cop_bool t) in Hbool.
    apply andb_prop in Hbool. destruct Hbool as [Hall Ht].
    assert (Hpt : plm_pairwise_coprime t) by (apply IH; exact Ht).
    assert (Hx : forall y : nat, In y (x :: t) -> Id (Nat.gcd x y) 1).
    { intros y Hy.
      assert (Heq : Nat.gcd x y = 1).
      { exact (proj1 (Nat.eqb_eq (Nat.gcd x y) 1)
                 (plm_forallb_in_elim _ _ Hall y Hy)). }
      exact (pr_eq_id nat (Nat.gcd x y) 1 Heq). }
    destruct (Nat.eq_dec a x) as [Ea | Na].
    + rewrite Ea. exact (Hx b Hbin).
    + assert (Hat : In a t).
      { destruct Ha as [Ha' | Ha'].
        - exfalso. apply Na. rewrite Ha'. reflexivity.
        - exact Ha'. }
      destruct (Nat.eq_dec b x) as [Eb | Nb].
      * assert (Hax : In a (x :: t)) by (apply in_cons; exact Hat).
        rewrite Eb. rewrite (Nat.gcd_comm a x). exact (Hx a Hax).
      * apply Hpt; [exact Hat |].
        destruct Hbin as [Hbin' | Hbin'].
        -- exfalso. apply Nb. rewrite Hbin'. reflexivity.
        -- exact Hbin'.
Defined.

(* Completeness: the certificate forces a true reading. *)
Lemma plm_pw_cop_bool_complete : forall l : list nat,
  plm_pairwise_coprime l -> plm_pw_cop_bool l = true.
Proof.
  intros l. induction l as [| x t IH]; intros Hpw.
  - reflexivity.
  - unfold plm_pairwise_coprime in Hpw.
    change (plm_pw_cop_bool (x :: t))
      with (forallb (fun y => Nat.eqb (Nat.gcd x y) 1) (x :: t)
            && plm_pw_cop_bool t).
    apply andb_true_intro. split.
    + apply plm_forallb_in_intro. intros y Hy.
      exact (proj2 (Nat.eqb_eq (Nat.gcd x y) 1)
               (id_eq_SI nat (Nat.gcd x y) 1 (Hpw x y (in_eq x t) Hy))).
    + apply IH. intros a b Ha Hbin.
      exact (Hpw a b (in_cons x a t Ha) (in_cons x b t Hbin)).
Qed.

(* ---- Sec.3  The negation flag, the decision carrier, the mirror ---- *)

(* Boolean negation flag: the complement of the scanner reading. *)
Definition plm_pairwise_coprime_neg (l : list nat) : bool :=
  negb (plm_pw_cop_bool l).

(* A lit flag refutes: a full certificate would force the scanner to *)
(* read true, contradicting the lit flag. *)
Theorem plm_pairwise_coprime_neg_refutes : forall l : list nat,
  plm_pairwise_coprime_neg l = true -> plm_pairwise_coprime l -> Empty_set.
Proof.
  intros l Hn Hpw. unfold plm_pairwise_coprime_neg in Hn.
  destruct (plm_pw_cop_bool l) eqn:E.
  - cbn in Hn. discriminate Hn.
  - assert (Hc : plm_pw_cop_bool l = true)
      by exact (plm_pw_cop_bool_complete l Hpw).
    rewrite E in Hc. discriminate Hc.
Defined.

(* Two-arm decision carrier over the scanner reading: the left arm  *)
(* carries the true reading as an identity witness, the right arm   *)
(* the false reading. The semantic bridge to pairwise coprimality   *)
(* lives in the sound/complete lemmas above; an arm holding a       *)
(* function into an empty type would cast at the extraction face. *)
Inductive plm_pw_cop_sb (l : list nat) : Set :=
| plm_pw_cop_sb_left : Id (plm_pw_cop_bool l) true -> plm_pw_cop_sb l
| plm_pw_cop_sb_right : Id (plm_pw_cop_bool l) false -> plm_pw_cop_sb l.

(* The decision: case on the scanner reading; each arm enters by    *)
(* lifting the boolean equation to the identity face. *)
Definition plm_pairwise_coprime_sb (l : list nat) : plm_pw_cop_sb l.
Proof.
  destruct (plm_pw_cop_bool l) eqn:E.
  - apply plm_pw_cop_sb_left. exact (pr_eq_id bool (plm_pw_cop_bool l) true E).
  - apply plm_pw_cop_sb_right. exact (pr_eq_id bool (plm_pw_cop_bool l) false E).
Defined.

(* Readout mirror: each arm matches the scanner reading. *)
Theorem plm_pairwise_coprime_sb_mirror : forall l : list nat,
  match plm_pairwise_coprime_sb l with
  | plm_pw_cop_sb_left _ _ => plm_pw_cop_bool l = true
  | plm_pw_cop_sb_right _ _ => plm_pw_cop_bool l = false
  end.
Proof.
  intros l.
  destruct (plm_pairwise_coprime_sb l) as [Eb | Eb].
  - exact (id_eq_SI bool (plm_pw_cop_bool l) true Eb).
  - exact (id_eq_SI bool (plm_pw_cop_bool l) false Eb).
Qed.

(* ---- Sec.4  The closed product-divisibility corollary ---- *)

(* Two-arm decision carrier: the left arm holds the product-       *)
(* divisibility certificate face, the right arm holds the false    *)
(* reading of the coprimality scanner as an identity witness. *)
Inductive plm_prod_dvd_sb (l : list nat) (c : nat) : Set :=
| plm_prod_dvd_sb_left :
    Nat.divide (fold_right Nat.mul 1 l) c -> plm_prod_dvd_sb l c
| plm_prod_dvd_sb_right :
    Id (plm_pw_cop_bool l) false -> plm_prod_dvd_sb l c.

Theorem plm_coprime_prod_dvd_closed : forall (l : list nat) (c : nat),
  (forall x : nat, In x l -> Nat.divide x c) -> plm_prod_dvd_sb l c.
Proof.
  intros l c Hdiv.
  destruct (plm_pairwise_coprime_sb l) as [Eb | Eb].
  - apply plm_prod_dvd_sb_left.
    exact (plm_coprime_prod_dvd l c Hdiv
             (plm_pw_cop_bool_sound l (id_eq_SI bool (plm_pw_cop_bool l) true Eb))).
  - apply plm_prod_dvd_sb_right. exact Eb.
Defined.

(* ---- Sec.5  The plm-side primality readout and the three-way ---- *)
(* ----      closed corollary                                     ---- *)

(* Readout alias: the plm-side name for the core primality decision. *)
Definition plm_prime_sb (p : nat) : bool := pr_prime_sb p.

(* Readout mirror, transparent passthrough of the core mirror. *)
Theorem plm_prime_sb_mirror : forall p : nat,
  match plm_prime_sb p with
  | true => pr_prime_bool p = true
  | false => pr_prime_bool p = false
  end.
Proof. intros p. exact (pr_prime_sb_mirror p). Qed.

(* Three-arm decision carrier for the corollary: the ok arm holds   *)
(* the gcd certificate as an identity face, the p/q arms hold the   *)
(* false reading of the respective primality scanner. A dependent   *)
(* match over an option-bool tag inside the pair family would cast  *)
(* at the extraction face, so the tag is carried by the arms        *)
(* themselves (same shape as the lw3x branch carrier). *)
Inductive plm_gcd_tri (p q : nat) : Set :=
| plm_gcd_tri_ok : Id (Nat.gcd p q) 1 -> plm_gcd_tri p q
| plm_gcd_tri_p : Id (plm_prime_sb p) false -> plm_gcd_tri p q
| plm_gcd_tri_q : Id (plm_prime_sb q) false -> plm_gcd_tri p q.

(* Three-way closed corollary: for distinct p and q, either the gcd *)
(* certificate, or refutation data against the primality of p, or   *)
(* against the primality of q. *)
Theorem plm_prime_gcd_1_closed : forall p q : nat,
  (p = q -> False) -> plm_gcd_tri p q.
Proof.
  intros p q Hne.
  destruct (plm_prime_sb p) eqn:Hp.
  - destruct (plm_prime_sb q) eqn:Hq.
    + assert (Hpp : pr_prime p).
      { unfold plm_prime_sb, pr_prime_sb in Hp.
        exact (pr_prime_bool_true p Hp). }
      assert (Hqq : pr_prime q).
      { unfold plm_prime_sb, pr_prime_sb in Hq.
        exact (pr_prime_bool_true q Hq). }
      exact (plm_gcd_tri_ok p q (plm_prime_gcd_1_open p q Hpp Hqq Hne)).
    + exact (plm_gcd_tri_q p q (pr_eq_id bool (plm_prime_sb q) false Hq)).
  - exact (plm_gcd_tri_p p q (pr_eq_id bool (plm_prime_sb p) false Hp)).
Defined.

(* ---- Sec.6  Numeric verdict readings (small concrete instances) ---- *)

(* Arm readout: true when the decision lands on the certificate arm. *)
Definition plm_pw_cop_arm (l : list nat) : bool :=
  match plm_pairwise_coprime_sb l with
  | plm_pw_cop_sb_left _ _ => true
  | plm_pw_cop_sb_right _ _ => false
  end.

(* Empty list, singleton lists, and the all-ones list land on the   *)
(* certificate arm; lists containing 2 land on the refutation arm   *)
(* (the diagonal pair gcd 2 2 = 2 excludes repeats). *)
Lemma plm_pw_sb_empty : sb_bid (plm_pw_cop_arm (@nil nat)).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Defined.

Lemma plm_pw_sb_1 : sb_bid (plm_pw_cop_arm (1 :: nil)).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Defined.

Lemma plm_pw_sb_11 : sb_bid (plm_pw_cop_arm (1 :: 1 :: nil)).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Defined.

Lemma plm_pw_sb_23 : sb_bid (negb (plm_pw_cop_arm (2 :: 3 :: nil))).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Defined.

Lemma plm_pw_sb_235 : sb_bid (negb (plm_pw_cop_arm (2 :: 3 :: 5 :: nil))).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Defined.

(* The plm-side readout passthrough computes on concrete numbers. *)
Lemma plm_prime_sb_7 : sb_bid (plm_prime_sb 7).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Defined.

Lemma plm_prime_sb_8 : sb_bid (negb (plm_prime_sb 8)).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Defined.

(* ---- Sec.7  Assumption audit (one Print Assumptions per statement) ---- *)

Print Assumptions plm_forallb_in_elim.
Print Assumptions plm_forallb_in_intro.
Print Assumptions plm_pw_cop_bool_sound.
Print Assumptions plm_pw_cop_bool_complete.
Print Assumptions plm_pairwise_coprime_neg.
Print Assumptions plm_pairwise_coprime_neg_refutes.
Print Assumptions plm_pairwise_coprime_sb.
Print Assumptions plm_pairwise_coprime_sb_mirror.
Print Assumptions plm_coprime_prod_dvd_closed.
Print Assumptions plm_prime_sb.
Print Assumptions plm_prime_sb_mirror.
Print Assumptions plm_prime_gcd_1_closed.
Print Assumptions plm_pw_cop_arm.
Print Assumptions plm_pw_sb_empty.
Print Assumptions plm_pw_sb_1.
Print Assumptions plm_pw_sb_11.
Print Assumptions plm_pw_sb_23.
Print Assumptions plm_pw_sb_235.
Print Assumptions plm_prime_sb_7.
Print Assumptions plm_prime_sb_8.
