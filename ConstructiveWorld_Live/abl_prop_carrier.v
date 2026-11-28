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

From Stdlib Require Import Arith.Arith List Bool.
Import ListNotations.
Require Import S01_BaseRing (Id, id_refl, id_eq_SI).
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_redischarge_pr01_sb.

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

(* Two-arm Set decision carrier: the left arm holds the pairwise *)
(* coprimality certificate, the right arm holds refutation data. *)
Inductive plm_pw_cop_sb (l : list nat) : Set :=
| plm_pw_cop_sb_left : plm_pairwise_coprime l -> plm_pw_cop_sb l
| plm_pw_cop_sb_right : (plm_pairwise_coprime l -> Empty_set) -> plm_pw_cop_sb l.

(* The decision: case on the scanner reading; the left arm enters by *)
(* soundness, the right arm by the lit negation flag. *)
Definition plm_pairwise_coprime_sb (l : list nat) : plm_pw_cop_sb l.
Proof.
  destruct (plm_pw_cop_bool l) eqn:E.
  - apply plm_pw_cop_sb_left. exact (plm_pw_cop_bool_sound l E).
  - apply plm_pw_cop_sb_right.
    assert (Hn : plm_pairwise_coprime_neg l = true).
    { unfold plm_pairwise_coprime_neg. rewrite E. reflexivity. }
    exact (plm_pairwise_coprime_neg_refutes l Hn).
Defined.

(* Readout mirror: each arm matches the scanner reading. *)
Theorem plm_pairwise_coprime_sb_mirror : forall l : list nat,
  match plm_pairwise_coprime_sb l with
  | plm_pw_cop_sb_left _ _ => plm_pw_cop_bool l = true
  | plm_pw_cop_sb_right _ _ => plm_pw_cop_bool l = false
  end.
Proof.
  intros l.
  destruct (plm_pairwise_coprime_sb l) as [Hpw | Href].
  - exact (plm_pw_cop_bool_complete l Hpw).
  - destruct (plm_pw_cop_bool l) eqn:E.
    + destruct (Href (plm_pw_cop_bool_sound l E)).
    + reflexivity.
Qed.

(* ---- Sec.4  The closed product-divisibility corollary ---- *)

(* Two-arm Set decision carrier: the left arm holds the product- *)
(* divisibility certificate face, the right arm holds refutation data *)
(* for the coprimality certificate. *)
Inductive plm_prod_dvd_sb (l : list nat) (c : nat) : Set :=
| plm_prod_dvd_sb_left :
    Nat.divide (fold_right Nat.mul 1 l) c -> plm_prod_dvd_sb l c
| plm_prod_dvd_sb_right :
    (plm_pairwise_coprime l -> Empty_set) -> plm_prod_dvd_sb l c.

Theorem plm_coprime_prod_dvd_closed : forall (l : list nat) (c : nat),
  (forall x : nat, In x l -> Nat.divide x c) -> plm_prod_dvd_sb l c.
Proof.
  intros l c Hdiv.
  destruct (plm_pairwise_coprime_sb l) as [Hpw | Href].
  - apply plm_prod_dvd_sb_left. exact (plm_coprime_prod_dvd l c Hdiv Hpw).
  - apply plm_prod_dvd_sb_right. exact Href.
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

(* Three-way closed corollary: for distinct p and q, either the gcd *)
(* certificate, or refutation data against the primality of p, or   *)
(* against the primality of q; the option-bool tag labels the arms. *)
Theorem plm_prime_gcd_1_closed : forall p q : nat,
  (p = q -> False) ->
  { e : option bool &
    match e with
    | None => Id (Nat.gcd p q) 1
    | Some true => pr_prime p -> Empty_set
    | Some false => pr_prime q -> Empty_set
    end }.
Proof.
  intros p q Hne.
  destruct (plm_prime_sb p) eqn:Hp.
  - assert (Hpp : pr_prime p).
    { unfold plm_prime_sb, pr_prime_sb in Hp.
      exact (pr_prime_bool_true p Hp). }
    destruct (plm_prime_sb q) eqn:Hq.
    + assert (Hqq : pr_prime q).
      { unfold plm_prime_sb, pr_prime_sb in Hq.
        exact (pr_prime_bool_true q Hq). }
      exists None. exact (plm_prime_gcd_1 p q Hpp Hqq Hne).
    + exists (Some false). intros Hqq.
      pose proof (pr_prime_bool_false q Hqq) as Hbid.
      assert (Hqf : pr_prime_bool q = true)
        by exact (id_eq_SI bool (pr_prime_bool q) true Hbid).
      unfold plm_prime_sb, pr_prime_sb in Hq. rewrite Hqf in Hq.
      discriminate Hq.
  - exists (Some true). intros Hpp.
    pose proof (pr_prime_bool_false p Hpp) as Hbid.
    assert (Hpf : pr_prime_bool p = true)
      by exact (id_eq_SI bool (pr_prime_bool p) true Hbid).
    unfold plm_prime_sb, pr_prime_sb in Hp. rewrite Hpf in Hp.
    discriminate Hp.
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
