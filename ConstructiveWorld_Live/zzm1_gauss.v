(* ===================================================================== *)
(*  zzm1_gauss.v - Q(i) residue arithmetic machine, layer 1 Z[i] base    *)
(*  (DM-ZZM1 slice 1, ZZM-1). Pool abl_dmw1_pool/ZZ/: mirror _mirror_zz.py *)
(*  MIRROR_GREEN 10/10 on record; design sheet _tdmZZ2, item 1 of 5 cast. *)
(*  Mission.: Gaussian integer base gz (Z x Z pair record) plus six      *)
(*  operations (add/neg/sub/mul/conj/eqb), the power gz_pow, the         *)
(*  division-free residue form gz_im_neg_frac (numerator -Im[e^j],       *)
(*  denominator norm^j, both kept in Z; readout via Qmake; Gaussian      *)
(*  division forbidden; mirror im_neg_power direct translation), and ten *)
(*  base lemmas (norm multiplicative; conj multiplicative; Im[zbar] =    *)
(*  -Im z; Im[(zbar)^j] = -Im[z^j]).                                     *)
(*  Dependencies.: Stdlib only (QArith.ZArith List, single Require line); zero tree *)
(*  imports; zero coupling with pool siblings zzm1b_linform_bridge / zzm2_qpoly. *)
(*  References.: DM-ZZM1 design sheet ZZM-1; mirror im_neg_power (division-free form source). *)
(*  Constructivity.: every statement face is Set-borne: identity carrier *)
(*  = inductive zzId (single-constructor Set-level identity); Prop       *)
(*  equality survives only inside proof bodies (zzId_from_eq /           *)
(*  zzId_bool bridges); definitions transparent; axiom-free (Print       *)
(*  Assumptions audit: Closed under the global context at every audited  *)
(*  station). Shape record: the three conclusion-position Prop faces of  *)
(*  the source moved one-to-one to the zzId carrier: zzId_true,          *)
(*  gz_eqb_refl, gz_eqb_true (boolean premise kept; binder/premise       *)
(*  positions untouched). Disclosure: gnorm uses the |z|^2 tier (mirror  *)
(*  red-pen 3: |4+2i|^2 = 20); the Cauchy-analytic face is disclosed at  *)
(*  design sheet layer 2.                                                *)
(*  Build.: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*  ulimit -s 65532 && cpu_guard.sh -Reg /tmp/cw_reg_nw6 -Front 0 -Mid 1 *)
(*  -MaxWaitSec 600 -- rocq c -native-compiler no -q -Q . ""             *)
(*  zzm1_gauss.v (born in place inside the world directory).             *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ============================================================ *)
(* Part 0: Set-layer monomorphic identity (S01_BaseRing Id       *)
(*    same-shape; pool-internal prefix naming zzId - on store    *)
(*    entry, mapped to the neighbor-piece name via the five-step *)
(*    same-name mapping)                                         *)
(* ============================================================ *)

Inductive zzId {A : Set} (x : A) : A -> Set :=
| zzIdR : zzId x x.

Arguments zzIdR {A} {x}.

(* Set-borne reflexive form of the boolean identity. Washed station:
   the source's Prop-erasure conclusion moved its duty into proof
   bodies (constructive Prop derivation inside proofs is lawful);
   this station is now the identity on zzId b true. *)
Definition zzId_true {b : bool} (p : zzId b true) : zzId b true := p.

(* Reinjection: Set-level carrier for boolean equality (eq_rect
   backward transport, constructive). *)
Definition zzId_bool {b : bool} (H : b = true) : zzId b true :=
  eq_rect true (fun y => zzId y true) zzIdR b (eq_sym H).

(* General reflection piece: Set-level identity reinjected from a
   Prop equality (eq_rect forward transport). *)
Definition zzId_from_eq {A : Set} {x y : A} (H : x = y) : zzId x y :=
  eq_rect x (fun z => zzId x z) zzIdR y H.

(* Set-borne carrier for the Q boolean equality Qeq_bool x x = true
   (usable on symbolic terms; stdlib Qeq_bool = Qnum cross-product
   Z.eqb shape, no andb component). *)
Lemma zzId_Qeqb_refl : forall x : Q, zzId (Qeq_bool x x) true.
Proof.
  intros [a n]. unfold Qeq_bool; simpl.
  apply zzId_from_eq. apply Z.eqb_eq. ring.
Qed.

(* ============================================================ *)
(* Part 1: Gaussian integer base (Z x Z pair carrier) + six      *)
(* operations + power + division-free form                       *)
(* ============================================================ *)

Record gz : Set := mkz { gre : Z ; gim : Z }.

Definition gz_zero : gz := mkz 0 0.
Definition gz_one : gz := mkz 1 0.

Definition gz_add (z w : gz) : gz := mkz (gre z + gre w) (gim z + gim w).
Definition gz_neg (z : gz) : gz := mkz (- gre z) (- gim z).
Definition gz_sub (z w : gz) : gz := gz_add z (gz_neg w).
Definition gz_mul (z w : gz) : gz :=
  mkz (gre z * gre w - gim z * gim w) (gre z * gim w + gim z * gre w).
Definition gnorm (z : gz) : Z := gre z * gre z + gim z * gim z.
Definition gz_conj (z : gz) : gz := mkz (gre z) (- gim z).
Definition gz_eqb (z w : gz) : bool :=
  andb (Z.eqb (gre z) (gre w)) (Z.eqb (gim z) (gim w)).

Fixpoint gz_pow (z : gz) (j : nat) : gz :=
  match j with
  | O => gz_one
  | S k => gz_mul (gz_pow z k) z
  end.

(* Division-free form (design sheet item 2; mirror im_neg_power
   direct translation): Im[(a+bi)^(-j)] = -Im[(a+bi)^j] / (a^2+b^2)^j
   - numerator and denominator separated in Z, readout via Qmake,
   Gaussian division forbidden, gcd-free. *)
Definition gz_im_neg_frac (e : gz) (j : nat) : Z * Z :=
  (Z.opp (gim (gz_pow e j)), gnorm (gz_pow e j)).

(* Z power (nat-indexed; used for the norm power readout) *)
Fixpoint zpow (a : Z) (j : nat) : Z :=
  match j with
  | O => 1
  | S k => a * zpow a k
  end.

(* ============================================================ *)
(* Part 2: ten base lemmas (all Set-borne, zero solver)          *)
(* ============================================================ *)

Lemma gz_add_comm_b : forall z w : gz, zzId (gz_eqb (gz_add z w) (gz_add w z)) true.
Proof.
  intros [a b] [c d]. unfold gz_add, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

Lemma gz_add_assoc_b : forall z w u : gz,
  zzId (gz_eqb (gz_add (gz_add z w) u) (gz_add z (gz_add w u))) true.
Proof.
  intros [a b] [c d] [e f]. unfold gz_add, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

Lemma gz_mul_comm_b : forall z w : gz, zzId (gz_eqb (gz_mul z w) (gz_mul w z)) true.
Proof.
  intros [a b] [c d]. unfold gz_mul, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

(* norm multiplicative: |zw|^2 = |z|^2|w|^2 (Lagrange identity,
   ring decides) *)
Lemma gnorm_mul_b : forall z w : gz,
  zzId (Z.eqb (gnorm (gz_mul z w)) (gnorm z * gnorm w)) true.
Proof.
  intros [a b] [c d]. unfold gz_mul, gnorm; simpl.
  apply zzId_from_eq. apply Z.eqb_eq; ring.
Qed.

(* conj multiplicative *)
Lemma gz_conj_mul_b : forall z w : gz,
  zzId (gz_eqb (gz_conj (gz_mul z w)) (gz_mul (gz_conj z) (gz_conj w))) true.
Proof.
  intros [a b] [c d]. unfold gz_mul, gz_conj, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

(* Im[zbar] = -Im z *)
Lemma gz_im_conj_b : forall z : gz,
  zzId (Z.eqb (gim (gz_conj z)) (Z.opp (gim z))) true.
Proof.
  intros [a b]. unfold gz_conj; simpl.
  apply zzId_from_eq. apply Z.eqb_eq; ring.
Qed.

(* gz_eqb reflexivity (washed: zzId-carried conclusion; usable on
   symbolic terms). *)
Lemma gz_eqb_refl : forall z : gz, zzId (gz_eqb z z) true.
Proof.
  intros z. apply zzId_from_eq. unfold gz_eqb.
  apply andb_true_intro; split; apply Z.eqb_refl.
Qed.

(* power step (definitional; bridge rewrite: boolean reflexivity
   reached through zzId_from_eq, no consumption of the washed
   gz_eqb_refl) *)
Lemma gz_pow_succ_b : forall (z : gz) (j : nat),
  zzId (gz_eqb (gz_pow z (S j)) (gz_mul (gz_pow z j) z)) true.
Proof.
  intros z j. apply zzId_from_eq. cbn [gz_pow].
  unfold gz_eqb. apply andb_true_intro; split; apply Z.eqb_refl.
Qed.

(* norm power: |z^j|^2 = (|z|^2)^j (bridge rewrite: the Prop core is
   derived by induction inside the proof body, one zzId_from_eq
   bridge at the end) *)
Lemma gnorm_pow_b : forall (z : gz) (j : nat),
  zzId (Z.eqb (gnorm (gz_pow z j)) (zpow (gnorm z) j)) true.
Proof.
  intros z j.
  assert (Hgn : forall a b : gz, gnorm (gz_mul a b) = gnorm a * gnorm b).
  { intros [a1 b1] [a2 b2]. unfold gnorm, gz_mul. simpl. ring. }
  apply zzId_from_eq.
  induction j as [|j IHj]; cbn [gz_pow zpow].
  - reflexivity.
  - apply Z.eqb_eq in IHj. apply Z.eqb_eq. rewrite Hgn, IHj. ring.
Qed.

(* gz_eqb completeness (washed: Set-borne conclusion; the boolean
   premise stays - constructive Prop derivation inside the proof
   body; auxiliary piece) *)
Lemma gz_eqb_true : forall z w : gz, gz_eqb z w = true -> zzId z w.
Proof.
  intros [a b] [c d] H. unfold gz_eqb in H; simpl in H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
  apply zzIdR.
Qed.

(* conj power: Im[(zbar)^j] = -Im[z^j] (Coq-form basis of the mirror
   im_neg_power, full-piece form; bridge rewrite: the Prop core is
   derived by induction with in-body record-injectivity and conj-mul
   helpers, one zzId_from_eq bridge at the end) *)
Lemma gz_pow_conj_b : forall (z : gz) (j : nat),
  zzId (gz_eqb (gz_pow (gz_conj z) j) (gz_conj (gz_pow z j))) true.
Proof.
  intros z j.
  assert (Hrec : forall p q : gz, gre p = gre q -> gim p = gim q -> p = q).
  { intros [a1 b1] [a2 b2] H1 H2. simpl in H1, H2. subst. reflexivity. }
  assert (Hcm : forall a b : gz,
    gz_conj (gz_mul a b) = gz_mul (gz_conj a) (gz_conj b)).
  { intros a b. destruct a as [a1 b1]; destruct b as [a2 b2].
    apply Hrec; unfold gz_mul, gz_conj; simpl; ring. }
  assert (Hcore : gz_pow (gz_conj z) j = gz_conj (gz_pow z j)).
  { induction j as [|j IHj]; cbn [gz_pow].
    - reflexivity.
    - rewrite IHj. rewrite Hcm. reflexivity. }
  apply zzId_from_eq. rewrite Hcore. unfold gz_eqb.
  apply andb_true_intro; split; apply Z.eqb_refl.
Qed.

(* ============================================================ *)
(* Part 3: literal anchors (red-pen 3 norm tier 20/40/5 +        *)
(* division-free readout + base smoke test)                      *)
(* ============================================================ *)

Lemma gnorm_anchor_4_2 : zzId (Z.eqb (gnorm (mkz 4 2)) 20) true.
Proof. vm_compute. reflexivity. Qed.

Lemma gnorm_anchor_6_2 : zzId (Z.eqb (gnorm (mkz 6 2)) 40) true.
Proof. vm_compute. reflexivity. Qed.

Lemma gnorm_anchor_m1_2 : zzId (Z.eqb (gnorm (mkz (Z.opp 1) 2)) 5) true.
Proof. vm_compute. reflexivity. Qed.

(* Division-free readout anchor: Im[(4+2i)^(-1)] = -2/20 (readout via
   Qmake, Qdiv shape) *)
Lemma gz_im_neg_frac_anchor_4_1 :
  zzId (Qeq_bool (((fst (gz_im_neg_frac (mkz 4 2) 1)) # 1) /
                  ((snd (gz_im_neg_frac (mkz 4 2) 1)) # 1))%Q
                  ((-2) # 20)%Q) true.
Proof. vm_compute. reflexivity. Qed.

(* Base smoke test: sub/pow/conj-pow composite in one shot; the dual
   face of Im[(-1+2i)^3] = -2, Im[(-1-2i)^3] = +2 *)
Lemma gz_pow_anchor_m1_2_3 :
  zzId (gz_eqb (gz_pow (mkz (Z.opp 1) 2) 3) (mkz 11 (Z.opp 2))) true.
Proof. vm_compute. reflexivity. Qed.

Lemma gz_sub_anchor : zzId (gz_eqb (gz_sub (mkz 5 3) (mkz 2 1)) (mkz 3 2)) true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Part 4: audit (zero global-trust recheck)                     *)
(* ============================================================ *)

Print Assumptions gz_im_neg_frac.
Print Assumptions gnorm_mul_b.
Print Assumptions gnorm_pow_b.
Print Assumptions gz_pow_conj_b.
Print Assumptions gnorm_anchor_4_2.
Print Assumptions gz_im_neg_frac_anchor_4_1.
