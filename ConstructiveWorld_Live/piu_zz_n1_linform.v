(* ========================================================================= *)
(* Mission. Statement carrier for the length face of the coefficient         *)
(*   linear forms in the Zeilberger-Zudilin certificate chain: for the       *)
(*   index set M_j of the partial-fraction expansion (eq. (5)) and the       *)
(*   weight T(m), carries the counting bound |M_j| <= (3n+1)^6 <= 2^(2n)     *)
(*   for all j and every n >= 18 (fails at n = 17), lifts the chain onto     *)
(*   QleT', proves the maximal tail tolerance over M_j attained at an        *)
(*   explicit sigT witness, gives a finite-check face for n < 18, and        *)
(*   fixes vm_compute acceptance samples from exact integer arithmetic.      *)
(* Dependencies. piu_zz_kernel_sum, piu_zz_gauss_pair (qeqT); LW0LeibWindow  *)
(*   (leiblw_Id, leiblw_id_eq); S02_CauchyComplete (QleT', Qle_to_QleT');    *)
(*   S01_BaseRing (Id); stdlib QArith, ZArith, Lia, Setoid, List.            *)
(* References. Zeilberger-Zudilin, Moscow J. Comb. Number Theory 9 (2020)    *)
(*   407-419, eq. (5); T(m) the binomial weight.                             *)
(* Constructivity. Zero Prop predicates on statement faces: conjunctions by  *)
(*   the Set carrier zz_and2, the length chain by leiblw_Id, the Q order     *)
(*   face by QleT', membership by the boolean zz_inMjb (computes under       *)
(*   vm_compute), witnesses as sigT pairs over zz6 with Set-only payloads;   *)
(*   propositional reasoning confined to proofs; definitions transparent;    *)
(*   vm_compute confined to concrete numeric pins.                           *)
(* Build. rocq c -native-compiler no -q -Q <Set Live vo tree> ""             *)
(*   piu_zz_n1_linform.v (Rocq 9.3).                                         *)
(* ========================================================================= *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import List.
Import ListNotations.
Require Import piu_zz_gauss_pair.
Require Import piu_zz_kernel_sum.
Require Import S02_CauchyComplete.
Require Import LW0LeibWindow.

(* ------------------------------------------------------------------ *)
(* Section 0. Local Set carriers and boolean membership faces.        *)
(* ------------------------------------------------------------------ *)

(* Set-carried conjunction: a two-argument Set with a single
   constructor, the conjunction shape of the mu criterion carrier. *)
Inductive zz_and2 (S1 S2 : Set) : Set :=
| zz_and2_i : S1 -> S2 -> zz_and2 S1 S2.

(* Decidable equality on zz6, boolean face. *)
Definition zz6_eqb (a b : zz6) : bool :=
  match a, b with
  | (a0, a1, a2, a3, a4, a5), (b0, b1, b2, b3, b4, b5) =>
      Nat.eqb a0 b0 && Nat.eqb a1 b1 && Nat.eqb a2 b2 &&
      Nat.eqb a3 b3 && Nat.eqb a4 b4 && Nat.eqb a5 b5
  end.

Lemma zz_nat_eqb_refl : forall n : nat, Nat.eqb n n = true.
Proof. intros n. apply (proj2 (Nat.eqb_eq _ _)). reflexivity. Qed.

Lemma zz6_eqb_refl : forall a : zz6, zz6_eqb a a = true.
Proof.
  intros [[[[[a0 a1] a2] a3] a4] a5].
  unfold zz6_eqb. cbn [zz6_eqb].
  rewrite !zz_nat_eqb_refl. reflexivity.
Qed.

(* Boolean membership in a zz6 list: existsb computes under vm_compute
   where the propositional In cannot. *)
Definition zz_inLb (L : list zz6) (m : zz6) : bool :=
  existsb (fun t => zz6_eqb t m) L.

(* Specialization to the index set M_j. *)
Definition zz_inMjb (n j : nat) (m : zz6) : bool :=
  zz_inLb (zz_Mj n j) m.

Lemma zz_inLb_sound : forall (L : list zz6) (m : zz6),
  In m L -> zz_inLb L m = true.
Proof.
  intros L. induction L as [| a L IH]; intros m Hin.
  - destruct Hin.
  - unfold zz_inLb in *. cbn [existsb]. destruct Hin as [E | Hin].
    + subst a. rewrite zz6_eqb_refl. apply Bool.orb_true_l.
    + rewrite (IH m Hin). apply Bool.orb_true_r.
Qed.

Lemma zz_inMjb_sound : forall (n j : nat) (m : zz6),
  In m (zz_Mj n j) -> zz_inMjb n j m = true.
Proof. intros n j m H. exact (zz_inLb_sound (zz_Mj n j) m H). Qed.

Lemma zz_inLb_cons : forall (t m : zz6) (L : list zz6),
  zz_inLb L m = true -> zz_inLb (t :: L) m = true.
Proof.
  intros t m L H. unfold zz_inLb in *. cbn [existsb].
  rewrite H. apply Bool.orb_true_r.
Qed.

(* Reverse face of the Set identity bridge: leiblw_Id discharges to a
   boolean equation in place, by the J computation of Id elimination. *)
Lemma zz_leiblw_true : forall b : bool, leiblw_Id b true -> b = true.
Proof. intros b H. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Section 1. The arithmetic chain  |M_j| <= (3n+1)^6 <= 2^(2n), n>=18.*)
(* ------------------------------------------------------------------ *)

(* Step 1: (2n+1)^5 <= (3n+1)^6 for every n, factorwise. *)
Lemma zz_box5_le_box6 : forall n : nat,
  (Nat.leb ((2 * n + 1) ^ 5) ((3 * n + 1) ^ 6)) = true.
Proof.
  intros n. apply (proj2 (Nat.leb_le _ _)).
  assert (H5 : ((2 * n + 1) ^ 5 <= (3 * n + 1) ^ 5)%nat).
  { replace ((2 * n + 1) ^ 5)%nat
      with ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * (2 * n + 1)))))%nat
      by (rewrite !Nat.pow_succ_r', Nat.pow_0_r, Nat.mul_1_r; reflexivity).
    replace ((3 * n + 1) ^ 5)%nat
      with ((3 * n + 1) * ((3 * n + 1) * ((3 * n + 1) * ((3 * n + 1) * (3 * n + 1)))))%nat
      by (rewrite !Nat.pow_succ_r', Nat.pow_0_r, Nat.mul_1_r; reflexivity).
    apply Nat.mul_le_mono; [ lia
    | apply Nat.mul_le_mono; [ lia
    | apply Nat.mul_le_mono; [ lia
    | apply Nat.mul_le_mono; lia ] ] ]. }
  eapply Nat.le_trans; [ exact H5 | apply Nat.pow_le_mono_r; lia ].
Qed.

(* Step 2: length (zz_Mj n j) <= (3n+1)^6 for all n j, through zz_len5. *)
Lemma zz_Mj_le_box6 : forall n j : nat,
  (Nat.leb (length (zz_Mj n j)) ((3 * n + 1) ^ 6)) = true.
Proof.
  intros n j. apply (proj2 (Nat.leb_le _ _)).
  eapply Nat.le_trans;
    [ | apply (proj1 (Nat.leb_le _ _)); apply zz_box5_le_box6 ].
  pose proof (zz_len5 n j) as HL.
  apply (proj1 (Nat.leb_le _ _)) in HL.
  replace ((2 * n + 1) ^ 5)%nat with
    ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * 1)))))%nat
    by (rewrite !Nat.pow_succ_r'; reflexivity).
  exact HL.
Qed.

(* Product-of-powers factorization: (a*b)^k = a^k * b^k. *)
Lemma zz_pow6_mul_distr : forall a b k : nat, ((a * b) ^ k = a ^ k * b ^ k)%nat.
Proof.
  intros a b k. induction k as [| k IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH.
    rewrite <- (Nat.mul_assoc a b (a ^ k * b ^ k)).
    rewrite (Nat.mul_assoc b (a ^ k) (b ^ k)).
    rewrite <- (Nat.mul_comm (a ^ k) b).
    rewrite <- (Nat.mul_assoc (a ^ k) b (b ^ k)).
    rewrite <- (Nat.mul_assoc a (a ^ k) (b * b ^ k)).
    reflexivity.
Qed.

(* Step 3: the ratio law  (3(n+1)+1)^6 <= 4 * (3n+1)^6  for n >= 4.
   Since 4*(3n+4) <= 5*(3n+1) holds from n >= 4, taking sixth powers
   gives 4^6*(3n+4)^6 <= 5^6*(3n+1)^6, and 5^6 = 15625 <= 16384 = 4^6*4
   absorbs the factor 4. *)
Lemma zz_pow6_step : forall n : nat, (4 <= n)%nat ->
  (Nat.leb ((3 * S n + 1) ^ 6) (4 * (3 * n + 1) ^ 6)) = true.
Proof.
  intros n Hn. apply (proj2 (Nat.leb_le _ _)).
  assert (Hq : (4 * (3 * n + 4) <= 5 * (3 * n + 1))%nat) by lia.
  assert (Hm : (4 ^ 6 * (3 * S n + 1) ^ 6 <= 5 ^ 6 * (3 * n + 1) ^ 6)%nat).
  { replace (3 * S n + 1)%nat with (3 * n + 4)%nat by lia.
    replace (4 ^ 6 * (3 * n + 4) ^ 6)%nat with ((4 * (3 * n + 4)) ^ 6)%nat
      by apply zz_pow6_mul_distr.
    replace (5 ^ 6 * (3 * n + 1) ^ 6)%nat with ((5 * (3 * n + 1)) ^ 6)%nat
      by apply zz_pow6_mul_distr.
    apply Nat.pow_le_mono_l; solve [ exact Hq | lia ]. }
  assert (Hc : (5 ^ 6 <= 4 ^ 6 * 4)%nat).
  { apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity. }
  assert (Hfin : (4 ^ 6 * (3 * S n + 1) ^ 6
                  <= 4 ^ 6 * (4 * (3 * n + 1) ^ 6))%nat).
  { eapply Nat.le_trans; [ exact Hm | ].
    replace (4 ^ 6 * (4 * (3 * n + 1) ^ 6))%nat
      with ((4 ^ 6 * 4) * (3 * n + 1) ^ 6)%nat
      by (rewrite Nat.mul_assoc; reflexivity).
    apply Nat.mul_le_mono; [ exact Hc | lia ]. }
  assert (Hp : (0 < 4 ^ 6)%nat).
  { apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity. }
  apply (proj2 (Nat.mul_le_mono_pos_l ((3 * S n + 1) ^ 6)
                  (4 * (3 * n + 1) ^ 6) (4 ^ 6) Hp)).
  exact Hfin.
Qed.

(* Step 4: base case n = 18, by exact numerals: 55^3 = 166375 <= 2^18 =
   262144, squared to 55^6 <= 2^36. *)
Lemma zz_pow6_base18 : (Nat.leb ((3 * 18 + 1) ^ 6) (2 ^ (2 * 18))) = true.
Proof.
  apply (proj2 (Nat.leb_le _ _)).
  assert (H3 : (Nat.leb ((3 * 18 + 1) ^ 3) (2 ^ 18)) = true)
    by (vm_compute; reflexivity).
  replace ((3 * 18 + 1) ^ 6)%nat
    with (((3 * 18 + 1) ^ 3) * ((3 * 18 + 1) ^ 3))%nat
    by (rewrite <- (Nat.pow_add_r (3 * 18 + 1) 3 3); f_equal; lia).
  replace (2 ^ (2 * 18))%nat with (2 ^ 18 * 2 ^ 18)%nat
    by (rewrite <- (Nat.pow_add_r 2 18 18); f_equal; lia).
  apply Nat.mul_le_mono; apply (proj1 (Nat.leb_le _ _)); exact H3.
Qed.

(* Step 5: the main arithmetic lemma, k-shift induction from n = 18. *)
Lemma zz_pow6_le_pow2_k : forall k : nat,
  (Nat.leb ((3 * (18 + k) + 1) ^ 6) (2 ^ (2 * (18 + k)))) = true.
Proof.
  induction k as [| k IH].
  - replace (18 + 0)%nat with (18)%nat by lia. exact zz_pow6_base18.
  - apply (proj2 (Nat.leb_le _ _)).
    assert (Hge : (4 <= 18 + k)%nat) by lia.
    pose proof (zz_pow6_step (18 + k) Hge) as Hstep.
    apply (proj1 (Nat.leb_le _ _)) in Hstep.
    replace (3 * S (18 + k) + 1)%nat with (3 * (18 + S k) + 1)%nat in Hstep by lia.
    replace (2 ^ (2 * (18 + S k)))%nat with (4 * 2 ^ (2 * (18 + k)))%nat
      by (replace (2 * (18 + S k))%nat with (S (S (2 * (18 + k))))%nat by lia;
          rewrite !Nat.pow_succ_r'; lia).
    eapply Nat.le_trans; [ exact Hstep
    | apply Nat.mul_le_mono; [ lia | apply (proj1 (Nat.leb_le _ _)); exact IH ] ].
Qed.

Lemma zz_pow6_le_pow2 : forall n : nat, (18 <= n)%nat ->
  (Nat.leb ((3 * n + 1) ^ 6) (2 ^ (2 * n))) = true.
Proof.
  intros n Hn.
  assert (Hk : (exists k : nat, n = 18 + k)%nat)
    by (exists (n - 18)%nat; lia).
  destruct Hk as [k Hk]. subst n.
  apply zz_pow6_le_pow2_k.
Qed.

(* The composite length chain, boolean face. *)
Lemma zz_Mj_le_pow2_leb : forall n j : nat, (18 <= n)%nat ->
  (Nat.leb (length (zz_Mj n j)) (2 ^ (2 * n))) = true.
Proof.
  intros n j Hn. apply (proj2 (Nat.leb_le _ _)).
  eapply Nat.le_trans;
    [ apply (proj1 (Nat.leb_le _ _)); apply zz_Mj_le_box6
    | apply (proj1 (Nat.leb_le _ _)); apply zz_pow6_le_pow2; exact Hn ].
Qed.

(* Main statement of the node: the two faces of the length chain, packed
   in the Set-carried conjunction on the leiblw_Id identity face. *)
Theorem piu_zz_s1_len : forall n j : nat, (18 <= n)%nat ->
  zz_and2
    (leiblw_Id (Nat.leb (length (zz_Mj n j)) ((3 * n + 1) ^ 6)) true)
    (leiblw_Id (Nat.leb ((3 * n + 1) ^ 6) (2 ^ (2 * n))) true).
Proof.
  intros n j Hn. apply zz_and2_i; apply leiblw_id_eq.
  - apply zz_Mj_le_box6.
  - apply zz_pow6_le_pow2. exact Hn.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2. Q face: the same chain under the QleT' predicate.       *)
(* ------------------------------------------------------------------ *)

Lemma zz_s1_len_QleT' : forall n j : nat, (18 <= n)%nat ->
  QleT' ((Z.of_nat (length (zz_Mj n j))) # 1) ((Z.of_nat (2 ^ (2 * n))) # 1).
Proof.
  intros n j Hn. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_le _ _)).
  apply (proj1 (Nat.leb_le _ _)). apply zz_Mj_le_pow2_leb. exact Hn.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3. Tail tolerance: zz_maxT and its attained witness.       *)
(* ------------------------------------------------------------------ *)

Definition zz_maxT (n j : nat) : nat :=
  fold_right (fun m acc => Nat.max (zz_Tnat n m) acc) (0)%nat (zz_Mj n j).

(* A fold-max over a nonempty list is attained at an element of the
   list; the witness is packed as a sigT pair with Set-only payloads. *)
Lemma zz_fold_max_attained : forall (L : list zz6) (n : nat), L <> [] ->
  sigT (fun m : zz6 => zz_and2 (leiblw_Id (zz_inLb L m) true)
    (leiblw_Id (Nat.eqb (zz_Tnat n m)
      (fold_right (fun u acc => Nat.max (zz_Tnat n u) acc) (0)%nat L)) true)).
Proof.
  intros L n. induction L as [| a L IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct L as [| b L'].
    + exists a. apply zz_and2_i; apply leiblw_id_eq.
      * unfold zz_inLb. cbn [existsb]. rewrite zz6_eqb_refl.
        apply Bool.orb_true_l.
      * cbn [fold_right]. apply Nat.eqb_eq. symmetry. apply Nat.max_l. lia.
    + assert (Hne' : (b :: L') <> []) by (intro E; discriminate E).
      destruct (IH Hne') as [w [Hin Hval]].
      cbn [fold_right] in Hval |- *.
      pose proof (zz_leiblw_true _ Hin) as Hinb.
      pose proof (zz_leiblw_true _ Hval) as Hvalb.
      apply Nat.eqb_eq in Hvalb.
      destruct (Nat.leb (Nat.max (zz_Tnat n b)
        (fold_right (fun u acc => Nat.max (zz_Tnat n u) acc) (0)%nat L'))
        (zz_Tnat n a)) eqn:Hcase.
      * exists a. apply zz_and2_i; apply leiblw_id_eq.
        -- unfold zz_inLb. cbn [existsb]. rewrite zz6_eqb_refl.
           apply Bool.orb_true_l.
        -- apply Nat.eqb_eq. symmetry. apply Nat.max_l.
           apply (proj1 (Nat.leb_le _ _)). exact Hcase.
      * assert (Hgt : (zz_Tnat n a < Nat.max (zz_Tnat n b)
            (fold_right (fun u acc => Nat.max (zz_Tnat n u) acc) (0)%nat L'))%nat)
          by (apply (proj1 (Nat.leb_gt _ _)); exact Hcase).
        exists w. apply zz_and2_i; apply leiblw_id_eq.
        -- apply zz_inLb_cons. exact Hinb.
        -- apply Nat.eqb_eq. rewrite Hvalb. symmetry. apply Nat.max_r. lia.
Qed.

(* The corner index (3n-j, 0, 0, 0, 0, 0) belongs to M_j whenever
   j <= 3n; hence M_j is nonempty on the whole range.  Boolean face. *)
Lemma zz_Mj_in_corner_b : forall n j : nat, (j <= 3 * n)%nat ->
  zz_inMjb n j ((3 * n - j)%nat, 0%nat, 0%nat, 0%nat, 0%nat, 0%nat) = true.
Proof.
  intros n j Hj. apply zz_inMjb_sound.
  assert (Hle : (Nat.leb j (3 * n)) = true) by (apply Nat.leb_le; exact Hj).
  assert (Hone : In ((3 * n - j)%nat, 0%nat, 0%nat, 0%nat, 0%nat, 0%nat)
                   (zz_one (3 * n - j) 0 0 0 0 0)).
  { unfold zz_one.
    assert (Hz : (Nat.leb (0 + 0 + 0 + 0 + 0) (3 * n - j)) = true)
      by (apply Nat.leb_le; lia).
    rewrite Hz. cbn [In]. left.
    replace (3 * n - j - (0 + 0 + 0 + 0 + 0))%nat with (3 * n - j)%nat
      by lia.
    reflexivity. }
  assert (Hseq : forall k : nat, In 0%nat (zz_seq (S k))).
  { intros k. induction k as [| k IHk].
    - cbn [zz_seq In]. left. reflexivity.
    - cbn [zz_seq In]. right. exact IHk. }
  unfold zz_Mj. rewrite Hle.
  replace (2 * n + 1)%nat with (S (2 * n))%nat by lia.
  rewrite in_flat_map. exists 0%nat. split; [ apply Hseq | ].
  cbv beta. rewrite in_flat_map. exists 0%nat. split; [ apply Hseq | ].
  cbv beta. rewrite in_flat_map. exists 0%nat. split; [ apply Hseq | ].
  cbv beta. rewrite in_flat_map. exists 0%nat. split; [ apply Hseq | ].
  cbv beta. rewrite in_flat_map. exists 0%nat. split; [ apply Hseq | ].
  cbv beta. exact Hone.
Qed.

Theorem zz_maxT_attained : forall n j : nat, (j <= 3 * n)%nat ->
  sigT (fun m : zz6 => zz_and2 (leiblw_Id (zz_inMjb n j m) true)
    (leiblw_Id (Nat.eqb (zz_Tnat n m) (zz_maxT n j)) true)).
Proof.
  intros n j Hj.
  assert (Hne : (zz_Mj n j) <> []).
  { intro E. pose proof (zz_Mj_in_corner_b n j Hj) as Hc.
    unfold zz_inMjb, zz_inLb in Hc. rewrite E in Hc.
    cbn [existsb] in Hc. discriminate Hc. }
  exact (zz_fold_max_attained (zz_Mj n j) n Hne).
Qed.

(* Numeric anchors of the tail-tolerance face (exact integer values;
   cross-checked independently). *)
Lemma zz_maxT_sample_1_0 : (Nat.eqb (zz_maxT 1 0) 20) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_maxT_sample_2_0 : (Nat.eqb (zz_maxT 2 0) 7168) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_T_sample_n1 : (Nat.eqb (zz_Tnat 1 (3%nat, 0%nat, 0%nat, 0%nat, 0%nat, 0%nat)) 20) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_T_sample_n2 : (Nat.eqb (zz_Tnat 2 (2%nat, 1%nat, 1%nat, 1%nat, 1%nat, 0%nat)) 7168) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_inMj_sample_n1 : (zz_inMjb 1 0 (3%nat, 0%nat, 0%nat, 0%nat, 0%nat, 0%nat)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_inMj_sample_neg : (zz_inMjb 1 0 (4%nat, 0%nat, 0%nat, 0%nat, 0%nat, 0%nat)) = false.
Proof. vm_compute. reflexivity. Qed.

(* Exact-value anchors of the tail face for later deep sampling:
   maxT(8,0)  = 2124012747816960000000   at m = (9,3,3,3,3,3);
   maxT(16,0) = 4239643874760002668669675078189645038197145600
                                        at m = (17,7,6,6,6,6). *)

(* ------------------------------------------------------------------ *)
(* Section 4. Finite-check face: pointwise flags for n < 18.          *)
(* ------------------------------------------------------------------ *)

(* True counting: max_j |M_j| <= 2^(2n) holds already from n = 9 on (at
   n = 8 it fails: 114795 > 65536), while the paper chain of Section 1
   needs n >= 18; in the overlap 9 <= n < 18 the pointwise flags below
   discharge the chain by finite check, and for n <= 8 the library-wide
   crude bound 2^(37n) (piu_zz_crude_size) applies instead. *)
Definition zz_forallb_le (n : nat) : bool :=
  forallb (fun j => Nat.leb (length (zz_Mj n j)) (2 ^ (2 * n)))
          (zz_seq (3 * n + 1)).

Lemma zz_finite_le_spec : forall n j : nat, (j <= 3 * n)%nat ->
  zz_forallb_le n = true -> (Nat.leb (length (zz_Mj n j)) (2 ^ (2 * n))) = true.
Proof.
  intros n j Hj H. unfold zz_forallb_le in H. rewrite forallb_forall in H.
  assert (Hin : forall k j0 : nat, (j0 < k)%nat -> In j0 (zz_seq k)).
  { intros k. induction k as [| k IHk]; intros j0 Hlt.
    - exfalso. lia.
    - cbn [zz_seq In]. destruct (Nat.eq_dec j0 k) as [E | Hne].
      + subst. left. reflexivity.
      + right. apply IHk. lia. }
  apply H. apply Hin. lia.
Qed.

Lemma zz_finite_n8_neg : (Nat.leb (length (zz_Mj 8 0)) (2 ^ (2 * 8))) = false.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Section 5. Machine-checked acceptance samples (vm_compute face).   *)
(* ------------------------------------------------------------------ *)

Lemma zz_len_sample_1_0 : (Nat.eqb (length (zz_Mj 1 0)) 51) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_1_1 : (Nat.eqb (length (zz_Mj 1 1)) 21) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_1_3 : (Nat.eqb (length (zz_Mj 1 3)) 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_2_0 : (Nat.eqb (length (zz_Mj 2 0)) 432) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_2_6 : (Nat.eqb (length (zz_Mj 2 6)) 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_3_0 : (Nat.eqb (length (zz_Mj 3 0)) 1897) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_3_9 : (Nat.eqb (length (zz_Mj 3 9)) 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_4_0 : (Nat.eqb (length (zz_Mj 4 0)) 5908) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_len_sample_8_0 : (Nat.eqb (length (zz_Mj 8 0)) 114795) = true.
Proof. vm_compute. reflexivity. Qed.

(* Full first rows of the coefficient face: A_{1,j} = [-2392; 6880;
   -11200; 8000] (j = 0 and j = 3 carried in piu_zz_kernel_sum), and
   A_{2,0} = 37324672. *)
Lemma piu_zz_sample_n1_j1 : qeqT (piu_zz_Aj 1 1) (6880 # 1)%Q.
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma piu_zz_sample_n1_j2 : qeqT (piu_zz_Aj 1 2) ((-11200) # 1)%Q.
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma piu_zz_sample_n2_j0 : qeqT (piu_zz_Aj 2 0) (37324672 # 1)%Q.
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Section 6. Assumption audit: one line per named statement.         *)
(* ------------------------------------------------------------------ *)

Print Assumptions zz_nat_eqb_refl.
Print Assumptions zz6_eqb_refl.
Print Assumptions zz_inLb_sound.
Print Assumptions zz_inMjb_sound.
Print Assumptions zz_inLb_cons.
Print Assumptions zz_leiblw_true.
Print Assumptions zz_box5_le_box6.
Print Assumptions zz_Mj_le_box6.
Print Assumptions zz_pow6_mul_distr.
Print Assumptions zz_pow6_step.
Print Assumptions zz_pow6_base18.
Print Assumptions zz_pow6_le_pow2_k.
Print Assumptions zz_pow6_le_pow2.
Print Assumptions zz_Mj_le_pow2_leb.
Print Assumptions piu_zz_s1_len.
Print Assumptions zz_s1_len_QleT'.
Print Assumptions zz_fold_max_attained.
Print Assumptions zz_Mj_in_corner_b.
Print Assumptions zz_maxT_attained.
Print Assumptions zz_maxT_sample_1_0.
Print Assumptions zz_maxT_sample_2_0.
Print Assumptions zz_T_sample_n1.
Print Assumptions zz_T_sample_n2.
Print Assumptions zz_inMj_sample_n1.
Print Assumptions zz_inMj_sample_neg.
Print Assumptions zz_finite_le_spec.
Print Assumptions zz_finite_n8_neg.
Print Assumptions zz_len_sample_1_0.
Print Assumptions zz_len_sample_1_1.
Print Assumptions zz_len_sample_1_3.
Print Assumptions zz_len_sample_2_0.
Print Assumptions zz_len_sample_2_6.
Print Assumptions zz_len_sample_3_0.
Print Assumptions zz_len_sample_3_9.
Print Assumptions zz_len_sample_4_0.
Print Assumptions zz_len_sample_8_0.
Print Assumptions piu_zz_sample_n1_j1.
Print Assumptions piu_zz_sample_n1_j2.
Print Assumptions piu_zz_sample_n2_j0.
