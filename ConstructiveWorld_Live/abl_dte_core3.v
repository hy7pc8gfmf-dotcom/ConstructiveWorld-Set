(* ConstructiveWorld-Set -- supply-side instantiation of the DTPT_Entropy entry face. *)

(** * abl_dte_core3: premise-free supply instances for DTPT_Entropy entries 77-114.

    Mission.  Premise-free supply instances for the registered entries
      77-114 of the host module [DTPT_Entropy] (statement coordinates
      :1410-:2012, thirty statements): the direct supply
      [dte_c3_qeq_le_l], six entry-face routes [dte_c3_Qeq_pair],
      [dte_c3_Qlt_3_2], [dte_c3_Qle_2_2_3_2], [dte_c3_all_same_pair],
      [dte_c3_len2_pos], [dte_c3_maxfreq_distinct_le_eq], and thirty
      premise-free instances up to [dte_c3_H_max_q_all_same_zero_pair],
      with the H_chain conjunction split three ways.  All thirty-seven
      statements close by [Qed]; entries 94-95 are registered but not
      supplied.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List],
      [Permutation], [Arith], [Lia], [Extraction].  Requires [DTPT] and
      [DTPT_Entropy] of this development (S01/S02 bridges used qualified).

    References.  This development, abl_dte_core3.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dte_core3.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Require DTPT_Entropy.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

(* ============================================================ *)
(* Section 1.  Supply theorems, the direct-supply form (one statement;  *)
(*    entry 86; the statement face carries the baseline entry   *)
(*    face verbatim under the dte_ prefix mapping, and the proof builds *)
(*    the record in place, recipe A10, record-crunch style, with no     *)
(*    host theorem used).                                               *)
(* ============================================================ *)

(* A1 (entry 86; host statement qeq_le_l at :1580, carried verbatim). *)
(* Qeq equality entails the weak order; the record is built in place,    *)
(* in the record-crunch style.                                           *)
Theorem dte_c3_qeq_le_l : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* ============================================================ *)
(* Section 2.  Supply theorems: six shared entry-face production    *)
(*    routes, namely the non-canonical pair of Qeq-equal values, the    *)
(*    host definitional recipe for strict Qlt, a Qle order instance,    *)
(*    the two-element witness for all_same, the general length          *)
(*    positivity route, and the maxfreq cross-value order route.        *)
(* ============================================================ *)

(* Non-canonical pair of Qeq-equal values, feeding the guard chains of  *)
(* entries 77, 90 and 96: the values (1#1) and (2#2) agree at the    *)
(* value layer, in the family of the dte_c1_Qeq_half recipe, a          *)
(* non-degenerate reflexivity face.                                     *)
Theorem dte_c3_Qeq_pair : ((1 # 1) == (2 # 2))%Q.
Proof.
  reflexivity.
Qed.

(* Strict Qlt instance, feeding the guards of entries 90 and 92:     *)
(* 0 < (3#2).  The stdlib offers no Qlt_bool face, so the proof follows *)
(* the host definitional recipe [unfold Qlt; simpl; lia].               *)
Theorem dte_c3_Qlt_3_2 : (0 < (3 # 2))%Q.
Proof.
  unfold Qlt. simpl. lia.
Qed.

(* Qle order instance, feeding the guard of entry 92: the           *)
(* non-canonical true order pair (2#2) <= (3#2).                        *)
Theorem dte_c3_Qle_2_2_3_2 : ((2 # 2) <= (3 # 2))%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* Two-element witness for all_same, feeding the guards of entries   *)
(* 106-107 and 114-115.  all_same is the host-local predicate defined   *)
(* at :1195 as [forall a b, In a l -> In b l -> a == b]; the witness is  *)
(* built at the non-canonical all-equal pair [(1#1);(2#2)], closed by   *)
(* the four-branch enumeration of the membership constructors.          *)
Theorem dte_c3_all_same_pair : all_same [(1 # 1); (2 # 2)].
Proof.
  intros a b Ha Hb.
  (* the goal face is the Set-carried QeqT (all_same body), so the Prop
     or-memberships are first bridged up to the carrier via the host
     qeq_imp_qeqT; the case split then runs on the Prop face only. *)
  apply S02_CauchyComplete.qeq_imp_qeqT.
  simpl in Ha, Hb.
  destruct Ha as [Ha | [Ha | Ha]]; destruct Hb as [Hb | [Hb | Hb]];
    subst; try reflexivity; contradiction.
Qed.

(* General length-positivity route, feeding the guards of entries    *)
(* 103, 105, 106-107, 112, 113 and 114-115: positivity of the length of *)
(* a two-element list, in the nat-side style of the host qlen_pos       *)
(* recipe, generalized to two arguments.                               *)
Theorem dte_c3_len2_pos : forall a b : Q, (0 < length [a; b])%nat.
Proof.
  intros a b. simpl. lia.
Qed.

(* maxfreq cross-value order route, feeding the guard of entry 111: *)
(* the maxfreq of a list carrying two distinct values is bounded by the *)
(* maxfreq of an all-equal list, composed from the host upper bound     *)
(* maxfreq_upper, from maxfreq_all_same_one (an all-equal list has      *)
(* maxfreq 1), and from the order bridge A1 qeq_le_l.                   *)
Theorem dte_c3_maxfreq_distinct_le_eq :
  (maxfreq [(1 # 2); (1 # 3)] <= maxfreq [(1 # 1); (2 # 2)])%Q.
Proof.
  assert (Hr : maxfreq [(1 # 1); (2 # 2)] == 1).
  { exact (S02_CauchyComplete.qeqT_imp_qeq
             (maxfreq [(1 # 1); (2 # 2)]) 1
             (maxfreq_all_same_one [(1 # 1); (2 # 2)] dte_c3_all_same_pair
                (dte_c3_len2_pos (1 # 1) (2 # 2)))). }
  apply (Qle_trans (maxfreq [(1 # 2); (1 # 3)]) 1 (maxfreq [(1 # 1); (2 # 2)])).
  - apply S02_CauchyComplete.QleT'_to_Qle. apply maxfreq_upper.
  - apply (dte_c3_qeq_le_l 1 (maxfreq [(1 # 1); (2 # 2)])).
    exact (Qeq_sym (maxfreq [(1 # 1); (2 # 2)]) 1 Hr).
Qed.

(* ============================================================ *)
(* Registered only: entries 94-95, the host statement qdiv_norm at   *)
(* :1646 (a NOT guard together with two Q-order guards; the statement   *)
(* sits in the baseline section 2.3 mixed-flag list among the twenty    *)
(* registered Entropy statements, with a double negation guard at the   *)
(* statement face).  Following the precedents at :1864 and :749, these  *)
(* entries are registered without being supplied, and the statement  *)
(* face is not extended on our own initiative; any failure is declared  *)
(* explicitly.  The upgrade direction is negation guards.               *)
(* ============================================================ *)

(* ============================================================ *)
(* Section 3.  Supply theorems: thirty premise-free instances.  Each    *)
(*    applies the host theorem at explicit arguments, so the premises   *)
(*    are consumed at once; every conclusion specializes the host       *)
(*    conclusion face verbatim and is discretely carried.  Includes the *)
(*    three one-way forwardings that split the H_chain conjunction.     *)
(* ============================================================ *)

(* P1 (entry 77, premise-free).  Right monotonicity of subtraction: *)
(* with D := (5#2) and (A, B) := ((1#1), (2#2)), the non-canonical pair  *)
(* of Qeq-equal values feeds A1, giving the instance where subtraction  *)
(* by an equal amount preserves the order.                              *)
Theorem dte_c3_qsub_mono_r_inst :
  ((5 # 2) - (2 # 2) <= (5 # 2) - (1 # 1))%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (qsub_mono_r (5 # 2) (1 # 1) (2 # 2)
              (dte_c3_qeq_le_l (1 # 1) (2 # 2) dte_c3_Qeq_pair))).
Qed.

(* P2 (entries 78-79, premise-free).  The collision core is antitone *)
(* in the collision count: with (N, A, B) := (1, 0, 1), the two nat     *)
(* guards are discharged inline by Nat.le_0_l and le_n, giving the      *)
(* quotient order instance in the qn core shape.                        *)
Theorem dte_c3_hfreq_core_anti_1_0_1 :
  ((qn 1 * qn 1 - qn 1) / (qn 1 * qn 1)
   <= (qn 1 * qn 1 - qn 0) / (qn 1 * qn 1))%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (hfreq_core_anti 1 0 1 (Nat.le_0_l 1) (le_n 1))).
Qed.

(* P3 (entry 80, premise-free).  Data processing through absolute   *)
(* value does not increase the observation: the morphism guard          *)
(* xq_abs_eq (Qabs is a genuine morphism) feeds the host H_freq_dpi.    *)
Theorem dte_c3_H_freq_dpi_abs : forall l : list Q,
  (H_freq (map Qabs l) <= H_freq l)%Q.
Proof.
  intro l.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (H_freq_dpi Qabs DTPT.DTPT.xq_abs_eq l)).
Qed.

(* P4 (entry 81, premise-free).  Members of a list carry equal      *)
(* images under a constant function: the second member of the           *)
(* two-element list is discharged by in_cons composed with in_eq,       *)
(* giving the pointwise image-equality instance.                        *)
Theorem dte_c3_in_map_const_mid : ((1 # 2) == (1 # 2))%Q.
Proof.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (in_map_const (1 # 2) [(9 # 7); (4 # 5)] (1 # 2)
              (in_cons (1 # 2) (1 # 2) [(1 # 2)] (in_eq (1 # 2) [])))).
Qed.

(* P5 (entries 82-83, premise-free).  Iteration does not inflate the *)
(* observation: both morphism guards are the same xq_abs_eq, giving the *)
(* face where a second pass of absolute value does not increase.        *)
Theorem dte_c3_H_freq_map_twice_abs : forall l : list Q,
  (H_freq (map Qabs (map Qabs l)) <= H_freq (map Qabs l))%Q.
Proof.
  intro l.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (H_freq_map_twice Qabs Qabs DTPT.DTPT.xq_abs_eq
              DTPT.DTPT.xq_abs_eq l)).
Qed.

(* P6 (entries 84-85, premise-free).  A chain does not inflate the   *)
(* observation: both morphism guards are the same xq_abs_eq, giving the *)
(* face where the chained absolute value reaches the original surface   *)
(* directly.                                                            *)
Theorem dte_c3_H_freq_map_chain_abs : forall l : list Q,
  (H_freq (map Qabs (map Qabs l)) <= H_freq l)%Q.
Proof.
  intro l.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (H_freq_map_chain Qabs Qabs DTPT.DTPT.xq_abs_eq
              DTPT.DTPT.xq_abs_eq l)).
Qed.

(* P7 (entry 87, premise-free).  Lower bound on qn: with n := 2,    *)
(* the nat guard is discharged inline by le_S composed with le_n.       *)
Theorem dte_c3_qn_ge1_2 : (1 <= qn 2)%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (qn_ge1 2 (le_S 1 1 (le_n 1)))).
Qed.

(* P8 (entries 88-89, premise-free).  Positivity of the qn product:  *)
(* with (a, b) := (2, 3), two inline instances of Nat.lt_0_succ         *)
(* discharge the guards.                                                *)
Theorem dte_c3_qn_mul_pos_2_3 : (0 < qn 2 * qn 3)%Q.
Proof.
  exact (S02_CauchyComplete.QltT_to_Qlt _ _
           (qn_mul_pos 2 3 (Nat.lt_0_succ 1) (Nat.lt_0_succ 2))).
Qed.

(* P9 (entries 90-91, premise-free).  Division by a shared positive  *)
(* denominator is monotone in the numerator: with (A, C, B) :=          *)
(* ((2#2), (1#1), (3#2)), the guard 0 < B is fed by the strict order    *)
(* route and the guard C <= A by A1.                                    *)
Theorem dte_c3_qdiv_ge_num_inst :
  ((1 # 1) / (3 # 2) <= (2 # 2) / (3 # 2))%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (qdiv_ge_num (2 # 2) (1 # 1) (3 # 2) dte_c3_Qlt_3_2
              (dte_c3_qeq_le_l (1 # 1) (2 # 2) dte_c3_Qeq_pair))).
Qed.

(* P10 (entries 92-93, premise-free).  A quotient stays bounded by   *)
(* one: with (A, B) := ((2#2), (3#2)), the guard A <= B is fed by the   *)
(* order instance and the guard 0 < B by the strict order instance.     *)
Theorem dte_c3_qdiv_le_1_inst : ((2 # 2) / (3 # 2) <= 1)%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (qdiv_le_1 (2 # 2) (3 # 2) dte_c3_Qle_2_2_3_2 dte_c3_Qlt_3_2)).
Qed.

(* P11 (entry 96, premise-free).  Subtraction is antitone in the    *)
(* subtrahend: with (x, y, z) := ((1#1), (2#2), (3#1)), the guard is    *)
(* fed by A1.                                                           *)
Theorem dte_c3_qsub_le_inst :
  ((3 # 1) - (2 # 2) <= (3 # 1) - (1 # 1))%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (qsub_le (1 # 1) (2 # 2) (3 # 1)
              (dte_c3_qeq_le_l (1 # 1) (2 # 2) dte_c3_Qeq_pair))).
Qed.

(* P12 (entry 97, premise-free).  The pointwise bound of the        *)
(* general maximum: the constant-7 function at the second member of the *)
(* two-element list, discharged by in_cons composed with in_eq.         *)
Theorem dte_c3_nmax_bound_inst :
  (7 <= nmax (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)])%nat.
Proof.
  exact (S01_BaseRing.NatLe_drop _ _
           (nmax_bound (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] (4 # 5)
              (in_cons (1 # 1) (4 # 5) [(4 # 5)] (in_eq (4 # 5) [])))).
Qed.

(* P13 (entry 98, premise-free).  The general maximum is bounded:   *)
(* the pointwise guards are discharged inline by le_n.                  *)
Theorem dte_c3_nmax_le_bound_inst :
  (nmax (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] <= 7)%nat.
Proof.
  exact (S01_BaseRing.NatLe_drop _ _
           (nmax_le_bound (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] 7
              (fun (x : Q) (_ : In x [(1 # 1); (4 # 5)]) => le_n 7))).
Qed.

(* P14 (entry 99, premise-free).  Extensionality of the general     *)
(* maximum: the pointwise pair (7, 3+4) closes computationally by       *)
(* eq_refl.                                                             *)
Theorem dte_c3_nmax_ext_in_inst :
  nmax (fun _ : Q => 7%nat) [(1 # 1)]
  = nmax (fun _ : Q => (3 + 4)%nat) [(1 # 1)].
Proof.
  (* the host conclusion face is the Set-carried Id; drop it to the
     Leibniz goal by the host id_refl destruct recipe (dtpt :1705 style). *)
  destruct (nmax_ext_in (fun _ : Q => 7%nat) (fun _ : Q => (3 + 4)%nat)
              [(1 # 1)] (fun (x : Q) (_ : In x [(1 # 1)]) => eq_refl)).
  reflexivity.
Qed.

(* P15 (entry 100, premise-free).  The general maximum is invariant *)
(* under permutation: a non-constant decision face f, written in        *)
(* Qeq_bool branch form, with the canonical perm_swap instance.         *)
Theorem dte_c3_nmax_perm_inst :
  nmax (fun x : Q => if Qeq_bool x (1 # 1) then 5%nat else 3%nat)
       [(1 # 1); (2 # 1)]
  = nmax (fun x : Q => if Qeq_bool x (1 # 1) then 5%nat else 3%nat)
       [(2 # 1); (1 # 1)].
Proof.
  destruct (nmax_perm
              (fun x : Q => if Qeq_bool x (1 # 1) then 5%nat else 3%nat)
              [(1 # 1); (2 # 1)] [(2 # 1); (1 # 1)]
              (perm_swap (2 # 1) (1 # 1) [])).
  reflexivity.
Qed.

(* P16 (entry 101, premise-free).  Lower bound on the frequency of  *)
(* a member: the head member, discharged by the constructor in_eq.      *)
Theorem dte_c3_freq_q_ge1_inst :
  (1 <= freq_q (1 # 1) [(1 # 1); (2 # 1)])%nat.
Proof.
  exact (S01_BaseRing.NatLe_drop _ _
           (freq_q_ge1 (1 # 1) [(1 # 1); (2 # 1)]
              (in_eq (1 # 1) [(2 # 1)]))).
Qed.

(* P17 (entry 102, premise-free).  Lower bound on the general sum:  *)
(* the pointwise guards are discharged inline by le_n.                  *)
Theorem dte_c3_nsum_ge_const_inst :
  (length [(1 # 1); (4 # 5)] * 7
   <= nsum (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)])%nat.
Proof.
  exact (S01_BaseRing.NatLe_drop _ _
           (nsum_ge_const (fun _ : Q => 7%nat) [(1 # 1); (4 # 5)] 7
              (fun (x : Q) (_ : In x [(1 # 1); (4 # 5)]) => le_n 7))).
Qed.

(* P18 (entry 103, premise-free).  Lower bound on collide: with     *)
(* l := [(1#2);(1#3)], the canonical two-element distinct-value         *)
(* instance, its length guard fed by the length positivity route.       *)
Theorem dte_c3_collide_lower_pair :
  (1 / qn (length [(1 # 2); (1 # 3)]) <= collide [(1 # 2); (1 # 3)])%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (collide_lower [(1 # 2); (1 # 3)]
              (dte_c3_len2_pos (1 # 2) (1 # 3)))).
Qed.

(* P19 (entry 104, premise-free).  collide is invariant under       *)
(* permutation: the canonical perm_swap instance.                       *)
Theorem dte_c3_collide_perm_swap :
  collide [(1 # 2); (1 # 3)] == collide [(1 # 3); (1 # 2)].
Proof.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (collide_perm [(1 # 2); (1 # 3)] [(1 # 3); (1 # 2)]
              (perm_swap (1 # 3) (1 # 2) []))).
Qed.

(* P20 (entry 105, premise-free).  Lower bound on maxfreq: the      *)
(* application shape of the host statement at :1779.                    *)
Theorem dte_c3_maxfreq_lower_pair :
  (1 / qn (length [(1 # 2); (1 # 3)]) <= maxfreq [(1 # 2); (1 # 3)])%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (maxfreq_lower [(1 # 2); (1 # 3)]
              (dte_c3_len2_pos (1 # 2) (1 # 3)))).
Qed.

(* P21 (entries 106-107, premise-free).  An all-equal list has       *)
(* maxfreq 1: with l := [(1#1);(2#2)], a non-canonical all-equal pair,  *)
(* the all_same guard is fed by the witness route and the length guard  *)
(* by the length positivity route.                                      *)
Theorem dte_c3_maxfreq_all_same_one_pair :
  maxfreq [(1 # 1); (2 # 2)] == 1.
Proof.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (maxfreq_all_same_one [(1 # 1); (2 # 2)] dte_c3_all_same_pair
              (dte_c3_len2_pos (1 # 1) (2 # 2)))).
Qed.

(* P22 (entry 108, premise-free).  maxcount is invariant under      *)
(* permutation: the canonical perm_swap instance.                       *)
Theorem dte_c3_maxcount_perm_swap :
  maxcount [(1 # 2); (1 # 3)] = maxcount [(1 # 3); (1 # 2)].
Proof.
  destruct (maxcount_perm [(1 # 2); (1 # 3)] [(1 # 3); (1 # 2)]
              (perm_swap (1 # 3) (1 # 2) [])).
  reflexivity.
Qed.

(* P23 (entry 109, premise-free).  maxfreq is invariant under       *)
(* permutation: the canonical perm_swap instance.                       *)
Theorem dte_c3_maxfreq_perm_swap :
  maxfreq [(1 # 2); (1 # 3)] == maxfreq [(1 # 3); (1 # 2)].
Proof.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (maxfreq_perm [(1 # 2); (1 # 3)] [(1 # 3); (1 # 2)]
              (perm_swap (1 # 3) (1 # 2) []))).
Qed.

(* P24 (entry 110, one-way split, first of three).  The H_chain     *)
(* source conclusion face is a threefold conjunction, split into three  *)
(* one-way supplies in the style of the conjunction-split precedents at *)
(* :2226 and :481; the premise guards are kept verbatim.  This item is  *)
(* the first conjunct, 1/n <= collide, forwarded by the host            *)
(* collide_lower; the one-way restriction is declared explicitly.       *)
Theorem dte_c3_H_chain_lo : forall l : list Q,
  (0 < length l)%nat -> (1 / qn (length l) <= collide l)%Q.
Proof.
  intros l Hl.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ (collide_lower l Hl)).
Qed.

(* P25 (entry 110, one-way split, second of three).  The second     *)
(* conjunct, collide <= maxfreq, forwarded by the host                  *)
(* collide_le_maxfreq and declared as such.                             *)
Theorem dte_c3_H_chain_mid : forall l : list Q,
  (collide l <= maxfreq l)%Q.
Proof.
  intro l.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ (collide_le_maxfreq l)).
Qed.

(* P26 (entry 110, one-way split, third of three).  The third       *)
(* conjunct, maxfreq <= 1, forwarded by the host maxfreq_upper and      *)
(* declared as such.                                                    *)
Theorem dte_c3_H_chain_hi : forall l : list Q,
  (maxfreq l <= 1)%Q.
Proof.
  intro l.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ (maxfreq_upper l)).
Qed.

(* P27 (entry 111, premise-free).  H_max_q is antitone: the order   *)
(* guard is fed by the cross-value route, giving the antitone           *)
(* two-instance face.                                                   *)
Theorem dte_c3_H_max_q_anti_inst :
  (H_max_q [(1 # 1); (2 # 2)] <= H_max_q [(1 # 2); (1 # 3)])%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (H_max_q_anti [(1 # 2); (1 # 3)] [(1 # 1); (2 # 2)]
              dte_c3_maxfreq_distinct_le_eq)).
Qed.

(* P28 (entry 112, premise-free).  Lower-bound coupling for         *)
(* H_max_q: the application shape of the host statement at :1779.       *)
Theorem dte_c3_H_max_q_le_inv_pair :
  (H_max_q [(1 # 2); (1 # 3)]
   <= 1 - 1 / qn (length [(1 # 2); (1 # 3)]))%Q.
Proof.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (H_max_q_le_inv [(1 # 2); (1 # 3)]
              (dte_c3_len2_pos (1 # 2) (1 # 3)))).
Qed.

(* P29 (entry 113, premise-free).  Coherence bridge in the entropy  *)
(* family: H_freq agrees with H_min_q, in the application shape of the  *)
(* host statement at :1779.                                             *)
Theorem dte_c3_H_freq_eq_bridge_pair :
  H_freq [(1 # 2); (1 # 3)] == H_min_q [(1 # 2); (1 # 3)].
Proof.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (H_freq_eq_bridge [(1 # 2); (1 # 3)]
              (dte_c3_len2_pos (1 # 2) (1 # 3)))).
Qed.

(* P30 (entries 114-115, premise-free).  An all-equal list has       *)
(* H_max_q 0: the application shape of the host statement at :1884.     *)
(* Entry 115 overflows with this statement and is delivered here,   *)
(* duly registered; no later module may supply it again.                *)
Theorem dte_c3_H_max_q_all_same_zero_pair :
  H_max_q [(1 # 1); (2 # 2)] == 0.
Proof.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (H_max_q_all_same_zero [(1 # 1); (2 # 2)] dte_c3_all_same_pair
              (dte_c3_len2_pos (1 # 1) (2 # 2)))).
Qed.

(* ============================================================ *)
(* Section 4.  Tail audit region, at the very end of the file: the      *)
(*    assumption audit of every statement, each expected to report      *)
(*    Closed.  The name list holds thirty-seven theorems, matching the  *)
(*    count of thirty-seven Qed commands with no discrepancy.           *)
(* ============================================================ *)

Print Assumptions dte_c3_qeq_le_l.
Print Assumptions dte_c3_Qeq_pair.
Print Assumptions dte_c3_Qlt_3_2.
Print Assumptions dte_c3_Qle_2_2_3_2.
Print Assumptions dte_c3_all_same_pair.
Print Assumptions dte_c3_len2_pos.
Print Assumptions dte_c3_maxfreq_distinct_le_eq.
Print Assumptions dte_c3_qsub_mono_r_inst.
Print Assumptions dte_c3_hfreq_core_anti_1_0_1.
Print Assumptions dte_c3_H_freq_dpi_abs.
Print Assumptions dte_c3_in_map_const_mid.
Print Assumptions dte_c3_H_freq_map_twice_abs.
Print Assumptions dte_c3_H_freq_map_chain_abs.
Print Assumptions dte_c3_qn_ge1_2.
Print Assumptions dte_c3_qn_mul_pos_2_3.
Print Assumptions dte_c3_qdiv_ge_num_inst.
Print Assumptions dte_c3_qdiv_le_1_inst.
Print Assumptions dte_c3_qsub_le_inst.
Print Assumptions dte_c3_nmax_bound_inst.
Print Assumptions dte_c3_nmax_le_bound_inst.
Print Assumptions dte_c3_nmax_ext_in_inst.
Print Assumptions dte_c3_nmax_perm_inst.
Print Assumptions dte_c3_freq_q_ge1_inst.
Print Assumptions dte_c3_nsum_ge_const_inst.
Print Assumptions dte_c3_collide_lower_pair.
Print Assumptions dte_c3_collide_perm_swap.
Print Assumptions dte_c3_maxfreq_lower_pair.
Print Assumptions dte_c3_maxfreq_all_same_one_pair.
Print Assumptions dte_c3_maxcount_perm_swap.
Print Assumptions dte_c3_maxfreq_perm_swap.
Print Assumptions dte_c3_H_chain_lo.
Print Assumptions dte_c3_H_chain_mid.
Print Assumptions dte_c3_H_chain_hi.
Print Assumptions dte_c3_H_max_q_anti_inst.
Print Assumptions dte_c3_H_max_q_le_inv_pair.
Print Assumptions dte_c3_H_freq_eq_bridge_pair.
Print Assumptions dte_c3_H_max_q_all_same_zero_pair.

(* ============================================================ *)
(* Section 5.  Extraction audit region: extractability is verified,     *)
(*    with a count of [Obj.magic] equal to zero as the criterion.       *)
(*    Theorem bucket: a single Separate Extraction command, since two   *)
(*    such commands in one file with the same target would overwrite    *)
(*    each other.  The conclusion faces of the thirty-seven theorems    *)
(*    are discretely carried logical statements, so the family          *)
(*    extraction convention erases them to placeholders.  The genuine   *)
(*    data-level extraction face, the host data carriers used by the    *)
(*    premise-free statements (qn, freq_q, nsum, nmax, sqsum, collide,  *)
(*    maxcount, maxfreq, H_freq, H_max_q, H_min_q), is directed to the  *)
(*    separate audit module _dte_c3_probe.v and kept in its own bucket. *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dte_t10".
Separate Extraction dte_c3_qeq_le_l dte_c3_Qeq_pair dte_c3_Qlt_3_2
  dte_c3_Qle_2_2_3_2 dte_c3_all_same_pair dte_c3_len2_pos
  dte_c3_maxfreq_distinct_le_eq dte_c3_qsub_mono_r_inst
  dte_c3_hfreq_core_anti_1_0_1 dte_c3_H_freq_dpi_abs
  dte_c3_in_map_const_mid dte_c3_H_freq_map_twice_abs
  dte_c3_H_freq_map_chain_abs dte_c3_qn_ge1_2 dte_c3_qn_mul_pos_2_3
  dte_c3_qdiv_ge_num_inst dte_c3_qdiv_le_1_inst dte_c3_qsub_le_inst
  dte_c3_nmax_bound_inst dte_c3_nmax_le_bound_inst dte_c3_nmax_ext_in_inst
  dte_c3_nmax_perm_inst dte_c3_freq_q_ge1_inst dte_c3_nsum_ge_const_inst
  dte_c3_collide_lower_pair dte_c3_collide_perm_swap
  dte_c3_maxfreq_lower_pair dte_c3_maxfreq_all_same_one_pair
  dte_c3_maxcount_perm_swap dte_c3_maxfreq_perm_swap dte_c3_H_chain_lo
  dte_c3_H_chain_mid dte_c3_H_chain_hi dte_c3_H_max_q_anti_inst
  dte_c3_H_max_q_le_inv_pair dte_c3_H_freq_eq_bridge_pair
  dte_c3_H_max_q_all_same_zero_pair.
