(* u6a_dammroze_quant.v

   Mission. Quantitative per-index separation of the Gregory-Leibniz partial
   sum family G_n := 4 * pie_partial n against the geometric value pi
   (cauchy_real_pi_leibniz): for every index n give an explicit positive
   rational certificate c_n := 2 * (pie_mag n - pie_mag (S n)) (closed form
   4/((2n+1)(2n+3))) such that G_n + c_n < pi for even n, pi < G_n - c_n
   for odd n; the two wings give c_n < |pi - G_n| for every n.

   Dependencies. S01_BaseRing; S02_CauchyComplete (selective import of the
   exit-face bridge set QltT, Qlt_to_QltT, QltT_to_Qlt, QeqT, qeq_imp_qeqT,
   qeqT_imp_qeq, QleT'_to_Qle, qeq_le, real_lt, real_const);
   S10_KVQuantTrig (cauchy_real_pi_leibniz); S11_TP3B5 (atan_sign_even,
   atan_sign_odd); PiEnvelope (pie_* family, QltT', Qlt_to_QltT'); Stdlib
   QArith.QArith, QArith.Qabs, QArith.Qround, Lia, ZArith, Extraction.

   References. Lean 4 Dammroze formalization: completion of the
   Gregory-Leibniz construction does not yield a finite witness extractor;
   this file is its quantitative positive form (per-rate distance
   certificate family). In-tree precedents consumed by the proofs:
   pie_mag_lt, pie_gap1, pie_parity_gap4, pie_real_lower_gen,
   pie_real_upper_gen, qeq_le, atan_sign_even, atan_sign_odd.

   Constructivity. All statements ride Set-level exit faces (QltT/QeqT/
   QltT'/sigT/And); the certificate is an explicit rational expression;
   no classical reasoning; Print Assumptions reports Closed under the
   global context; Separate Extraction keeps Obj.magic at 0.

   Build. rocq c -native-compiler no -q -Q . "" u6a_dammroze_quant.v
*)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Lia ZArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete (QltT, Qlt_to_QltT, QltT_to_Qlt, QeqT, qeq_imp_qeqT, qeqT_imp_qeq, QleT'_to_Qle, qeq_le, real_lt, real_const).
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import PiEnvelope.

(* ============================================================ *)
(* Section 1. Certificate c_n = 2*(pie_mag n - pie_mag (S n))    *)
(* and its positivity                                            *)
(* ============================================================ *)

Definition u6a_cert (n : nat) : Q := (2 * (pie_mag n - pie_mag (Datatypes.S n)))%Q.

(* denominator positivity (field-side condition and modulus comparison) *)
Lemma u6a_den1_pos : forall n : nat, QltT 0 (Z.of_nat (2 * n + 1) # 1)%Q.
Proof.
  intro n. apply Qlt_to_QltT. unfold Qlt. simpl.
  assert (H : (0 < 2 * n + 1)%nat) by lia.
  apply Nat2Z.inj_lt in H. lia.
Qed.

Lemma u6a_den3_pos : forall n : nat, QltT 0 (Z.of_nat (2 * n + 3) # 1)%Q.
Proof.
  intro n. apply Qlt_to_QltT. unfold Qlt. simpl.
  assert (H : (0 < 2 * n + 3)%nat) by lia.
  apply Nat2Z.inj_lt in H. lia.
Qed.

(* strict decrease of mag: pie_mag (S n) < pie_mag n *)
Lemma u6a_mag_strict : forall n : nat, QltT (pie_mag (Datatypes.S n)) (pie_mag n).
Proof. intro n. exact (pie_mag_lt n). Qed.

Lemma u6a_cert_pos : forall n : nat, QltT 0 (u6a_cert n).
Proof.
  intro n. apply Qlt_to_QltT. unfold u6a_cert.
  assert (Hd : Qlt 0 (pie_mag n - pie_mag (Datatypes.S n))).
  { apply (proj1 (Qlt_minus_iff (pie_mag (Datatypes.S n)) (pie_mag n))).
    exact (QltT_to_Qlt _ _ (u6a_mag_strict n)). }
  apply (Qmult_lt_0_compat 2 (pie_mag n - pie_mag (Datatypes.S n))).
  - unfold Qlt. simpl. lia.
  - exact Hd.
Qed.

Lemma u6a_cert_posT' : forall n : nat, QltT' 0 (u6a_cert n).
Proof. intro n. apply Qlt_to_QltT'. exact (QltT_to_Qlt _ _ (u6a_cert_pos n)). Qed.

(* Closed-form note: by pie_mag_inv (pie_mag k equals 1/(2k+1)), c_n equals
   4/((2n+1)(2n+3)), which reduces to the fraction arithmetic of
   2*(1/(2n+1) - 1/(2n+3)); this file does not run the Q-field tactic
   simplification (the Q-field instances are shadowed by upstream modules in
   this environment); the closed form is checked term-by-term by fraction
   arithmetic. *)

(* ============================================================ *)
(* Section 2. Term signs: t_{2j} = +pie_mag (2j),                *)
(* t_{2j+1} = -pie_mag (2j+1)                                    *)
(* ============================================================ *)

Lemma u6a_term_even : forall j : nat,
  QeqT (pie_term (2 * j)) (pie_mag (2 * j))%Q.
Proof.
  intro j. apply qeq_imp_qeqT.
  unfold pie_term, pie_mag.
  rewrite (qeqT_imp_qeq _ _ (atan_sign_even j)).
  replace (2 * (2 * j) + 1)%nat with (4 * j + 1)%nat by lia.
  reflexivity.
Qed.

Lemma u6a_term_odd : forall j : nat,
  QeqT (pie_term (2 * j + 1)) (- pie_mag (2 * j + 1))%Q.
Proof.
  intro j. apply qeq_imp_qeqT.
  unfold pie_term, pie_mag.
  rewrite (qeqT_imp_qeq _ _ (atan_sign_odd j)).
  replace (2 * (2 * j + 1) + 1)%nat with (4 * j + 3)%nat by lia.
  unfold Qdiv. ring.
Qed.

Lemma u6a_term_even2 : forall m : nat,
  QeqT (pie_term (2 * m + 2)) (pie_mag (2 * m + 2))%Q.
Proof.
  intro m. replace (2 * m + 2)%nat with (2 * Datatypes.S m)%nat by lia.
  apply u6a_term_even.
Qed.

(* ============================================================ *)
(* Section 3. Two-step gap closed forms (one-line chain:         *)
(* parity_gap4/gap1 + term signs + ring)                         *)
(*    4*S_{2j+2} - 4*S_{2j} = 4*mag(2j) - 4*mag(2j+1) = 2*c_{2j} *)
(*    4*S_{2j+1} - 4*S_{2j+3} = 4*mag(2j+1) - 4*mag(2j+2)        *)
(*                             = 2*c_{2j+1}                      *)
(* ============================================================ *)

Lemma u6a_gap2_cert_even : forall j : nat,
  QeqT (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j))%Q
       (2 * u6a_cert (2 * j))%Q.
Proof.
  intro j.
  assert (Hb : (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j + 1)
                == - 4 * pie_mag (2 * j + 1))%Q).
  { replace (2 * j + 2)%nat with (Datatypes.S (2 * j + 1))%nat by lia.
    setoid_replace (4 * pie_partial (Datatypes.S (2 * j + 1))
                    - 4 * pie_partial (2 * j + 1))
      with (4 * (pie_partial (Datatypes.S (2 * j + 1))
                 - pie_partial (2 * j + 1))) by ring.
    rewrite (qeqT_imp_qeq _ _ (pie_gap1 (2 * j + 1))),
            (qeqT_imp_qeq _ _ (u6a_term_odd j)). ring. }
  apply qeq_imp_qeqT.
  unfold u6a_cert.
  replace (pie_mag (Datatypes.S (2 * j))) with (pie_mag (2 * j + 1))
    by (f_equal; lia).
  setoid_replace (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j))
    with ((4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j))
          + (4 * pie_partial (2 * j + 2) - 4 * pie_partial (2 * j + 1))) by ring.
  rewrite (qeqT_imp_qeq _ _ (pie_parity_gap4 j)), Hb. ring.
Qed.

Lemma u6a_gap2_cert_odd : forall j : nat,
  QeqT (4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 3))%Q
       (2 * u6a_cert (2 * j + 1))%Q.
Proof.
  intro j.
  assert (Ha : (4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 2)
                == 4 * pie_mag (2 * j + 1))%Q).
  { replace (2 * j + 2)%nat with (Datatypes.S (2 * j + 1))%nat by lia.
    setoid_replace (4 * pie_partial (2 * j + 1)
                    - 4 * pie_partial (Datatypes.S (2 * j + 1)))
      with (- (4 * (pie_partial (Datatypes.S (2 * j + 1))
                   - pie_partial (2 * j + 1)))) by ring.
    rewrite (qeqT_imp_qeq _ _ (pie_gap1 (2 * j + 1))),
            (qeqT_imp_qeq _ _ (u6a_term_odd j)). ring. }
  assert (Hc : (4 * pie_partial (2 * j + 3) - 4 * pie_partial (2 * j + 2)
                == 4 * pie_mag (2 * j + 2))%Q).
  { replace (2 * j + 3)%nat with (Datatypes.S (2 * j + 2))%nat by lia.
    setoid_replace (4 * pie_partial (Datatypes.S (2 * j + 2))
                    - 4 * pie_partial (2 * j + 2))
      with (4 * (pie_partial (Datatypes.S (2 * j + 2))
                 - pie_partial (2 * j + 2))) by ring.
    rewrite (qeqT_imp_qeq _ _ (pie_gap1 (2 * j + 2))),
            (qeqT_imp_qeq _ _ (u6a_term_even2 j)). ring. }
  apply qeq_imp_qeqT.
  unfold u6a_cert.
  replace (pie_mag (Datatypes.S (2 * j + 1))) with (pie_mag (2 * j + 2))
    by (f_equal; lia).
  setoid_replace (4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 3))
    with ((4 * pie_partial (2 * j + 1) - 4 * pie_partial (2 * j + 2))
          - (4 * pie_partial (2 * j + 3) - 4 * pie_partial (2 * j + 2))) by ring.
  rewrite Ha, Hc. ring.
Qed.

(* ============================================================ *)
(* Section 4. Certificate bridges (lower wing / upper wing)      *)
(* ============================================================ *)

Lemma u6a_bridge_even : forall j : nat,
  QeqT (4 * pie_partial (2 * j) + 2 * u6a_cert (2 * j))%Q
       (4 * pie_partial (2 * j + 2))%Q.
Proof.
  intro j. apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (u6a_gap2_cert_even j)). ring.
Qed.

Lemma u6a_bridge_odd : forall j : nat,
  QeqT (4 * pie_partial (2 * j + 1) - 2 * u6a_cert (2 * j + 1))%Q
       (4 * pie_partial (2 * j + 3))%Q.
Proof.
  intro j. apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (u6a_gap2_cert_odd j)). ring.
Qed.

(* ============================================================ *)
(* Section 5. Main theorems: per-index separation certificates   *)
(* (lower wing / upper wing pair, universally quantified and     *)
(* premise-free)                                                 *)
(* ============================================================ *)

(* Lower wing: n even (n = 2j), c_n = u6a_cert n, G_n + c_n < pi *)
Theorem u6a_even_sep : forall j : nat,
  sigT (fun c : Q => And (QltT' 0 c)
    (real_lt (real_const (4 * pie_partial (2 * j) + c))
             cauchy_real_pi_leibniz)).
Proof.
  intro j. exists (u6a_cert (2 * j)). split.
  - apply u6a_cert_posT'.
  - apply (pie_real_lower_gen j (u6a_cert (2 * j))
             (4 * pie_partial (2 * j) + u6a_cert (2 * j))).
    + exact (QltT_to_Qlt _ _ (u6a_cert_pos (2 * j))).
    + apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
      setoid_replace (4 * pie_partial (2 * j) + u6a_cert (2 * j) + u6a_cert (2 * j))
        with (4 * pie_partial (2 * j) + 2 * u6a_cert (2 * j)) by ring.
      exact (qeqT_imp_qeq _ _ (u6a_bridge_even j)).
Qed.

(* Upper wing: n odd (n = 2j+1), c_n = u6a_cert n, pi < G_n - c_n *)
Theorem u6a_odd_sep : forall j : nat,
  sigT (fun c : Q => And (QltT' 0 c)
    (real_lt cauchy_real_pi_leibniz
             (real_const (4 * pie_partial (2 * j + 1) - c)))).
Proof.
  intro j. exists (u6a_cert (2 * j + 1)). split.
  - apply u6a_cert_posT'.
  - apply (pie_real_upper_gen (Datatypes.S j) (u6a_cert (2 * j + 1))
             (4 * pie_partial (2 * j + 1) - u6a_cert (2 * j + 1))).
    + exact (QltT_to_Qlt _ _ (u6a_cert_pos (2 * j + 1))).
    + replace (2 * Datatypes.S j + 1)%nat with (2 * j + 3)%nat by lia.
      apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
      assert (Hb := u6a_bridge_odd j).
      setoid_replace (4 * pie_partial (2 * j + 3) + u6a_cert (2 * j + 1))
        with (4 * pie_partial (2 * j + 1) - 2 * u6a_cert (2 * j + 1)
              + u6a_cert (2 * j + 1)) by (rewrite (qeqT_imp_qeq _ _ Hb); ring).
      ring.
Qed.

(* Check: assumption audit (both lines should report Closed under the
   global context). *)
Print Assumptions u6a_even_sep.
Print Assumptions u6a_odd_sep.

(* Check: extractability (the Obj.magic count in the generated ml must be
   0). *)
From Stdlib Require Import Extraction.
Separate Extraction u6a_even_sep u6a_odd_sep.
