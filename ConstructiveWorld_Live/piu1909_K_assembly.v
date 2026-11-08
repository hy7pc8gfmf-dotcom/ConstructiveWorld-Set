(* ConstructiveWorld-Set -- coordinate assembly of the separated kernel load K. *)

(** * piu1909_K_assembly: the K-model assembly and its floor over the q-band.

    Mission.  The coordinate assembly of the separated kernel load K:
      [piu1909_Kmodel q b n] = |b^n * sev_full q n| * (105410/1341)
      + |b^n * sodd_full q n| * (9664/447) + 1/8 (sev/sodd the even/odd-side
      alternating sums), with the floor (9664/447) * (62125/82944) *
      (b^n * [piu1888_T0 n]) <= [piu1909_Kmodel q b n] in [piu1909_K_lower];
      the odd-side sum joins [piu1905_sodd_full] through the bridge
      [piu1909_sodd_full_bridge] (reflexivity after unfold).

    Dependencies.  Stdlib [QArith], [Lia].  Requires
      [piu1888_growth_quant_lemma] ([piu1888_qpow], [piu1888_qfact],
      [piu1888_T0] and the companion definitions) and [piu1905_sodd_lower]
      (the odd-side floor, main lemma [piu1905_sodd_lower]).

    References.  LW0LeibSeparation.v, K = BF*C1 + BFd*C2 + 1/8 (:5469);
      the independent numerical recheck piu1888_mirror.py, Kexact (:72-74),
      bit-for-bit identical; this development, piu1909_K_assembly.v, the
      baseline module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim.  Interface note: the conclusion faces of [piu1888_qpow_pos] / [piu1888_T0_pos] / [piu1888_mul_ge0] (new generation: [QltT] / [QleT']) are bridged with [QltT_to_Qlt] / [QleT'_to_Qle] imported from S02_CauchyComplete by name (call-form precedent piu1909_sall_upper.v), statement names untouched.

    Constructivity.  Statements are stated with [Qle] at the [Prop] layer,
      with the wrappers [piu1909_QleT] and [piu1909_band] carried by [Set];
      definitions are transparent; no classical logic, every proof closes
      by [Qed]; the final criterion is [Print Assumptions] Closed.

    Build.  [coqc -native-compiler no -q -Q . "" piu1909_K_assembly.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
Require Import piu1888_growth_quant_lemma.
Require Import piu1905_sodd_lower.
Require Import S02_CauchyComplete (QltT_to_Qlt, QleT'_to_Qle).

Inductive piu1909_QleT (x y : Q) : Set :=
  piu1909_qleT_intro : x <= y -> piu1909_QleT x y.
Inductive piu1909_band (q : Q) : Set :=
  piu1909_band_intro : (35#12) <= q -> q <= (41#12) -> piu1909_band q.

Definition piu1909_T (q : Q) (n m : nat) : Q :=
  piu1888_qpow q m * piu1888_qfact (2 * n - m) *
  / (piu1888_qfact (n - m) * piu1888_qfact m).

Fixpoint piu1909_sodd (q : Q) (n k : nat) {struct k} : Q :=
  match k with
  | O => (if Nat.even 0 then piu1909_T q n (2 * 0 + 1)
          else Qopp (piu1909_T q n (2 * 0 + 1)))
  | S k' => piu1909_sodd q n k'
            + (if Nat.even (S k') then piu1909_T q n (2 * S k' + 1)
               else Qopp (piu1909_T q n (2 * S k' + 1)))
  end.

Fixpoint piu1909_half (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => S (piu1909_half n')
  end.

Definition piu1909_sodd_full (q : Q) (n : nat) : Q :=
  piu1909_sodd q n (piu1909_half (Nat.pred n)).

Lemma piu1909_sodd_full_bridge : forall (q : Q) (n : nat),
  piu1905_sodd_full q n == piu1909_sodd_full q n.
Proof.
  intros q n.
  unfold piu1905_sodd_full, piu1909_sodd_full.
  unfold piu1905_half, piu1909_half.
  unfold piu1905_sodd, piu1909_sodd.
  unfold piu1905_sodd_term.
  unfold piu1905_T, piu1909_T.
  reflexivity.
Qed.

Definition piu1909_sev_term (q : Q) (n k : nat) : Q :=
  if Nat.even k then piu1909_T q n (2 * k)
                else Qopp (piu1909_T q n (2 * k)).
Fixpoint piu1909_sev (q : Q) (n k : nat) {struct k} : Q :=
  match k with
  | O => piu1909_sev_term q n 0
  | S k' => piu1909_sev q n k' + piu1909_sev_term q n (S k')
  end.
Definition piu1909_sev_full (q : Q) (n : nat) : Q :=
  piu1909_sev q n (piu1909_half n).

Definition piu1909_Qabs (x : Q) : Q :=
  if Qle_bool (0#1) x then x else Qopp x.

Definition piu1909_Kmodel (q : Q) (b : Q) (n : nat) : Q :=
  piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n) * (105410#1341)
  + piu1909_Qabs (piu1888_qpow b n * piu1909_sodd_full q n) * (9664#447)
  + (1#8).

Lemma piu1909_band_pos : forall q : Q,
  piu1909_band q -> (0#1) < q.
Proof.
  intros q Hb. destruct Hb as [Hlo Hhi].
  apply (Qlt_le_trans (0#1) (35#12) q).
  - vm_compute. reflexivity.
  - exact Hlo.
Qed.

Lemma piu1909_abs_nonneg : forall x : Q, (0#1) <= piu1909_Qabs x.
Proof.
  intros x. unfold piu1909_Qabs.
  destruct (Qle_bool (0#1) x) eqn:E.
  - exact (proj1 (Qle_bool_iff (0#1) x) E).
  - destruct (Qlt_le_dec x (0#1)) as [Hneg | Hpos0].
    + apply (Qlt_le_weak (Qopp (0#1)) (Qopp x)).
      exact (Qopp_lt_compat x (0#1) Hneg).
    + assert (Hb : Qle_bool (0#1) x = true)
        by (apply (proj2 (Qle_bool_iff (0#1) x)); exact Hpos0).
      rewrite Hb in E. discriminate E.
Qed.

Lemma piu1909_abs_id : forall x : Q,
  (0#1) <= x -> piu1909_Qabs x == x.
Proof.
  intros x H. unfold piu1909_Qabs.
  destruct (Qle_bool (0#1) x) eqn:E.
  - reflexivity.
  - assert (Hb : Qle_bool (0#1) x = true)
      by (apply (proj2 (Qle_bool_iff (0#1) x)); exact H).
    rewrite Hb in E. discriminate E.
Qed.

Theorem piu1909_K_lower : forall (q : Q) (b : Q) (n : nat),
  (0#1) < b -> (3 <= n)%nat -> piu1909_band q ->
  (9664#447) * (62125#82944) * (piu1888_qpow b n * piu1888_T0 n)
  <= piu1909_Kmodel q b n.
Proof.
  intros q b n Hb Hn3 Hbnd.
  assert (Hq : (0#1) < q) by (apply piu1909_band_pos; exact Hbnd).
  destruct Hbnd as [Hlo Hhi].
  assert (Hb05 : piu1905_band q) by (apply piu1905_band_intro; assumption).
  assert (Hfl := piu1905_sodd_lower q n Hn3 Hb05).
  assert (HbT0 : (0#1) < piu1888_qpow b n)
    by (apply QltT_to_Qlt; apply piu1888_qpow_pos; exact Hb).
  assert (Hstep1 : piu1888_qpow b n * ((62125#82944) * piu1888_T0 n)
                   <= piu1888_qpow b n * piu1909_sodd_full q n).
  { rewrite (Qmult_comm (piu1888_qpow b n) ((62125#82944) * piu1888_T0 n)).
    rewrite (Qmult_comm (piu1888_qpow b n) (piu1909_sodd_full q n)).
    apply (Qmult_le_compat_r ((62125#82944) * piu1888_T0 n)
             (piu1909_sodd_full q n) (piu1888_qpow b n)).
    - destruct Hfl as [Hfl1].
      rewrite <- (piu1909_sodd_full_bridge q n). exact Hfl1.
    - apply Qlt_le_weak. exact HbT0. }
  assert (Hge0 : (0#1) <= piu1888_qpow b n * piu1909_sodd_full q n).
  { apply (Qle_trans (0#1)
             (piu1888_qpow b n * ((62125#82944) * piu1888_T0 n))
             (piu1888_qpow b n * piu1909_sodd_full q n)).
    - apply QleT'_to_Qle. apply piu1888_mul_ge0.
      + apply Qlt_le_weak. exact HbT0.
      + apply QleT'_to_Qle. apply piu1888_mul_ge0.
        * vm_compute. discriminate.
        * apply Qlt_le_weak. apply QltT_to_Qlt. apply piu1888_T0_pos.
    - exact Hstep1. }
  unfold piu1909_Kmodel.
  rewrite (piu1909_abs_id (piu1888_qpow b n * piu1909_sodd_full q n) Hge0).
  assert (Er : piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n)
                 * (105410#1341)
               + piu1888_qpow b n * piu1909_sodd_full q n * (9664#447)
               + (1#8)
               == piu1888_qpow b n * piu1909_sodd_full q n * (9664#447)
                  + (piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n)
                       * (105410#1341) + (1#8)))
    by ring.
  rewrite Er.
  apply (Qle_trans ((9664#447) * (62125#82944) * (piu1888_qpow b n * piu1888_T0 n))
             (piu1888_qpow b n * piu1909_sodd_full q n * (9664#447))
             (piu1888_qpow b n * piu1909_sodd_full q n * (9664#447)
                + (piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n)
                     * (105410#1341) + (1#8)))).
  - assert (E2 : (9664#447) * (62125#82944) * (piu1888_qpow b n * piu1888_T0 n)
                 == (piu1888_qpow b n * ((62125#82944) * piu1888_T0 n))
                    * (9664#447)) by ring.
    rewrite E2.
    apply (Qmult_le_compat_r
             (piu1888_qpow b n * ((62125#82944) * piu1888_T0 n))
             (piu1888_qpow b n * piu1909_sodd_full q n) (9664#447)).
    + exact Hstep1.
    + vm_compute. discriminate.
  - apply (Qle_trans
             (piu1888_qpow b n * piu1909_sodd_full q n * (9664#447))
             (piu1888_qpow b n * piu1909_sodd_full q n * (9664#447) + (0#1))
             (piu1888_qpow b n * piu1909_sodd_full q n * (9664#447)
                + (piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n)
                     * (105410#1341) + (1#8)))).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat
               (piu1888_qpow b n * piu1909_sodd_full q n * (9664#447))
               (piu1888_qpow b n * piu1909_sodd_full q n * (9664#447))
               (0#1)
               (piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n)
                  * (105410#1341) + (1#8))).
      * apply Qle_refl.
      * apply (Qle_trans (0#1) ((0#1) + (1#8))
                 (piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n)
                    * (105410#1341) + (1#8))).
        -- vm_compute. discriminate.
        -- apply (Qplus_le_compat (0#1)
                     (piu1909_Qabs (piu1888_qpow b n * piu1909_sev_full q n)
                        * (105410#1341))
                     (1#8) (1#8)).
           ++ apply QleT'_to_Qle. apply piu1888_mul_ge0.
              ** apply piu1909_abs_nonneg.
              ** vm_compute. discriminate.
           ++ apply Qle_refl.
Qed.

Print Assumptions piu1909_sodd_full_bridge.
Print Assumptions piu1909_abs_nonneg.
Print Assumptions piu1909_abs_id.
Print Assumptions piu1909_K_lower.
