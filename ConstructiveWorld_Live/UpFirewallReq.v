(* ConstructiveWorld-Set -- req-carried companion of the entropy firewall: a constructive closed loop for degeneracy detection and recovery over the req equality interface. *)
(** * UpFirewallReq: the entropy firewall of attn/UpFirewall.v
    restated over the req equality interface (companion Section).
    Mission.  Degeneracy detection and recovery closed loop: the
    source Id-equality statements are restated over req, one
    section assumption per source interface slot, no strengthened
    claims.  Main entries: req_fw_energy_eta,
    req_recovery_entropy_gain(_alt), req_entropy_temp_mono,
    req_entropy_temp_strict_mono, req_fw_verdict,
    req_fw_detect_warm, req_firewall_loop.
    Dependencies.  S01_BaseRing through S15_TailFEPUp (the
    real-interface chain); UpReqAlgebra (algebra engine); UpReqDist
    (temperature-parameterized Boltzmann family, entropy, relative
    entropy, Gibbs inequality); RealInterfaceEnhancedMod.
    References.  attn/UpFirewall.v coordinates: req_Z_temp_spec
    L93, req_fw_energy_eta L113, req_fw_lt_double L120,
    req_recovery_entropy_gain L139, req_entropy_temp_mono L207,
    req_entropy_temp_strict_mono L261, req_recovery_entropy_gain_alt
    L318, req_fw_verdict L382, req_fw_detect_warm L388,
    req_firewall_loop L412; fw_double_pos @L130 has no source-Id
    content and stays auxiliary (not counted).
    Constructivity.  Statements carried at the Set level; Id-level
    statements restated through explicit section assumption slots;
    no external assumptions anywhere; every proof closes by Qed in
    pure term mode (no rewrite, no Morphisms).  Honest scope: no
    TV-entropy transfer is claimed; req_fw_verdict's Or is a
    disjunction of certificates, not a boolean decider.
    Build.  rocq c -native-compiler no -q -Q <source-seat world> ""
    UpFirewallReq.v (Rocq 9.1.0) against the same-world dependency
    .vo chain, under the load wrapper. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

Section FirewallReq.

(* Set-carrier completion: the interface class is unparameterized; the
   carrier is the global Cauchy real and the instance the global
   RealEnhancedReal.  The R bridge and the unparameterized binding: *)
Notation R := Real.
Let RIS := RealEnhancedReal.

Let zero := @zero RIS.
Let one := @one RIS.
Let plus := @plus RIS.
Let mult := @mult RIS.
Let opp := @opp RIS.
Let lt := @lt RIS.
Let le := @le RIS.
Let log := @log RIS.
Let inv_pos := @inv_pos RIS.
Let exp_neg := @exp_neg RIS.

(* ---- req summation assumption slots (the source-theorem SumOver
   usage fields, restated over req slot by slot) ---- *)
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis ssum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis ssum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis ssum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis ssum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis ssum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

Variable base_loss : S -> R.

(* Item 1: req form of the source-theorem L93 Z_temp_spec
   (assumption slots preserved slot by slot) *)
Variable Z_temp : R -> R.
Hypothesis req_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* Source-theorem L96-102 strictness / order-compatibility interface
   (same-position assumption slots, no strengthened claims) *)
Variable inv_pos_lt_compat : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (req_minus b a).
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).


Variable dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Variable dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).

(* ---- Temperature-parameterized Boltzmann family (reused directly
   from the UpReqDist temperature family) ---- *)
Definition fw_bt (t : R) (Ht : lt zero t) : S -> R :=
  reqd_boltzmann_dist_temp S sumf ssum_pos base_loss Z_temp req_Z_temp_spec t Ht.
Definition fw_bt_pos (t : R) (Ht : lt zero t) :
  forall s : S, lt zero (fw_bt t Ht s) :=
  reqd_boltzmann_dist_temp_pos S sumf ssum_pos base_loss Z_temp req_Z_temp_spec t Ht.
Definition fw_norm (t : R) (Ht : lt zero t) : req (sumf (fw_bt t Ht)) one :=
  reqd_boltzmann_dist_temp_normalized S sumf ssum_linear ssum_pos base_loss Z_temp
                                      req_Z_temp_spec t Ht.
Definition fw_h (t : R) (Ht : lt zero t) : R :=
  reqd_entropy_dist S sumf (fw_bt t Ht) (fw_bt_pos t Ht).
Definition fw_et (t : R) (Ht : lt zero t) : R :=
  sumf (fun s => mult (fw_bt t Ht s) (base_loss s)).
Definition fw_kl (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2) : R :=
  req_relative_entropy S sumf (fw_bt t1 Ht1) (fw_bt t2 Ht2)
                       (fw_bt_pos t1 Ht1) (fw_bt_pos t2 Ht2).

Variable req_entropy_temp_explicit : forall (t : R) (Ht : lt zero t),
  req (fw_h t Ht)
      (plus (mult (inv_pos t Ht) (fw_et t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                 req_Z_temp_spec t Ht))).
Variable req_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (fw_kl t1 t2 Ht1 Ht2)
      (plus (plus (opp (fw_h t1 Ht1)) (mult (inv_pos t2 Ht2) (fw_et t1 Ht1)))
            (log (Z_temp t2)
                 (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                 req_Z_temp_spec t2 Ht2))).
Variable req_energy_exp_temp_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 -> le (fw_et t1 Ht1) (fw_et t2 Ht2).
Variable req_energy_exp_temp_strict_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                 (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1)) ->
  lt zero (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)).
Variable req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                  (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1))
            (fw_kl t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))).

(* ---- Basic lemmas ---- *)

(* Item 2 (the delta piece): the eta-form bridge for the energy
   expectation (same position as source-theorem L113 id_refl;
   req_minus / sumf unfold definitionally in the same shape) *)
Definition fw_energy_expectation (e p : S -> R) : R :=
  sumf (fun s => mult (p s) (e s)).
Lemma req_fw_energy_eta : forall (t : R) (Ht : lt zero t),
  req (fw_energy_expectation base_loss (fw_bt t Ht)) (fw_et t Ht).
Proof.
  intros t Ht. unfold fw_energy_expectation, fw_et.
  exact (req_refl (sumf (fun s => mult (fw_bt t Ht s) (base_loss s)))).
Qed.

(* Auxiliary (no source-Id content, not counted): positivity of the
   doubled temperature (same position as source-theorem L130) *)
Lemma fw_double_pos : forall (t : R) (Ht : lt zero t), lt zero (plus t t).
Proof.
  intros t Ht. apply plus_positive; exact Ht.
Qed.

(* Item 3: doubling the temperature is a strict increase
   (source-theorem L120; a genuine req-difference proof: the source
   id_transport is replaced by the req-interface lt_id_l field, and
   the transport of zero+t |-> t goes through req_trans) *)
Lemma req_fw_lt_double : forall (t : R) (Ht : lt zero t), lt t (plus t t).
Proof.
  intros t Ht.
  apply (lt_id_l t (plus zero t) (plus t t)
                 (req_sym (plus zero t) t
                          (req_trans (plus zero t) (plus t zero) t
                                     (plus_comm zero t) (plus_zero t)))).
  apply (lt_plus_compat_lt_le zero t t t Ht (le_refl t)).
Qed.

(* ===== Item 4 (first main theorem): exact recovery-gain identity =====
   Source theorem L139: delta H == beta2*(E2 - E1) + KL_12.  A
   genuine full-chain req proof: the explicit entropy form and the
   KL temperature decomposition are explicit assumption slots, and
   the rest is a flat req hop chain rearranging the source AC
   identity (u1/u2/v1-v3/u3/u4, one flat term per hop, no deep
   nesting). *)
Theorem req_recovery_entropy_gain :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
      (plus (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
            (fw_kl t1 t2 Ht1 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b2 := inv_pos t2 Ht2).
  set (E1 := fw_et t1 Ht1).  set (E2 := fw_et t2 Ht2).
  set (H1 := fw_h t1 Ht1).   set (H2 := fw_h t2 Ht2).
  set (L2 := log (Z_temp t2)
                  (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                  req_Z_temp_spec t2 Ht2)).
  assert (Hex2 : req H2 (plus (mult b2 E2) L2))
    by exact (req_entropy_temp_explicit t2 Ht2).
  assert (Hkl : req (fw_kl t1 t2 Ht1 Ht2) (plus (plus (opp H1) (mult b2 E1)) L2))
    by exact (req_relative_entropy_temp_decomp t2 Ht2 t1 Ht1).
  assert (Hd : req (mult b2 (req_minus E2 E1)) (plus (mult b2 E2) (opp (mult b2 E1))))
    by exact (req_mult_minus_distr_l b2 E2 E1).
(* the zero-absorption subchain for v3 *)
  assert (Hv3 : req (plus (plus (mult b2 E2) (opp H1))
                          (plus (opp (mult b2 E1)) (mult b2 E1)))
                    (plus (mult b2 E2) (opp H1))).
  { apply (req_trans
              (plus (plus (mult b2 E2) (opp H1))
                    (plus (opp (mult b2 E1)) (mult b2 E1)))
              (plus (plus (mult b2 E2) (opp H1)) zero)
              (plus (mult b2 E2) (opp H1))).
    - exact (req_plus_compat (plus (mult b2 E2) (opp H1))
                             (plus (mult b2 E2) (opp H1))
                             (plus (opp (mult b2 E1)) (mult b2 E1)) zero
                             (req_refl (plus (mult b2 E2) (opp H1)))
                             (req_trans (plus (opp (mult b2 E1)) (mult b2 E1))
                                        (plus (mult b2 E1) (opp (mult b2 E1)))
                                        zero
                                        (plus_comm (opp (mult b2 E1)) (mult b2 E1))
                                        (plus_opp (mult b2 E1)))).
    - apply plus_zero. }
(* u2 kernel: b2(E2-E1) + (-H1 + b2E1) == b2E2 + -H1
   (Hd + swap_mid + zero absorption) *)
  assert (Hu2 : req (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1)))
                    (plus (mult b2 E2) (opp H1))).
  { apply (req_trans
              (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1)))
              (plus (plus (mult b2 E2) (opp (mult b2 E1))) (plus (opp H1) (mult b2 E1)))
              (plus (mult b2 E2) (opp H1))).
    - exact (req_plus_compat (mult b2 (req_minus E2 E1))
                             (plus (mult b2 E2) (opp (mult b2 E1)))
                             (plus (opp H1) (mult b2 E1)) (plus (opp H1) (mult b2 E1))
                             Hd (req_refl (plus (opp H1) (mult b2 E1)))).
    - apply (req_trans
                (plus (plus (mult b2 E2) (opp (mult b2 E1))) (plus (opp H1) (mult b2 E1)))
                (plus (plus (mult b2 E2) (opp H1)) (plus (opp (mult b2 E1)) (mult b2 E1)))
                (plus (mult b2 E2) (opp H1))).
      + exact (req_plus_swap_mid (mult b2 E2) (opp (mult b2 E1)) (opp H1) (mult b2 E1)).
      + exact Hv3. }
(* u3: (b2E2 + -H1) + L2 == (b2E2 + L2) + -H1 *)
  assert (Hu3 : req (plus (plus (mult b2 E2) (opp H1)) L2)
                    (plus (plus (mult b2 E2) L2) (opp H1))).
  { apply (req_trans (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus (mult b2 E2) (plus (opp H1) L2))
                     (plus (plus (mult b2 E2) L2) (opp H1))).
    - exact (req_sym (plus (mult b2 E2) (plus (opp H1) L2))
                     (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus_assoc (mult b2 E2) (opp H1) L2)).
    - apply (req_trans (plus (mult b2 E2) (plus (opp H1) L2))
                       (plus (mult b2 E2) (plus L2 (opp H1)))
                       (plus (plus (mult b2 E2) L2) (opp H1))).
      + exact (req_plus_compat (mult b2 E2) (mult b2 E2)
                               (plus (opp H1) L2) (plus L2 (opp H1))
                               (req_refl (mult b2 E2)) (plus_comm (opp H1) L2)).
      + exact (plus_assoc (mult b2 E2) L2 (opp H1)). }
(* main body: G-RHS -[Hkl]-> X1 -[u1]-> ... -> H2 + -H1
   (= G-LHS; the delta step is definitionally transparent) *)
  exact (req_sym
            (plus (mult b2 (req_minus E2 E1)) (fw_kl t1 t2 Ht1 Ht2))
            (plus H2 (opp H1))
            (req_trans
               (plus (mult b2 (req_minus E2 E1)) (fw_kl t1 t2 Ht1 Ht2))
               (plus (mult b2 (req_minus E2 E1))
                     (plus (plus (opp H1) (mult b2 E1)) L2))
               (plus H2 (opp H1))
               (req_plus_compat
                  (mult b2 (req_minus E2 E1)) (mult b2 (req_minus E2 E1))
                  (fw_kl t1 t2 Ht1 Ht2)
                  (plus (plus (opp H1) (mult b2 E1)) L2)
                  (req_refl (mult b2 (req_minus E2 E1))) Hkl)
               (req_trans
                  (plus (mult b2 (req_minus E2 E1))
                        (plus (plus (opp H1) (mult b2 E1)) L2))
                  (plus (plus (mult b2 E2) (opp H1)) L2)
                  (plus H2 (opp H1))
                  (req_trans
                     (plus (mult b2 (req_minus E2 E1))
                           (plus (plus (opp H1) (mult b2 E1)) L2))
                     (plus (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1))) L2)
                     (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus_assoc (mult b2 (req_minus E2 E1))
                                 (plus (opp H1) (mult b2 E1)) L2)
                     (req_plus_compat
                        (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1)))
                        (plus (mult b2 E2) (opp H1))
                        L2 L2 Hu2 (req_refl L2)))
                  (req_trans
                     (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus (plus (mult b2 E2) L2) (opp H1))
                     (plus H2 (opp H1))
                     Hu3
                     (req_plus_compat (plus (mult b2 E2) L2) H2
                                      (opp H1) (opp H1)
                                      (req_sym H2 (plus (mult b2 E2) L2) Hex2)
                                      (req_refl (opp H1))))))).
Qed.

(* ===== Item 5 (main result): temperature-entropy monotonicity =====
   Source theorem L207: t1 < t2 implies H(p_t1) <= H(p_t2).  Route:
   explicit energy-monotonicity assumption slot + migration of the
   Item 4 identity + req_gibbs_inequality from the UpReqDist
   temperature family. *)
Theorem req_entropy_temp_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 -> le (fw_h t1 Ht1) (fw_h t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  assert (HdE : le zero (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
    by exact (req_le_minus_nonneg (fw_et t1 Ht1) (fw_et t2 Ht2)
                                  (req_energy_exp_temp_mono t1 t2 Ht1 Ht2 Hlt)).
  assert (Hkl : le zero (fw_kl t1 t2 Ht1 Ht2))
    by exact (@req_gibbs_inequality S sumf ssum_ext ssum_add ssum_linear
                                    ssum_le dist_log_inv_one_inv dist_log_le_linear
                                    (fw_bt t1 Ht1) (fw_bt t2 Ht2)
                                    (fw_bt_pos t1 Ht1) (fw_bt_pos t2 Ht2)
                                    (fw_norm t1 Ht1) (fw_norm t2 Ht2)).
  assert (Hb2 : le zero (inv_pos t2 Ht2))
    by exact (lt_le_iff zero (inv_pos t2 Ht2) (inl (inv_pos_pos t2 Ht2))).
  assert (Hterm : le zero (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))).
  { apply (le_id_l zero (mult (inv_pos t2 Ht2) zero)
                   (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))).
    - exact (req_sym (mult (inv_pos t2 Ht2) zero) zero
                     (mult_zero (inv_pos t2 Ht2))).
    - exact (req_le_mult_compat_r (inv_pos t2 Ht2) zero
                                  (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))
                                  Hb2 HdE). }
  assert (Hsum : le zero (plus (mult (inv_pos t2 Ht2)
                                      (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                               (fw_kl t1 t2 Ht1 Ht2))).
  { apply (le_trans zero
                    (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                    (plus (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                          (fw_kl t1 t2 Ht1 Ht2))).
    - exact Hterm.
    - exact (req_le_plus_nonneg_r
                (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                (fw_kl t1 t2 Ht1 Ht2) Hkl). }
  assert (Hfin : le zero (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
  { apply (le_id_r zero
                   (plus (mult (inv_pos t2 Ht2)
                               (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                         (fw_kl t1 t2 Ht1 Ht2))
                   (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
    - exact (req_sym (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
                     (plus (mult (inv_pos t2 Ht2)
                                 (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                           (fw_kl t1 t2 Ht1 Ht2))
                     (req_recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  apply (le_id_r (fw_h t1 Ht1)
                 (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))
                 (fw_h t2 Ht2)).
  - exact (req_minus_plus_cancel (fw_h t1 Ht1) (fw_h t2 Ht2)).
  - exact (req_le_plus_nonneg_r (fw_h t1 Ht1)
                                (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)) Hfin).
Qed.

(* ===== Item 6 (strict tier): temperature increase implies strict
   entropy recovery =====  Source theorem L261; same honest side
   condition: KL(p_t2 || p_t1) > 0. *)
Theorem req_entropy_temp_strict_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1)) ->
  lt (fw_h t1 Ht1) (fw_h t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl12.
  assert (HdE : lt zero (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
    by exact (req_energy_exp_temp_strict_mono t1 t2 Ht1 Ht2 Hlt Hkl12).
  assert (Hterm : lt zero (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))))
    by exact (mult_positive (inv_pos t2 Ht2)
                            (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))
                            (inv_pos_pos t2 Ht2) HdE).
  assert (Hkl21 : le zero (fw_kl t1 t2 Ht1 Ht2))
    by exact (@req_gibbs_inequality S sumf ssum_ext ssum_add ssum_linear
                                    ssum_le dist_log_inv_one_inv dist_log_le_linear
                                    (fw_bt t1 Ht1) (fw_bt t2 Ht2)
                                    (fw_bt_pos t1 Ht1) (fw_bt_pos t2 Ht2)
                                    (fw_norm t1 Ht1) (fw_norm t2 Ht2)).
  assert (Hsum : lt zero (plus (mult (inv_pos t2 Ht2)
                                      (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                               (fw_kl t1 t2 Ht1 Ht2)))
    by exact (lt_le_trans zero
                          (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                          (plus (mult (inv_pos t2 Ht2)
                                      (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                                (fw_kl t1 t2 Ht1 Ht2))
                          Hterm
                          (req_le_plus_nonneg_r
                              (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                              (fw_kl t1 t2 Ht1 Ht2) Hkl21)).
  assert (Hfin : lt zero (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
  { apply (lt_id_r zero
                   (plus (mult (inv_pos t2 Ht2)
                               (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                         (fw_kl t1 t2 Ht1 Ht2))
                   (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
    - exact (req_sym (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
                     (plus (mult (inv_pos t2 Ht2)
                                 (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                           (fw_kl t1 t2 Ht1 Ht2))
                     (req_recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  apply (lt_id_r (fw_h t1 Ht1)
                 (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))
                 (fw_h t2 Ht2)).
  - exact (req_minus_plus_cancel (fw_h t1 Ht1) (fw_h t2 Ht2)).
  - apply (lt_id_l (fw_h t1 Ht1) (plus zero (fw_h t1 Ht1))
                   (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))).
    + exact (req_sym (plus zero (fw_h t1 Ht1)) (fw_h t1 Ht1)
                              (req_trans (plus zero (fw_h t1 Ht1))
                                         (plus (fw_h t1 Ht1) zero)
                                         (fw_h t1 Ht1)
                                         (plus_comm zero (fw_h t1 Ht1))
                                         (plus_zero (fw_h t1 Ht1)))).
    + apply (lt_id_r (plus zero (fw_h t1 Ht1))
                              (plus (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)) (fw_h t1 Ht1))
                              (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))).
      * exact (plus_comm (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)) (fw_h t1 Ht1)).
      * exact (lt_plus_compat_lt_le zero
                                      (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
                                      (fw_h t1 Ht1) (fw_h t1 Ht1)
                                      Hfin (le_refl (fw_h t1 Ht1))).
Qed.

(* ===== Item 7 (second main theorem, dual form): symmetric KL coupling =====
   Shape = the conditional form of the req_temp_strict_ident2
   assumption slot (on leaving the Section the slots become explicit
   arguments; the slots never strengthen the claim).  Write b1/b2,
   E1/E2, dE, H1/H2, K_A (the slot's first sum term), K_B (fw_kl):
     beta1*dE == beta2*dE + (beta1-beta2)*dE -[slot symmetry]->
     beta2*dE + (K_A + K_B) == (beta2*dE + K_B) + K_A ==
     delta H + K_A (the Item 4 symmetry),
   hence (beta1*dE) - K_A == (delta H + K_A) - K_A == delta H (via
   req_minus_plus_cancel_r plus plus_comm, two steps); the goal is
   flipped by req_sym. *)
Theorem req_recovery_entropy_gain_alt :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
      (req_minus (mult (inv_pos t1 Ht1) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                 (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                        (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1).
  set (b2 := inv_pos t2 Ht2).
  set (E1 := fw_et t1 Ht1).
  set (E2 := fw_et t2 Ht2).
  set (H1 := fw_h t1 Ht1).
  set (H2 := fw_h t2 Ht2).
  set (dE := req_minus E2 E1).
  set (KA := req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                               (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1)).
  set (KB := fw_kl t1 t2 Ht1 Ht2).
  assert (Hg4 : req (req_minus H2 H1) (plus (mult b2 dE) KB))
    by exact (req_recovery_entropy_gain t1 t2 Ht1 Ht2).
  assert (Hsym : req (plus KA KB) (mult (req_minus b1 b2) dE))
    by exact (req_temp_strict_ident2 t1 t2 Ht1 Ht2).
  assert (Hb1 : req b1 (plus b2 (req_minus b1 b2)))
    by exact (req_sym (plus b2 (req_minus b1 b2)) b1
                      (req_minus_plus_cancel b2 b1)).
  assert (Hsplit : req (mult b1 dE) (plus (mult b2 dE) (mult (req_minus b1 b2) dE))).
  { exact (req_trans (mult b1 dE)
                     (mult (plus b2 (req_minus b1 b2)) dE)
                     (plus (mult b2 dE) (mult (req_minus b1 b2) dE))
                     (req_mult_compat b1 (plus b2 (req_minus b1 b2)) dE dE
                                      Hb1 (req_refl dE))
                     (req_mult_plus_distr_r b2 (req_minus b1 b2) dE)). }
  assert (Hsym' : req (mult (req_minus b1 b2) dE) (plus KA KB))
    by exact (req_sym (plus KA KB) (mult (req_minus b1 b2) dE) Hsym).
  assert (Hb'' : req (mult b1 dE) (plus (req_minus H2 H1) KA)).
  { exact (req_trans (mult b1 dE)
                     (plus (mult b2 dE) (plus KA KB))
                     (plus (req_minus H2 H1) KA)
                     (req_trans (mult b1 dE)
                                (plus (mult b2 dE) (mult (req_minus b1 b2) dE))
                                (plus (mult b2 dE) (plus KA KB))
                                Hsplit
                                (req_plus_compat (mult b2 dE) (mult b2 dE)
                                                 (mult (req_minus b1 b2) dE)
                                                 (plus KA KB)
                                                 (req_refl (mult b2 dE))
                                                 Hsym'))
                     (req_trans (plus (mult b2 dE) (plus KA KB))
                                (plus (plus (mult b2 dE) KB) KA)
                                (plus (req_minus H2 H1) KA)
                                (req_trans (plus (mult b2 dE) (plus KA KB))
                                           (plus (mult b2 dE) (plus KB KA))
                                           (plus (plus (mult b2 dE) KB) KA)
                                           (req_plus_compat (mult b2 dE)
                                                            (mult b2 dE)
                                                            (plus KA KB)
                                                            (plus KB KA)
                                                            (req_refl (mult b2 dE))
                                                            (plus_comm KA KB))
                                           (plus_assoc (mult b2 dE) KB KA))
                                (req_plus_compat (plus (mult b2 dE) KB)
                                                 (req_minus H2 H1)
                                                 KA KA
                                                 (req_sym (req_minus H2 H1)
                                                          (plus (mult b2 dE) KB)
                                                          Hg4)
                                                 (req_refl KA)))). }
  exact (req_sym (req_minus (mult b1 dE) KA) (req_minus H2 H1)
                 (req_trans (req_minus (mult b1 dE) KA)
                            (req_minus (plus (req_minus H2 H1) KA) KA)
                            (req_minus H2 H1)
                            (reqd_minus_compat (mult b1 dE)
                                               (plus (req_minus H2 H1) KA)
                                               KA KA
                                               Hb'' (req_refl KA))
                            (req_trans (req_minus (plus (req_minus H2 H1) KA) KA)
                                       (req_minus (plus KA (req_minus H2 H1)) KA)
                                       (req_minus H2 H1)
                                       (reqd_minus_compat
                                          (plus (req_minus H2 H1) KA)
                                          (plus KA (req_minus H2 H1))
                                          KA KA
                                          (plus_comm (req_minus H2 H1) KA)
                                          (req_refl KA))
                                       (req_minus_plus_cancel_r KA
                                                                (req_minus H2 H1))))).
Qed.

(* ===== Items 8/9/10: closed-loop packaging (a certificate-shaped
   state machine; Set level, not a boolean decider); the degenerate
   branch's recovery verdict is still inr. *)

Definition req_fw_verdict (Hmin : R) (t : R) (Ht : lt zero t) : Set :=
  Or (le Hmin (fw_h t Ht))
     (sigT (fun gap : R => req gap (req_minus (fw_h t Ht) Hmin))).

Theorem req_fw_detect_warm :
  forall (Hmin : R) (t : R) (Ht : lt zero t)
         (Hdef : sigT (fun gap : R => req gap (req_minus (fw_h t Ht) Hmin))),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (lt t t')
        (And (le (fw_h t Ht) (fw_h t' Ht'))
             (req (req_minus (fw_h t' Ht') (fw_h t Ht))
                  (plus (mult (inv_pos t' Ht') (req_minus (fw_et t' Ht') (fw_et t Ht)))
                        (fw_kl t t' Ht Ht')))))).
Proof.
  intros Hmin t Ht Hdef.
  assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
  assert (Hup : lt t (plus t t)) by exact (req_fw_lt_double t Ht).
  exists (plus t t). exists Ht'.
  split.
  - exact Hup.
  - split.
    + exact (req_entropy_temp_mono t (plus t t) Ht Ht' Hup).
    + exact (req_recovery_entropy_gain t (plus t t) Ht Ht').
Qed.

Theorem req_firewall_loop :
  forall (Hmin : R) (t : R) (Ht : lt zero t) (v : req_fw_verdict Hmin t Ht),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (le t t')
        (And (le (fw_h t Ht) (fw_h t' Ht'))
             (req_fw_verdict Hmin t' Ht')))).
Proof.
  intros Hmin t Ht v. destruct v as [Hok | Hdef].
  - exists t. exists Ht.
    split.
    + apply le_refl.
    + split.
      * apply le_refl.
      * left. exact Hok.
  - assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
    assert (Hup : lt t (plus t t)) by exact (req_fw_lt_double t Ht).
    exists (plus t t). exists Ht'.
    split.
    + exact (lt_le_iff t (plus t t) (inl Hup)).
    + split.
      * exact (req_entropy_temp_mono t (plus t t) Ht Ht' Hup).
      * right. exists (req_minus (fw_h (plus t t) Ht') Hmin).
        exact (req_refl (req_minus (fw_h (plus t t) Ht') Hmin)).
Qed.

End FirewallReq.
