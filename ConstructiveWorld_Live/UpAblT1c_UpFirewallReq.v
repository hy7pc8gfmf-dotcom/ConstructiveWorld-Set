(* ConstructiveWorld-Set -- upstream temperature-entropy firewall requirements. *)

(** * UpAblT1c_UpFirewallReq: five temperature-strictness firewall
    requirements over a Set-carried real interface.

    Mission.  Formalizes the five temperature-strictness requirements that
      the use-face firewall places on the Boltzmann temperature family
      [fw_bt]/[fw_et]/[fw_h]/[fw_kl]: explicit entropy [uabt1c_fw_entropy_temp_explicit],
      relative-entropy temperature decomposition [uabt1c_fw_relative_entropy_temp_decomp],
      energy-expectation monotonicity [uabt1c_fw_energy_exp_temp_mono],
      the strict identity [uabt1c_fw_temp_strict_ident2], and strict
      energy-expectation monotonicity [uabt1c_fw_energy_exp_temp_strict_mono].

    Dependencies.  Requires the base chain [S01_BaseRing] through
      [S15_TailFEPUp] (importing [RealInterfaceEnhancedMod]) and
      [UpReqAlgebra], [UpReqDist], [UpReqTempEntropy] of this development.

    References.  This development, UpAblT1c_UpFirewallReq.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].  The seven [Set]-carried section premises are declared
      with [Variable] because their conclusions are boolean-carried data
      statements, [Variable] and [Hypothesis] being interchangeable there.

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT1c_UpFirewallReq.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import UpReqTempEntropy.
Import RealInterfaceEnhancedMod.
(* Set-carrier completion bridge: the interface class in this tree is *)
(*   unparameterized; its carrier is the global Cauchy real Real.     *)
Notation R := Real.
(* The relation premises are written over the concrete layer relation
   names ([real_eq]/[real_lt]/[real_le]), the extraction discipline of
   the temperature entropy layer (bare class fields are projections
   whose casts surface on the extraction face). *)
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

Section UabT1cFirewallReq.


(* ---- The interface premises of the use-face firewall, carried verbatim:
   extensional, additive and linear finite sums on [S] with monotone and
   positive bounds, the weight [base_loss], and the partition function
   [Z_temp] fixed by the exponential sum. ---- *)
Variable S : Set.
Variable sumf : (S -> R) -> R.
Variable ssum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Variable ssum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Variable ssum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Variable ssum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Variable ssum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

Variable base_loss : S -> R.

Variable Z_temp : R -> R.
Variable req_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ---- The strictness premises of the use-face firewall, carried
   verbatim: inversion of order under [inv_pos], positivity of a
   difference under [lt], the log-inverse identity, and the log-linear
   upper bound. ---- *)
Variable inv_pos_lt_compat : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (req_minus b a).

Variable dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Variable dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).

(* ---- Supplementary premise: the logarithm of [exp_neg u] agrees with
   [opp u].  The use-face premises do not include this entry, while the
   upstream statement signatures require it, so the section carries it
   explicitly. ---- *)
Variable uabt1c_dist_log_exp_neg_slot :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* ---- Transparent aliases of the temperature family: the Boltzmann
   distribution [fw_bt], its positivity [fw_bt_pos], the normalization
   [fw_norm], the entropy [fw_h], the energy expectation [fw_et], and
   the relative entropy [fw_kl]. ---- *)
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

(* ---- Strictness side condition shared by bridges 3 and 5: from
   [lt t1 t2], [inv_pos_lt_compat] reverses the order of the inverses
   and [lt_minus_nonneg] turns it into a positive difference of
   inverses. ---- *)
Lemma uabt1c_inv_anti_side :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 -> lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  exact (lt_minus_nonneg (inv_pos t2 Ht2) (inv_pos t1 Ht1)
           (inv_pos_lt_compat t1 t2 Ht1 Ht2 Hlt)).
Qed.

(* ============================================================ *)
(* Bridge 1, explicit entropy: the entropy [fw_h t Ht] equals the scaled
   energy expectation plus the logarithmic partition term; the proof is
   a direct application of [req_entropy_temp_explicit] to the section
   premises. *)
(* ============================================================ *)
Theorem uabt1c_fw_entropy_temp_explicit :
  forall (t : R) (Ht : lt zero t),
  req (fw_h t Ht)
      (plus (mult (inv_pos t Ht) (fw_et t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                 req_Z_temp_spec t Ht))).
Proof.
  intros t Ht.
  exact (@req_entropy_temp_explicit S sumf ssum_ext ssum_add ssum_linear
           ssum_pos base_loss dist_log_inv_one_inv uabt1c_dist_log_exp_neg_slot
           Z_temp req_Z_temp_spec t Ht).
Qed.

(* ============================================================ *)
(* Bridge 2, relative entropy temperature decomposition: the relative
   entropy [fw_kl t1 t2 Ht1 Ht2] expands into the negated entropy at
   [t1], the energy expectation of [t1] scaled by [inv_pos t2], and the
   logarithmic partition term at [t2]; direct application of
   [req_relative_entropy_temp_decomp]. *)
(* ============================================================ *)
Theorem uabt1c_fw_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (fw_kl t1 t2 Ht1 Ht2)
      (plus (plus (opp (fw_h t1 Ht1)) (mult (inv_pos t2 Ht2) (fw_et t1 Ht1)))
            (log (Z_temp t2)
                 (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                 req_Z_temp_spec t2 Ht2))).
Proof.
  intros t2 Ht2 t1 Ht1.
  exact (@req_relative_entropy_temp_decomp S sumf ssum_ext ssum_add
           ssum_linear ssum_pos base_loss dist_log_inv_one_inv
           uabt1c_dist_log_exp_neg_slot Z_temp req_Z_temp_spec t2 Ht2
           (fw_bt t1 Ht1) (fw_bt_pos t1 Ht1) (fw_norm t1 Ht1)).
Qed.

(* ============================================================ *)
(* Bridge 3, energy expectation monotone in the temperature: [lt t1 t2]
   makes the expectation [fw_et t1] at most [fw_et t2]; the proof
   applies [req_energy_exp_temp_mono] and closes the strictness side
   condition by [uabt1c_inv_anti_side]. *)
(* ============================================================ *)
Theorem uabt1c_fw_energy_exp_temp_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 -> le (fw_et t1 Ht1) (fw_et t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  exact (@req_energy_exp_temp_mono S sumf ssum_ext ssum_add ssum_linear
           ssum_pos ssum_le base_loss dist_log_inv_one_inv
           uabt1c_dist_log_exp_neg_slot dist_log_le_linear Z_temp
           req_Z_temp_spec t1 t2 Ht1 Ht2 Hlt
           (uabt1c_inv_anti_side t1 t2 Ht1 Ht2 Hlt)).
Qed.

(* ============================================================ *)
(* Bridge 4, second strict temperature identity: the relative entropy
   of [t2] against [t1] together with [fw_kl t1 t2] equals the product
   of the difference of inverses and the difference of expectations;
   direct application of [req_temp_strict_ident2]. *)
(* ============================================================ *)
Theorem uabt1c_fw_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                  (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1))
            (fw_kl t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (@req_temp_strict_ident2 S sumf ssum_ext ssum_add ssum_linear
           ssum_pos base_loss dist_log_inv_one_inv uabt1c_dist_log_exp_neg_slot
           Z_temp req_Z_temp_spec t1 t2 Ht1 Ht2).
Qed.

(* ============================================================ *)
(* Bridge 5, strict energy expectation monotonicity: [lt t1 t2] with
   positive relative entropy of [t2] against [t1] makes the expectation
   difference positive; the proof applies
   [req_energy_exp_temp_strict_mono] with the same side condition. *)
(* ============================================================ *)
Theorem uabt1c_fw_energy_exp_temp_strict_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1)) ->
  lt zero (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl21.
  exact (@req_energy_exp_temp_strict_mono S sumf ssum_ext ssum_add
           ssum_linear ssum_pos ssum_le base_loss dist_log_inv_one_inv
           uabt1c_dist_log_exp_neg_slot dist_log_le_linear Z_temp
           req_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl21
           (uabt1c_inv_anti_side t1 t2 Ht1 Ht2 Hlt)).
Qed.

End UabT1cFirewallReq.

(* ---- Closing audit: the global exit statements must each report
   Closed under the global context. ---- *)
Print Assumptions uabt1c_fw_entropy_temp_explicit.
Print Assumptions uabt1c_fw_relative_entropy_temp_decomp.
Print Assumptions uabt1c_fw_energy_exp_temp_mono.
Print Assumptions uabt1c_fw_temp_strict_ident2.
Print Assumptions uabt1c_fw_energy_exp_temp_strict_mono.
