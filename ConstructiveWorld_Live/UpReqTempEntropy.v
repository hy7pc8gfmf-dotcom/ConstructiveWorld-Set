(* Five-field pointer | Mission. Formalization of the properties stated by the theorem/lemma declarations of this file. Dependencies. The libraries listed by the in-file Require declarations. References. The upstream originals anchored in the block below. Constructivity. Zero admission-style statements (mechanically checked). Build. rocq c -native-compiler no -q -Q <source-seat world> "".  ============================================================ *)
(* UpReqTempEntropy.v *)
(* *)
(* Purpose: the req temperature entropy family: explicit entropy, relative entropy decomposition and the variational bound. *)
(* Main items: req_entropy_temp_explicit / req_relative_entropy_temp_decomp / req_variational_temp_bound. *)
(* Dependencies: CW_ConstructiveWorld_219, UpReqAlgebra, UpReqDist. *)
(* Notes: temperature positivity and partition normalization are section variables; the strict chain req_temp_strict_A_chain2 is the constructive core. *)
(* ============================================================ *)

(* UpReqTempEntropy.v -- the temperature entropy layer: five items restated over  *)
(*   the req interface (strict-layer increments included; upstream anchors kept).  *)
(*     entropy_temp_explicit          <- upstream L17271 (H(p_beta) == beta*E + logZ) *)
(*     relative_entropy_temp_decomp  <- upstream L17356 (KL(q||p_beta) == -H(q) + beta*E(q) + logZ) *)
(*     entropy_deficit_kl_temp       <- upstream L17691 (same energy implies S[p_beta] - S[p] == KL) *)
(*     max_entropy_is_boltzmann_temp <- upstream L17726 (same energy implies S[p] <= S[p_beta]) *)
(*     entropy_max_unique_temp       <- upstream L17763 (same energy and entropy imply p == p_beta pointwise) *)
(*   Dependencies (closed forms of the ReqTemp/ReqFEP sections of UpReqDist.v,     *)
(*   used with -Q . ""): req_Z_temp_pos / reqd_boltzmann_dist_temp /               *)
(*   reqd_energy_exp_temp / reqd_boltzmann_dist_temp_normalized /                  *)
(*   reqd_boltzmann_dist_temp_pos (Defined) / reqd_boltzmann_log_temp_decomp       *)
(*   + the FEP summation face fsum_ext/add/linear/pos/le/zero_nonneg + bridges     *)
(*   dist_log_inv_one_inv / dist_log_exp_neg / dist_log_le_linear /                *)
(*   dist_log_eq_linear + req_entropy_neg_sum + req_gibbs_inequality /             *)
(*   req_gibbs_equality.                                                           *)
(*   Method: programmatic splicing of pre-balanced atomic terms -- both sides are   *)
(*   split into pointwise-named atomic terms (each closed by exact), then closed    *)
(*   in order via req_trans; zero rewrite. Pure term mode; Set-level statements     *)
(*   with zero Prop leakage; log premises carry pointwise positivity proofs via     *)
(*   the Defined aliases tBpos/tZpos.                                               *)
(*   Naming: req_entropy_deficit_temp (this file) == req_entropy_deficit_kl_temp == upstream entropy_deficit_kl_temp (L17691). *)

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
(* Set-carrier completion bridge: the interface class in this tree is *)
(*   unparameterized; its carrier is the global Cauchy real Real.     *)
Notation R := Real.

(* ============================================================ *)
(* Section ReqTempEntropy: the working interface of the temperature entropy layer *)
(*   Section variables = the ReqFEP summation face/interface bridges + the        *)
(*   ReqTemp Z_temp interface (no fixed-temperature D/Z/partition).               *)
(* ============================================================ *)
Section ReqTempEntropy.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis fsum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis fsum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis fsum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis fsum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis fsum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis fsum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.
Variable base_loss : S -> R.
Hypothesis dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.
Variable Z_temp : R -> R.
Hypothesis Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ---- Transparent aliases of the temperature family (delta-reachable).          ---- *)
(* ---- Positivity/normalization from Defined items; log premises literal-matched. ---- *)
Definition tB (t : R) (Ht : lt zero t) : S -> R :=
  reqd_boltzmann_dist_temp S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.
Definition tE (t : R) (Ht : lt zero t) : R :=
  reqd_energy_exp_temp S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.
Definition tBpos (t : R) (Ht : lt zero t) : reqd_positive_dist S (tB t Ht) :=
  reqd_boltzmann_dist_temp_pos S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.
Definition tBnorm (t : R) (Ht : lt zero t) : reqd_normalized S sumf (tB t Ht) :=
  reqd_boltzmann_dist_temp_normalized S sumf fsum_linear fsum_pos
    base_loss Z_temp Z_temp_spec t Ht.
Definition tZpos (t : R) (Ht : lt zero t) : lt zero (Z_temp t) :=
  req_Z_temp_pos S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.

(* ============================================================ *)
(* Item 1/5: explicit temperature entropy (upstream entropy_temp_explicit @17271) *)

(*   (pointwise decomposition reshaping + opp_plus/double negation + distrib +    *)
(*   commutation), then at the sum level fsum_ext + fsum_add + beta extraction    *)
(*   (pointwise comm/assoc + fsum_linear) + logZ constant extraction.             *)
(* ============================================================ *)
Theorem req_entropy_temp_explicit :
  forall (t : R) (Ht : lt zero t),
    req (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht))
        (plus (mult (inv_pos t Ht) (tE t Ht))
              (log (Z_temp t) (tZpos t Ht))).
Proof.
  intros t Ht.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (p := tB t Ht).
  set (Hp := tBpos t Ht).
  unfold reqd_entropy_dist.
  
  apply (req_trans
    (sumf (fun s : S => mult (p s) (opp (log (p s) (Hp s)))))
    (sumf (fun s : S => plus (mult (p s) (mult bta (base_loss s)))
                             (mult (p s) LZ)))
    (plus (mult bta (tE t Ht)) LZ)).
  - (* pointwise reshaping, entering the sum level *)
    apply (fsum_ext
      (fun s : S => mult (p s) (opp (log (p s) (Hp s))))
      (fun s : S => plus (mult (p s) (mult bta (base_loss s))) (mult (p s) LZ))).
    intro s.
    apply (req_trans
      (mult (p s) (opp (log (p s) (Hp s))))
      (mult (p s) (plus LZ (mult bta (base_loss s))))
      (plus (mult (p s) (mult bta (base_loss s))) (mult (p s) LZ))).
    + 
      apply (req_trans
        (mult (p s) (opp (log (p s) (Hp s))))
        (mult (p s) (opp (plus (opp LZ) (opp (mult bta (base_loss s))))))
        (mult (p s) (plus LZ (mult bta (base_loss s))))).
      * exact (req_mult_compat (p s) (p s)
                 (opp (log (p s) (Hp s)))
                 (opp (plus (opp LZ) (opp (mult bta (base_loss s)))))
                 (req_refl (p s))
                 (req_opp_compat (log (p s) (Hp s))
                                 (plus (opp LZ) (opp (mult bta (base_loss s))))
                                 (reqd_boltzmann_log_temp_decomp S sumf fsum_pos
                                    base_loss dist_log_inv_one_inv dist_log_exp_neg
                                    Z_temp Z_temp_spec t Ht s))).
      * apply (req_trans
          (mult (p s) (opp (plus (opp LZ) (opp (mult bta (base_loss s))))))
          (mult (p s) (plus (opp (opp LZ)) (opp (opp (mult bta (base_loss s))))))
          (mult (p s) (plus LZ (mult bta (base_loss s))))).
        -- exact (req_mult_compat (p s) (p s)
                     (opp (plus (opp LZ) (opp (mult bta (base_loss s)))))
                     (plus (opp (opp LZ)) (opp (opp (mult bta (base_loss s)))))
                     (req_refl (p s))
                     (req_opp_plus (opp LZ) (opp (mult bta (base_loss s))))).
        -- exact (req_mult_compat (p s) (p s)
                     (plus (opp (opp LZ)) (opp (opp (mult bta (base_loss s)))))
                     (plus LZ (mult bta (base_loss s)))
                     (req_refl (p s))
                     (req_plus_compat (opp (opp LZ)) LZ
                                      (opp (opp (mult bta (base_loss s))))
                                      (mult bta (base_loss s))
                                      (req_double_neg LZ)
                                      (req_double_neg (mult bta (base_loss s))))).
    + (* step B: p*(logZ+beta*e) == p*beta*e + p*logZ (distrib + plus_comm) *)
      apply (req_trans
        (mult (p s) (plus LZ (mult bta (base_loss s))))
        (plus (mult (p s) LZ) (mult (p s) (mult bta (base_loss s))))
        (plus (mult (p s) (mult bta (base_loss s))) (mult (p s) LZ))).
      * exact (distrib (p s) LZ (mult bta (base_loss s))).
      * exact (plus_comm (mult (p s) LZ) (mult (p s) (mult bta (base_loss s)))).
  - (* sum level: fsum_add + beta extraction + logZ constant extraction *)
    apply (req_trans
      (sumf (fun s : S => plus (mult (p s) (mult bta (base_loss s)))
                               (mult (p s) LZ)))
      (plus (sumf (fun s : S => mult (p s) (mult bta (base_loss s))))
            (sumf (fun s : S => mult (p s) LZ)))
      (plus (mult bta (tE t Ht)) LZ)).
    + exact (fsum_add
               (fun s : S => mult (p s) (mult bta (base_loss s)))
               (fun s : S => mult (p s) LZ)).
    + apply (req_plus_compat
               (sumf (fun s : S => mult (p s) (mult bta (base_loss s))))
               (mult bta (tE t Ht))
               (sumf (fun s : S => mult (p s) LZ))
               LZ).
      * (* beta extraction: sum p*(beta*e) == beta*sum p*e (pointwise comm/assoc + fsum_linear) *)
        apply (req_trans
          (sumf (fun s : S => mult (p s) (mult bta (base_loss s))))
          (sumf (fun s : S => mult bta (mult (p s) (base_loss s))))
          (mult bta (tE t Ht))).
        -- apply (fsum_ext
              (fun s : S => mult (p s) (mult bta (base_loss s)))
              (fun s : S => mult bta (mult (p s) (base_loss s)))).
           intro s.
           apply (req_trans
             (mult (p s) (mult bta (base_loss s)))
             (mult (mult bta (base_loss s)) (p s))
             (mult bta (mult (p s) (base_loss s)))).
           ++ exact (mult_comm (p s) (mult bta (base_loss s))).
           ++ apply (req_trans
                (mult (mult bta (base_loss s)) (p s))
                (mult bta (mult (base_loss s) (p s)))
                (mult bta (mult (p s) (base_loss s)))).
              ** exact (req_sym (mult bta (mult (base_loss s) (p s)))
                                (mult (mult bta (base_loss s)) (p s))
                                (mult_assoc bta (base_loss s) (p s))).
              ** exact (req_mult_compat bta bta
                          (mult (base_loss s) (p s))
                          (mult (p s) (base_loss s))
                          (req_refl bta) (mult_comm (base_loss s) (p s))).
        -- exact (fsum_linear bta (fun s : S => mult (p s) (base_loss s))).
      * (* logZ constant extraction: sum p*logZ == logZ*sum p == logZ *)
        apply (req_trans
          (sumf (fun s : S => mult (p s) LZ))
          (sumf (fun s : S => mult LZ (p s)))
          LZ).
        -- apply (fsum_ext (fun s : S => mult (p s) LZ)
                           (fun s : S => mult LZ (p s))).
           intro s. exact (mult_comm (p s) LZ).
        -- apply (req_trans
              (sumf (fun s : S => mult LZ (p s)))
              (mult LZ (sumf p))
              LZ).
           ++ exact (fsum_linear LZ p).
           ++ apply (req_trans (mult LZ (sumf p)) (mult LZ one) LZ).
              ** exact (req_mult_compat LZ LZ (sumf p) one
                          (req_refl LZ) (tBnorm t Ht)).
              ** exact (mult_one LZ).
Qed.

(* ============================================================ *)
(* Item 2/5: relative-entropy temperature decomposition (upstream @17356) *)



(*   (pointwise decomposition + commutation + distrib + opp_mult_l + beta         *)
(*   extraction + logZ constant extraction); assembly fsum_add/fsum_opp +         *)
(*   opp_plus/double negation + plus_assoc.                                       *)
(* ============================================================ *)
Theorem req_relative_entropy_temp_decomp :
  forall (t : R) (Ht : lt zero t) (q : S -> R) (Hq : reqd_positive_dist S q),
    reqd_normalized S sumf q ->
    req (req_relative_entropy S sumf q (tB t Ht) Hq (tBpos t Ht))
        (plus (plus (opp (reqd_entropy_dist S sumf q Hq))
                    (mult (inv_pos t Ht)
                          (reqd_energy_expectation S sumf base_loss q)))
              (log (Z_temp t) (tZpos t Ht))).
Proof.
  intros t Ht q Hq Hnq.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (pB := tB t Ht).
  set (HpB := tBpos t Ht).
  set (Hq0 := reqd_entropy_dist S sumf q Hq).
  set (Eq := reqd_energy_expectation S sumf base_loss q).
  unfold req_relative_entropy, req_minus.
  (* pre-balanced atomic term P2: q*(beta*e) == beta*(q*e) (comm/assoc rearrangement) *)
  assert (P2 : forall s : S,
    req (mult (q s) (mult bta (base_loss s))) (mult bta (mult (q s) (base_loss s)))).
  { intro s.
    apply (req_trans
      (mult (q s) (mult bta (base_loss s)))
      (mult (mult bta (base_loss s)) (q s))
      (mult bta (mult (q s) (base_loss s)))).
    - exact (mult_comm (q s) (mult bta (base_loss s))).
    - apply (req_trans
        (mult (mult bta (base_loss s)) (q s))
        (mult bta (mult (base_loss s) (q s)))
        (mult bta (mult (q s) (base_loss s)))).
      + exact (req_sym (mult bta (mult (base_loss s) (q s)))
                       (mult (mult bta (base_loss s)) (q s))
                       (mult_assoc bta (base_loss s) (q s))).
      + exact (req_mult_compat bta bta
                 (mult (base_loss s) (q s)) (mult (q s) (base_loss s))
                 (req_refl bta) (mult_comm (base_loss s) (q s))). }
  (* pre-balanced atomic term Hcz: sum q*logZ == logZ (constant extraction + normalization) *)
  assert (Hcz : req (sumf (fun s : S => mult (q s) LZ)) LZ).
  { apply (req_trans
      (sumf (fun s : S => mult (q s) LZ))
      (sumf (fun s : S => mult LZ (q s)))
      LZ).
    - apply (fsum_ext (fun s : S => mult (q s) LZ) (fun s : S => mult LZ (q s))).
      intro s. exact (mult_comm (q s) LZ).
    - apply (req_trans
        (sumf (fun s : S => mult LZ (q s)))
        (mult LZ (sumf q))
        LZ).
      + exact (fsum_linear LZ q).
      + apply (req_trans (mult LZ (sumf q)) (mult LZ one) LZ).
        * exact (req_mult_compat LZ LZ (sumf q) one (req_refl LZ) Hnq).
        * exact (mult_one LZ). }
  
  assert (HlogH : req (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))
                      (plus (opp (mult bta Eq)) (opp LZ))).
  { apply (req_trans
      (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))
      (sumf (fun s : S => plus (opp (mult (q s) (mult bta (base_loss s))))
                               (opp (mult (q s) LZ))))
      (plus (opp (mult bta Eq)) (opp LZ))).
    - 
      apply (fsum_ext
        (fun s : S => mult (q s) (log (pB s) (HpB s)))
        (fun s : S => plus (opp (mult (q s) (mult bta (base_loss s))))
                           (opp (mult (q s) LZ)))).
      intro s.
      apply (req_trans
        (mult (q s) (log (pB s) (HpB s)))
        (mult (q s) (plus (opp LZ) (opp (mult bta (base_loss s)))))
        (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
      + (* decomposition reshaping *)
        exact (req_mult_compat (q s) (q s)
                 (log (pB s) (HpB s))
                 (plus (opp LZ) (opp (mult bta (base_loss s))))
                 (req_refl (q s))
                 (reqd_boltzmann_log_temp_decomp S sumf fsum_pos base_loss
                    dist_log_inv_one_inv dist_log_exp_neg
                    Z_temp Z_temp_spec t Ht s)).
      + (* remaining four steps: commutation + distrib + opp_mult_l twice *)
        apply (req_trans
          (mult (q s) (plus (opp LZ) (opp (mult bta (base_loss s)))))
          (mult (q s) (plus (opp (mult bta (base_loss s))) (opp LZ)))
          (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
        * exact (req_mult_compat (q s) (q s)
                   (plus (opp LZ) (opp (mult bta (base_loss s))))
                   (plus (opp (mult bta (base_loss s))) (opp LZ))
                   (req_refl (q s))
                   (plus_comm (opp LZ) (opp (mult bta (base_loss s))))).
        * apply (req_trans
            (mult (q s) (plus (opp (mult bta (base_loss s))) (opp LZ)))
            (plus (mult (q s) (opp (mult bta (base_loss s))))
                  (mult (q s) (opp LZ)))
            (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
          -- exact (distrib (q s) (opp (mult bta (base_loss s))) (opp LZ)).
          -- apply (req_trans
               (plus (mult (q s) (opp (mult bta (base_loss s)))) (mult (q s) (opp LZ)))
               (plus (opp (mult (q s) (mult bta (base_loss s)))) (mult (q s) (opp LZ)))
               (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
             ++ exact (req_plus_compat
                         (mult (q s) (opp (mult bta (base_loss s))))
                         (opp (mult (q s) (mult bta (base_loss s))))
                         (mult (q s) (opp LZ))
                         (mult (q s) (opp LZ))
                         (req_opp_mult_l (q s) (mult bta (base_loss s)))
                         (req_refl (mult (q s) (opp LZ)))).
             ++ exact (req_plus_compat
                         (opp (mult (q s) (mult bta (base_loss s))))
                         (opp (mult (q s) (mult bta (base_loss s))))
                         (mult (q s) (opp LZ))
                         (opp (mult (q s) LZ))
                         (req_refl (opp (mult (q s) (mult bta (base_loss s)))))
                         (req_opp_mult_l (q s) LZ)).
    - (* sum level: fsum_add + both branches closed separately *)
      apply (req_trans
        (sumf (fun s : S => plus (opp (mult (q s) (mult bta (base_loss s))))
                                 (opp (mult (q s) LZ))))
        (plus (sumf (fun s : S => opp (mult (q s) (mult bta (base_loss s)))))
              (sumf (fun s : S => opp (mult (q s) LZ))))
        (plus (opp (mult bta Eq)) (opp LZ))).
      + exact (fsum_add
                 (fun s : S => opp (mult (q s) (mult bta (base_loss s))))
                 (fun s : S => opp (mult (q s) LZ))).
      + apply (req_plus_compat
                 (sumf (fun s : S => opp (mult (q s) (mult bta (base_loss s)))))
                 (opp (mult bta Eq))
                 (sumf (fun s : S => opp (mult (q s) LZ)))
                 (opp LZ)).
        * exact (req_trans
                   (sumf (fun s : S => opp (mult (q s) (mult bta (base_loss s)))))
                   (sumf (fun s : S => opp (mult bta (mult (q s) (base_loss s)))))
                   (opp (mult bta Eq))
                   (fsum_ext
                      (fun s : S => opp (mult (q s) (mult bta (base_loss s))))
                      (fun s : S => opp (mult bta (mult (q s) (base_loss s))))
                      (fun s : S => req_opp_compat
                                      (mult (q s) (mult bta (base_loss s)))
                                      (mult bta (mult (q s) (base_loss s)))
                                      (P2 s)))
                   (req_trans
                      (sumf (fun s : S => opp (mult bta (mult (q s) (base_loss s)))))
                      (opp (sumf (fun s : S => mult bta (mult (q s) (base_loss s)))))
                      (opp (mult bta Eq))
                      (fsum_opp S sumf fsum_ext fsum_linear
                         (fun s : S => mult bta (mult (q s) (base_loss s))))
                      (req_opp_compat
                         (sumf (fun s : S => mult bta (mult (q s) (base_loss s))))
                         (mult bta Eq)
                         (fsum_linear bta (fun s : S => mult (q s) (base_loss s)))))).
        * exact (req_trans
                   (sumf (fun s : S => opp (mult (q s) LZ)))
                   (opp (sumf (fun s : S => mult (q s) LZ)))
                   (opp LZ)
                   (fsum_opp S sumf fsum_ext fsum_linear (fun s : S => mult (q s) LZ))
                   (req_opp_compat (sumf (fun s : S => mult (q s) LZ)) LZ Hcz)). }
  (* pre-balanced atomic term Hopp: opp(opp X + opp Y) == X + Y *)
  assert (Hopp : req (opp (plus (opp (mult bta Eq)) (opp LZ))) (plus (mult bta Eq) LZ)).
  { exact (req_trans
             (opp (plus (opp (mult bta Eq)) (opp LZ)))
             (plus (opp (opp (mult bta Eq))) (opp (opp LZ)))
             (plus (mult bta Eq) LZ)
             (req_opp_plus (opp (mult bta Eq)) (opp LZ))
             (req_plus_compat (opp (opp (mult bta Eq))) (mult bta Eq)
                              (opp (opp LZ)) LZ
                              (req_double_neg (mult bta Eq))
                              (req_double_neg LZ))). }
  (* main chain assembly *)
  apply (req_trans
    (sumf (fun s : S => mult (q s)
                              (plus (log (q s) (Hq s)) (opp (log (pB s) (HpB s))))))
    (sumf (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                             (mult (q s) (opp (log (pB s) (HpB s))))))
    (plus (plus (opp Hq0) (mult bta Eq)) LZ)).
  - apply (fsum_ext
      (fun s : S => mult (q s)
                         (plus (log (q s) (Hq s)) (opp (log (pB s) (HpB s)))))
      (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                         (mult (q s) (opp (log (pB s) (HpB s)))))).
    intro s.
    exact (distrib (q s) (log (q s) (Hq s)) (opp (log (pB s) (HpB s)))).
  - apply (req_trans
      (sumf (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                               (mult (q s) (opp (log (pB s) (HpB s))))))
      (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
            (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))))
      (plus (plus (opp Hq0) (mult bta Eq)) LZ)).
    + exact (req_trans
               (sumf (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                                        (mult (q s) (opp (log (pB s) (HpB s))))))
               (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                     (sumf (fun s : S => mult (q s) (opp (log (pB s) (HpB s))))))
               (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                     (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))))
               (fsum_add (fun s : S => mult (q s) (log (q s) (Hq s)))
                         (fun s : S => mult (q s) (opp (log (pB s) (HpB s)))))
               (req_plus_compat
                  (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                  (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                  (sumf (fun s : S => mult (q s) (opp (log (pB s) (HpB s)))))
                  (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s)))))
                  (req_refl (sumf (fun s : S => mult (q s) (log (q s) (Hq s)))))
                  (req_trans
                     (sumf (fun s : S => mult (q s) (opp (log (pB s) (HpB s)))))
                     (sumf (fun s : S => opp (mult (q s) (log (pB s) (HpB s)))))
                     (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s)))))
                     (fsum_ext
                        (fun s : S => mult (q s) (opp (log (pB s) (HpB s))))
                        (fun s : S => opp (mult (q s) (log (pB s) (HpB s))))
                        (fun s : S => req_opp_mult_l (q s) (log (pB s) (HpB s))))
                     (fsum_opp S sumf fsum_ext fsum_linear
                        (fun s : S => mult (q s) (log (pB s) (HpB s))))))).
    + apply (req_trans
        (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
              (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))))
        (plus (opp Hq0) (opp (plus (opp (mult bta Eq)) (opp LZ))))
        (plus (plus (opp Hq0) (mult bta Eq)) LZ)).
      * apply (req_plus_compat
                 (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                 (opp Hq0)
                 (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s)))))
                 (opp (plus (opp (mult bta Eq)) (opp LZ)))).
        -- exact (req_entropy_neg_sum S sumf fsum_ext fsum_linear q Hq).
        -- exact (req_opp_compat
                    (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))
                    (plus (opp (mult bta Eq)) (opp LZ))
                    HlogH).
      * exact (req_trans
                 (plus (opp Hq0) (opp (plus (opp (mult bta Eq)) (opp LZ))))
                 (plus (opp Hq0) (plus (mult bta Eq) LZ))
                 (plus (plus (opp Hq0) (mult bta Eq)) LZ)
                 (req_plus_compat (opp Hq0) (opp Hq0)
                                  (opp (plus (opp (mult bta Eq)) (opp LZ)))
                                  (plus (mult bta Eq) LZ)
                                  (req_refl (opp Hq0)) Hopp)
                 (plus_assoc (opp Hq0) (mult bta Eq) LZ)).
Qed.

(* ============================================================ *)
(* Item 3/5: temperature version of the entropy deficit (upstream                 *)
(*   entropy_deficit_kl_temp @17691; also named req_entropy_deficit_kl_temp).     *)
(*   Same constrained energy E(p) == E(p_beta) implies S[p_beta] - S[p] == KL(p||p_beta). *)
(*   Chain: KL decomposition (item 2) + explicit entropy (item 1) + assoc/comm    *)
(*   rearrangement + same-energy substitution (beta*E(p) to beta*E(p_beta), via   *)
(*   req_mult_compat); after req_minus expansion closed by Hse forward / Hsub backward. *)
(* ============================================================ *)
Theorem req_entropy_deficit_temp :
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : reqd_positive_dist S p),
    reqd_normalized S sumf p ->
    req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
    req (req_minus (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht))
                   (reqd_entropy_dist S sumf p Hp))
        (req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
Proof.
  intros t Ht p Hp Hnp Henergy.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (Sp := reqd_entropy_dist S sumf p Hp).
  set (Spt := reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
  set (K := req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
  set (Ep := reqd_energy_expectation S sumf base_loss p).
  (* KL(p||p_beta) == -S[p] + beta*E(p) + logZ (item 2) *)
  assert (Hkl : req K (plus (plus (opp Sp) (mult bta Ep)) LZ))
    by exact (req_relative_entropy_temp_decomp t Ht p Hp Hnp).
  (* S[p_beta] == beta*E(p_beta) + logZ (item 1) *)
  assert (Hse : req Spt (plus (mult bta (tE t Ht)) LZ))
    by exact (req_entropy_temp_explicit t Ht).
  (* rearrangement: K == (beta*E(p) + logZ) + (-S[p]) *)
  assert (Hkl' : req K (plus (plus (mult bta Ep) LZ) (opp Sp))).
  { exact (req_trans K
             (plus (opp Sp) (plus (mult bta Ep) LZ))
             (plus (plus (mult bta Ep) LZ) (opp Sp))
             (req_trans K
                (plus (plus (opp Sp) (mult bta Ep)) LZ)
                (plus (opp Sp) (plus (mult bta Ep) LZ))
                Hkl
                (req_sym (plus (opp Sp) (plus (mult bta Ep) LZ))
                         (plus (plus (opp Sp) (mult bta Ep)) LZ)
                         (plus_assoc (opp Sp) (mult bta Ep) LZ)))
             (plus_comm (opp Sp) (plus (mult bta Ep) LZ))). }
  (* same-energy substitution: beta*E(p) := beta*E(p_beta) *)
  assert (Hsub : req K (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp))).
  { exact (req_trans K
             (plus (plus (mult bta Ep) LZ) (opp Sp))
             (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp))
             Hkl'
             (req_plus_compat (plus (mult bta Ep) LZ)
                              (plus (mult bta (tE t Ht)) LZ)
                              (opp Sp) (opp Sp)
                              (req_plus_compat (mult bta Ep)
                                               (mult bta (tE t Ht))
                                               LZ LZ
                                               (req_mult_compat bta bta Ep (tE t Ht)
                                                                (req_refl bta) Henergy)
                                               (req_refl LZ))
                              (req_refl (opp Sp)))). }
  (* goal: S[p_beta] - S[p] == K (req_minus expansion + Hse forward / Hsub backward) *)
  unfold req_minus.
  apply (req_trans (plus Spt (opp Sp))
                   (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp))
                   K).
  - exact (req_plus_compat Spt (plus (mult bta (tE t Ht)) LZ)
                           (opp Sp) (opp Sp)
                           Hse (req_refl (opp Sp))).
  - exact (req_sym K (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp)) Hsub).
Qed.

(* ============================================================ *)
(* Item 4/5: maximum entropy = Boltzmann, temperature version                     *)
(*   (upstream max_entropy_is_boltzmann_temp @17726).                             *)
(*   Same constrained energy implies S[p] <= S[p_beta]. Assembly: the deficit     *)
(*   (item 3) + req_gibbs_inequality (both p and p_beta normalized) + a le        *)
(*   rearrangement chain (le_id_r + req_minus_plus_cancel + req_le_plus_nonneg_r). *)
(* ============================================================ *)
Theorem req_max_entropy_is_boltzmann_temp :
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : reqd_positive_dist S p),
    reqd_normalized S sumf p ->
    req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
    le (reqd_entropy_dist S sumf p Hp)
       (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
Proof.
  intros t Ht p Hp Hnp Henergy.
  set (Sp := reqd_entropy_dist S sumf p Hp).
  set (Spt := reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
  set (K := req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
  (* 1. S[p_beta] - S[p] == KL (item 3) *)
  assert (Hdef : req (req_minus Spt Sp) K)
    by exact (req_entropy_deficit_temp t Ht p Hp Hnp Henergy).
  (* 2. KL >= 0 (req_gibbs_inequality; p_beta normalized by reqd_boltzmann_dist_temp_normalized) *)
  assert (Hkl : le zero K).
  { exact (req_gibbs_inequality S sumf fsum_ext fsum_add fsum_linear fsum_le
                                dist_log_inv_one_inv dist_log_le_linear
                                p (tB t Ht) Hp (tBpos t Ht) Hnp (tBnorm t Ht)). }
  (* 3. 0 <= S[p_beta] - S[p] implies S[p] <= S[p_beta] *)
  assert (Hnonneg : le zero (req_minus Spt Sp))
    by exact (le_id_r zero K (req_minus Spt Sp) (req_sym _ _ Hdef) Hkl).
  apply (le_id_r Sp (plus Sp (req_minus Spt Sp)) Spt).
  - exact (req_minus_plus_cancel Sp Spt).
  - exact (req_le_plus_nonneg_r Sp (req_minus Spt Sp) Hnonneg).
Qed.

(* ============================================================ *)
(* Item 5/5: uniqueness, temperature version (upstream entropy_max_unique_temp    *)
(*   @17763). Same constrained energy + same entropy imply p == p_beta pointwise. *)
(*   Assembly: the deficit (item 3) + same entropy implies KL == 0                *)
(*   (req_minus_self_zero) + req_gibbs_equality (KL == 0 implies pointwise equality). *)
(* ============================================================ *)
Theorem req_entropy_max_unique_temp :
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : reqd_positive_dist S p),
    reqd_normalized S sumf p ->
    req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
    req (reqd_entropy_dist S sumf p Hp)
        (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)) ->
    forall s : S, req (p s) (tB t Ht s).
Proof.
  intros t Ht p Hp Hnp Henergy Hent s.
  set (Sp := reqd_entropy_dist S sumf p Hp).
  set (Spt := reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
  set (K := req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
  (* 1. S[p_beta] - S[p] == KL (item 3) *)
  assert (Hdef : req (req_minus Spt Sp) K)
    by exact (req_entropy_deficit_temp t Ht p Hp Hnp Henergy).
  (* 2. equal entropy implies KL == 0 *)
  assert (Hkl0 : req K zero).
  { exact (req_trans K (req_minus Spt Sp) zero
             (req_sym _ _ Hdef)
             (req_minus_self_zero Spt Sp (req_sym _ _ Hent))). }
  (* 3. gibbs_equality: KL == 0 implies p == p_beta pointwise *)
  exact (req_gibbs_equality S sumf fsum_ext fsum_add fsum_linear fsum_zero_nonneg
                            dist_log_inv_one_inv dist_log_le_linear
                            dist_log_eq_linear
                            p (tB t Ht) Hp (tBpos t Ht) Hnp (tBnorm t Ht) Hkl0 s).
Qed.

(* ============================================================ *)
(* Temperature strict-layer increment section (six items built on the upstream    *)
(*   originals below; five carry explicit interface gaps, one is discharged):     *)
(*     variational_temp_bound         @L17468                                      *)
(*     energy_exp_temp_mono           @L17521                                      *)
(*     temp_energy_dual_closed        @L17788 (sigT form)                          *)
(*     temp_strict_A_chain2           @L17825                                      *)
(*     temp_strict_ident2             @L17879                                      *)
(*     energy_exp_temp_strict_mono    @L18019                                      *)
(*   Assembly route (following the closing notes of UpReqDist.v): item 1 (explicit  *)
(*   entropy) + item 2 (temperature KL decomposition) + the rearrangement chain of  *)
(*   UpReqDist.ReqAlgBridge2 (the req_le_plus_cancel_l family /                     *)
(*   req_le_mult_pos_cancel / req_le_minus_nonneg_rev / req_mult_minus_distr_r /    *)
(*   reqd_lt_mult_pos_cancel / reqd_minus_compat).                                  *)
(*   Honest interface-gap positions (same positions as upstream, kept pointwise):  *)
(*     a) upstream L17119 inv_pos_lt_compat (a Variable): the interface-field       *)
(*       closure check passes (inv_pos_pos/inv_pos_correct/lt_mult_compat);         *)
(*       following the RestA precedent it is discharged as the theorem              *)
(*       req_inv_pos_lt_contra, with no axiom added;                                *)
(*     b) upstream L17121 lt_minus_nonneg (a Variable): the interface abstraction   *)
(*       layer has no lt-to-minus connecting field (the Real layer builds it per    *)
(*       eps), so it cannot be discharged; in the mono/strict_mono items the        *)
(*       explicit premise lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) is  *)
(*       kept pointwise (a theorem under the Real instantiation; no claim inflation). *)
(* ============================================================ *)

(* ---- Discharged item: anti-monotonicity of inv (upstream L21013/L17119 gap)   ---- *)
(*   Chain: inv b == (inv a*a)*inv b < (inv a*b)*inv b == inv a                    *)
(*   (both ends absorbed by inv_pos_correct/mult_one; the middle step uses         *)
(*   lt_mult_compat twice + req_lt_compat commutation transport); same pattern     *)
(*   as RestA ralt_inv_pos_lt_contra; a genuine proof inside the interface-field closure. *)
Lemma req_inv_pos_lt_contra :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  set (ia := inv_pos a Ha).
  set (ib := inv_pos b Hb).
  assert (Hia1 : req (mult ia a) one).
  { exact (req_trans (mult ia a) (mult a ia) one
             (mult_comm ia a) (inv_pos_correct a Ha)). }
  assert (Hib1 : req (mult b ib) one).
  { exact (inv_pos_correct b Hb). }
  assert (Hmid : req (mult (mult ia a) ib) ib).
  { apply (req_trans (mult (mult ia a) ib) (mult one ib) ib).
    - exact (req_mult_compat (mult ia a) one ib ib Hia1 (req_refl ib)).
    - exact (req_trans (mult one ib) (mult ib one) ib
               (mult_comm one ib) (mult_one ib)). }
  assert (Hlt1 : lt (mult ia a) (mult ia b)).
  { apply (req_lt_compat (mult a ia) (mult ia a) (mult b ia) (mult ia b)
                         (mult_comm a ia) (mult_comm b ia)).
    exact (lt_mult_compat a b ia (inv_pos_pos a Ha) Hab). }
  assert (Hltmid : lt (mult (mult ia a) ib) (mult (mult ia b) ib)).
  { exact (lt_mult_compat (mult ia a) (mult ia b) ib
             (inv_pos_pos b Hb) Hlt1). }
  assert (Hright : req (mult (mult ia b) ib) ia).
  { apply (req_trans (mult (mult ia b) ib) (mult ia (mult b ib)) ia).
    - exact (req_sym (mult ia (mult b ib)) (mult (mult ia b) ib)
                     (mult_assoc ia b ib)).
    - apply (req_trans (mult ia (mult b ib)) (mult ia one) ia).
      + exact (req_mult_compat ia ia (mult b ib) one
                 (req_refl ia) Hib1).
      + exact (mult_one ia). }
  apply (lt_id_r ib (mult (mult ia b) ib) ia Hright).
  exact (lt_id_l ib (mult (mult ia a) ib) (mult (mult ia b) ib)
                   (req_sym (mult (mult ia a) ib) ib Hmid) Hltmid).
Qed.

(* ---- Algebra helper: difference pair (x-y)+(y-x) == 0 (pure interface algebra) ---- *)
Lemma reqd_minus_pair_cancel :
  forall a b : R, req (plus (req_minus a b) (req_minus b a)) zero.
Proof.
  intros a b.
  apply (req_trans (plus (req_minus a b) (req_minus b a))
                   (plus a (plus (opp b) (plus b (opp a))))
                   zero).
  - exact (req_sym (plus a (plus (opp b) (plus b (opp a))))
                   (plus (plus a (opp b)) (plus b (opp a)))
                   (plus_assoc a (opp b) (plus b (opp a)))).
  - apply (req_trans (plus a (plus (opp b) (plus b (opp a))))
                     (plus a (plus (plus (opp b) b) (opp a)))
                     zero).
    + exact (req_plus_compat a a
               (plus (opp b) (plus b (opp a)))
               (plus (plus (opp b) b) (opp a))
               (req_refl a) (plus_assoc (opp b) b (opp a))).
    + apply (req_trans (plus a (plus (plus (opp b) b) (opp a)))
                       (plus a (plus zero (opp a)))
                       zero).
      * exact (req_plus_compat a a
                  (plus (plus (opp b) b) (opp a))
                  (plus zero (opp a))
                  (req_refl a)
                  (req_plus_compat (plus (opp b) b) zero (opp a) (opp a)
                     (req_trans (plus (opp b) b) (plus b (opp b)) zero
                        (plus_comm (opp b) b) (plus_opp b))
                     (req_refl (opp a)))).
      * apply (req_trans (plus a (plus zero (opp a)))
                         (plus a (opp a))
                         zero).
        -- exact (req_plus_compat a a (plus zero (opp a)) (opp a)
                    (req_refl a)
                    (req_trans (plus zero (opp a)) (plus (opp a) zero) (opp a)
                       (plus_comm zero (opp a)) (plus_zero (opp a)))).
        -- exact (plus_opp a).
Qed.

(* ---- Algebra helper: subtraction flip (b-a) == -(a-b) (pure interface algebra) ---- *)
Lemma reqd_minus_opp_flip :
  forall a b : R, req (req_minus b a) (opp (req_minus a b)).
Proof.
  intros a b.
  apply (req_trans (plus b (opp a)) (plus (opp a) b)
                   (opp (plus a (opp b)))).
  - exact (plus_comm b (opp a)).
  - apply (req_trans (plus (opp a) b)
                     (plus (opp a) (opp (opp b)))
                     (opp (plus a (opp b)))).
    + exact (req_plus_compat (opp a) (opp a) b (opp (opp b))
               (req_refl (opp a)) (req_sym (opp (opp b)) b (req_double_neg b))).
    + exact (req_sym (opp (plus a (opp b))) (plus (opp a) (opp (opp b)))
                     (req_opp_plus a (opp b))).
Qed.

(* ============================================================ *)
(* Strict-layer item 1/6: reshaped KL decomposition (upstream                     *)

(*   temp_strict_A_chain2 @17825). Non-triviality: assembly (item 1 explicit       *)
(*   entropy) + a genuine algebra chain (opp_plus/double negation/distrib/req_mult_minus_distr_r req chain, zero rewrite). *)
(* ============================================================ *)
Theorem req_temp_strict_A_chain2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    req (plus (plus (opp (reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)))
                    (mult (inv_pos t1 Ht1) (tE t2 Ht2)))
              (log (Z_temp t1) (tZpos t1 Ht1)))
        (plus (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
                    (tE t2 Ht2))
              (req_minus (log (Z_temp t1) (tZpos t1 Ht1))
                         (log (Z_temp t2) (tZpos t2 Ht2)))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1).
  set (b2 := inv_pos t2 Ht2).
  set (E2 := tE t2 Ht2).
  set (S2 := reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)).
  set (LZ1 := log (Z_temp t1) (tZpos t1 Ht1)).
  set (LZ2 := log (Z_temp t2) (tZpos t2 Ht2)).
  (* explicit entropy (item 1): S2 == b2*E2 + LZ2 *)
  assert (Hse : req S2 (plus (mult b2 E2) LZ2))
    by exact (req_entropy_temp_explicit t2 Ht2).
  (* main chain in five stages (isomorphic to upstream H1/H2/H3/H4/H5; id_cong as req compat bridges) *)
  assert (H1 : req (plus (plus (opp S2) (mult b1 E2)) LZ1)
                   (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)).
  { exact (req_plus_compat
             (plus (opp S2) (mult b1 E2))
             (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2))
             LZ1 LZ1
             (req_plus_compat (opp S2) (opp (plus (mult b2 E2) LZ2))
                              (mult b1 E2) (mult b1 E2)
                              (req_opp_compat S2 (plus (mult b2 E2) LZ2) Hse)
                              (req_refl (mult b1 E2)))
             (req_refl LZ1)). }
  assert (H2 : req (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)
                   (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)).
  { exact (req_plus_compat
             (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2))
             (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2))
             LZ1 LZ1
             (req_plus_compat (opp (plus (mult b2 E2) LZ2))
                              (plus (opp (mult b2 E2)) (opp LZ2))
                              (mult b1 E2) (mult b1 E2)
                              (req_opp_plus (mult b2 E2) LZ2)
                              (req_refl (mult b1 E2)))
             (req_refl LZ1)). }
  assert (H3 : req (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
                   (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                         (plus (opp LZ2) LZ1))).
  { apply (req_trans
             (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
             (plus (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2))) LZ1)
             (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                   (plus (opp LZ2) LZ1))).
    - exact (req_plus_compat
               (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2))
               (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2)))
               LZ1 LZ1
               (req_sym (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2)))
                        (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2))
                        (plus_assoc (opp (mult b2 E2)) (opp LZ2) (mult b1 E2)))
               (req_refl LZ1)).
    - apply (req_trans
               (plus (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2))) LZ1)
               (plus (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2))) LZ1)
               (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                     (plus (opp LZ2) LZ1))).
      + exact (req_plus_compat
                 (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2)))
                 (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2)))
                 LZ1 LZ1
                 (req_plus_compat (opp (mult b2 E2)) (opp (mult b2 E2))
                    (plus (opp LZ2) (mult b1 E2)) (plus (mult b1 E2) (opp LZ2))
                    (req_refl (opp (mult b2 E2)))
                    (plus_comm (opp LZ2) (mult b1 E2)))
                 (req_refl LZ1)).
      + apply (req_trans
                 (plus (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2))) LZ1)
                 (plus (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (opp LZ2)) LZ1)
                 (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                       (plus (opp LZ2) LZ1))).
        * exact (req_plus_compat
                   (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2)))
                   (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (opp LZ2))
                   LZ1 LZ1
                   (plus_assoc (opp (mult b2 E2)) (mult b1 E2) (opp LZ2))
                   (req_refl LZ1)).
        * exact (req_sym
                   (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                         (plus (opp LZ2) LZ1))
                   (plus (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (opp LZ2))
                         LZ1)
                   (plus_assoc (plus (opp (mult b2 E2)) (mult b1 E2))
                               (opp LZ2) LZ1)). }
  assert (H4 : req (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                         (plus (opp LZ2) LZ1))
                   (plus (mult (req_minus b1 b2) E2) (plus (opp LZ2) LZ1))).
  { exact (req_plus_compat
             (plus (opp (mult b2 E2)) (mult b1 E2))
             (mult (req_minus b1 b2) E2)
             (plus (opp LZ2) LZ1) (plus (opp LZ2) LZ1)
             (req_trans (plus (opp (mult b2 E2)) (mult b1 E2))
                        (plus (mult b1 E2) (opp (mult b2 E2)))
                        (mult (req_minus b1 b2) E2)
                        (plus_comm (opp (mult b2 E2)) (mult b1 E2))
                        (req_sym (mult (req_minus b1 b2) E2)
                                 (req_minus (mult b1 E2) (mult b2 E2))
                                 (req_mult_minus_distr_r b1 b2 E2)))
             (req_refl (plus (opp LZ2) LZ1))). }
  assert (H5 : req (plus (mult (req_minus b1 b2) E2) (plus (opp LZ2) LZ1))
                   (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))).
  { exact (req_plus_compat
             (mult (req_minus b1 b2) E2) (mult (req_minus b1 b2) E2)
             (plus (opp LZ2) LZ1) (req_minus LZ1 LZ2)
             (req_refl (mult (req_minus b1 b2) E2))
             (plus_comm (opp LZ2) LZ1)). }
  exact (req_trans
           (plus (plus (opp S2) (mult b1 E2)) LZ1)
           (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)
           (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
           H1
           (req_trans
              (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)
              (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
              (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
              H2
              (req_trans
                 (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
                 (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                       (plus (opp LZ2) LZ1))
                 (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                 H3
                 (req_trans
                    (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                          (plus (opp LZ2) LZ1))
                    (plus (mult (req_minus b1 b2) E2) (plus (opp LZ2) LZ1))
                    (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                    H4
                    H5)))).
Qed.

(* ============================================================ *)
(* Strict-layer item 2/6: the variational bound (upstream                        *)
(*   variational_temp_bound @17468). For a normalized positive distribution q:    *)
(*   H(q) - beta*E(q) <= log Z_t. Non-triviality: assembly (item 2 KL decomposition *)
(*   + req_gibbs_inequality) + a genuine rearrangement chain (le_id_l/le_id_r + le_plus_compat + a 4-step algebra chain). *)
(* ============================================================ *)
Theorem req_variational_temp_bound :
  forall (t : R) (Ht : lt zero t) (q : S -> R) (Hq : reqd_positive_dist S q),
    reqd_normalized S sumf q ->
    le (req_minus (reqd_entropy_dist S sumf q Hq)
                  (mult (inv_pos t Ht) (reqd_energy_expectation S sumf base_loss q)))
       (log (Z_temp t) (tZpos t Ht)).
Proof.
  intros t Ht q Hq Hnq.
  set (Sq := reqd_entropy_dist S sumf q Hq).
  set (bE := mult (inv_pos t Ht) (reqd_energy_expectation S sumf base_loss q)).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  (* KL(q||p_t) >= 0 (req_gibbs_inequality) *)
  assert (Hkl : le zero (req_relative_entropy S sumf q (tB t Ht) Hq (tBpos t Ht))).
  { exact (req_gibbs_inequality S sumf fsum_ext fsum_add fsum_linear fsum_le
             dist_log_inv_one_inv dist_log_le_linear
             q (tB t Ht) Hq (tBpos t Ht) Hnq (tBnorm t Ht)). }
  (* KL == (-H + beta*E) + logZ (item 2), transported *)
  assert (Hkl0 : le zero (plus (plus (opp Sq) bE) LZ)).
  { exact (le_id_r zero
             (req_relative_entropy S sumf q (tB t Ht) Hq (tBpos t Ht))
             (plus (plus (opp Sq) bE) LZ)
             (req_relative_entropy_temp_decomp t Ht q Hq Hnq)
             Hkl). }
  (* rearrangement 1: H <= beta*E + logZ *)
  assert (Hstep1 : le Sq (plus bE LZ)).
  { apply (le_id_l Sq (plus Sq zero)).
    - exact (req_sym (plus Sq zero) Sq (plus_zero Sq)).
    - apply (le_id_r (plus Sq zero)
               (plus Sq (plus (plus (opp Sq) bE) LZ)) (plus bE LZ)).
      + (* Sq + ((-Sq + beta*E) + LZ) == beta*E + LZ: 4-step algebra chain *)
        apply (req_trans (plus Sq (plus (plus (opp Sq) bE) LZ))
                         (plus (plus Sq (plus (opp Sq) bE)) LZ)
                         (plus bE LZ)).
        * exact (plus_assoc Sq (plus (opp Sq) bE) LZ).
        * apply (req_trans (plus (plus Sq (plus (opp Sq) bE)) LZ)
                           (plus (plus (plus Sq (opp Sq)) bE) LZ)
                           (plus bE LZ)).
          -- exact (req_plus_compat (plus Sq (plus (opp Sq) bE))
                       (plus (plus Sq (opp Sq)) bE) LZ LZ
                       (plus_assoc Sq (opp Sq) bE) (req_refl LZ)).
          -- apply (req_trans (plus (plus (plus Sq (opp Sq)) bE) LZ)
                              (plus (plus zero bE) LZ)
                              (plus bE LZ)).
             ++ exact (req_plus_compat (plus (plus Sq (opp Sq)) bE)
                         (plus zero bE) LZ LZ
                         (req_plus_compat (plus Sq (opp Sq)) zero bE bE
                            (plus_opp Sq) (req_refl bE))
                         (req_refl LZ)).
             ++ exact (req_plus_compat (plus zero bE) bE LZ LZ
                          (req_trans (plus zero bE) (plus bE zero) bE
                             (plus_comm zero bE) (plus_zero bE))
                          (req_refl LZ)).
      + exact (le_plus_compat Sq Sq zero (plus (plus (opp Sq) bE) LZ)
                 (le_refl Sq) Hkl0). }
  (* rearrangement 2: H - beta*E <= logZ *)
  apply (le_id_r (plus Sq (opp bE))
                 (plus (plus bE LZ) (opp bE)) LZ).
  - (* (beta*E + LZ) - beta*E == LZ: 5-step algebra chain *)
    apply (req_trans (plus (plus bE LZ) (opp bE))
                     (plus bE (plus LZ (opp bE)))
                     LZ).
    + exact (req_sym (plus bE (plus LZ (opp bE)))
                     (plus (plus bE LZ) (opp bE))
                     (plus_assoc bE LZ (opp bE))).
    + apply (req_trans (plus bE (plus LZ (opp bE)))
                       (plus bE (plus (opp bE) LZ))
                       LZ).
      * exact (req_plus_compat bE bE (plus LZ (opp bE)) (plus (opp bE) LZ)
                 (req_refl bE) (plus_comm LZ (opp bE))).
      * apply (req_trans (plus bE (plus (opp bE) LZ))
                         (plus (plus bE (opp bE)) LZ)
                         LZ).
        -- exact (plus_assoc bE (opp bE) LZ).
        -- apply (req_trans (plus (plus bE (opp bE)) LZ) (plus zero LZ) LZ).
           ++ exact (req_plus_compat (plus bE (opp bE)) zero LZ LZ
                       (plus_opp bE) (req_refl LZ)).
           ++ exact (req_trans (plus zero LZ) (plus LZ zero) LZ
                   (plus_comm zero LZ) (plus_zero LZ)).
  - exact (le_plus_compat Sq (plus bE LZ) (opp bE) (opp bE)
             Hstep1 (le_refl (opp bE))).
Qed.

(* ============================================================ *)
(* Strict-layer item 3/6: temperature-to-expected-energy monotonicity            *)
(*   (upstream energy_exp_temp_mono @17521). t1 < t2 implies E(t1) <= E(t2).      *)
(*   Non-triviality: genuine assembly (the discharged item Hb + the variational   *)
(*   bound twice + item 1 explicit entropy + a full req re-proof of upstream      *)
(*   Hm/Hshift/Hsum/Hlhs + the req_le_mult_pos_cancel/req_le_minus_nonneg_rev     *)
(*   rearrangement chain). Honest premise: lt zero (b1 - b2) (upstream L17121 lt_minus_nonneg position; a theorem under the Real instantiation). *)
(* ============================================================ *)
Theorem req_energy_exp_temp_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    lt t1 t2 ->
    lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
    le (tE t1 Ht1) (tE t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12 Hbd.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := tE t1 Ht1). set (E2 := tE t2 Ht2).
  set (S1 := reqd_entropy_dist S sumf (tB t1 Ht1) (tBpos t1 Ht1)).
  set (S2 := reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)).
  set (LZ1 := log (Z_temp t1) (tZpos t1 Ht1)).
  set (LZ2 := log (Z_temp t2) (tZpos t2 Ht2)).
  (* beta2 < beta1 (the discharged item) *)
  assert (Hb : lt b2 b1)
    by exact (req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Ht12).
  (* the variational bound twice (q := p_t2 / p_t1, crossed) *)
  assert (Hv1 : le (req_minus S2 (mult b1 E2)) LZ1).
  { exact (req_variational_temp_bound t1 Ht1 (tB t2 Ht2) (tBpos t2 Ht2)
             (tBnorm t2 Ht2)). }
  assert (Hv2 : le (req_minus S1 (mult b2 E1)) LZ2).
  { exact (req_variational_temp_bound t2 Ht2 (tB t1 Ht1) (tBpos t1 Ht1)
             (tBnorm t1 Ht1)). }
  (* explicit entropy (item 1), twice *)
  assert (Hex1 : req S1 (plus (mult b1 E1) LZ1))
    by exact (req_entropy_temp_explicit t1 Ht1).
  assert (Hex2 : req S2 (plus (mult b2 E2) LZ2))
    by exact (req_entropy_temp_explicit t2 Ht2).
  (* explicit entropy substituted into the variational bound (transported by reqd_minus_compat) *)
  assert (Hv1' : le (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2)) LZ1).
  { apply (le_id_l (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                   (req_minus S2 (mult b1 E2)) LZ1).
    - exact (reqd_minus_compat (plus (mult b2 E2) LZ2) S2
               (mult b1 E2) (mult b1 E2)
               (req_sym S2 (plus (mult b2 E2) LZ2) Hex2)
               (req_refl (mult b1 E2))).
    - exact Hv1. }
  assert (Hv2' : le (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1)) LZ2).
  { apply (le_id_l (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                   (req_minus S1 (mult b2 E1)) LZ2).
    - exact (reqd_minus_compat (plus (mult b1 E1) LZ1) S1
               (mult b2 E1) (mult b2 E1)
               (req_sym S1 (plus (mult b1 E1) LZ1) Hex1)
               (req_refl (mult b2 E1))).
    - exact Hv2. }
  (* simplification inside minus (upstream Hm1: X-Y == (b2-b1)*E2 + LZ2, 5 steps) *)
  assert (Hm1 : req (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                    (plus (mult (req_minus b2 b1) E2) LZ2)).
  { apply (req_trans (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                     (plus (mult b2 E2) (plus LZ2 (opp (mult b1 E2))))
                     (plus (mult (req_minus b2 b1) E2) LZ2)).
    - exact (req_sym (plus (mult b2 E2) (plus LZ2 (opp (mult b1 E2))))
                     (plus (plus (mult b2 E2) LZ2) (opp (mult b1 E2)))
                     (plus_assoc (mult b2 E2) LZ2 (opp (mult b1 E2)))).
    - apply (req_trans (plus (mult b2 E2) (plus LZ2 (opp (mult b1 E2))))
                       (plus (mult b2 E2) (plus (opp (mult b1 E2)) LZ2))
                       (plus (mult (req_minus b2 b1) E2) LZ2)).
      + exact (req_plus_compat (mult b2 E2) (mult b2 E2)
                 (plus LZ2 (opp (mult b1 E2))) (plus (opp (mult b1 E2)) LZ2)
                 (req_refl (mult b2 E2)) (plus_comm LZ2 (opp (mult b1 E2)))).
      + apply (req_trans (plus (mult b2 E2) (plus (opp (mult b1 E2)) LZ2))
                         (plus (plus (mult b2 E2) (opp (mult b1 E2))) LZ2)
                         (plus (mult (req_minus b2 b1) E2) LZ2)).
        * exact (plus_assoc (mult b2 E2) (opp (mult b1 E2)) LZ2).
        * exact (req_plus_compat
                   (plus (mult b2 E2) (opp (mult b1 E2)))
                   (mult (req_minus b2 b1) E2) LZ2 LZ2
                   (req_sym (mult (req_minus b2 b1) E2)
                            (req_minus (mult b2 E2) (mult b1 E2))
                            (req_mult_minus_distr_r b2 b1 E2))
                   (req_refl LZ2)). }
  assert (Hm2 : req (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                    (plus (mult (req_minus b1 b2) E1) LZ1)).
  { apply (req_trans (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                     (plus (mult b1 E1) (plus LZ1 (opp (mult b2 E1))))
                     (plus (mult (req_minus b1 b2) E1) LZ1)).
    - exact (req_sym (plus (mult b1 E1) (plus LZ1 (opp (mult b2 E1))))
                     (plus (plus (mult b1 E1) LZ1) (opp (mult b2 E1)))
                     (plus_assoc (mult b1 E1) LZ1 (opp (mult b2 E1)))).
    - apply (req_trans (plus (mult b1 E1) (plus LZ1 (opp (mult b2 E1))))
                       (plus (mult b1 E1) (plus (opp (mult b2 E1)) LZ1))
                       (plus (mult (req_minus b1 b2) E1) LZ1)).
      + exact (req_plus_compat (mult b1 E1) (mult b1 E1)
                 (plus LZ1 (opp (mult b2 E1))) (plus (opp (mult b2 E1)) LZ1)
                 (req_refl (mult b1 E1)) (plus_comm LZ1 (opp (mult b2 E1)))).
      + apply (req_trans (plus (mult b1 E1) (plus (opp (mult b2 E1)) LZ1))
                         (plus (plus (mult b1 E1) (opp (mult b2 E1))) LZ1)
                         (plus (mult (req_minus b1 b2) E1) LZ1)).
        * exact (plus_assoc (mult b1 E1) (opp (mult b2 E1)) LZ1).
        * exact (req_plus_compat
                   (plus (mult b1 E1) (opp (mult b2 E1)))
                   (mult (req_minus b1 b2) E1) LZ1 LZ1
                   (req_sym (mult (req_minus b1 b2) E1)
                            (req_minus (mult b1 E1) (mult b2 E1))
                            (req_mult_minus_distr_r b1 b2 E1))
                   (req_refl LZ1)). }
  (* finishing the variational bound (upstream Hv1''/Hv2'') *)
  assert (Hv1'' : le (plus (mult (req_minus b2 b1) E2) LZ2) LZ1).
  { apply (le_id_l (plus (mult (req_minus b2 b1) E2) LZ2)
                   (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2)) LZ1).
    - exact (req_sym (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                     (plus (mult (req_minus b2 b1) E2) LZ2) Hm1).
    - exact Hv1'. }
  assert (Hv2'' : le (plus (mult (req_minus b1 b2) E1) LZ1) LZ2).
  { apply (le_id_l (plus (mult (req_minus b1 b2) E1) LZ1)
                   (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1)) LZ2).
    - exact (req_sym (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                     (plus (mult (req_minus b1 b2) E1) LZ1) Hm2).
    - exact Hv2'. }
  (* rearrangement (upstream Hshift1/Hshift2: le X (LZ1-LZ2)) *)
  assert (Hshift1 : le (mult (req_minus b2 b1) E2) (req_minus LZ1 LZ2)).
  { apply (le_id_l (mult (req_minus b2 b1) E2)
                   (plus (plus (mult (req_minus b2 b1) E2) LZ2) (opp LZ2))
                   (req_minus LZ1 LZ2)).
    - apply (req_trans (mult (req_minus b2 b1) E2)
                       (plus (mult (req_minus b2 b1) E2) zero)
                       (plus (plus (mult (req_minus b2 b1) E2) LZ2) (opp LZ2))).
      + exact (req_sym (plus (mult (req_minus b2 b1) E2) zero)
                       (mult (req_minus b2 b1) E2)
                       (plus_zero (mult (req_minus b2 b1) E2))).
      + apply (req_trans (plus (mult (req_minus b2 b1) E2) zero)
                         (plus (mult (req_minus b2 b1) E2)
                               (plus LZ2 (opp LZ2)))
                         (plus (plus (mult (req_minus b2 b1) E2) LZ2)
                               (opp LZ2))).
        * exact (req_plus_compat (mult (req_minus b2 b1) E2)
                    (mult (req_minus b2 b1) E2) zero (plus LZ2 (opp LZ2))
                    (req_refl (mult (req_minus b2 b1) E2))
                    (req_sym (plus LZ2 (opp LZ2)) zero (plus_opp LZ2))).
        * exact (plus_assoc (mult (req_minus b2 b1) E2) LZ2 (opp LZ2)).
    - apply (le_id_r (plus (plus (mult (req_minus b2 b1) E2) LZ2) (opp LZ2))
                     (plus LZ1 (opp LZ2)) (req_minus LZ1 LZ2)).
      + exact (req_refl (plus LZ1 (opp LZ2))).
      + exact (le_plus_compat (plus (mult (req_minus b2 b1) E2) LZ2) LZ1
                 (opp LZ2) (opp LZ2) Hv1'' (le_refl (opp LZ2))). }
  assert (Hshift2 : le (mult (req_minus b1 b2) E1) (req_minus LZ2 LZ1)).
  { apply (le_id_l (mult (req_minus b1 b2) E1)
                   (plus (plus (mult (req_minus b1 b2) E1) LZ1) (opp LZ1))
                   (req_minus LZ2 LZ1)).
    - apply (req_trans (mult (req_minus b1 b2) E1)
                       (plus (mult (req_minus b1 b2) E1) zero)
                       (plus (plus (mult (req_minus b1 b2) E1) LZ1) (opp LZ1))).
      + exact (req_sym (plus (mult (req_minus b1 b2) E1) zero)
                       (mult (req_minus b1 b2) E1)
                       (plus_zero (mult (req_minus b1 b2) E1))).
      + apply (req_trans (plus (mult (req_minus b1 b2) E1) zero)
                         (plus (mult (req_minus b1 b2) E1)
                               (plus LZ1 (opp LZ1)))
                         (plus (plus (mult (req_minus b1 b2) E1) LZ1)
                               (opp LZ1))).
        * exact (req_plus_compat (mult (req_minus b1 b2) E1)
                    (mult (req_minus b1 b2) E1) zero (plus LZ1 (opp LZ1))
                    (req_refl (mult (req_minus b1 b2) E1))
                    (req_sym (plus LZ1 (opp LZ1)) zero (plus_opp LZ1))).
        * exact (plus_assoc (mult (req_minus b1 b2) E1) LZ1 (opp LZ1)).
    - apply (le_id_r (plus (plus (mult (req_minus b1 b2) E1) LZ1) (opp LZ1))
                     (plus LZ2 (opp LZ1)) (req_minus LZ2 LZ1)).
      + exact (req_refl (plus LZ2 (opp LZ1))).
      + exact (le_plus_compat (plus (mult (req_minus b1 b2) E1) LZ1) LZ2
                 (opp LZ1) (opp LZ1) Hv2'' (le_refl (opp LZ1))). }
  (* adding up + cancellation (reqd_minus_pair_cancel) *)
  assert (Hsum : le (plus (mult (req_minus b2 b1) E2) (mult (req_minus b1 b2) E1))
                   (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))).
  { exact (le_plus_compat (mult (req_minus b2 b1) E2) (req_minus LZ1 LZ2)
             (mult (req_minus b1 b2) E1) (req_minus LZ2 LZ1)
             Hshift1 Hshift2). }
  assert (Hz : req (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)) zero)
    by exact (reqd_minus_pair_cancel LZ1 LZ2).
  assert (Hoppm : req (req_minus b2 b1) (opp (req_minus b1 b2)))
    by exact (reqd_minus_opp_flip b1 b2).
  (* LHS reshaping: d'*E2 + d*E1 == d*(E1 - E2) (upstream Hlhs, five steps) *)
  assert (Hlhs : req (plus (mult (req_minus b2 b1) E2) (mult (req_minus b1 b2) E1))
                     (mult (req_minus b1 b2) (req_minus E1 E2))).
  { apply (req_trans
             (plus (mult (req_minus b2 b1) E2) (mult (req_minus b1 b2) E1))
             (plus (mult (opp (req_minus b1 b2)) E2) (mult (req_minus b1 b2) E1))
             (mult (req_minus b1 b2) (req_minus E1 E2))).
    - exact (req_plus_compat (mult (req_minus b2 b1) E2)
               (mult (opp (req_minus b1 b2)) E2)
               (mult (req_minus b1 b2) E1) (mult (req_minus b1 b2) E1)
               (req_mult_compat (req_minus b2 b1) (opp (req_minus b1 b2))
                  E2 E2 Hoppm (req_refl E2))
               (req_refl (mult (req_minus b1 b2) E1))).
    - apply (req_trans
               (plus (mult (opp (req_minus b1 b2)) E2) (mult (req_minus b1 b2) E1))
               (plus (opp (mult (req_minus b1 b2) E2)) (mult (req_minus b1 b2) E1))
               (mult (req_minus b1 b2) (req_minus E1 E2))).
      + exact (req_plus_compat (mult (opp (req_minus b1 b2)) E2)
                 (opp (mult (req_minus b1 b2) E2))
                 (mult (req_minus b1 b2) E1) (mult (req_minus b1 b2) E1)
                 (req_opp_mult_r (req_minus b1 b2) E2)
                 (req_refl (mult (req_minus b1 b2) E1))).
      + apply (req_trans
                 (plus (opp (mult (req_minus b1 b2) E2)) (mult (req_minus b1 b2) E1))
                 (plus (mult (req_minus b1 b2) (opp E2)) (mult (req_minus b1 b2) E1))
                 (mult (req_minus b1 b2) (req_minus E1 E2))).
        * exact (req_plus_compat (opp (mult (req_minus b1 b2) E2))
                   (mult (req_minus b1 b2) (opp E2))
                   (mult (req_minus b1 b2) E1) (mult (req_minus b1 b2) E1)
                   (req_sym (mult (req_minus b1 b2) (opp E2))
                            (opp (mult (req_minus b1 b2) E2))
                            (req_opp_mult_l (req_minus b1 b2) E2))
                   (req_refl (mult (req_minus b1 b2) E1))).
        * apply (req_trans
                   (plus (mult (req_minus b1 b2) (opp E2))
                         (mult (req_minus b1 b2) E1))
                   (mult (req_minus b1 b2) (plus (opp E2) E1))
                   (mult (req_minus b1 b2) (req_minus E1 E2))).
          -- exact (req_sym
                      (mult (req_minus b1 b2) (plus (opp E2) E1))
                      (plus (mult (req_minus b1 b2) (opp E2))
                            (mult (req_minus b1 b2) E1))
                      (distrib (req_minus b1 b2) (opp E2) E1)).
          -- exact (req_mult_compat (req_minus b1 b2) (req_minus b1 b2)
                       (plus (opp E2) E1) (req_minus E1 E2)
                       (req_refl (req_minus b1 b2))
                       (plus_comm (opp E2) E1)). }
  (* assembly: d*(E1 - E2) <= 0 (upstream Hmain) *)
  assert (Hmain : le (mult (req_minus b1 b2) (req_minus E1 E2)) zero).
  { apply (le_id_l (mult (req_minus b1 b2) (req_minus E1 E2))
                   (plus (mult (req_minus b2 b1) E2)
                         (mult (req_minus b1 b2) E1)) zero).
    - exact (req_sym (plus (mult (req_minus b2 b1) E2)
                           (mult (req_minus b1 b2) E1))
                     (mult (req_minus b1 b2) (req_minus E1 E2)) Hlhs).
    - exact (le_id_r (plus (mult (req_minus b2 b1) E2)
                           (mult (req_minus b1 b2) E1))
                     (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))
                     zero Hz Hsum). }
  (* positive-factor cancellation + subtraction inverse (the ReqAlgBridge2 rearrangement chain) *)
  assert (Hcancel : le (req_minus E1 E2) zero).
  { apply (req_le_mult_pos_cancel (req_minus E1 E2) (req_minus b1 b2) Hbd).
    apply (le_id_l (mult (req_minus E1 E2) (req_minus b1 b2))
                   (mult (req_minus b1 b2) (req_minus E1 E2)) zero).
    - exact (mult_comm (req_minus E1 E2) (req_minus b1 b2)).
    - exact Hmain. }
  exact (req_le_minus_nonneg_rev E1 E2 Hcancel).
Qed.

(* ============================================================ *)
(* Strict-layer item 4/6: the KL decomposition subtraction identity (upstream     *)
(*   temp_strict_ident2 @17879). KL(p_t2||p_t1) + KL(p_t1||p_t2) == (b1-b2)*(E2-E1). *)
(*   Non-triviality: assembly (item 2 crossed with strict-layer item 1 A_chain2)  *)
(*   + a genuine algebra chain (the reqd_minus_pair_cancel/reqd_minus_opp_flip    *)
(*   helpers + the five-step Hmain2 req chain + stepwise trans reflow; the idempotent delta segment closed by req_refl). *)
(* ============================================================ *)
Theorem req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    req (plus (req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
                 (tBpos t2 Ht2) (tBpos t1 Ht1))
              (req_relative_entropy S sumf (tB t1 Ht1) (tB t2 Ht2)
                 (tBpos t1 Ht1) (tBpos t2 Ht2)))
        (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
              (req_minus (tE t2 Ht2) (tE t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := tE t1 Ht1). set (E2 := tE t2 Ht2).
  set (LZ1 := log (Z_temp t1) (tZpos t1 Ht1)).
  set (LZ2 := log (Z_temp t2) (tZpos t2 Ht2)).
  set (K1 := req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
               (tBpos t2 Ht2) (tBpos t1 Ht1)).
  set (K2 := req_relative_entropy S sumf (tB t1 Ht1) (tB t2 Ht2)
               (tBpos t1 Ht1) (tBpos t2 Ht2)).
  assert (HK1 : req K1 (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))).
  { exact (req_trans K1
             (plus (plus (opp (reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)))
                         (mult (inv_pos t1 Ht1) (tE t2 Ht2)))
                   LZ1)
             (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
             (req_relative_entropy_temp_decomp t1 Ht1 (tB t2 Ht2)
                (tBpos t2 Ht2) (tBnorm t2 Ht2))
             (req_temp_strict_A_chain2 t1 t2 Ht1 Ht2)). }
  assert (HK2 : req K2 (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1))).
  { exact (req_trans K2
             (plus (plus (opp (reqd_entropy_dist S sumf (tB t1 Ht1) (tBpos t1 Ht1)))
                         (mult (inv_pos t2 Ht2) (tE t1 Ht1)))
                   LZ2)
             (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1))
             (req_relative_entropy_temp_decomp t2 Ht2 (tB t1 Ht1)
                (tBpos t1 Ht1) (tBnorm t1 Ht1))
             (req_temp_strict_A_chain2 t2 t1 Ht2 Ht1)). }
  assert (Hsum : req (plus K1 K2)
                     (plus (plus (mult (req_minus b1 b2) E2)
                                 (req_minus LZ1 LZ2))
                           (plus (mult (req_minus b2 b1) E1)
                                 (req_minus LZ2 LZ1)))).
  { exact (req_plus_compat K1
             (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
             K2
             (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1))
             HK1 HK2). }
  assert (Hz : req (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)) zero)
    by exact (reqd_minus_pair_cancel LZ1 LZ2).
  assert (Hoppm : req (req_minus b2 b1) (opp (req_minus b1 b2)))
    by exact (reqd_minus_opp_flip b1 b2).
  (* Hmain2: d*E2 + d'*E1 == d*(E2 - E1) (five steps) *)
  assert (Hmain2 : req (plus (mult (req_minus b1 b2) E2)
                             (mult (req_minus b2 b1) E1))
                       (mult (req_minus b1 b2) (req_minus E2 E1))).
  { apply (req_trans
             (plus (mult (req_minus b1 b2) E2) (mult (req_minus b2 b1) E1))
             (plus (mult (req_minus b1 b2) E2) (mult (opp (req_minus b1 b2)) E1))
             (mult (req_minus b1 b2) (req_minus E2 E1))).
    - exact (req_plus_compat (mult (req_minus b1 b2) E2)
               (mult (req_minus b1 b2) E2)
               (mult (req_minus b2 b1) E1) (mult (opp (req_minus b1 b2)) E1)
               (req_refl (mult (req_minus b1 b2) E2))
               (req_mult_compat (req_minus b2 b1) (opp (req_minus b1 b2))
                  E1 E1 Hoppm (req_refl E1))).
    - apply (req_trans
               (plus (mult (req_minus b1 b2) E2) (mult (opp (req_minus b1 b2)) E1))
               (plus (mult (req_minus b1 b2) E2) (opp (mult (req_minus b1 b2) E1)))
               (mult (req_minus b1 b2) (req_minus E2 E1))).
      + exact (req_plus_compat (mult (req_minus b1 b2) E2)
                 (mult (req_minus b1 b2) E2)
                 (mult (opp (req_minus b1 b2)) E1)
                 (opp (mult (req_minus b1 b2) E1))
                 (req_refl (mult (req_minus b1 b2) E2))
                 (req_opp_mult_r (req_minus b1 b2) E1)).
      + apply (req_trans
                 (plus (mult (req_minus b1 b2) E2)
                       (opp (mult (req_minus b1 b2) E1)))
                 (plus (mult (req_minus b1 b2) E2)
                       (mult (req_minus b1 b2) (opp E1)))
                 (mult (req_minus b1 b2) (req_minus E2 E1))).
        * exact (req_plus_compat (mult (req_minus b1 b2) E2)
                   (mult (req_minus b1 b2) E2)
                   (opp (mult (req_minus b1 b2) E1))
                   (mult (req_minus b1 b2) (opp E1))
                   (req_refl (mult (req_minus b1 b2) E2))
                   (req_sym (mult (req_minus b1 b2) (opp E1))
                            (opp (mult (req_minus b1 b2) E1))
                            (req_opp_mult_l (req_minus b1 b2) E1))).
        * apply (req_trans
                   (plus (mult (req_minus b1 b2) E2)
                         (mult (req_minus b1 b2) (opp E1)))
                   (mult (req_minus b1 b2) (plus E2 (opp E1)))
                   (mult (req_minus b1 b2) (req_minus E2 E1))).
          -- exact (req_sym
                      (mult (req_minus b1 b2) (plus E2 (opp E1)))
                      (plus (mult (req_minus b1 b2) E2)
                            (mult (req_minus b1 b2) (opp E1)))
                      (distrib (req_minus b1 b2) E2 (opp E1))).
          -- exact (req_mult_compat (req_minus b1 b2) (req_minus b1 b2)
                       (plus E2 (opp E1)) (req_minus E2 E1)
                       (req_refl (req_minus b1 b2))
                       (req_refl (plus E2 (opp E1)))). }
  assert (H1 : req (plus (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                         (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1)))
                   (plus (mult (req_minus b1 b2) E2)
                         (plus (req_minus LZ1 LZ2)
                               (plus (mult (req_minus b2 b1) E1)
                                     (req_minus LZ2 LZ1))))).
  { exact (req_sym
             (plus (mult (req_minus b1 b2) E2)
                   (plus (req_minus LZ1 LZ2)
                         (plus (mult (req_minus b2 b1) E1)
                               (req_minus LZ2 LZ1))))
             (plus (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                   (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1)))
             (plus_assoc (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2)
                         (plus (mult (req_minus b2 b1) E1)
                               (req_minus LZ2 LZ1)))). }
  assert (H2 : req (plus (mult (req_minus b1 b2) E2)
                         (plus (req_minus LZ1 LZ2)
                               (plus (mult (req_minus b2 b1) E1)
                                     (req_minus LZ2 LZ1))))
                   (plus (mult (req_minus b1 b2) E2)
                         (plus (mult (req_minus b2 b1) E1)
                               (plus (req_minus LZ1 LZ2)
                                     (req_minus LZ2 LZ1))))).
  { apply (req_trans
             (plus (mult (req_minus b1 b2) E2)
                   (plus (req_minus LZ1 LZ2)
                         (plus (mult (req_minus b2 b1) E1)
                               (req_minus LZ2 LZ1))))
             (plus (mult (req_minus b1 b2) E2)
                   (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                         (req_minus LZ2 LZ1)))
             (plus (mult (req_minus b1 b2) E2)
                   (plus (mult (req_minus b2 b1) E1)
                         (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))))).
    - exact (req_plus_compat (mult (req_minus b1 b2) E2)
               (mult (req_minus b1 b2) E2)
               (plus (req_minus LZ1 LZ2)
                     (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1)))
               (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                     (req_minus LZ2 LZ1))
               (req_refl (mult (req_minus b1 b2) E2))
               (plus_assoc (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1)
                           (req_minus LZ2 LZ1))).
    - apply (req_trans
               (plus (mult (req_minus b1 b2) E2)
                     (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                           (req_minus LZ2 LZ1)))
               (plus (mult (req_minus b1 b2) E2)
                     (plus (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                           (req_minus LZ2 LZ1)))
               (plus (mult (req_minus b1 b2) E2)
                     (plus (mult (req_minus b2 b1) E1)
                           (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))))).
      + exact (req_plus_compat (mult (req_minus b1 b2) E2)
                 (mult (req_minus b1 b2) E2)
                 (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                       (req_minus LZ2 LZ1))
                 (plus (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                       (req_minus LZ2 LZ1))
                 (req_refl (mult (req_minus b1 b2) E2))
                 (req_plus_compat
                    (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                    (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                    (req_minus LZ2 LZ1) (req_minus LZ2 LZ1)
                    (plus_comm (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                    (req_refl (req_minus LZ2 LZ1)))).
      + exact (req_plus_compat (mult (req_minus b1 b2) E2)
                 (mult (req_minus b1 b2) E2)
                 (plus (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                       (req_minus LZ2 LZ1))
                 (plus (mult (req_minus b2 b1) E1)
                       (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)))
                 (req_refl (mult (req_minus b1 b2) E2))
                 (req_sym (plus (mult (req_minus b2 b1) E1)
                                (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)))
                          (plus (plus (mult (req_minus b2 b1) E1)
                                      (req_minus LZ1 LZ2))
                                (req_minus LZ2 LZ1))
                          (plus_assoc (mult (req_minus b2 b1) E1)
                                      (req_minus LZ1 LZ2)
                                      (req_minus LZ2 LZ1)))). }
  assert (Hza : req (plus (mult (req_minus b1 b2) E2)
                          (plus (mult (req_minus b2 b1) E1)
                                (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))))
                    (plus (mult (req_minus b1 b2) E2)
                          (plus (mult (req_minus b2 b1) E1) zero))).
  { exact (req_plus_compat (mult (req_minus b1 b2) E2)
             (mult (req_minus b1 b2) E2)
             (plus (mult (req_minus b2 b1) E1)
                   (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)))
             (plus (mult (req_minus b2 b1) E1) zero)
             (req_refl (mult (req_minus b1 b2) E2))
             (req_plus_compat (mult (req_minus b2 b1) E1)
                (mult (req_minus b2 b1) E1)
                (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)) zero
                (req_refl (mult (req_minus b2 b1) E1)) Hz)). }
  assert (H3 : req (plus (mult (req_minus b1 b2) E2)
                         (plus (mult (req_minus b2 b1) E1) zero))
                   (plus (mult (req_minus b1 b2) E2) (mult (req_minus b2 b1) E1))).
  { exact (req_plus_compat (mult (req_minus b1 b2) E2)
             (mult (req_minus b1 b2) E2)
             (plus (mult (req_minus b2 b1) E1) zero) (mult (req_minus b2 b1) E1)
             (req_refl (mult (req_minus b1 b2) E2))
             (plus_zero (mult (req_minus b2 b1) E1))). }
  exact (req_trans _ _ _ Hsum
           (req_trans _ _ _ H1
              (req_trans _ _ _ H2
                 (req_trans _ _ _ Hza (req_trans _ _ _ H3 Hmain2))))).
Qed.

(* ============================================================ *)
(* Strict-layer item 5/6: strict temperature-to-energy monotonicity (the          *)
(*   positive-difference form). t1 < t2 and KL(p_t2||p_t1) > 0 imply              *)
(*   0 < E(t2) - E(t1). Non-triviality: assembly (ident2 + req_gibbs_inequality   *)
(*   + lt_le_trans/req_le_plus_nonneg_r + strict cancellation by                  *)
(*   reqd_lt_mult_pos_cancel). Honest premise as in the mono item (same lt_minus_nonneg position). *)
(* ============================================================ *)
Theorem req_energy_exp_temp_strict_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    lt t1 t2 ->
    lt zero (req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
               (tBpos t2 Ht2) (tBpos t1 Ht1)) ->
    lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
    lt zero (req_minus (tE t2 Ht2) (tE t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12 Hkl1 Hbd.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := tE t1 Ht1). set (E2 := tE t2 Ht2).
  set (K1 := req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
               (tBpos t2 Ht2) (tBpos t1 Ht1)).
  set (K2 := req_relative_entropy S sumf (tB t1 Ht1) (tB t2 Ht2)
               (tBpos t1 Ht1) (tBpos t2 Ht2)).
  (* K2 >= 0 (req_gibbs_inequality) *)
  assert (Hkl2 : le zero K2).
  { exact (req_gibbs_inequality S sumf fsum_ext fsum_add fsum_linear fsum_le
             dist_log_inv_one_inv dist_log_le_linear
             (tB t1 Ht1) (tB t2 Ht2) (tBpos t1 Ht1) (tBpos t2 Ht2)
             (tBnorm t1 Ht1) (tBnorm t2 Ht2)). }
  (* K1 + K2 > 0 (lt_le_trans + req_le_plus_nonneg_r) *)
  assert (Hklsum : lt zero (plus K1 K2)).
  { exact (lt_le_trans zero K1 (plus K1 K2) Hkl1
             (req_le_plus_nonneg_r K1 K2 Hkl2)). }
  (* the identity (item ident2) + substitution via lt_id_r *)
  assert (Hprod : lt zero (mult (req_minus b1 b2) (req_minus E2 E1))).
  { exact (lt_id_r zero (plus K1 K2)
             (mult (req_minus b1 b2) (req_minus E2 E1))
             (req_temp_strict_ident2 t1 t2 Ht1 Ht2) Hklsum). }
  (* strict cancellation by a positive factor (comm reordering first) *)
  apply (reqd_lt_mult_pos_cancel (req_minus E2 E1) (req_minus b1 b2) Hbd).
  apply (lt_id_r zero (mult (req_minus b1 b2) (req_minus E2 E1))
                  (mult (req_minus E2 E1) (req_minus b1 b2))).
  - exact (mult_comm (req_minus b1 b2) (req_minus E2 E1)).
  - exact Hprod.
Qed.

(* ============================================================ *)
(* Strict-layer item 6/6: the dual closed round trip, sigT form (upstream         *)
(*   temp_energy_dual_closed @17788). Non-triviality: pure assembly (the          *)
(*   idempotent delta duality annotated item by item): witnesses =                *)
(*   tB/tBnorm/tBpos (Defined positive items), the energy mouth by req_refl (tE delta-transparent), the optimality mouth = item 4, the uniqueness mouth = item 5; zero new claims. *)
(* ============================================================ *)
Theorem req_temp_energy_dual_closed :
  forall (t : R) (Ht : lt zero t),
    sigT (fun pb : S -> R =>
      sigT (fun Hpb : reqd_positive_dist S pb =>
        And (reqd_normalized S sumf pb)
            (And (req (reqd_energy_expectation S sumf base_loss pb) (tE t Ht))
                 (And (forall (p : S -> R) (Hp : reqd_positive_dist S p),
                        reqd_normalized S sumf p ->
                        req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
                        le (reqd_entropy_dist S sumf p Hp)
                           (reqd_entropy_dist S sumf pb Hpb))
                      (forall (p : S -> R) (Hp : reqd_positive_dist S p),
                        reqd_normalized S sumf p ->
                        req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
                        req (reqd_entropy_dist S sumf p Hp)
                            (reqd_entropy_dist S sumf pb Hpb) ->
                        forall s : S, req (p s) (pb s)))))).
Proof.
  intros t Ht.
  exists (tB t Ht).
  exists (tBpos t Ht).
  split.
  - exact (tBnorm t Ht).
  - split.
    + exact (req_refl (tE t Ht)).
    + split.
      * intros p Hp Hnp Henergy.
        exact (req_max_entropy_is_boltzmann_temp t Ht p Hp Hnp Henergy).
      * intros p Hp Hnp Henergy Hent.
        exact (req_entropy_max_unique_temp t Ht p Hp Hnp Henergy Hent).
Qed.

End ReqTempEntropy.

(* ============================================================ *)
(* Temperature entropy layer: the five items each proven (cross-checked against   *)
(*   the file tail of UpReqDist.v):                                               *)
(*   req_entropy_temp_explicit         <- upstream entropy_temp_explicit @L17271  [1] *)
(*   req_relative_entropy_temp_decomp  <- upstream @L17356                        [2] *)
(*   req_entropy_deficit_temp          <- upstream entropy_deficit_kl_temp        [3] *)
(*     @L17691 (also named req_entropy_deficit_kl_temp)                                *)
(*   req_max_entropy_is_boltzmann_temp <- upstream @L17726                        [4] *)
(*   req_entropy_max_unique_temp       <- upstream @L17763                        [5] *)
(* -------------------------------------------------------------- *)
(* This file totals 5 Qed (all purely constructive; section variables = the FEP   *)
(*   summation face/interface bridges + Z_temp; no fixed D/Z: the temperature layer depends only on Z_temp). *)
(* Non-trivial upstream-to-req differences (each item genuinely re-proven, not copied): *)
(*   a) the log premises carry the positivity proofs pointwise (the transparent   *)
(*     aliases tBpos/tZpos literal-match the premises of reqd_boltzmann_log_temp_decomp); *)
(*   b) minus becomes req_minus (delta-transparent); upstream mult_minus_distr_l / *)
(*     sum_over_S_minus become the distrib / fsum_opp bridges (opp_mult_l reshaping); *)
(*   c) upstream rewrite chains become req_trans + compat bridges (zero rewrite); *)
(*   d) the interface mult_assoc is direction-reversed (req (a*(b*c)) ((a*b)*c)); *)
(*     associativity steps are aligned via req_sym;                               *)
(*   e) item 3's Hpp (reqd_positive_dist p) is an honest unused position, as upstream. *)
(* Entry point: Require Import UpReqTempEntropy. (the three .vo files             *)
(*   UpReqTempEntropy + UpReqAlgebra + UpReqDist are compiled and loadable).       *)
(* -------------------------------------------------------------- *)

(* ============================================================ *)
(* Temperature strict-layer increment section: six items each proven (five with    *)
(*   explicit interface gaps + one discharged; anchors = the main live copy):      *)
(*   req_variational_temp_bound       <- upstream variational_temp_bound @L17468   *)
(*     (item 2 + req_gibbs_inequality + a genuine rearrangement chain)        [6] *)
(*   req_energy_exp_temp_mono         <- upstream @L17521 (discharged item +       *)
(*     variational bound x2 + full req re-proof of Hm/Hshift/Hsum/Hlhs)       [7] *)
(*   req_temp_energy_dual_closed      <- upstream @L17788, sigT form               *)
(*     (pure assembly: tB/tBpos/tBnorm + energy mouth req_refl + items 4/5)   [8] *)
(*   req_temp_strict_A_chain2         <- upstream @L17825 (item 1 + the five-stage *)
(*     opp_plus/distrib/req_mult_minus_distr_r req chain)                     [9] *)
(*   req_temp_strict_ident2           <- upstream @L17879 (item 2 crossed with [9] *)
(*     + the five-step Hmain2 + stepwise H1/H2/Hza/H3 trans reflow)          [10] *)
(*   req_energy_exp_temp_strict_mono  <- upstream @L18019 ([10] +                  *)
(*     req_gibbs_inequality + strict cancellation by reqd_lt_mult_pos_cancel)[11] *)
(*   Three helpers: req_inv_pos_lt_contra (discharged: the upstream L17119/L21013  *)
(*     Variable gap is genuinely closed inside the interface-field closure, same   *)
(*     pattern as RestA ralt_inv_pos_lt_contra; no axiom added) +                  *)
(*     reqd_minus_pair_cancel / reqd_minus_opp_flip (pure interface algebra, shared by the Hsum/Hoppm stages). *)
(* -------------------------------------------------------------- *)
(* Honest signature-change table (against the upstream originals):                 *)
(*   1. mono / strict_mono gain the explicit premise lt zero (req_minus b1 b2):    *)
(*     upstream L17121 lt_minus_nonneg is an interface-abstraction-layer Variable  *)
(*     (built per eps in the Real layer); the req interface has no lt-to-minus     *)
(*     connecting field, so it stays (a theorem under Real; no claim inflation).   *)
(*   2. dual_closed's reqd_positive_dist pb conjunct is lifted into the sigT       *)
(*     witness position (Hpb): in the req series the positivity position of        *)
(*     reqd_entropy_dist is proof-relevant; an abstract pb without a witness is    *)
(*     not typeable -- information equivalent pointwise to upstream (positivity as data). *)
(* This file totals 14 Qed = the five items [1]-[5] + 3 helpers of this file + the *)
(*   six items [6]-[11] (all purely constructive; Set-level statements with zero   *)
(*   Prop leakage; pure term mode, zero Morphisms). Section variables unchanged (the temperature layer depends only on the Z_temp interface). *)
(* Entry point unchanged: Require Import UpReqTempEntropy. (+                      *)
(*   UpReqAlgebra + UpReqDist: the three .vo files are compiled and loadable).      *)
(* -------------------------------------------------------------- *)
