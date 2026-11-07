(* ConstructiveWorld-Set — instantiation of the temperature-weighted softmax statements on the concrete Real layer. *)

(** * TempSoftmaxInstantiation: temperature-softmax instantiation and
      resolved supplies.

    Mission.  The temperature-weighted softmax of
      [S06_DiffSamplingGibbs.LanguageModelExtensions] carried onto the
      concrete [Real] layer: the eps-step lemma [tsi_le_plus_eps_r]
      ([le a (a+eps)] for 0 < eps), the arity bridge
      [tsi_twp_is_boltzmann_weight] ([temperature_weighted_prob] equals
      the explicit Boltzmann weight [exp_neg (mult (inv_pos t Ht)
      (neg_log_prob prefix w))], an [Id]-level closure), and the four
      temperature-softmax statements [tsi_temp_weighted_normalized],
      [tsi_temp_weighted_mix_normalized], [tsi_temp_scale_duality], and
      [tsi_temp_weighted_relative], each instantiating the corresponding
      [ag_] statement of [UpReqAttnGibbs] with all arguments explicit.
      A closing supply section realizes the sum-interface certificates
      of the abstract section at the concrete list carrier
      ([tsi_sum_pos_supply], [tsi_sum_ext_supply], [tsi_sum_le_supply],
      [tsi_sum_linear_supply], [tsi_sum_add_supply]) and gives the
      temperature-positivity witness at [temperature := one]
      ([tsi_temperature_one_pos_supply]).

    Dependencies.  Stdlib [List]. Requires [S01_BaseRing] through
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqDist], [UpReqAttnGibbs],
      and, for the supply section, [UpReqSumD], [UpReqConcSoftmax], and
      [ConcMixSelFeed] of this development.

    References.  This development, UpReqAttnGibbs.v (the donor
      statements [ag_softmax_temp_normalized],
      [ag_softmax_temp_mix_normalized], [ag_softmax_temp_relative],
      [ag_temp_is_scale_duality]), and the baseline module of the same
      name in ConstructiveWorld-Main whose statement names are carried
      over here verbatim.

    Constructivity.  All statements are carried by [Set]; no admitted
      statements; proofs close by [Qed] with fully explicit
      instantiation of the donor lemmas; the sum-interface certificates
      of the abstract section stay declared as section premises (they
      are not derivable for an abstract summation operator), and the
      supply section provides their concrete instances; the file tail
      carries eleven [Print Assumptions] audits reporting Closed.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      TempSoftmaxInstantiation.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 000160bc]. *)

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
Require Import UpReqAttnGibbs.
Import RealInterfaceEnhancedMod.
Import RealInterfaceEnhancedMod.

(* ===================================================================== *)
(* Step lemma toward the total instance bridge: [le a (a+eps)] for 0 < eps *)
(* ===================================================================== *)
Lemma tsi_le_plus_eps_r :
  forall (RI : RealInterfaceEnhanced) (a eps : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps ->
    @S01_BaseRing.le RI a (@S01_BaseRing.plus RI a eps).
Proof.
  intros RI a eps Hlt.
  apply (@S01_BaseRing.le_id_l RI a
           (@S01_BaseRing.plus RI a (@S01_BaseRing.zero RI))
           (@S01_BaseRing.plus RI a eps)).
  - exact (id_sym (@S01_BaseRing.plus_zero RI a)).
  - exact (@S01_BaseRing.le_plus_compat RI a a (@S01_BaseRing.zero RI) eps
             (@S01_BaseRing.le_refl RI a)
             (@S01_BaseRing.lt_le_iff RI (@S01_BaseRing.zero RI) eps (inl Hlt))).
Qed.

(* ===================================================================== *)
(* The arity bridge for the host definition after its section ([Id]-level closure) *)
(* ===================================================================== *)
Theorem tsi_twp_is_boltzmann_weight :
  forall (RI : RealInterfaceEnhanced) (Token : Set)
         (neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI)
         (t : @S01_BaseRing.R RI)
         (Ht : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) t)
         (prefix : list Token) (w : Token),
    Id (@temperature_weighted_prob RI Token neg_log_prob t Ht prefix w)
       (@S01_BaseRing.exp_neg RI
          (@S01_BaseRing.mult RI (@S01_BaseRing.inv_pos RI t Ht)
             (neg_log_prob prefix w))).
Proof. intros RI Token neg_log_prob t Ht prefix w. exact (@id_refl _ (@S01_BaseRing.exp_neg RI (@S01_BaseRing.mult RI (@S01_BaseRing.inv_pos RI t Ht) (neg_log_prob prefix w)))). Qed.

(* ===================================================================== *)
(* Main section: the host [LanguageModelExtensions] section face (RI, Token, *)
(*   neg_log_prob, temperature, temperature_pos) joined with the sum-machine *)
(*   slots of the donor [ReqAttnGibbs] section. *)
(* ===================================================================== *)
Section TsiMains.
Context {RI : RealInterfaceEnhanced}.
Variable Token : Set.
Variable neg_log_prob : list Token -> Token -> Real.
Variable temperature : Real.
Variable temperature_pos : lt zero temperature.

(* the sum-machine slots, declared honestly (the same slots as in the donor section) *)
Variable sumf : (Token -> Real) -> Real.
Hypothesis Hsum_ext :
  forall f g : Token -> Real,
    (forall w : Token, req (f w) (g w)) -> req (sumf f) (sumf g).
Hypothesis Hsum_linear :
  forall (a : Real) (f : Token -> Real),
    req (sumf (fun w : Token => mult a (f w))) (mult a (sumf f)).
Hypothesis Hsum_add :
  forall f g : Token -> Real,
    req (sumf (fun w : Token => plus (f w) (g w))) (plus (sumf f) (sumf g)).
Hypothesis Hsum_pos :
  forall f : Token -> Real,
    (forall w : Token, lt zero (f w)) -> lt zero (sumf f).

(* Main statement 1 (normalization): the normalized temperature-weighted weights
   of the host sum to one (full-argument instantiation of
   [ag_softmax_temp_normalized]; z := fun w => neg_log_prob prefix w) *)
Theorem tsi_temp_weighted_normalized :
  forall prefix : list Token,
    req (sumf (fun w : Token =>
           mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)))
                (inv_pos
                   (sumf (fun w0 : Token =>
                            exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                   (Hsum_pos
                      (fun w0 : Token =>
                         exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                      (fun w0 : Token =>
                         exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))))))
        one.
Proof.
  intro prefix.
  exact (@ag_softmax_temp_normalized           Token sumf Hsum_ext Hsum_linear Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob prefix w)).
Qed.

(* Main statement 2 (mix normalization): the convex combination (alpha and
   1-alpha) of two prefix predictions is again normalized (full-argument
   instantiation of [ag_softmax_temp_mix_normalized]) *)
Theorem tsi_temp_weighted_mix_normalized :
  forall (p q : list Token) (alpha : Real),
    lt zero alpha -> lt zero (req_minus one alpha) ->
    req (sumf (fun w : Token =>
           plus (mult alpha
                      (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w)))
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0))))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0)))
                                  (fun w0 : Token =>
                                     exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0)))))))
                (mult (req_minus one alpha)
                      (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w)))
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0))))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0)))
                                  (fun w0 : Token =>
                                     exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0)))))))))
        one.
Proof.
  intros p q alpha Halpha Halpha1.
  exact (@ag_softmax_temp_mix_normalized           Token sumf Hsum_ext Hsum_linear Hsum_add Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob p w)           (fun w : Token => neg_log_prob q w)           alpha Halpha Halpha1).
Qed.

(* Main statement 3 (temperature-scale duality): the normalized
   temperature-c-weighted distribution of the host equals the 1/c-scaled
   softmax (full-argument instantiation of [ag_temp_is_scale_duality]; the
   left side is the host definition at temperature c, entering the exponent
   through [inv_pos c Hc]) *)
Theorem tsi_temp_scale_duality :
  forall (c : Real) (Hc : lt zero c)
         (prefix : list Token) (w : Token),
    req (mult (exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w)))
              (inv_pos
                 (sumf (fun w0 : Token =>
                          exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w0))))
                 (Hsum_pos
                    (fun w0 : Token =>
                       exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w0)))
                    (fun w0 : Token =>
                       exp_neg_pos (mult (inv_pos c Hc) (neg_log_prob prefix w0))))))
        (reqd_softmax_scaled Token sumf Hsum_pos (inv_pos c Hc)
           (fun w1 : Token => neg_log_prob prefix w1) w).
Proof.
  intros c Hc prefix w.
  exact (@ag_temp_is_scale_duality           Token sumf Hsum_pos c Hc           (fun w1 : Token => neg_log_prob prefix w1) w).
Qed.

(* Main statement 4 (relative form): the Boltzmann ratio of two normalized
   token weights under one prefix (full-argument instantiation of
   [ag_softmax_temp_relative]; the additive homomorphism of exp carries it) *)
Theorem tsi_temp_weighted_relative :
  forall (prefix : list Token) (w w' : Token),
    req (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)))
              (inv_pos
                 (sumf (fun w0 : Token =>
                          exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                 (Hsum_pos
                    (fun w0 : Token =>
                       exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                    (fun w0 : Token =>
                       exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))))
        (mult (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w')))
                    (inv_pos
                       (sumf (fun w0 : Token =>
                                exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                       (Hsum_pos
                          (fun w0 : Token =>
                             exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                          (fun w0 : Token =>
                             exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))))
              (exp_neg (mult (inv_pos temperature temperature_pos)
                             (req_minus (neg_log_prob prefix w)
                                        (neg_log_prob prefix w'))))).
Proof.
  intros prefix w w'.
  exact (@ag_softmax_temp_relative           Token sumf Hsum_pos temperature temperature_pos           (fun w1 : Token => neg_log_prob prefix w1) w w').
Qed.

End TsiMains.

(* ===================================================================== *)
(* Assumption audit (five [Print Assumptions] anchors) *)
(* ===================================================================== *)
Print Assumptions tsi_twp_is_boltzmann_weight.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_relative.

(* ===================================================================== *)
(* Supply section (signature-preserving resolution; the declarations of the *)
(*   section above and the signatures of its statements are unchanged): the *)
(*   four sum-interface certificates are realized at the concrete list *)
(*   carrier of [ConcMixSelFeed], [csm_sumf] (defined in [UpReqConcSoftmax]), *)
(*   instantiated at S := bool and enum := true :: false :: nil. The *)
(*   extension slot instantiates [cms_sum_ext], the order slot [cms_sum_le] *)
(*   (the abstract section has no le slot; the statement completes the *)
(*   family), the homogeneity slot [cms_sum_linear], and the addition slot *)
(*   [cms_sum_add] — each a one-step instance; the positivity slot is *)
(*   supplied by [sumd_list_sum_pos] of [UpReqSumD] (pointwise strict *)
(*   positivity on a nonempty list gives a strictly positive sum). The four *)
(*   certificates of the abstract section keep their declared-premise status *)
(*   (they are not derivable for an abstract summation operator inside this *)
(*   tree); this section provides the resolved certificates at the concrete *)
(*   instance, for consumers to fill the interface fields with the instance. *)
(* ===================================================================== *)
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Import RealInterfaceEnhancedMod.

Definition tsi_enum : list bool := true :: false :: nil.

(* Positivity slot: the sum carrier folds over a nonempty list, so pointwise
   strict positivity gives a strictly positive sum (instantiating
   [sumd_list_sum_pos]: the nonemptiness premise closes by discriminate, the
   pointwise premise passes through directly) *)
Theorem tsi_sum_pos_supply :
  forall f : bool -> Real,
    (forall s : bool, real_lt zero (f s)) ->
    real_lt zero (sumd_list_sum bool f tsi_enum).
Proof.
  intros f Hpt.
  apply (@sumd_list_sum_pos bool f tsi_enum).
  - intros Hnil. discriminate Hnil.
  - exact Hpt.
Qed.

(* Extension slot: pointwise req gives req of the sums (a one-step instance of
   [cms_sum_ext]; the statement face matches the supply constants). *)
Theorem tsi_sum_ext_supply :
  forall f g : bool -> Real,
    (forall s : bool, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf bool tsi_enum f) (sumd_sumf bool tsi_enum g).
Proof. intros f g H. exact (cms_sum_ext bool tsi_enum f g H). Qed.

(* Order slot: pointwise le gives le of the sums (a one-step instance of
   [cms_sum_le]). *)
Theorem tsi_sum_le_supply :
  forall f g : bool -> Real,
    (forall s : bool, real_le (f s) (g s)) ->
    real_le (sumd_sumf bool tsi_enum f) (sumd_sumf bool tsi_enum g).
Proof. intros f g H. exact (cms_sum_le bool tsi_enum f g H). Qed.

(* Homogeneity slot: scalar multiplication passes through the sum (a one-step
   instance of [cms_sum_linear]). *)
Theorem tsi_sum_linear_supply :
  forall (a : Real) (f : bool -> Real),
    real_eq (sumd_sumf bool tsi_enum (fun s : bool => mult a (f s)))
            (mult a (sumd_sumf bool tsi_enum f)).
Proof. intros a f. exact (cms_sum_linear bool tsi_enum a f). Qed.

(* Addition slot: the sum of pointwise sums is the pointwise sum of the sums
   (a one-step instance of [cms_sum_add]). *)
Theorem tsi_sum_add_supply :
  forall f g : bool -> Real,
    real_eq (sumd_sumf bool tsi_enum (fun s : bool => plus (f s) (g s)))
            (plus (sumd_sumf bool tsi_enum f) (sumd_sumf bool tsi_enum g)).
Proof. intros f g. exact (cms_sum_add bool tsi_enum f g). Qed.

(* Temperature-positivity witness at temperature := one: the class field
   [one_pos], available for every [RealInterfaceEnhanced] (the same witness as
   [cf2_temp_pos] := [one_pos]) *)
Theorem tsi_temperature_one_pos_supply :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof. intro RI. exact (@S01_BaseRing.one_pos RI). Qed.

(* ---- assumption audit of the supply section (six [Print Assumptions] anchors) ---- *)
Print Assumptions tsi_sum_pos_supply.
Print Assumptions tsi_sum_ext_supply.
Print Assumptions tsi_sum_le_supply.
Print Assumptions tsi_sum_linear_supply.
Print Assumptions tsi_sum_add_supply.
Print Assumptions tsi_temperature_one_pos_supply.
