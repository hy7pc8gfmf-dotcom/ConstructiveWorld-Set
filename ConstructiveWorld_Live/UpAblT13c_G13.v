(* ConstructiveWorld-Set -- minimal-instance discharge file for the G13 eviction family. *)

(** * G13 eviction discharge: six slots discharged on two minimal concrete worlds.

    Mission.  Discharges six slot obligations of the G13 eviction family on
      two minimal concrete worlds over the global [Real]: the one-point
      supply world (carrier [unit], sum [uab_unit_sum]; partition
      positivity, evicted partition, row normalization, detailed balance)
      and the two-point carrier [bool] with [uab_t2sum]/[uab_half] at the
      req layer.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [G13_EvictFam] of this development.

    References.  This development, the same-named baseline module in
      ConstructiveWorld-Main; statement names verbatim (statements
      re-faced on the concrete [evq] family of [G13_EvictFam] per the
      binder-shell carrier-ization precedent of this tree).

    Constructivity.  All named statements and fields are carried by [Set]
      over the concrete [Real] carrier (decidable Q-carriers and boolean
      identity carriers); [coqchk] reports [Axioms: none].  Every
      statement face is concrete-carrier, so the module extracts with
      [Obj.magic] = 0 and no erasure.

    Build.  [coqc -native-compiler no -q -Q . "" <module>.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import G13_EvictFam.

Import RealInterfaceEnhancedMod.
(* re-require after the Mod import: G13_EvictFam re-imports the S-chain on
   top of the Mod surface, so the concrete sections below bind the
   Set-carried algebra names (the binding order the two-point section
   has always relied on for a magic-free extraction face) *)
Require Import G13_EvictFam.

(* ======== part one, the one-point supply world (concrete [Real]
  carrier, carrier [unit], sum [uab_unit_sum]) ======== *)

Section UabT13cG13Unit.

Definition uab_unit_sum (f : unit -> Real) : Real := f tt.

(* ---- swap-family core lemma (one-point carrier):
        p(s) * (p(s') * c) == p(s') * (p(s) * c) ---- *)
Lemma uabT13c_swap_unit_gen :
  forall (p : unit -> Real) (c : Real) (s s' : unit),
    req (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros p c s s'.
  (* named witness assembly: the left-associativity witness, then the
  commutation compatibility step (comm and refl as its two premises),
  then the right-associativity inverse, with the middle terms of
  req_trans explicit *)
  pose proof (mult_assoc (p s) (p s') c) as Hassoc_l.
  pose proof (req_mult_compat (mult (p s) (p s')) (mult (p s') (p s)) c c
                (mult_comm (p s) (p s')) (req_refl c)) as Hcomm.
  pose proof (req_sym (mult (p s') (mult (p s) c))
                      (mult (mult (p s') (p s)) c)
                      (mult_assoc (p s') (p s) c)) as Hassoc_r.
  exact (req_trans (mult (p s) (mult (p s') c))
                   (mult (mult (p s) (p s')) c)
                   (mult (p s') (mult (p s) c))
                   Hassoc_l
                   (req_trans (mult (mult (p s) (p s')) c)
                              (mult (mult (p s') (p s)) c)
                              (mult (p s') (mult (p s) c))
                              Hcomm
                              Hassoc_r)).
Qed.

(* ---- slot 1 from G13:61 (partition positivity discharged: the
        one-point sum is the single factor row, [exp_neg_pos]
        substituted directly) ---- *)
Theorem uabT13c_evict61 :
  forall (D : Real) (D_pos : lt zero D) (energy : unit -> Real),
    lt zero (@evq_Z_thermo unit uab_unit_sum D D_pos energy).
Proof.
  intros D D_pos energy.
  unfold evq_Z_thermo, uab_unit_sum, evq_boltzmann_factor.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy tt))).
Qed.

(* ---- slot 4 from G13:87 (evicted-partition positivity: the keep-all
        decision supplies the branch, reducing to slot 1 after the
        one-point sum) ---- *)
Theorem uabT13c_evict87 :
  forall (D : Real) (D_pos : lt zero D) (energy : unit -> Real),
    lt zero (@evq_evicted_partition unit uab_unit_sum D D_pos energy
               (fun _ : unit => unit)
               (fun _ : unit => inl tt : Or unit (Not unit))).
Proof.
  intros D D_pos energy.
  unfold evq_evicted_partition, uab_unit_sum, evq_boltzmann_factor.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy tt))).
Qed.

(* ---- slot 2 from G13:68 (row normalization discharged: the
        constant-one kernel, the one-point sum of a row is the row
        itself, hence one) ---- *)
Theorem uabT13c_evict68 :
  forall s : unit,
    req (uab_unit_sum (fun _ : unit => one)) one.
Proof.
  intro s.
  unfold uab_unit_sum.
  exact (req_refl one).
Qed.

(* ---- slot 3 from G13:71 (detailed balance discharged for the
        source-kernel scaling family t(s,s') = dist(s') * c;
        partition positivity is discharged by slot 1, with no data
        slots; the one-point world is the minimal instance face)
        ---- *)
Theorem uabT13c_evict71 :
  forall (D : Real) (D_pos : lt zero D) (energy : unit -> Real) (c : Real),
    forall s s' : unit,
      req (mult (@evq_boltzmann_dist_attn unit uab_unit_sum D D_pos energy
                   (uabT13c_evict61 D D_pos energy) s)
                (mult (@evq_boltzmann_dist_attn unit uab_unit_sum D D_pos energy
                         (uabT13c_evict61 D D_pos energy) s') c))
          (mult (@evq_boltzmann_dist_attn unit uab_unit_sum D D_pos energy
                   (uabT13c_evict61 D D_pos energy) s')
                (mult (@evq_boltzmann_dist_attn unit uab_unit_sum D D_pos energy
                         (uabT13c_evict61 D D_pos energy) s) c)).
Proof.
  intros D D_pos energy c s s'.
  (* controlled unfolding at the definition level: dist_attn unfolds to
  the raw scaled-product family, the req swap lemma is instantiated on
  the bare products (named witnesses), and the unfolded face closes by
  conversion *)
  unfold evq_boltzmann_dist_attn.
  pose proof (uabT13c_swap_unit_gen
                (fun x : unit =>
                   mult (inv_pos
                           (@evq_Z_thermo unit uab_unit_sum D D_pos energy)
                           (uabT13c_evict61 D D_pos energy))
                        (@evq_boltzmann_factor unit D D_pos energy
                           x))
                c s s') as Hswap.
  exact Hswap.
Qed.

End UabT13cG13Unit.

(* ======== part two, the req layer: the two-point supply world
  (concrete [Real] carrier, no bridges, no data slots) ======== *)

Section UabT13cG13Req.

Definition uab_t2sum (f : bool -> Real) : Real := plus (f true) (f false).

Definition uab_half : Real :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* ---- swap-family core lemma (req layer, two-point carrier) ---- *)
Lemma uabT13c_swap_req_gen :
  forall (p : bool -> Real) (c : Real) (s s' : bool),
    req (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros p c s s'.
  (* named witness assembly: left associativity, then the commutation
  compatibility step (comm and refl as its two premises), then the
  right associativity inverse, with the middle terms of req_trans
  explicit *)
  pose proof (mult_assoc (p s) (p s') c) as Hassoc_l.
  pose proof (req_mult_compat (mult (p s) (p s')) (mult (p s') (p s)) c c
                (mult_comm (p s) (p s')) (req_refl c)) as Hcomm.
  pose proof (req_sym (mult (p s') (mult (p s) c))
                      (mult (mult (p s') (p s)) c)
                      (mult_assoc (p s') (p s) c)) as Hassoc_r.
  exact (req_trans (mult (p s) (mult (p s') c))
                   (mult (mult (p s) (p s')) c)
                   (mult (p s') (mult (p s) c))
                   Hassoc_l
                   (req_trans (mult (mult (p s) (p s')) c)
                              (mult (mult (p s') (p s)) c)
                              (mult (p s') (mult (p s) c))
                              Hcomm
                              Hassoc_r)).
Qed.

(* the two-point row-normalization algebraic core: half + half == one *)
Lemma uabT13c_half_row : req (plus uab_half uab_half) one.
Proof.
  unfold uab_half.
  assert (H1 : req (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                   (inv_pos (plus one one) (plus_positive one one one_pos one_pos))).
  { exact (req_trans (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))
                     (mult_comm one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult_one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))). }
  assert (HDL : req (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                    (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                          (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))).
  { exact (req_trans (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                     (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                     (mult_comm (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (req_trans (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                                (plus (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one))
                                (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                (distrib (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one one)
                                (req_plus_compat (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one)))). }
  (* named witness assembly: right unit-multiplication normalization
  twice, then positive-sum compatibility, then distributivity over the
  inverse, closing with the inverse-correctness identity; all four
  witnesses are named and the middle terms are explicit *)
  pose proof (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1) as Hone_r.
  pose proof (req_plus_compat (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                Hone_r Hone_r) as Hsum.
  pose proof (req_sym (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                      (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                      HDL) as Hdistr.
  pose proof (inv_pos_correct (plus one one) (plus_positive one one one_pos one_pos))
    as Hinv.
  exact (req_trans
           (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
           (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
           one
           (req_trans
              (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
              (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
              (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
              Hsum
              Hdistr)
           Hinv).
Qed.

(* ---- slot 5 from G13:464 (row normalization discharged: the
        two-point uniform kernel, row sum = half + half = one)
        ---- *)
Theorem uabT13c_evq_norm464 :
  forall s : bool,
    req (uab_t2sum (fun s' : bool => uab_half)) one.
Proof.
  intro s.
  unfold uab_t2sum.
  exact uabT13c_half_row.
Qed.

(* ---- two-point partition positivity (supplies Z_thermo_pos for
        slot 6: pointwise exp_neg_pos plus the two-point positive sum)
        -- *)
Theorem uabT13c_evq_Zpos2 :
  forall (D : Real) (D_pos : lt zero D) (energy : bool -> Real),
    lt zero (@evq_Z_thermo bool uab_t2sum D D_pos energy).
Proof.
  intros D D_pos energy.
  unfold evq_Z_thermo, uab_t2sum, evq_boltzmann_factor.
  exact (plus_positive (exp_neg (mult (inv_pos D D_pos) (energy true)))
                       (exp_neg (mult (inv_pos D D_pos) (energy false)))
                       (exp_neg_pos (mult (inv_pos D D_pos) (energy true)))
                       (exp_neg_pos (mult (inv_pos D D_pos) (energy false)))).
Qed.

(* ---- slot 6 from G13:468 (detailed balance discharged for the
        source-kernel scaling family t(s,s') = dist(s') * c; the
        two-point positive sum discharges partition positivity, with
        no data slots) ---- *)
Theorem uabT13c_evq_db468 :
  forall (D : Real) (D_pos : lt zero D) (energy : bool -> Real) (c : Real),
    forall s s' : bool,
      req (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                   (uabT13c_evq_Zpos2 D D_pos energy) s)
                (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                         (uabT13c_evq_Zpos2 D D_pos energy) s') c))
          (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                   (uabT13c_evq_Zpos2 D D_pos energy) s')
                (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                         (uabT13c_evq_Zpos2 D D_pos energy) s) c)).
Proof.
  intros D D_pos energy c s s'.
  (* controlled unfolding at the definition level: dist_attn unfolds to
  the raw scaled-product family, the req swap lemma is instantiated on
  the bare products (named witnesses), and the unfolded face closes by
  conversion *)
  unfold evq_boltzmann_dist_attn.
  pose proof (uabT13c_swap_req_gen
                (fun x : bool =>
                   mult (inv_pos
                           (@evq_Z_thermo bool uab_t2sum D D_pos energy)
                           (uabT13c_evq_Zpos2 D D_pos energy))
                        (@evq_boltzmann_factor bool D D_pos energy x))
                c s s') as Hswap.
  exact Hswap.
Qed.

End UabT13cG13Req.

(* ---- closing audit ---- *)
Print Assumptions uabT13c_evict61.
Print Assumptions uabT13c_evict87.
Print Assumptions uabT13c_evict68.
Print Assumptions uabT13c_evict71.
Print Assumptions uabT13c_evq_norm464.
Print Assumptions uabT13c_evq_db468.
(* -- supplementary assumption audit for the helper lemmas (all should
   report Closed under the global context) -- *)
Print Assumptions uabT13c_swap_unit_gen.
Print Assumptions uabT13c_swap_req_gen.
Print Assumptions uabT13c_half_row.
