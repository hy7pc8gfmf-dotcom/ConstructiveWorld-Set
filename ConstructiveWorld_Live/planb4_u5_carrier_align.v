(** * planb4_u5_carrier_align: the G1 dual-route closing register.

    Mission.  (1) A_j dual-route carrier alignment: the Laurent pole
      readout [nth j (planb4_g1_poleA n) 0] versus the Gaussian pair
      series carrier [piu_zz_Aj n j], eleven bites n = 1..2, j = 0..3n,
      all machine true; n = 2 is the deepest certified multi-sum depth.
      (2) t_n dual-route bites [planb4_tn n] versus
      [zz_phat (planb4_g1_pq n)], n = 1..3: all machine false, so the
      zzm2 pdivmod route is the authoritative polynomial part and the
      witness planb4_pdiv face is superseded.  (3) The legacy aq/bq
      faces are superseded by planb4_g1_ab_def; the machine anchors
      -2392/8000 close the scale question (piu_zz_Aj already in the
      reduced A_j scale).  Machine-printed values sit in the registers.
    Dependencies.  DTPT_a (Set carriers Id/QeqT); planb4_g1_laur_extract
      (poleA/pq); piu_zz_kernel_sum (piu_zz_Aj); zzm1b_linform_bridge
      (zz_phat); planb4_g1_witness (planb4_tn, legacy faces); stdlib
      QArith, ZArith, List.
    References.  ZZ2020 Lemma 3 and Prop 1; planb4_g1_ab_def (A/B
      assembly, exponent -floor(5n/2)+2 pinned by the frozen tables);
      Laurent certification tables zz3_poleA_1..6 / zz3_pq_1..3;
      piu_zz_n1_linform (zz_Mj 8 0 spans 114795 entries: no multi-sum
      bite at n >= 3 is claimed here).
    Constructivity.  All statements carried at the Set layer: true bites
      are the boolean identity carrier QeqT, false bites the boolean
      identity face at false, over transparent Q faces; one computation
      step per anchor; admission-free, postulate-free, zero Prop-carried
      statement face; all closes transparent (Defined).
    Build.  coqc -Q <Set world root> "" planb4_u5_carrier_align.v
      (Rocq 9.3, single lane under cpu_guard v3). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import DTPT_a.
Require Import planb4_g1_laur_extract.
Require Import piu_zz_kernel_sum.
Require Import zzm1b_linform_bridge.
Require Import planb4_g1_witness.

(* ================================================================== *)
(* Section 1. Route law and the A_j dual-route carrier bites.          *)
(* ================================================================== *)

(* Both faces read the coefficient family A_{n,j} of one rational
   function N/D by disjoint routes:
   - planb4_g1_poleA n (planb4_g1_laur_extract) reads
     A_{n,j} = [w^(3n-j)](N(5-w)/(10-w)^(3n+1)) off the Laurent series
     of the zzm2 chain (pdivmod -> pshift -> Laurent); that route is
     table-certified at n = 1..6 (zz3_poleA_1..6) and feeds the
     certified r/s assembly (planb4_g1_rs_assembly).
   - piu_zz_Aj n j = gz_Re (piu_zz_Mj_gz n j) (piu_zz_kernel_sum) sums
     the Gaussian pair series zz_Mj over the six-index term face; it
     feeds the witness S_n assembly (planb4_g1_witness) and carries the
     in-tree certified samples A_{1,1} = 6880, A_{1,2} = -11200,
     A_{2,0} = 37324672 (piu_zz_n1_linform).
   The eleven bites weld the two routes to one coefficient family over
   the whole computable window n <= 2: n = 1 (j = 0..3) and n = 2
   (j = 0..6).  The multi-sum route is the depth bottleneck: the term
   list zz_Mj 8 0 already spans 114795 entries (zz_len_sample_8_0) and
   evaluation beyond n = 2 exceeds the working memory budget, so no
   multi-sum bite at n >= 3 is claimed here.  Machine-printed bite
   values (exact arithmetic; the series side prints unreduced Q,
   e.g. piu_zz_Aj 1 3 = 16000 # 2 = 8000):
   poleA 1 = [-2392; 6880; -11200; 8000];  poleA 2 =
   [37324672; -112234880; 256441600; -431872000; 506880000;
   -371200000; 128000000]. *)

Example planb4_u5_aj_1_0 :
  QeqT (nth 0%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 0%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_1_1 :
  QeqT (nth 1%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 1%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_1_2 :
  QeqT (nth 2%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 2%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_1_3 :
  QeqT (nth 3%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 3%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_2_0 :
  QeqT (nth 0%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 0%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_2_1 :
  QeqT (nth 1%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 1%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_2_2 :
  QeqT (nth 2%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 2%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_2_3 :
  QeqT (nth 3%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 3%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_2_4 :
  QeqT (nth 4%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 4%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_2_5 :
  QeqT (nth 5%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 5%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

Example planb4_u5_aj_2_6 :
  QeqT (nth 6%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 6%nat).
Proof. vm_compute. exact (@id_refl bool true). Defined.

(* ================================================================== *)
(* Section 2. The t_n dual-route bites: machine refutation register.   *)
(* ================================================================== *)

(* The witness t_n face (planb4_tn, built on its own planb4_pdiv long
   division) against the zzm2 certified route zz_phat (planb4_g1_pq n),
   the polynomial-part integral readout of zzm1b_linform_bridge.  All
   three bites come out machine false, so the zzm2 route is the
   authoritative polynomial part and the independent witness long
   division is superseded.  Root cause (machine-printed): planb4_shift
   builds the shifted subtractend as repeat c k ++ map (fun x => c * x) b,
   echoing the quotient coeff c in the k low padding slots where the
   long division needs zeros; the low coefficients are corrupted and
   the leading slot cancels (5 - 5 = 0 at n = 1), so every later step
   reads c = 0 until the fuel burns out.  The quotients collapse to
   the leading coeff alone: planb4_P 1 = [5; 0; ..; 0] (11 entries)
   versus the authoritative planb4_g1_pq 1 = [560; 0; 5]; likewise
   [-5; 0; ..; 0] (21) and [5; 0; ..; 0] (31) at n = 2, 3.  Hence
   planb4_tn 1..3 = 40, -40, 40 exactly (each = 2 * leading *
   Re(int_0) = 8 * leading, with leading = 5*(-1)^(3n+1)), while the
   authoritative side reads zz_phat (planb4_g1_pq n) = 6700 # 6
   (= 3350/3), -89832405120 # 5040 (= -374301688/21),
   12829747424385024000 # 39916800 at n = 1..3 (exact arithmetic).
   The authoritative pq face is table-certified upstream (zz3_pq_1..3)
   and zz_phat is exercised by the certified born-window chain
   zz_r_1..6 (zzm1b_linform_bridge).  This register also explains the
   honest kernel-refuted item on the witness a-composite (composite
   3602 versus frozen A(1) = 22544): the same collapsed quotient feeds
   planb4_a_cleared. *)

Example planb4_u5_tn_dual_red_1 :
  @Id bool (Qeq_bool (planb4_tn 1%nat) (zz_phat (planb4_g1_pq 1%nat)))
           false.
Proof. vm_compute. exact (@id_refl bool false). Defined.

Example planb4_u5_tn_dual_red_2 :
  @Id bool (Qeq_bool (planb4_tn 2%nat) (zz_phat (planb4_g1_pq 2%nat)))
           false.
Proof. vm_compute. exact (@id_refl bool false). Defined.

Example planb4_u5_tn_dual_red_3 :
  @Id bool (Qeq_bool (planb4_tn 3%nat) (zz_phat (planb4_g1_pq 3%nat)))
           false.
Proof. vm_compute. exact (@id_refl bool false). Defined.

(* ================================================================== *)
(* Section 3. Legacy-face disposal register (comment-only).            *)
(* ================================================================== *)

(* (a) Supersession.  The witness aq/bq sub-faces (planb4_aq,
   planb4_bq) are Q-valued carriers of the S-only / A_{n,0}-only
   sub-assemblies: they lack the L_n clearing factor, the (-1)^(n+1)
   sign and the polynomial part t_n, and the witness header formula
   writes the assembly exponent as -floor(5n/2)+1.  That +1 exponent
   form is refuted by the frozen tables at n = 1 and n = 2: it yields
   1/2 * 12 * 5636/3 = 11272 != 22544 = A(1) and
   1/2 * 840 * (-1) * (-3078046528/105) = 1539023264
   != 3078046528 = A(2), while the +2 form 2^(-floor(5n/2)+2) yields
   both table values (pinned in planb4_g1_ab_def, whose born-window
   anchors are green in planb4_g1_ab_def.vo).  Both sub-faces are
   superseded by planb4_g1_ab_def (planb4_abqA, planb4_abqB, projected
   by planb4_g1_A/planb4_g1_B, the total nat -> Z assembly with 36
   verified anchors); the witness aq/bq Definitions stay in place
   upstream as superseded faces, together with the planb4_pdiv face of
   Section 2.

   (b) Scale disposal.  The witness scale note asks for a carrier scale
   factor to be pinned against the oracle faces A_{1,0} = -2392 and
   A_{1,3} = 8000, under the premise that piu_zz_Aj lives in a raw
   M_j-sum scale (the |A| * 2^(4n) erratum route).  The machine anchors
   planb4_A10_anchor and planb4_A13_anchor close by kernel conversion:
   Qeq_bool (piu_zz_Aj 1 0) (-2392 # 1) = true and Qeq_bool
   (piu_zz_Aj 1 3) (8000 # 1) = true, both green in
   planb4_g1_witness.vo, so piu_zz_Aj already lives in the reduced
   A_j scale, the raw-scale premise is refuted, and no carrier rescale
   is due.  The Section 1 bites stand on the same reduced scale: the
   poleA readout and the series carrier agree at all eleven points
   with no intervening factor. *)

(* ================================================================== *)
(* Section 4. Assumption audit.                                        *)
(* ================================================================== *)

Print Assumptions planb4_u5_aj_1_0.
Print Assumptions planb4_u5_aj_1_1.
Print Assumptions planb4_u5_aj_1_2.
Print Assumptions planb4_u5_aj_1_3.
Print Assumptions planb4_u5_aj_2_0.
Print Assumptions planb4_u5_aj_2_1.
Print Assumptions planb4_u5_aj_2_2.
Print Assumptions planb4_u5_aj_2_3.
Print Assumptions planb4_u5_aj_2_4.
Print Assumptions planb4_u5_aj_2_5.
Print Assumptions planb4_u5_aj_2_6.
Print Assumptions planb4_u5_tn_dual_red_1.
Print Assumptions planb4_u5_tn_dual_red_2.
Print Assumptions planb4_u5_tn_dual_red_3.
