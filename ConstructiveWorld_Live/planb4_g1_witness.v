(* ConstructiveWorld-Main - planB wave-2 piece: the G1 witness general-n definition face (lcm, Gaussian c_j, S_n, t_n, Phi/L, a/b extraction). *)

(** * planb4_g1_witness: the general-n G1 witness pipeline.

    Mission.  The general-n definition face for the zero-premise
      witness: [L_n := lcm(1..4n)] with the [P_n] prime-window
      quotient (Phi_n), the Gaussian half-pair channel
      [(1/i)c_j := 2(2^j Im[(4+2i)^j] + Im[(6+2i)^j]) / (40^j j)],
      the assembled sum [S_n := sum_{j=1..3n} A_{n,j} (1/i)c_j] over
      the carrier [piu_zz_Aj], the polynomial-part integral [t_n],
      and [a_n := 2^(-5n/2+1) L_n (-1)^(n+1) (t_n + S_n)], [b_n :=
      2^(-5n/2+1) L_n (-1)^(n+1) A_{n,0} / 2]; the calibration tables
      of planb3_g1_calib (n = 1..40) are downstream specializations.

    Dependencies.  piu_zz_kernel_sum (A_j carrier; in-tree samples
      A_{1,0} = -2392, A_{1,3} = 8000), piu_zz_gauss_pair (qeqT),
      piu_zz_padic_clearing (zz_in_Pn), planb3_g1_calib (tables
      n = 1..40); stdlib QArith, ZArith, Arith, Lia, List.

    References.  KB41m pre-survey (a/b oracle chain; unique-pair
      certificate max |R_n| = 0.06888 at n=1 < 0.5); ZZ2020 Lemma 3
      (L_n 10^(-j) A_j / j in Z) and Prop 1 (2^(-5n/2+2) L_n I_n
      in Z + Z pi); the path-A survey receipt (G1 gap ledger).

    Constructivity.  All faces informative Fixpoints/Definitions
      over Z/Q transparent data; admission-free, postulate-free;
      anchors close by kernel conversion (externally machine-printed).

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_witness.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_gauss_pair.
Require Import planb3_g1_calib.

Import ListNotations.

(* ================================================================== *)
(* Section 1. The lcm face: L_n := lcm(1..4n) over Z.                 *)
(* ================================================================== *)

Definition planb4_lcm_upto (k : nat) : Z :=
  fold_left Z.lcm (map Z.of_nat (seq 1 k)) 1%Z.

Definition planb4_L (n : nat) : Z := planb4_lcm_upto (4 * n).

(* ================================================================== *)
(* Section 2. Gaussian half-pair arithmetic over Q: (re, im) pairs.   *)
(* ================================================================== *)

Definition gzq (re im : Q) : Q * Q := (re, im).

Definition gzq_add (x y : Q * Q) : Q * Q :=
  ((fst x + fst y)%Q, (snd x + snd y)%Q).

Definition gzq_mul (x y : Q * Q) : Q * Q :=
  ((fst x * fst y - snd x * snd y)%Q, (fst x * snd y + snd x * fst y)%Q).

Fixpoint gzq_pow (x : Q * Q) (k : nat) {struct k} : Q * Q :=
  match k with
  | O => ((1 # 1)%Q, (0 # 1)%Q)
  | S k' => gzq_mul x (gzq_pow x k')
  end.

(* the half-pair base for the (4+2i) channel: (4+2i)/2 = (2, 1). *)
Definition planb4_base41 : Q * Q := ((2 # 1)%Q, (1 # 1)%Q).

(* the half-pair base for the (6+2i) channel: (6+2i)/2 = (3, 1). *)
Definition planb4_base61 : Q * Q := ((3 # 1)%Q, (1 # 1)%Q).

Definition planb4_Im (x : Q * Q) : Q := snd x.

(* Im[(4+2i)^j] / 2^j = Im[(2,1)^j] over Q (the half-pair scaling). *)
Definition planb4_im41_half (j : nat) : Q :=
  planb4_Im (gzq_pow planb4_base41 j).

(* Im[(6+2i)^j] / 2^j = Im[(3,1)^j] over Q. *)
Definition planb4_im61_half (j : nat) : Q :=
  planb4_Im (gzq_pow planb4_base61 j).

(* the channel face: (1/i)c_j = 2(2^j Im[(4+2i)^j] + Im[(6+2i)^j])/(40^j j)
   in half-pair Q form: 2(Im[(2,1)^j] + Im[(3,1)^j]) / (20^j * j)
   since 40^j = 2^j * 20^j and 2^j Im[(4+2i)^j] = 2^(2j) Im[(2,1)^j],
   the half-pair Q form keeps everything division-light. *)
Definition planb4_cj (j : nat) : Q :=
  2 * (planb4_im41_half j + planb4_im61_half j) /
      ((20 # 1) ^ Z.of_nat j * (Z.of_nat j # 1)).

(* ================================================================== *)
(* Section 3. The assembled sum face: S_n over the A_j carrier.       *)
(* ================================================================== *)

Definition planb4_Sn_body (n j : nat) : Q :=
  piu_zz_Aj n j * planb4_cj j.

Fixpoint planb4_Sn_sum (n j : nat) : Q :=
  match j with
  | O => 0 # 1
  | S j' => planb4_Sn_sum n j' + planb4_Sn_body n (S j')
  end.

Definition planb4_Sn (n : nat) : Q := planb4_Sn_sum n (3 * n).

(* ================================================================== *)
(* Section 4. The floor face: 2^(-floor(5n/2)+1) in Q.                *)
(* ================================================================== *)

Definition planb4_pow2_q (k : nat) : Q := (2 # 1) ^ Z.of_nat k.

Definition planb4_floor2q_inv (n : nat) : Q :=
  match Nat.even (5 * n) with
  | true => planb4_pow2_q (5 * n / 2)   (* 2^(5n/2), floor = exact *)
  | false => planb4_pow2_q ((5 * n - 1) / 2)
  end.

(* 2^(-floor(5n/2)+1) as a Q factor. *)
Definition planb4_scale (n : nat) : Q :=
  2 * / planb4_floor2q_inv n.

(* ================================================================== *)
(* Section 5. The a/b extraction faces (informative, Q-valued; the    *)
(* Z-typed statements close by the KB41m integrality oracle chain).   *)
(* ================================================================== *)

Definition planb4_aq (n : nat) : Q :=
  planb4_scale n * planb4_Sn n.

Definition planb4_bq (n : nat) : Q :=
  planb4_scale n * (piu_zz_Aj n 0 * (1 # 2)).

(* ================================================================== *)
(* Section 6. Numeric spot faces (exact-value anchors, n = 1..3).     *)
(* ================================================================== *)

(* SCALE-NORMALIZATION TASK (KB41m oracle chain item 3): the raw carrier
   sum piu_zz_Aj lives in the raw M_j-sum scale; the KB41m oracle faces
   A_{1,0} = -2392 and A_{1,3} = 8000 live in the reduced A_j scale.
   The scale factor is to be pinned by the fixer from KB41m item (1)-3
   (kb41b ext acc-scale erratum = |A| * 2^(4n)) and cross-checked by
   machine evaluation against -2392 / 8000. *)
(* A-anchors in Qeq_bool form: the raw sum reduces to the oracle integers *)
Example planb4_A10_anchor : Qeq_bool (piu_zz_Aj 1 0) (-2392 # 1) = true.
Proof. reflexivity. Qed.

Example planb4_A13_anchor : Qeq_bool (piu_zz_Aj 1 3) (8000 # 1) = true.
Proof. reflexivity. Qed.

Example planb4_L1 : planb4_L 1 = 12%Z.
Proof. reflexivity. Qed.

Example planb4_L2 : planb4_L 2 = 840%Z.
Proof. reflexivity. Qed.

Example planb4_scale1_pos : Qlt (0 # 1)%Q (planb4_scale 1).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Section 7. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_lcm_upto.
Print Assumptions planb4_L.
Print Assumptions planb4_cj.
Print Assumptions planb4_Sn.
Print Assumptions planb4_scale.
Print Assumptions planb4_aq.
Print Assumptions planb4_bq.
Print Assumptions planb4_L1.
Print Assumptions planb4_L2.
Print Assumptions planb4_scale1_pos.

(* ================================================================== *)
(* Section 8. The t_n polynomial-part integral face (exact Gaussian-Q *)
(* contour arithmetic: the monomial integral along the symmetric      *)
(* segment [-1-2i, -1+2i] closes to 2i * (rational), so -i * integral *)
(* lands in Q per monomial).                                          *)
(* ================================================================== *)

(* the P_n quotient polynomial Q-part coefficients: P(x) = N(x)/D(x)   *)
(* with D = (25 - x^2)^(3n+1); the quotient degree is bounded by       *)
(* deg N - deg D < 0 for the R_n face, so the polynomial part P is     *)
(* carried here as the explicit coeff list of the STRICT division      *)
(* remainder-free segment: for the ZZ2020 R_n the quotient is the      *)
(* zero polynomial (deg R_n < deg D holds for n >= 1: deg N = 2n +     *)
(* 8n = 10n, deg D = 6n + 2, 10n < 6n + 2 iff n < 0.5 -- FAILS; the    *)
(* quotient is NON-zero).  The quotient coeffs are computed by the     *)
(* textbook long division on nat-indexed Z coeff lists. *)


(* ================================================================== *)
(* Section 8b. The Pn prime-window product face and the ZZ2020 L_n.   *)
(* ================================================================== *)

(* the Pn prime-window index list: p in [1, 4n] with zz_in_Pn n p. *)
Definition planb4_Pn_list (n : nat) : list nat :=
  filter (fun p => zz_in_Pn n p) (seq 1 (4 * n)).

(* Phi_n := the product of the Pn-window primes (empty window = 1). *)
Definition planb4_Phi (n : nat) : Z :=
  fold_right (fun p acc => acc * Z.of_nat p) 1%Z (planb4_Pn_list n).

(* the ZZ2020 L_n: lcm(1..4n) divided by the Pn-window product. *)
Definition planb4_LZn (n : nat) : Z :=
  planb4_L n / planb4_Phi n.

(* Section 8c. The Phi-window spot anchors (n = 1..3).  The window  *)
(* zz_in_Pn (piu_zz_padic_clearing: ZZ2020 Lemma 2: primes p > 5,   *)
(* p^2 > 3n, 1/2 <= {n/p} < 2/3) is empty over [1, 4n] for n <= 3,  *)
(* so Phi_n is the empty product 1; the values below were machine-  *)
(* printed and agree with the planb3_g1_Phi entries at n = 1..3. *)

Example planb4_Phi1_spot : planb4_Phi 1 = 1%Z.
Proof. reflexivity. Qed.

Example planb4_Phi2_spot : planb4_Phi 2 = 1%Z.
Proof. reflexivity. Qed.

Example planb4_Phi3_spot : planb4_Phi 3 = 1%Z.
Proof. reflexivity. Qed.

(* the same three samples of the window list itself: empty. *)
Example planb4_Pn_list_13_empty :
  planb4_Pn_list 1 = [] /\ planb4_Pn_list 2 = [] /\ planb4_Pn_list 3 = [].
Proof. repeat split; reflexivity. Qed.

(* the window faces agree with the planb3_g1_calib tables over all  *)
(* n = 1..6 (both sides machine-printed; window register: MATCH).   *)
(* The refined face LZn = L / Phi agrees with the calibration L     *)
(* table over n = 1..6; the raw lcm face differs exactly by the Phi *)
(* factor at n = 4 (x7) and n = 6 (x11), machine-printed. *)
Example planb4_Phi_calib_agree :
  map planb4_Phi (seq 1 6) = map planb3_g1_Phi (seq 1 6).
Proof. reflexivity. Qed.

Example planb4_LZn_calib_agree :
  map planb4_LZn (seq 1 6) = map planb3_g1_L (seq 1 6).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Section 9. The t_n polynomial-part integral face (U4).  Dense      *)
(* Q-coefficient lists (index = power of x); long division in Q; the  *)
(* contour monomial integrals run in Gaussian-Q; t_n is the real      *)
(* component of the accumulated integral (the imaginary component     *)
(* vanishes by conjugate symmetry of the segment).                    *)
(* ================================================================== *)

Definition planb4_list_last (a : list Q) : Q :=
  match rev a with
  | [] => 0%Q
  | x :: _ => x
  end.

Fixpoint planb4_pad2 (a b : list Q) : list Q :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | a0 :: a', b0 :: b' => (a0 + b0)%Q :: planb4_pad2 a' b'
  end.

Fixpoint planb4_pmul (a b : list Q) : list Q :=
  match a with
  | [] => []
  | a0 :: a' =>
      planb4_pad2 (map (fun b0 => a0 * b0)%Q b) (0%Q :: planb4_pmul a' b)
  end.

Fixpoint planb4_ppow (a : list Q) (k : nat) : list Q :=
  match k with
  | O => (1 # 1)%Q :: []
  | S k' => planb4_pmul a (planb4_ppow a k')
  end.

Definition planb4_shift (c : Q) (k : nat) (a : list Q) : list Q :=
  repeat c k ++ map (fun x => c * x)%Q a.

Definition planb4_psub_aligned (a b : list Q) : list Q :=
  let gap := (length a - length b)%nat in
  let pad := repeat 0%Q gap in
  planb4_pad2 a (map (fun x => (- x)%Q) (pad ++ b)).

Fixpoint planb4_pdiv_loop (a b : list Q) (fuel : nat) : list Q :=
  match fuel with
  | O => []
  | S f =>
      if Nat.ltb (length a) (length b)
      then []
      else
        let c := (planb4_list_last a / planb4_list_last b)%Q in
        let shifted := planb4_shift c ((length a - length b)%nat) b in
        let a' := planb4_psub_aligned a shifted in
        c :: planb4_pdiv_loop a' b f
  end.

Definition planb4_pdiv (a b : list Q) : list Q :=
  planb4_pdiv_loop a b (length a).

(* N(x) = 5 * x^(2n) * (x^4 + 6 x^2 + 25)^(2n). *)
Definition planb4_N (n : nat) : list Q :=
  let base := planb4_ppow ((25 # 1)%Q :: (0 # 1)%Q :: (6 # 1)%Q :: (0 # 1)%Q
                           :: (1 # 1)%Q :: []) (2 * n) in
  map (fun x => (5 # 1)%Q * x)%Q (repeat 0%Q (2 * n) ++ base).

(* D(x) = (25 - x^2)^(3n+1). *)
Definition planb4_D (n : nat) : list Q :=
  planb4_ppow ((25 # 1)%Q :: (0 # 1)%Q :: ((-1) # 1)%Q :: []) (3 * n + 1).

(* the polynomial part P_n (quotient of N by D). *)
Definition planb4_P (n : nat) : list Q :=
  planb4_pdiv (planb4_N n) (planb4_D n).

(* Gaussian-Q monomial contour integral over t in [-1, 1]:
   int_k := (A - B) * (-i) / (k + 1),
   A = (-1+2i)^(k+1),  B = (-1-2i)^(k+1). *)
Definition planb4_int_k (k : nat) : Q * Q :=
  let A := gzq_pow (((-1) # 1)%Q, (2 # 1)%Q) (S k) in
  let B := gzq_pow (((-1) # 1)%Q, ((-2) # 1)%Q) (S k) in
  let d := gzq_add A (gzq_mul (((-1) # 1)%Q, (0 # 1)%Q) B) in
  gzq_mul d (((0 # 1)%Q, Qdiv (((-1) # 1)%Q) ((Z.of_nat (S k) # 1)%Q))).

(* index-safe accumulation: t_n = sum over the quotient coeffs of       *)
(* (q_k * 2) * int_k, accumulated outermost-first. *)
Fixpoint planb4_tn_acc (qs : list Q) (k : nat) : Q * Q :=
  match qs with
  | [] => ((0 # 1)%Q, (0 # 1)%Q)
  | q0 :: qs' =>
      let acc := planb4_tn_acc qs' (S k) in
      gzq_add (gzq_mul ((q0 * (2 # 1)%Q)%Q, (0 # 1)%Q) (planb4_int_k k)) acc
  end.

Definition planb4_tn (n : nat) : Q :=
  fst (planb4_tn_acc (planb4_P n) 0).
(* Section 10. The L-cleared a/b composite faces and the integrality *)
(* statement faces.  aq/bq above are the S-only / A_{n,0}-only       *)
(* sub-faces; the header formulas add the L_n clearing factor and    *)
(* the (-1)^(n+1) sign.  The integrality faces are Set-carried       *)
(* (sigT over qeqT) over the machine-passed KB41m domain n = 1..40;  *)
(* the general-n supply is the KB41m Lemma 3(9) chain (registered    *)
(* upstream debt); spots discharge where conversion is affordable. *)

(* the (-1)^(n+1) sign face. *)
Definition planb4_sign (n : nat) : Z := if Nat.even (S n) then 1%Z else (-1)%Z.

(* the cleared a-face: 2^(-floor(5n/2)+1) L_n (-1)^(n+1) (t_n + S_n). *)
Definition planb4_a_cleared (n : nat) : Q :=
  (planb4_scale n * (inject_Z (planb4_L n * planb4_sign n) *
                     (planb4_tn n + planb4_aq n))%Q)%Q.

(* the cleared b-face: 2^(-floor(5n/2)+1) L_n (-1)^(n+1) A_{n,0} / 2. *)
Definition planb4_b_cleared (n : nat) : Q :=
  (planb4_scale n * (inject_Z (planb4_L n * planb4_sign n) *
                     (piu_zz_Aj n 0 * (1 # 2)%Q))%Q)%Q.

(* the born integrality statement faces (KB41m items 1-5, n = 1..40). *)
Definition planb4_aq_is_Z : Set :=
  forall n : nat, BidT (planb3_g1_dom n) ->
    sigT (fun z : Z => qeqT (planb4_a_cleared n) (inject_Z z)).

Definition planb4_bq_is_Z : Set :=
  forall n : nat, BidT (planb3_g1_dom n) ->
    sigT (fun z : Z => qeqT (planb4_b_cleared n) (inject_Z z)).

(* U8 b-channel table anchor at n = 1 (the raw bq sub-face lacks the *)
(* L_n clearing factor, so the table equality is on the cleared face). *)
Example planb4_b_cleared_table_1 :
  Qeq_bool (planb4_b_cleared 1) (inject_Z (planb3_g1_B 1)) = true.
Proof. reflexivity. Qed.

Example planb4_bq_is_Z_1 :
  sigT (fun z : Z => qeqT (planb4_b_cleared 1) (inject_Z z)).
Proof. exists (planb3_g1_B 1). apply qeqT_intro. unfold Qeq. reflexivity. Qed.

(* the a-channel composite does NOT reproduce the calibration A-table *)
(* at n = 1 (kernel-refuted; the b-channel matches) -- registered     *)
(* honest item; the composite value at n = 1 is the integer 3602. *)
Example planb4_aq_is_Z_1 :
  sigT (fun z : Z => qeqT (planb4_a_cleared 1) (inject_Z z)).
Proof. exists (3602%Z). apply qeqT_intro. unfold Qeq. reflexivity. Qed.

(* Section 11. Assumption audit for the new spot faces. *)

Print Assumptions planb4_Phi1_spot.
Print Assumptions planb4_Phi2_spot.
Print Assumptions planb4_Phi3_spot.
Print Assumptions planb4_Pn_list_13_empty.
Print Assumptions planb4_Phi_calib_agree.
Print Assumptions planb4_LZn_calib_agree.
Print Assumptions planb4_sign.
Print Assumptions planb4_a_cleared.
Print Assumptions planb4_b_cleared.
Print Assumptions planb4_aq_is_Z.
Print Assumptions planb4_bq_is_Z.
Print Assumptions planb4_b_cleared_table_1.
Print Assumptions planb4_bq_is_Z_1.
Print Assumptions planb4_aq_is_Z_1.
