(* ConstructiveWorld-Set -- exact rational constants for the Zeilberger-Zudilin route to pi irrationality measures. *)

(** * piu_zz_constants: rational constant faces and the Giraudin closed-law skeleton.

    Mission.  Exact rational (Q) encodings of the constants on the
      Zeilberger-Zudilin 2020 route to an upper bound of the irrationality
      measure of pi (arXiv:1912.06345v2), and the Giraudin 2026 closed-form
      law (arXiv:2609.37459v2) in tree-computable rational form: constant
      faces [piu_zzc_sigma], [piu_zzc_tau], [piu_zzc_s], [piu_zzc_Lambda_223];
      closed forms [piu_zzc_mu_223], [zz_mu_closed], [piu_zzc_mu_g_223];
      cross-checks [piu_zzc_mu223_matches_lit],
      [piu_zzc_giraudin_matches_zz_223], [piu_zzc_bai_below_zz]; and the
      Machin identities [piu_zzc_machin_01] to [piu_zzc_prim_16].

    Dependencies.  Stdlib [ZArith], [QArith.QArith], [QArith.Qabs].
      Requires no other module of this development.

    References.  This development, piu_zz_constants.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      via the boolean identity face (boolean test plus the in-file carrier
      [zzId], local twin of the tree-canonical [Id]); extraction has
      [Obj.magic] = 0, no erasure; the Section 9 audit reads [Closed] on
      all 123 [Print Assumptions] exits; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" piu_zz_constants.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (the 9.3
      fingerprint, version bits 90300). *)
From Stdlib Require Import ZArith QArith.QArith QArith.Qabs.
Open Scope Q_scope.

(* ============================================================ *)
(*  Section 0.  Set-carried boolean identity carriers, self-contained, zz-prefixed names. *)
(* ============================================================ *)

(* Local twin of the tree-canonical Set-level identity carrier Id
   (S01_BaseRing), defined in-file because this module is standalone. *)
Inductive zzId {A : Set} (x : A) : A -> Set :=
| zz_id_refl : zzId x x.

Arguments zz_id_refl {A} {x}.

(* Uniform boolean identity face: a boolean test carried as
   @zzId bool expected actual. *)
Definition zzZeqT (n m : Z) : Set := @zzId bool true (Z.eqb n m).

Definition zzNatEqT (n m : nat) : Set := @zzId bool true (Nat.eqb n m).

Definition zzQeqT (x y : Q) : Set := @zzId bool true (Qeq_bool x y).

(* Strict order on Q in cross-multiplying form (valid for non-normalized denominators too) *)
Definition zzQlt_bool (x y : Q) : bool := (Qnum x * QDen y <? Qnum y * QDen x)%Z.

Definition zzQltT (x y : Q) : Set := @zzId bool true (zzQlt_bool x y).

Definition zzQleT (x y : Q) : Set := @zzId bool true (Qle_bool x y).

(* Interval carrier: lo <= x <= hi *)
Definition zzQband (x lo hi : Q) : Set :=
  @zzId bool true (andb (Qle_bool lo x) (Qle_bool x hi)).

Definition zzQmax (x y : Q) : Q := if Qle_bool x y then y else x.

Definition zzQ_of_Z (n : Z) : Q := (n # 1).

(* ============================================================ *)
(*  Section 1.  Literature constant faces, exact Q forms of decimal truncations. *)
(* ============================================================ *)

(* sigma = 11.61389004533104820528984629866735...  [ZZ2020], World record, second equation; 32-digit truncation *)
Definition piu_zzc_sigma : Q :=
  (1161389004533104820528984629866735 # 100000000000000000000000000000000).

(* tau = 1.90291648559998216823282018815429...  [ZZ2020], World record, first equation in absolute value; 32-digit truncation *)
Definition piu_zzc_tau : Q :=
  (190291648559998216823282018815429 # 100000000000000000000000000000000).

(* s = 3.52477292396528388...  high-precision continuation of the calibrated value s = 3.524772924 of [G26], Thm 2, the saddle-point min-max decay rate; 17-digit truncation *)
Definition piu_zzc_s : Q := (352477292396528388 # 100000000000000000).

(* Lambda(2,2,3) = 1.62185643836530171941...  [G26], Sec. 6 calibration table row 1; 20-digit truncation *)
Definition piu_zzc_Lambda_223 : Q := (162185643836530171941 # 100000000000000000000).

(* mu(2,2,3) = 7.1032053341370017275057734228103...  published value of [ZZ2020]; 31-digit truncation, cross-check baseline *)
Definition piu_zzc_mu_223_lit : Q := (71032053341370017275057734228103 # 10000000000000000000000000000000).

(* mu(Bai) = 7.1018628323563507  [G26], Sec. 6 calibration table row 3; 16 digits *)
Definition piu_zzc_mu_bai_lit : Q := (71018628323563507 # 10000000000000000).

(* mu(3,3,5) = 7.6063085207111912  [G26], Sec. 6 calibration table row 2, Salikhov route; 16 digits *)
Definition piu_zzc_mu_335_lit : Q := (76063085207111912 # 10000000000000000).

(* W = 0.645275610234...  window constant of the (2,2,3) configuration in [G26], equal to pi/(2 sqrt(3)) - log(3 sqrt(3)/4); 12-digit truncation *)
Definition piu_zzc_W_223 : Q := (645275610234 # 1000000000000).

(* W_Bai = 601.2828866806  window constant at the Bai point in [G26], 10-digit recorded input of the literature *)
Definition piu_zzc_W_bai : Q := (6012828866806 # 10000000000).

(* log 2 = 0.6931471805599453...  16-digit truncation, logarithmic input of the closed-form law *)
Definition piu_zzc_ln2 : Q := (6931471805599453 # 10000000000000000).

(* Lambda(Bai) = 1503.8827864689270  [G26], Sec. 6 calibration table row 3; 13 digits, cross-check baseline *)
Definition piu_zzc_Lambda_bai_lit : Q := (15038827864689270 # 10000000000000).

(* Upstream saddle-point and discriminant quantities (roots of the integer-coefficient cubic of [ZZ2020], Prop. 2, equation (18); recorded faces) *)
Definition piu_zzc_N3 : Q := (2185169139621956 # 100000000000).
Definition piu_zzc_y3 : Q := (6633950152462140 # 100000000000000).
Definition piu_zzc_absN1 : Q := (29458495928116876 # 1000000000000000000).

(* Coarse working values, early published rounded or truncated faces of the literature *)
Definition piu_zzc_sigma_coarse : Q := (116139 # 10000).
Definition piu_zzc_tau_coarse : Q := (19029 # 10000).
Definition piu_zzc_s_coarse : Q := (3525 # 1000).
Definition piu_zzc_Lambda_coarse : Q := (1621 # 1000).

(* ============================================================ *)
(*  Section 2.  Derived closed forms. *)
(* ============================================================ *)

(* ZZ closed form: mu = 1 + sigma/tau (the definition is already its
   computational form; agreement with the Giraudin law at (2,2,3) is
   re-checked within a tolerance band by piu_zzc_giraudin_matches_zz_223
   of Section 6) *)
Definition piu_zzc_mu_223 : Q := (1 # 1) + piu_zzc_sigma / piu_zzc_tau.

(* 12-digit decimal downward truncation and upward rounding of the ZZ value 7.103205334137 *)
Definition piu_zzc_mu_zz_lower : Q := (7103205334137 # 1000000000000).
Definition piu_zzc_mu_zz_upper : Q := (7103205334138 # 1000000000000).

(* Saddle-point index S = max_i log|g(zeta_i)| = log N_3, solved back from sigma = S + Lambda *)
Definition piu_zzc_S_223 : Q := piu_zzc_sigma - piu_zzc_Lambda_223.

(* Configuration (5, 1+2i): N(P+w) and N(P-w), w = 1+2i, P = 5 *)
Definition piu_zzc_np_w : Z := ((5 + 1) * (5 + 1) + 2 * 2)%Z.
Definition piu_zzc_nm_w : Z := ((5 - 1) * (5 - 1) + (0 - 2) * (0 - 2))%Z.

(* 2-adic valuation (recursive on the positive part; 0 for negative and non-positive input) *)
Fixpoint zz_v2_pos (p : positive) : nat :=
  match p with
  | xO q => S (zz_v2_pos q)
  | _ => 0
  end.

Definition zz_v2 (n : Z) : nat :=
  match n with Zpos p => zz_v2_pos p | _ => 0 end.

(* lambda+- = v_2(N(P+-w))/2: the configuration (5, 1+2i) gives lambda+ = 3/2 and lambda- = 1 *)
Definition piu_zzc_lam_p : Q := zzQ_of_Z (Z.of_nat (zz_v2 piu_zzc_np_w)) * (1 # 2).
Definition piu_zzc_lam_m : Q := zzQ_of_Z (Z.of_nat (zz_v2 piu_zzc_nm_w)) * (1 # 2).

(* ============================================================ *)
(*  Section 3.  Rational skeleton of the Giraudin closed-form law
   (Defined computational form, Q throughout).  The law itself,
   [G26] Sec. 6:  Lambda = R_lcm - W - c_2 log 2 + c_P log P
   minus the sum over odd q of c_q log q;
   mu = 1 + (S + Lambda) / (s - Lambda).
   The logarithmic inputs W, log 2 and log P, the saddle-point
   quantities S and s, and the Gaussian-prime characteristics
   lambda+ and lambda- enter as explicit Q arguments: no
   transcendental quantity hides behind an axiom; the interface
   is honest. *)
(* ============================================================ *)

(* lcm window radius R_lcm = max(b, a0 + 4a1 - 2b)  [G26], Thm 3 *)
Definition zz_R_lcm (a0 a1 b : Z) : Z := Z.max b (a0 + 4 * a1 - 2 * b)%Z.

(* P-adic grade c_P = max(0, 2b - a0 - 2a1)  [G26], Thm 3 *)
Definition zz_cP (a0 a1 b : Z) : Z := Z.max 0 (2 * b - a0 - 2 * a1)%Z.

(* 2-adic saving c_2 in general form, with lambda+ and lambda- as
   arguments  [G26], Thm 3: for b <= 2a1,
   c_2 = 2(lambda+ + lambda-)a1 - (1 + max(lambda+, lambda-, 1))b;
   for b > 2a1,  c_2 = 4 lambda- a1 - (1 + lambda-) b. *)
Definition zz_c2g (lp lm : Q) (a1 b : Z) : Q :=
  if Z.leb b (2 * a1)%Z
  then (2 # 1) * (lp + lm) * zzQ_of_Z a1
       - ((1 # 1) + zzQmax lp (zzQmax lm (1 # 1))) * zzQ_of_Z b
  else (4 # 1) * lm * zzQ_of_Z a1 - ((1 # 1) + lm) * zzQ_of_Z b.

(* Specialization to the configuration (5, 1+2i), lambda+ = 3/2 and lambda- = 1: c_2 = 5a1 - (5/2) b for b <= 2a1 *)
Definition zz_c2_51 (a1 b : Z) : Q := zz_c2g (3 # 2) (1 # 1) a1 b.

(* Combination constant Lambda (configuration without odd-q branch, so c_q = 0) *)
Definition zz_Lambda (a0 a1 b : Z) (lp lm Wx l2 lP : Q) : Q :=
  zzQ_of_Z (zz_R_lcm a0 a1 b) - Wx - zz_c2g lp lm a1 b * l2
  + zzQ_of_Z (zz_cP a0 a1 b) * lP.

(* Giraudin closed-form law: mu = 1 + (S + Lambda) / (s - Lambda) *)
Definition zz_mu_closed (a0 a1 b : Z) (Sx sx Wx l2 lP lp lm : Q) : Q :=
  let L := zz_Lambda a0 a1 b lp lm Wx l2 lP in
  (1 # 1) + (Sx + L) / (sx - L).

(* Instance of the law at (2,2,3) on literature inputs, and recomputation form of Lambda at the Bai point *)
Definition piu_zzc_mu_g_223 : Q :=
  zz_mu_closed 2 2 3 piu_zzc_S_223 piu_zzc_s piu_zzc_W_223 piu_zzc_ln2
               (0 # 1) (3 # 2) (1 # 1).

Definition piu_zzc_Lambda_223_rec : Q :=
  zzQ_of_Z (zz_R_lcm 2 2 3) - piu_zzc_W_223 - zz_c2_51 2 3 * piu_zzc_ln2
  + zzQ_of_Z (zz_cP 2 2 3) * (0 # 1).

Definition piu_zzc_Lambda_bai_rec : Q :=
  zzQ_of_Z (zz_R_lcm 1857 1857 2785) - piu_zzc_W_bai
  - zz_c2_51 1857 2785 * piu_zzc_ln2
  + zzQ_of_Z (zz_cP 1857 1857 2785) * (0 # 1).

(* ============================================================ *)
(*  Section 4.  The 16 Machin-admissible configurations (P, u, v)
   with P < 100 and w = u + v i, the table of [G26] Sec. 9.
   Admissibility: u^2 + (v+P)^2 = 2P^2, primitive solution,
   gcd(P, u, v) = 1. *)
(* ============================================================ *)

Definition piu_zzc_cfg01 : Z * Z * Z := (5%Z, 1%Z, 2%Z).
Definition piu_zzc_cfg02 : Z * Z * Z := (13%Z, 7%Z, 4%Z).
Definition piu_zzc_cfg03 : Z * Z * Z := (17%Z, 7%Z, 6%Z).
Definition piu_zzc_cfg04 : Z * Z * Z := (25%Z, 17%Z, 6%Z).
Definition piu_zzc_cfg05 : Z * Z * Z := (29%Z, 1%Z, 12%Z).
Definition piu_zzc_cfg06 : Z * Z * Z := (37%Z, 23%Z, 10%Z).
Definition piu_zzc_cfg07 : Z * Z * Z := (41%Z, 31%Z, 8%Z).
Definition piu_zzc_cfg08 : Z * Z * Z := (53%Z, 17%Z, 20%Z).
Definition piu_zzc_cfg09 : Z * Z * Z := (61%Z, 49%Z, 10%Z).
Definition piu_zzc_cfg10 : Z * Z * Z := (65%Z, 23%Z, 24%Z).
Definition piu_zzc_cfg11 : Z * Z * Z := (65%Z, 47%Z, 14%Z).
Definition piu_zzc_cfg12 : Z * Z * Z := (73%Z, 7%Z, 30%Z).
Definition piu_zzc_cfg13 : Z * Z * Z := (85%Z, 41%Z, 28%Z).
Definition piu_zzc_cfg14 : Z * Z * Z := (85%Z, 71%Z, 12%Z).
Definition piu_zzc_cfg15 : Z * Z * Z := (89%Z, 41%Z, 30%Z).
Definition piu_zzc_cfg16 : Z * Z * Z := (97%Z, 7%Z, 40%Z).

Definition piu_zzc_machin_b (c : Z * Z * Z) : bool :=
  let '(P, u, v) := c in Z.eqb (u * u + (v + P) * (v + P))%Z (2 * (P * P))%Z.

Definition piu_zzc_prim_b (c : Z * Z * Z) : bool :=
  let '(P, u, v) := c in Z.eqb (Z.gcd P (Z.gcd u v)) 1%Z.

(* ============================================================ *)
(*  Section 5.  lambda+ and lambda- and the content of the configuration (5, 1+2i). *)
(* ============================================================ *)

Lemma piu_zzc_np_w_val : zzZeqT piu_zzc_np_w 40%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_nm_w_val : zzZeqT piu_zzc_nm_w 20%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_lam_p_val : zzQeqT piu_zzc_lam_p (3 # 2).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_lam_m_val : zzQeqT piu_zzc_lam_m (1 # 1).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_content_p_plus : zzZeqT (Z.gcd (5 + 1)%Z 2%Z) 2%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_content_p_minus : zzZeqT (Z.gcd (5 - 1)%Z 2%Z) 2%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

(* ============================================================ *)
(*  Section 6.  Verification theorem faces. *)
(* ============================================================ *)

(* -- 6.1  Coarse values agree with the full-precision forms, within the rounding and truncation radius -- *)

Lemma piu_zzc_sigma_coarse_band :
  zzQband (Qabs (piu_zzc_sigma - piu_zzc_sigma_coarse)) (0 # 1) (1 # 20000).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_tau_coarse_band :
  zzQband (Qabs (piu_zzc_tau - piu_zzc_tau_coarse)) (0 # 1) (1 # 20000).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_s_coarse_band :
  zzQband (Qabs (piu_zzc_s - piu_zzc_s_coarse)) (0 # 1) (1 # 2000).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_Lambda_coarse_band :
  zzQband (Qabs (piu_zzc_Lambda_223 - piu_zzc_Lambda_coarse)) (0 # 1) (1 # 1000).
Proof. vm_compute. exact zz_id_refl. Qed.

(* -- 6.2  Digit-by-digit 26-decimal re-check of the ZZ closed form
   mu = 1 + sigma/tau, and its 12-decimal two-sided enclosure.
   Re-checked value: 1 + sigma/tau = 7.1032053341370017275057734 22810327...
   The first 26 decimals agree digit by digit with the published value
   7.1032053341370017275057734228103... of [ZZ2020]; from the 27th decimal
   on, the difference is at most 3.8e-32, caused by truncation of sigma/tau. *)

Lemma piu_zzc_mu223_floor26 :
  zzZeqT (Z.div (Qnum piu_zzc_mu_223 * 100000000000000000000000000)%Z
                 (Z.pos (Qden piu_zzc_mu_223)))
         710320533413700172750577342%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_mu223_lower_bound : zzQltT piu_zzc_mu_zz_lower piu_zzc_mu_223.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_mu223_upper_bound : zzQltT piu_zzc_mu_223 piu_zzc_mu_zz_upper.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_mu223_matches_lit :
  zzQband (Qabs (piu_zzc_mu_223 - piu_zzc_mu_223_lit)) (0 # 1)
          (1 # 1000000000000000000000000000000).
Proof. vm_compute. exact zz_id_refl. Qed.

(* -- 6.3  Rational skeleton at (2,2,3) -- *)

Lemma piu_zzc_R_lcm_223 : zzZeqT (zz_R_lcm 2 2 3) 4%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_cP_223 : zzZeqT (zz_cP 2 2 3) 0%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_c2_223 : zzQeqT (zz_c2_51 2 3) (5 # 2).
Proof. vm_compute. exact zz_id_refl. Qed.

(* On truncated inputs (W at 12 digits, log 2 at 16 digits), the recomputed Lambda differs from the 20-digit recorded value by less than 1e-12 *)
Lemma piu_zzc_Lambda_223_rec_band :
  zzQband (Qabs (piu_zzc_Lambda_223_rec - piu_zzc_Lambda_223)) (0 # 1)
          (1 # 1000000000000).
Proof. vm_compute. exact zz_id_refl. Qed.

(* -- 6.4  Coefficient identity system at the Bai point (1857, 1857, 2785).
   Vertex Q = 2a/(3a-2b) = 3714; R_lcm = 3715; c_P = 0;
   c_2 = 4645/2 = 5a1 - (5/2) b; b/a1 = 3/2 - 1/3714. *)

Lemma piu_zzc_bai_vertex :
  zzQeqT (zzQ_of_Z (2 * 1857)%Z / zzQ_of_Z (3 * 1857 - 2 * 2785)%Z) (3714 # 1).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_R_lcm_bai : zzZeqT (zz_R_lcm 1857 1857 2785) 3715%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_cP_bai : zzZeqT (zz_cP 1857 1857 2785) 0%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_c2_bai : zzQeqT (zz_c2_51 1857 2785) (4645 # 2).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_bai_ratio : zzQeqT (2785 # 1857) ((3 # 2) - (1 # 3714)).
Proof. vm_compute. exact zz_id_refl. Qed.

(* Digit-by-digit 13-decimal re-check of the recomputed Lambda(Bai) on
   truncated inputs: 3715 - 601.2828866806 - (4645/2) log 2 =
   1503.88278646892704..., and floor of the value scaled by ten to the
   thirteenth equals 15038827864689270, matching the 13-digit recorded value. *)
Lemma piu_zzc_Lambda_bai_rec_floor13 :
  zzZeqT (Z.div (Qnum piu_zzc_Lambda_bai_rec * 10000000000000)%Z
                 (Z.pos (Qden piu_zzc_Lambda_bai_rec)))
         15038827864689270%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_Lambda_bai_rec_band :
  zzQband (Qabs (piu_zzc_Lambda_bai_rec - piu_zzc_Lambda_bai_lit)) (0 # 1)
          (1 # 10000000000000).
Proof. vm_compute. exact zz_id_refl. Qed.

(* Directional comparison: the Bai recorded value lies below the (2,2,3)
   value.  For the claim that 7.101862832356 bounds the whole method from
   below, [G26] Result J itself supplies no proof; this file likewise
   proves only the directional comparison and asserts nothing about that
   bound. *)
Lemma piu_zzc_bai_below_zz : zzQltT piu_zzc_mu_bai_lit piu_zzc_mu_223.
Proof. vm_compute. exact zz_id_refl. Qed.

(* -- 6.5  Cross re-check of the Giraudin law against the ZZ closed form
   at (2,2,3).  The propagated truncation error of the inputs is at most
   3.2e-12 (dominated by W at 12 digits), tolerance 1e-11. *)
Lemma piu_zzc_giraudin_matches_zz_223 :
  zzQband (Qabs (piu_zzc_mu_g_223 - piu_zzc_mu_223)) (0 # 1)
          (1 # 100000000000).
Proof. vm_compute. exact zz_id_refl. Qed.

(* -- 6.6  Per-configuration exact identities for the 16 configurations -- *)

Lemma piu_zzc_machin_01 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg01 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg01 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_01 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg01 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_02 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg02 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg02 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_02 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg02 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_03 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg03 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg03 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_03 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg03 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_04 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg04 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg04 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_04 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg04 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_05 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg05 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg05 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_05 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg05 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_06 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg06 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg06 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_06 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg06 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_07 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg07 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg07 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_07 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg07 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_08 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg08 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg08 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_08 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg08 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_09 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg09 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg09 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_09 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg09 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_10 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg10 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg10 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_10 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg10 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_11 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg11 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg11 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_11 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg11 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_12 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg12 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg12 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_12 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg12 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_13 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg13 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg13 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_13 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg13 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_14 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg14 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg14 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_14 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg14 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_15 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg15 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg15 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_15 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg15 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_machin_16 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg16 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg16 in (2 * (P * P))%Z).
Proof. vm_compute. exact zz_id_refl. Qed.

Lemma piu_zzc_prim_16 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg16 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact zz_id_refl. Qed.

(* ============================================================ *)
(*  Section 7.  Statement-face records of the three p-adic lemmas
   ([ZZ2020] Lemma 1 / Lemma 2 / Lemma 3; statement faces only, their
   proofs belong to a later companion file, and this file does not open
   them.  Lemma 2 must take the v2 corrected statement: the v1
   integrality claim about T(m) was retracted by the authors and may
   not be adopted.)
   ------------------------------------------------------------
   Notation.  Partial fractions of I_{A,B}(n):
     R(x) = 5x^{2n}(x^4+6x^2+25)^{2n} / ((5+x)^{3n+1}(5-x)^{3n+1})
          = P(x) + sum over j = 0..3n of
            ( A_j/(5+x)^{j+1} + A_j/(5-x)^{j+1} ),
   where P lies in Z[x^2] of degree 4n-2, and R(-x) = R(x).
   Write {x} = x - floor(x) for the fractional part.

   Lemma A ([ZZ2020] Lemma 1, integrality lower bound).  For
   j = 0, ..., 3n:
         2^{-floor((5n+3j)/2)+1} 5^{-j} A_j lies in Z.
     Proof tools: the operators D_m : f |-> f^{(m)}(-5)/m!; the
     Leibniz expansion gives
     A_j = sum over m in M_j of (-1)^{m1+...+m5} T(m)
     2^{4n-1+j+m1} (1-i)^{-m4} (1+i)^{-m5} 5^j
     (2+i)^{m2+m5} (2-i)^{m3+m4},
     with M_j = {m0+...+m5 = 3n-j, m1..5 <= 2n}; the key step is
     (1+-i)^2 = +-2i.

   Lemma B ([ZZ2020] Lemma 2, v2 corrected form).  For any prime
   p in P_n = { p > max{5, sqrt(3n)} : 1/2 <= {n/p} < 2/3 } and
   j in {-4n+1, -4n+2, ..., 3n}: if p divides j, then
         A_j is 0 mod p  (equivalently p divides 10^{-j} A_j).

   Lemma C ([ZZ2020] Lemma 3, clearing denominators).  Put
   Phi_n = product over p in P_n of p and
   L_n = lcm(1, 2, ..., 4n) / Phi_n in Z; then
         L_n 10^{-j} A_j / j lies in Z  (j in {-4n, ..., 3n},
         j nonzero), and
         Phi_n^{-1} A_0 lies in Z.
     Appendix (equation (10)): the limit of (log Phi_n)/n as n grows
     unboundedly equals pi/(2 sqrt(3)) - log(3 sqrt(3)/4) =
     0.64527561... (the constant recorded as piu_zzc_W_223). *)
(* ============================================================ *)

(* ============================================================ *)
(*  Section 8.  vm_compute value checks, compile-log output for digit-by-digit table comparison. *)
(* ============================================================ *)

Eval vm_compute in piu_zzc_mu_223.
Eval vm_compute in piu_zzc_Lambda_223_rec.
Eval vm_compute in piu_zzc_Lambda_bai_rec.
Eval vm_compute in piu_zzc_mu_g_223.
Eval vm_compute in piu_zzc_lam_p.
Eval vm_compute in piu_zzc_lam_m.
Eval vm_compute in (piu_zzc_machin_b piu_zzc_cfg01, piu_zzc_machin_b piu_zzc_cfg02,
  piu_zzc_machin_b piu_zzc_cfg03, piu_zzc_machin_b piu_zzc_cfg04,
  piu_zzc_machin_b piu_zzc_cfg05, piu_zzc_machin_b piu_zzc_cfg06,
  piu_zzc_machin_b piu_zzc_cfg07, piu_zzc_machin_b piu_zzc_cfg08,
  piu_zzc_machin_b piu_zzc_cfg09, piu_zzc_machin_b piu_zzc_cfg10,
  piu_zzc_machin_b piu_zzc_cfg11, piu_zzc_machin_b piu_zzc_cfg12,
  piu_zzc_machin_b piu_zzc_cfg13, piu_zzc_machin_b piu_zzc_cfg14,
  piu_zzc_machin_b piu_zzc_cfg15, piu_zzc_machin_b piu_zzc_cfg16).
Eval vm_compute in (piu_zzc_prim_b piu_zzc_cfg01, piu_zzc_prim_b piu_zzc_cfg02,
  piu_zzc_prim_b piu_zzc_cfg03, piu_zzc_prim_b piu_zzc_cfg04,
  piu_zzc_prim_b piu_zzc_cfg05, piu_zzc_prim_b piu_zzc_cfg06,
  piu_zzc_prim_b piu_zzc_cfg07, piu_zzc_prim_b piu_zzc_cfg08,
  piu_zzc_prim_b piu_zzc_cfg09, piu_zzc_prim_b piu_zzc_cfg10,
  piu_zzc_prim_b piu_zzc_cfg11, piu_zzc_prim_b piu_zzc_cfg12,
  piu_zzc_prim_b piu_zzc_cfg13, piu_zzc_prim_b piu_zzc_cfg14,
  piu_zzc_prim_b piu_zzc_cfg15, piu_zzc_prim_b piu_zzc_cfg16).

(* ============================================================ *)
(*  Section 9.  Closing audit: the full statement roster, one
   [Check] per name (type impression) and one [Print Assumptions]
   per name (closedness audit; every exit reads [Closed under the
   global context], matching the [Axioms: none] report of [coqchk]). *)
(* ============================================================ *)

Check zzZeqT.
Check zzNatEqT.
Check zzQeqT.
Check zzQlt_bool.
Check zzQltT.
Check zzQleT.
Check zzQband.
Check zzQmax.
Check zzQ_of_Z.
Check piu_zzc_sigma.
Check piu_zzc_tau.
Check piu_zzc_s.
Check piu_zzc_Lambda_223.
Check piu_zzc_mu_223_lit.
Check piu_zzc_mu_bai_lit.
Check piu_zzc_mu_335_lit.
Check piu_zzc_W_223.
Check piu_zzc_W_bai.
Check piu_zzc_ln2.
Check piu_zzc_Lambda_bai_lit.
Check piu_zzc_N3.
Check piu_zzc_y3.
Check piu_zzc_absN1.
Check piu_zzc_sigma_coarse.
Check piu_zzc_tau_coarse.
Check piu_zzc_s_coarse.
Check piu_zzc_Lambda_coarse.
Check piu_zzc_mu_223.
Check piu_zzc_mu_zz_lower.
Check piu_zzc_mu_zz_upper.
Check piu_zzc_S_223.
Check piu_zzc_np_w.
Check piu_zzc_nm_w.
Check zz_v2_pos.
Check zz_v2.
Check piu_zzc_lam_p.
Check piu_zzc_lam_m.
Check zz_R_lcm.
Check zz_cP.
Check zz_c2g.
Check zz_c2_51.
Check zz_Lambda.
Check zz_mu_closed.
Check piu_zzc_mu_g_223.
Check piu_zzc_Lambda_223_rec.
Check piu_zzc_Lambda_bai_rec.
Check piu_zzc_cfg01.
Check piu_zzc_cfg02.
Check piu_zzc_cfg03.
Check piu_zzc_cfg04.
Check piu_zzc_cfg05.
Check piu_zzc_cfg06.
Check piu_zzc_cfg07.
Check piu_zzc_cfg08.
Check piu_zzc_cfg09.
Check piu_zzc_cfg10.
Check piu_zzc_cfg11.
Check piu_zzc_cfg12.
Check piu_zzc_cfg13.
Check piu_zzc_cfg14.
Check piu_zzc_cfg15.
Check piu_zzc_cfg16.
Check piu_zzc_machin_b.
Check piu_zzc_prim_b.
Check piu_zzc_np_w_val.
Check piu_zzc_nm_w_val.
Check piu_zzc_lam_p_val.
Check piu_zzc_lam_m_val.
Check piu_zzc_content_p_plus.
Check piu_zzc_content_p_minus.
Check piu_zzc_sigma_coarse_band.
Check piu_zzc_tau_coarse_band.
Check piu_zzc_s_coarse_band.
Check piu_zzc_Lambda_coarse_band.
Check piu_zzc_mu223_floor26.
Check piu_zzc_mu223_lower_bound.
Check piu_zzc_mu223_upper_bound.
Check piu_zzc_mu223_matches_lit.
Check piu_zzc_R_lcm_223.
Check piu_zzc_cP_223.
Check piu_zzc_c2_223.
Check piu_zzc_Lambda_223_rec_band.
Check piu_zzc_bai_vertex.
Check piu_zzc_R_lcm_bai.
Check piu_zzc_cP_bai.
Check piu_zzc_c2_bai.
Check piu_zzc_bai_ratio.
Check piu_zzc_Lambda_bai_rec_floor13.
Check piu_zzc_Lambda_bai_rec_band.
Check piu_zzc_bai_below_zz.
Check piu_zzc_giraudin_matches_zz_223.
Check piu_zzc_machin_01.
Check piu_zzc_prim_01.
Check piu_zzc_machin_02.
Check piu_zzc_prim_02.
Check piu_zzc_machin_03.
Check piu_zzc_prim_03.
Check piu_zzc_machin_04.
Check piu_zzc_prim_04.
Check piu_zzc_machin_05.
Check piu_zzc_prim_05.
Check piu_zzc_machin_06.
Check piu_zzc_prim_06.
Check piu_zzc_machin_07.
Check piu_zzc_prim_07.
Check piu_zzc_machin_08.
Check piu_zzc_prim_08.
Check piu_zzc_machin_09.
Check piu_zzc_prim_09.
Check piu_zzc_machin_10.
Check piu_zzc_prim_10.
Check piu_zzc_machin_11.
Check piu_zzc_prim_11.
Check piu_zzc_machin_12.
Check piu_zzc_prim_12.
Check piu_zzc_machin_13.
Check piu_zzc_prim_13.
Check piu_zzc_machin_14.
Check piu_zzc_prim_14.
Check piu_zzc_machin_15.
Check piu_zzc_prim_15.
Check piu_zzc_machin_16.
Check piu_zzc_prim_16.

Print Assumptions zzZeqT.
Print Assumptions zzNatEqT.
Print Assumptions zzQeqT.
Print Assumptions zzQlt_bool.
Print Assumptions zzQltT.
Print Assumptions zzQleT.
Print Assumptions zzQband.
Print Assumptions zzQmax.
Print Assumptions zzQ_of_Z.
Print Assumptions piu_zzc_sigma.
Print Assumptions piu_zzc_tau.
Print Assumptions piu_zzc_s.
Print Assumptions piu_zzc_Lambda_223.
Print Assumptions piu_zzc_mu_223_lit.
Print Assumptions piu_zzc_mu_bai_lit.
Print Assumptions piu_zzc_mu_335_lit.
Print Assumptions piu_zzc_W_223.
Print Assumptions piu_zzc_W_bai.
Print Assumptions piu_zzc_ln2.
Print Assumptions piu_zzc_Lambda_bai_lit.
Print Assumptions piu_zzc_N3.
Print Assumptions piu_zzc_y3.
Print Assumptions piu_zzc_absN1.
Print Assumptions piu_zzc_sigma_coarse.
Print Assumptions piu_zzc_tau_coarse.
Print Assumptions piu_zzc_s_coarse.
Print Assumptions piu_zzc_Lambda_coarse.
Print Assumptions piu_zzc_mu_223.
Print Assumptions piu_zzc_mu_zz_lower.
Print Assumptions piu_zzc_mu_zz_upper.
Print Assumptions piu_zzc_S_223.
Print Assumptions piu_zzc_np_w.
Print Assumptions piu_zzc_nm_w.
Print Assumptions zz_v2_pos.
Print Assumptions zz_v2.
Print Assumptions piu_zzc_lam_p.
Print Assumptions piu_zzc_lam_m.
Print Assumptions zz_R_lcm.
Print Assumptions zz_cP.
Print Assumptions zz_c2g.
Print Assumptions zz_c2_51.
Print Assumptions zz_Lambda.
Print Assumptions zz_mu_closed.
Print Assumptions piu_zzc_mu_g_223.
Print Assumptions piu_zzc_Lambda_223_rec.
Print Assumptions piu_zzc_Lambda_bai_rec.
Print Assumptions piu_zzc_cfg01.
Print Assumptions piu_zzc_cfg02.
Print Assumptions piu_zzc_cfg03.
Print Assumptions piu_zzc_cfg04.
Print Assumptions piu_zzc_cfg05.
Print Assumptions piu_zzc_cfg06.
Print Assumptions piu_zzc_cfg07.
Print Assumptions piu_zzc_cfg08.
Print Assumptions piu_zzc_cfg09.
Print Assumptions piu_zzc_cfg10.
Print Assumptions piu_zzc_cfg11.
Print Assumptions piu_zzc_cfg12.
Print Assumptions piu_zzc_cfg13.
Print Assumptions piu_zzc_cfg14.
Print Assumptions piu_zzc_cfg15.
Print Assumptions piu_zzc_cfg16.
Print Assumptions piu_zzc_machin_b.
Print Assumptions piu_zzc_prim_b.
Print Assumptions piu_zzc_np_w_val.
Print Assumptions piu_zzc_nm_w_val.
Print Assumptions piu_zzc_lam_p_val.
Print Assumptions piu_zzc_lam_m_val.
Print Assumptions piu_zzc_content_p_plus.
Print Assumptions piu_zzc_content_p_minus.
Print Assumptions piu_zzc_sigma_coarse_band.
Print Assumptions piu_zzc_tau_coarse_band.
Print Assumptions piu_zzc_s_coarse_band.
Print Assumptions piu_zzc_Lambda_coarse_band.
Print Assumptions piu_zzc_mu223_floor26.
Print Assumptions piu_zzc_mu223_lower_bound.
Print Assumptions piu_zzc_mu223_upper_bound.
Print Assumptions piu_zzc_mu223_matches_lit.
Print Assumptions piu_zzc_R_lcm_223.
Print Assumptions piu_zzc_cP_223.
Print Assumptions piu_zzc_c2_223.
Print Assumptions piu_zzc_Lambda_223_rec_band.
Print Assumptions piu_zzc_bai_vertex.
Print Assumptions piu_zzc_R_lcm_bai.
Print Assumptions piu_zzc_cP_bai.
Print Assumptions piu_zzc_c2_bai.
Print Assumptions piu_zzc_bai_ratio.
Print Assumptions piu_zzc_Lambda_bai_rec_floor13.
Print Assumptions piu_zzc_Lambda_bai_rec_band.
Print Assumptions piu_zzc_bai_below_zz.
Print Assumptions piu_zzc_giraudin_matches_zz_223.
Print Assumptions piu_zzc_machin_01.
Print Assumptions piu_zzc_prim_01.
Print Assumptions piu_zzc_machin_02.
Print Assumptions piu_zzc_prim_02.
Print Assumptions piu_zzc_machin_03.
Print Assumptions piu_zzc_prim_03.
Print Assumptions piu_zzc_machin_04.
Print Assumptions piu_zzc_prim_04.
Print Assumptions piu_zzc_machin_05.
Print Assumptions piu_zzc_prim_05.
Print Assumptions piu_zzc_machin_06.
Print Assumptions piu_zzc_prim_06.
Print Assumptions piu_zzc_machin_07.
Print Assumptions piu_zzc_prim_07.
Print Assumptions piu_zzc_machin_08.
Print Assumptions piu_zzc_prim_08.
Print Assumptions piu_zzc_machin_09.
Print Assumptions piu_zzc_prim_09.
Print Assumptions piu_zzc_machin_10.
Print Assumptions piu_zzc_prim_10.
Print Assumptions piu_zzc_machin_11.
Print Assumptions piu_zzc_prim_11.
Print Assumptions piu_zzc_machin_12.
Print Assumptions piu_zzc_prim_12.
Print Assumptions piu_zzc_machin_13.
Print Assumptions piu_zzc_prim_13.
Print Assumptions piu_zzc_machin_14.
Print Assumptions piu_zzc_prim_14.
Print Assumptions piu_zzc_machin_15.
Print Assumptions piu_zzc_prim_15.
Print Assumptions piu_zzc_machin_16.
Print Assumptions piu_zzc_prim_16.
