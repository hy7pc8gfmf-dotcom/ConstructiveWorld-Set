(* ConstructiveWorld-Set -- constructive analysis over Q with every statement face carried by [Set]. *)

(** * tlw1729_negform: negative-form witnesses for the tail of the conv(V_2, altser) coefficient sequence.

    Mission.  The tail-head absolute values of conv(V_2, altser) are not
      monotone at n = 1: [conv_head_nonmono_n1] and its rational-literal
      anchor [conv_head_nonmono_n1_literal] decide 12/35 < 8/21 as a
      decidable conjunction on the Q order; [kappa_nat] computes the tail
      ratio threshold kappa_n = 2n^2 + n - 2; [b_route_mono_fail] casts the
      failure of the tail ratio relation as a dependent pair of nat
      witnesses with residual fiber [bid]; [b_route_mono_fail_witness]
      supplies the witness (n, k) = (1, 0).

    Dependencies.  Requires [tlw1463_pade_table] of this development
      ([bid], [bidI], [vconv], [padeV], [altser]).  Stdlib:
      [QArith], [QArith.Qabs], [ZArith], [List].

    References.  This development, tlw1729_negform.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).  Anchor style
      follows [tlw1463_pade_table] (Mahler 1953, Lambert fraction for pi).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" tlw1729_negform.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import tlw1463_pade_table.

(* ------------------------------------------------------------------ *)
(* Negative form at n = 1: the tail-head absolute values of            *)
(* conv(V_2, altser) increase at the head, b_0 = |c_3| = 12/35 <       *)
(* b_1 = |c_4| = 8/21, decided on the table machinery.  The strict     *)
(* order is carried as the decidable conjunction of b_0 <= b_1 and     *)
(* the negation of b_1 <= b_0 on the Q order.                          *)
(* ------------------------------------------------------------------ *)
Lemma conv_head_nonmono_n1 :
  bid (andb (Qle_bool (Qabs (nth 3 (vconv (padeV 2) (altser 6)) 0%Q))
                      (Qabs (nth 4 (vconv (padeV 2) (altser 6)) 0%Q)))
            (negb (Qle_bool (Qabs (nth 4 (vconv (padeV 2) (altser 6)) 0%Q))
                            (Qabs (nth 3 (vconv (padeV 2) (altser 6)) 0%Q)))))
       true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* Auxiliary literal anchor for the same comparison at rational        *)
(* literals: 12/35 < 8/21 (cross-multiplied, 252 < 280), carried as    *)
(* the same decidable conjunction on the Q order.                      *)
Lemma conv_head_nonmono_n1_literal :
  bid (andb (Qle_bool (12 # 35)%Q (8 # 21)%Q)
            (negb (Qle_bool (8 # 21)%Q (12 # 35)%Q)))
       true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* kappa_n = 2n^2 + n - 2, the exact threshold of the tail ratio       *)
(* relation b_{k+1} < b_k iff 2k > kappa_n, as a computable nat        *)
(* function.  Only the witness n = 1 is consumed below; nat            *)
(* subtraction underflows at n = 0 (giving kappa_0 = 0), which does    *)
(* not affect that witness.                                            *)
(* ------------------------------------------------------------------ *)
Definition kappa_nat (n : nat) : nat := (2 * n * n + n - 2)%nat.

(* ------------------------------------------------------------------ *)
(* Negative form with explicit witness: there exist n and k with       *)
(* k < kappa_n and b_{k+1} >= b_k, where                               *)
(* b_j := |conv(V_{2n}, altser)[2n+1+j]|.  The statement is a          *)
(* dependent pair over two nat witnesses whose residual fiber is the   *)
(* Set-level boolean carrier bid -- informative, not Prop.              *)
(* ------------------------------------------------------------------ *)
Definition b_route_mono_fail : Set :=
  sigT (fun n : nat =>
    sigT (fun k : nat =>
      bid (andb (Z.ltb (Z.of_nat k) (Z.of_nat (kappa_nat n)))
                (Qle_bool
                   (Qabs (nth (2 * n + 1 + k)
                              (vconv (padeV (2 * n)) (altser (2 * n + 6))) 0%Q))
                   (Qabs (nth (2 * n + 2 + k)
                              (vconv (padeV (2 * n)) (altser (2 * n + 6))) 0%Q))))
           true)).

(* The explicit witness (n, k) = (1, 0): k = 0 < kappa_1 = 1 and       *)
(* b_1 = 8/21 >= b_0 = 12/35, so tail-head monotonicity fails.         *)
Lemma b_route_mono_fail_witness : b_route_mono_fail.
Proof.
  exists 1%nat. exists 0%nat.
  apply bidI. vm_compute. reflexivity.
Qed.

(* ---- per-statement closure audit by [Print Assumptions]. ---- *)
Print Assumptions conv_head_nonmono_n1.
Print Assumptions conv_head_nonmono_n1_literal.
Print Assumptions kappa_nat.
Print Assumptions b_route_mono_fail.
Print Assumptions b_route_mono_fail_witness.
