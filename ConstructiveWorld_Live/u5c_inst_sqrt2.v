(* ConstructiveWorld-Set -- constructive analysis over Q with every statement face carried by [Set]. *)

(** * u5c_inst_sqrt2: explicit escape-point separation constant for the Newton sequence of the square root of 2.

    Mission.  Formalize the irrationality separation theorem for the
      Newton sequence [ir2_x] with [x 0 = 2] and [x (S n) = (x n + 2 / x n) / 2]:
      for every rational [q] the escape-point witness of [ir2_escape], with
      [ir2_e n0 < |q - x n0|], feeds the generic separation lemma
      [u5c_escape_to_dist] and yields a positive rational constant
      [c = (|q - x n0| - ir2_e n0) / 2] with [QltT 0 c] and
      [real_const c < |sqrt2 - q|].  Main statement:
      [u5c_sqrt2_criterion_escape_pt].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [SumInvFactEscape], [UpReqBanachNormOpp],
      [UpReqIrrationalCriterion], [UpReqSqrt3Irrational] and
      [u5c_bridge] of this development.  Stdlib: [QArith.QArith],
      [QArith.Qabs], [ZArith.ZArith], [Arith.Arith] and [Bool.Bool].

    References.  This development, u5c_inst_sqrt2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" u5c_inst_sqrt2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.

Theorem u5c_sqrt2_criterion_escape_pt : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                            (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
       (real_const q)))).
Proof.
  intro q.
  destruct (ir2_escape q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist ir2_x ir2_e ir2_tail ir2_vanish q n0 Hn01 Hesc).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_sqrt2_criterion_escape_pt.

Print Assumptions u5c_sqrt2_criterion_escape_pt.
