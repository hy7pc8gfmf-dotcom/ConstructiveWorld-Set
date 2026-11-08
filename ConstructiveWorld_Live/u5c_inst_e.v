(* ConstructiveWorld-Set -- constructive analysis over Q with every statement face carried by [Set]. *)

(** * u5c_inst_e: explicit escape-point separation constant for the exponential series of e.

    Mission.  Formalize the irrationality separation theorem for the natural
      exponential series [X] with [x n = exp_series n 1], the limit of the
      partial sums of [1 / j!]: for every rational [q] the escape-point
      witness of [lic_witness_e], with [1 / q_fact n0 < |q - x n0|], feeds
      [u5c_escape_to_dist] and yields [c = (|q - x n0| - 1 / q_fact n0) / 2]
      with [QltT 0 c] and [real_const c < |X - q|].  Main statement:
      [u5c_e_criterion_escape_pt].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [SumInvFactEscape], [UpReqBanachNormOpp], [UpReqIrrationalCriterion]
      and [u5c_bridge] of this development.  Stdlib: [QArith.QArith],
      [QArith.Qabs], [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
      [Arith.Factorial], [Setoid], [Morphisms] and [Qfield].

    References.  This development, u5c_inst_e.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" u5c_inst_e.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

Theorem u5c_e_criterion_escape_pt : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
                            (fun n => exp_series n 1)
                            (lic_seq_cauchy (fun n => exp_series n 1)
                                            (fun n => 1%Q / q_fact n)
                                            lic_tail_e lic_vanish_e))
       (real_const q)))).
Proof.
  intro q.
  destruct (lic_witness_e q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist (fun n => exp_series n 1) (fun n => 1%Q / q_fact n)
           lic_tail_e lic_vanish_e q n0 Hn01 Hesc).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_e_criterion_escape_pt.

Print Assumptions u5c_e_criterion_escape_pt.
