(* ConstructiveWorld-Set -- explicit escape-point instances of the quadratic-irrationality separation criterion. *)

(** * u5c_inst_sqrt3: separation of sqrt 3 from every rational by explicit escape points.

    Mission.  For every rational [q], the witness [is3_escape q] provides an
      explicit escape point [n0] of the Newton sequence [is3_x] (x(0) = 2,
      x(n+1) = (x(n) + 3 / x(n)) / 2), whose error gauge [is3_e]
      (e(n) = (x(n)^2 - 3) / 2) vanishes along [is3_tail]; the general
      separation lemma [u5c_escape_to_dist] then yields a positive rational
      constant [c] with [real_const c] strictly below the distance from
      sqrt 3 to [q].  Main statement: [u5c_sqrt3_criterion_escape_pt].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Bool.Bool], [Extraction].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [SumInvFactEscape],
      [UpReqBanachNormOpp], [UpReqIrrationalCriterion],
      [UpReqSqrt3Irrational], [u5c_bridge] of this development.

    References.  This development, u5c_inst_sqrt3.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" u5c_inst_sqrt3.v] compiles cleanly
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

Theorem u5c_sqrt3_criterion_escape_pt : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) is3_x
                            (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
       (real_const q)))).
Proof.
  intro q.
  destruct (is3_escape q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist is3_x is3_e is3_tail is3_vanish q n0 Hn01 Hesc).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_sqrt3_criterion_escape_pt.

Print Assumptions u5c_sqrt3_criterion_escape_pt.
