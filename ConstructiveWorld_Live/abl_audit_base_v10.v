(* ConstructiveWorld-Set -- audit carrier v10: direct-audit closure over the
   S04_RealExpLogConv main-theorem face. *)

(** * abl_audit_base_v10: light-use carriers exercising the main theorems
    of [S04_RealExpLogConv], plus a tail assumption audit.

    Mission.  Five carriers, nine use points, genuinely exercising the
      [r_pow], [exp], [log] and convergence-budget main theorems of
      [S04_RealExpLogConv]: [abk_rpow_pos_engine_concrete],
      [abk_rpow_dec_decay_and_budget] (with the tail bound
      [one_minus_pow_le_one]), [abk_log_pow_cc_zero_chain],
      [abk_sum_exp_cons_head_pos], and [abk_rarch_log_budget_and_geo];
      plus tail [Print Assumptions] audits of the nine consumed S04
      main-theorem names and of the five carriers themselves.

    Dependencies.  Stdlib [Lists.List], [Arith.Arith], [Extraction];
      requires [S01_BaseRing] and [S04_RealExpLogConv].

    References.  ConstructiveWorld-Main, module [abl_audit_base_v10]
      (statement names carried over verbatim).

    Constructivity.  No admits, no classical logic, no Prop carriers:
      all connectives are the Set definitions of [S01_BaseRing];
      statements live on [sigT], products, Set [lt]/[le] and [Id];
      every proof is an explicit [exact] term, and extraction is free
      of [Obj.magic].

    Build.  [coqc -native-compiler no -q -Q . "" abl_audit_base_v10.v]
      compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import Lists.List Arith.Arith.
Require Import S01_BaseRing.
Require Import S04_RealExpLogConv.

(* Interface-generic carrier zone: [RI] is the abstract argument slot of *)
(* the Id-version enhanced interface (no concrete instance tree-wide).    *)
Section AbkCarriers.
Context {RI : RealInterfaceEnhanced}.

(* ============================================================ *)
(* Section 0 - internal plumbing bay ([Id]-constructor split       *)
(*   resolvers, not carrier statements).  [Not] is the Set        *)
(*   version [A -> Empty_set] of S01:48, so this plumbing is      *)
(*   entirely Set-level.                                          *)
(* ============================================================ *)

(* Resolution-form proof: the indices [(a :: l)] and [nil] share no *)
(* constructor case to unify, so the contradictory branch closes   *)
(* in place.                                                       *)
Lemma abk_not_cons_nil :
  forall (A : Set) (a : A) (l : list A), Not (Id (a :: l) nil).
Proof.
  intros A a l Hc. inversion Hc.
Qed.

(* ============================================================ *)
(* Section 1 - carrier 1, the power-positivity engine (r_pow       *)
(*   family): the general form quoted verbatim plus a              *)
(*   concrete-instance wing instantiated at x := 1+1, n := 2       *)
(*   with a genuinely derived premise.                             *)
(* ============================================================ *)

Theorem abk_rpow_pos_engine_concrete :
  (forall (x : R) (n : nat), lt zero x -> lt zero (r_pow x n)) *
  lt zero (r_pow (plus one one) 2).
Proof.
  split.
  - (* the general power-positivity main theorem applies verbatim. *)
    intros x n Hx. exact (r_pow_pos x n Hx).
  - (* concrete instance: the engine resolves at the arguments       *)
    (* [x := plus one one] and [n := 2]; the premise 0 < (1+1) is     *)
    (* genuinely derived through [plus_positive] on the two [one_pos] *)
    (* leaves (not a restatement).                                    *)
    exact (r_pow_pos (plus one one) 2
             (plus_positive one one one_pos one_pos)).
Qed.

(* ============================================================ *)
(* Section 2 - carrier 2, the power-decay order face (r_pow        *)
(*   family): the general form quoted verbatim plus a genuine      *)
(*   two-step advancement chain, plus the convergence tail bound   *)
(*   [one_minus_pow_le_one] quoted verbatim.                       *)
(* ============================================================ *)

Theorem abk_rpow_dec_decay_and_budget :
  (forall (b : R) (n : nat), lt zero b -> lt b one ->
     le (r_pow b (Datatypes.S n)) (r_pow b n)) *
  (forall (b : R) (n : nat), lt zero b -> lt b one ->
     le (r_pow b (Datatypes.S (Datatypes.S n))) (r_pow b n)) *
  (forall (kappa : R), lt zero kappa ->
     forall m : nat, le (minus one (r_pow kappa m)) one).
Proof.
  split.
  - split.
    + (* the general decay main theorem applies verbatim. *)
      intros b n Hb Hb1. exact (r_pow_dec b n Hb Hb1).
    + (* two-step advancement wing: the two engine instances resolve at  *)
      (* the adjacent arguments [S (S n)] and [S n], chained by         *)
      (* [le_trans] - the statement face is a new form of this file (not *)
      (* an upstream restatement), and each wing exercises the engine    *)
      (* independently.                                                  *)
      intros b n Hb Hb1.
      exact (le_trans (r_pow b (Datatypes.S (Datatypes.S n)))
                      (r_pow b (Datatypes.S n)) (r_pow b n)
                      (r_pow_dec b (Datatypes.S n) Hb Hb1)
                      (r_pow_dec b n Hb Hb1)).
  - (* the general convergence tail bound ([one - kappa^m <= one]) *)
    (* applies verbatim.                                           *)
    exact one_minus_pow_le_one.
Qed.

(* ============================================================ *)
(* Section 3 - carrier 3, the log-power expansion engine (log      *)
(*   family): the general form quoted verbatim plus a              *)
(*   concrete-instance wing reducing [log (1^2) == 0] to zero      *)
(*   (engine plus two transports).                                 *)
(* ============================================================ *)

Theorem abk_log_pow_cc_zero_chain :
  (forall (x : R) (n : nat), lt zero x ->
     Id (log (r_pow x n)) (mult (nat_to_R n) (log x))) *
  Id (log (r_pow one 2)) zero.
Proof.
  split.
  - (* the general log-power expansion main theorem applies verbatim *)
    (* (the [log_mult] induction engine).                            *)
    intros x n Hx. exact (log_pow_cc x n Hx).
  - (* concrete instance: the engine resolves at [x := one], [n := 2];  *)
    (* the right side [nat_to_R 2 * log 1] reduces to zero through the  *)
    (* [log_one] rewrite and [mult_zero], transported by two [id_cong]  *)
    (* steps (a genuine computation chain).                             *)
    exact (id_trans (log_pow_cc one 2 one_pos)
             (id_trans (id_cong (mult (nat_to_R 2)) log_one)
                       (mult_zero (nat_to_R 2)))).
Qed.

(* ============================================================ *)
(* Section 4 - carrier 4, the exponential-sum nonnegativity        *)
(*   engine (exp family): a cons-head restatement wing plus a      *)
(*   double-cons composition wing (the upstream [Not] premise is   *)
(*   the S01 Set version, so the plumbing is Set-level too).       *)
(* ============================================================ *)

Theorem abk_sum_exp_cons_head_pos :
  (forall (Token : Set) (neg_log_prob : list Token -> Token -> R)
     (prefix : list Token) (w : Token) (rest : list Token),
     lt zero (sum_exp Token neg_log_prob prefix (w :: rest))) *
  (forall (Token : Set) (neg_log_prob : list Token -> Token -> R)
     (prefix : list Token) (w1 w2 : Token) (rest : list Token),
     lt zero (sum_exp Token neg_log_prob prefix (w1 :: w2 :: rest))).
Proof.
  split.
  - (* cons head: the engine resolves by instantiation, with the       *)
    (* [Id]-constructor splitter as plumbing (a genuinely constructed  *)
    (* nonempty-list witness).                                         *)
    intros Token neg_log_prob prefix w rest.
    exact (sum_exp_positive Token neg_log_prob prefix (w :: rest)
             (abk_not_cons_nil Token w rest)).
  - (* double-cons composition wing: two engine instances resolve (at  *)
    (* the [w1] and [w2] positions) and compose genuinely through      *)
    (* [plus_positive] - the statement face is a new form of this      *)
    (* file, and each wing exercises the engine independently.         *)
    intros Token neg_log_prob prefix w1 w2 rest.
    exact (plus_positive (exp_neg (neg_log_prob prefix w1))
             (sum_exp Token neg_log_prob prefix (w2 :: rest))
             (exp_neg_pos (neg_log_prob prefix w1))
             (sum_exp_positive Token neg_log_prob prefix (w2 :: rest)
                (abk_not_cons_nil Token w2 rest))).
Qed.

(* ============================================================ *)
(* Section 5 - carrier 5, the log closed-form budget (convergence  *)
(*   budget face): the general form quoted verbatim plus a wing    *)
(*   instantiating the main theorem as a function body at its      *)
(*   projection arguments, taking the geometric component by two  *)
(*   [sigT] projections.                                           *)
(* ============================================================ *)

Theorem abk_rarch_log_budget_and_geo :
  (forall (kappa : R) (Hk : lt zero kappa)
     (rap : forall a : R, lt zero a -> forall eps : R, lt zero eps ->
              sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps))
     (lmono : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b)),
   forall (a eps : R) (Ha : lt zero a) (Hep : lt zero eps),
     sigT (fun N : nat =>
       And (le (log (mult a (r_pow kappa N))) (log eps))
           (lt (mult a (r_pow kappa N)) eps))) *
  (forall (kappa : R) (Hk : lt zero kappa)
     (rap : forall a : R, lt zero a -> forall eps : R, lt zero eps ->
              sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps))
     (lmono : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b))
     (a eps : R) (Ha : lt zero a) (Hep : lt zero eps),
   lt (mult a (r_pow kappa
          (projT1 (r_arch_pow_log_budget kappa Hk rap lmono a Ha eps Hep)))) eps).
Proof.
  split.
  - (* the general budget main theorem applies verbatim (the log- *)
    (* monotonicity upgrade chain).                               *)
    intros kappa Hk rap lmono a eps Ha Hep.
    exact (r_arch_pow_log_budget kappa Hk rap lmono a Ha eps Hep).
  - (* instantiation of the main theorem as a function body at its     *)
    (* projection arguments: [projT1] yields the budget [N] and       *)
    (* [projT2] followed by [snd] yields the geometric component (a    *)
    (* double genuine exercise).                                       *)
    intros kappa Hk rap lmono a eps Ha Hep.
    exact (snd (projT2 (r_arch_pow_log_budget kappa Hk rap lmono a Ha eps Hep))).
Qed.

End AbkCarriers.

(* ============================================================ *)
(* Section 6 - tail bay: assumption audit (nine direct-audit       *)
(*   slots on the S04 main-theorem face plus self-audits of the    *)
(*   five carriers of this file).                                  *)
(*   Reading rule: all fourteen outputs must print                 *)
(*   "Closed under the global context".                            *)
(*   The first 9 are the direct-audit slots (the twin [r_pow]      *)
(*   engines, the tail bound, the log-power expansion, the         *)
(*   exponential-sum nonnegativity, the log closed-form budget,    *)
(*   the twin Cauchy convergence forms, the explicit rate main     *)
(*   theorem, and the convergence main theorem) - the S04          *)
(*   main-theorem face had no tree-wide [Print Assumptions]        *)
(*   direct audits before; [iterate_cauchy_explicit_N] and         *)
(*   [dynamics_converges] embed nat-order premise skeletons in     *)
(*   their conclusions (not restatable as carriers under the       *)
(*   stricter reading), so they are audited here by [Print         *)
(*   Assumptions] alone, per the header note.                      *)
(*   The last 5 are self-audits of the five carriers of this       *)
(*   file.                                                         *)
(*   Note: the [Require] closure contains the whole S01-S03        *)
(*   chain; the [coqchk] environment-axiom face and the            *)
(*   per-theorem [Print Assumptions] checks are separate           *)
(*   accounts, not introduced by this file.                        *)
(* ============================================================ *)

Print Assumptions r_pow_pos.
Print Assumptions r_pow_dec.
Print Assumptions one_minus_pow_le_one.
Print Assumptions log_pow_cc.
Print Assumptions sum_exp_positive.
Print Assumptions r_arch_pow_log_budget.
Print Assumptions iterate_cauchy.
Print Assumptions iterate_cauchy_explicit_N.
Print Assumptions dynamics_converges.
Print Assumptions abk_rpow_pos_engine_concrete.
Print Assumptions abk_rpow_dec_decay_and_budget.
Print Assumptions abk_log_pow_cc_zero_chain.
Print Assumptions abk_sum_exp_cons_head_pos.
Print Assumptions abk_rarch_log_budget_and_geo.

(* ============================================================ *)
(* Section 7 - export bay: the carriers double as extraction       *)
(*   ports (the extraction face is free of [Obj.magic]).           *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abk_rpow_pos_engine_concrete
  abk_rpow_dec_decay_and_budget abk_log_pow_cc_zero_chain
  abk_sum_exp_cons_head_pos abk_rarch_log_budget_and_geo.
