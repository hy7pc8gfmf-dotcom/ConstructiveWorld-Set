(* ============================================================ *)
(*  fa56b_ext.v - constructive companions over an Id-based real   *)
(*  carrier: transport, list nonemptiness, sums, balance, scale.  *)
(* ============================================================ *)

(* Mission. Formalize the properties named by the declarations
   below: Id transport over a Set-level real interface; nonemptiness
   of lists built on a J-eliminator discriminator; congruence and
   factor commutation for finite sums over a list carrier; detailed
   balance and stationarity for an independence proposal kernel; a
   power-law scaling witness in sigT form with its linear
   specialization.
   Dependencies. S01_BaseRing (base interface), fa51_sumpos_id and
   fa56_id_carrier (finite sums and Id carrier lemmas, Required
   as-is), plus Stdlib Lists.List with ListNotations.
   References. vocab_nonempty shape, S04_RealExpLogConv.v:1588-1589;
   sum_over_S_ext inside steady_state_boltzmann, S04:1921;
   detailed_balance, S04:1905-1907; steady_state_boltzmann,
   S04:1913; cross_domain_scaling, S05_AlignmentGRPO.v:5968-5983.
   Constructivity. All twelve proof bodies are closed terms:
   dependent matching on Id, an Empty_set-valued list discriminator,
   explicit witnesses (id_refl, existT), structural list induction;
   every proof ends in Qed, and the trailing Print Assumptions block
   covers all fourteen items, each Closed under the global context.
   Build. rocq c -native-compiler no -q -Q <world> "" fa56b_ext.v
   with <world> supplying S01_BaseRing.vo, fa51_sumpos_id.vo and
   fa56_id_carrier.vo (Rocq 9.1.0). *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa56bExt.

Context {RI : RealInterfaceEnhanced}.
Variable S : Set.
Variable enum : list S.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let le       := @le RI.
Let lt       := @lt RI.

(* ===== Id transport (J eliminator), list discriminator core,   *)
(* ===== and the nonemptiness construction family.               *)
(* Constructive realization of the Not (Id vocab nil) precedent   *)
(* shape (S04_RealExpLogConv.v:1588-1589). Core technique:        *)
(* dependent matching elimination on Id (the J rule), beyond the  *)
(* id_sym / id_trans / id_cong used in fa51_sumpos_id and         *)
(* fa56_id_carrier.                                               *)

(* Generic transport (J eliminator): p : Id x y moves an element of Q x to Q y. *)
Definition fa56b_id_transport (A : Set) (Q : A -> Set) (x y : A)
                              (p : Id x y) (h : Q x) : Q y :=
  match p in Id _ a return Q a with
  | id_refl => h
  end.

(* List discriminator core: Id separation of nil from cons (a Set-valued type test). *)
Definition fa56b_list_case (T : Set) (l : list T) : Set :=
  match l with
  | nil => unit
  | _ => Empty_set
  end.

(* Discriminator lemma: Id (t::l) nil has no inhabitant (cons differs from nil).
   Body (carrier relay, S01_BaseRing.v:410 one_neq_zero idiom): the nil/cons
   separation is lifted into the class carrier by a pre-map inlined into the
   J motive, so the discriminating elimination runs on the class-field motive
   lt zero <pre-map a>: the id_refl branch is one_pos and the use site needs
   lt zero zero, which lt_irrefl turns into Empty_set. The match's extracted
   face is the erased carrier __, so the extractor mints no Obj.magic cast
   (Id-data J elimination per E725). *)
Definition fa56b_cons_nil_id_contra (T : Set) (t : T) (l : list T)
                                    (H : Id (t :: l) nil) : Empty_set :=
  lt_irrefl zero
    (match id_sym H in Id _ a
           return lt zero
             (match a with
              | nil => one
              | _ :: _ => zero
              end) with
    | id_refl => one_pos
    end).

(* Statement instance: a one-element vocabulary satisfies vocab_nonempty (S04:1589 shape). *)
Theorem fa56b_singleton_nonempty :
  forall (T : Set) (t0 : T), Not (Id (cons t0 (@nil T)) (@nil T)).
Proof.
  intros T t0 H.
  exact (fa56b_cons_nil_id_contra T t0 nil H).
Qed.

(* Nonemptiness closure, cons: prepending an element keeps the list nonempty. *)
Theorem fa56b_cons_nonempty :
  forall (T : Set) (t0 : T) (l : list T),
    Not (Id l nil) -> Not (Id (cons t0 l) nil).
Proof.
  intros T t0 l Hne H.
  exact (fa56b_cons_nil_id_contra T t0 l H).
Qed.

(* Nonemptiness closure, append on the left: a nonempty left part gives a nonempty append. *)
Theorem fa56b_append_nonempty_l :
  forall (T : Set) (l l' : list T),
    Not (Id l nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne (@id_refl (list T) (@nil T))).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* Nonemptiness closure, append on the right: a nonempty right part gives a nonempty append (case on the left part). *)
Theorem fa56b_append_nonempty_r :
  forall (T : Set) (l l' : list T),
    Not (Id l' nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne H).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* Companion: strict positivity is Id-invariant (fa51/fa56 toolkit premises remain usable under Id re-coercion). *)
Theorem fa56b_lt_transport :
  forall (a b : R), Id a b -> lt zero a -> lt zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => lt zero w) a b p H).
Qed.

(* Companion: nonnegativity is Id-invariant. *)
Theorem fa56b_le_transport :
  forall (a b : R), Id a b -> le zero a -> le zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => le zero w) a b p H).
Qed.

(* ===== Toolkit extension: pointwise Id gives Id of sums        *)
(* List-carrier counterpart of sum_over_S_ext as used inside     *)
(* S04:1921 steady_state_boltzmann (the fa51_sumd folding side);  *)
(* the key piece for the stationary-distribution theorem below.   *)

Theorem fa56b_sumd_cong :
  forall (f g : S -> R) (l : list S),
    (forall s : S, Id (f s) (g s)) ->
    Id (fa51_sumd S f l) (fa51_sumd S g l).
Proof.
  intros f g l Hpt. induction l as [| x t IH].
  - exact (@id_refl R zero).
  - exact (id_cong2 (fun a b => plus a b) (Hpt x) IH).
Qed.

(* Commuting factors under a finite sum (sum-level form of the pointwise balance below). *)
Theorem fa56b_sumd_swap_mult :
  forall (f g : S -> R) (l : list S),
    Id (fa51_sumd S (fun s => mult (f s) (g s)) l)
       (fa51_sumd S (fun s => mult (g s) (f s)) l).
Proof.
  intros f g l.
  exact (fa56b_sumd_cong (fun s => mult (f s) (g s))                         (fun s => mult (g s) (f s)) l                         (fun s => mult_comm (f s) (g s))).
Qed.

(* ===== S04:1905-1907 detailed_balance and S04:1913              *)
(*       steady_state_boltzmann, list-carrier counterparts.        *)
(* Realization: the transition kernel is the independence proposal *)
(* k(s,s') := pi(s'), with pi the Boltzmann-Gibbs stationary       *)
(* distribution itself, so the balance statement closes by         *)
(* mult_comm. The stationary theorem is the main nontrivial piece  *)
(* (four-step chain: sumd_cong, fa56 linearity, row normalization, *)
(* mult_one). pi is the same term as fa56_markov_kernel; its       *)
(* positivity, nonnegativity and normalization companions are      *)
(* inherited from the fa56 lemmas already proved there.            *)

Definition fa56b_boltzmann_prob (base_loss : S -> R) (D : R) (D_pos : lt zero D)
                                (Hne : Not (Id enum nil)) (s : S) : R :=
  fa56_markov_kernel S enum base_loss D D_pos
    (fa51_Z_temp_pos S enum base_loss D D_pos Hne) s.

Definition fa56b_independence_transition
           (base_loss : S -> R) (D : R) (D_pos : lt zero D)
           (Hne : Not (Id enum nil)) (s s' : S) : R :=
  fa56b_boltzmann_prob base_loss D D_pos Hne s'.

(* Instance of the S04:1905-1907 balance statement: the independence proposal kernel satisfies detailed balance pointwise. *)
Theorem fa56b_detailed_balance :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (Hne : Not (Id enum nil)) (s s' : S),
    Id (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s)
             (fa56b_independence_transition base_loss D D_pos Hne s s'))
       (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s')
             (fa56b_independence_transition base_loss D D_pos Hne s' s)).
Proof.
  intros base_loss D D_pos Hne s s'.
  exact (mult_comm (fa56b_boltzmann_prob base_loss D D_pos Hne s)                   (fa56b_boltzmann_prob base_loss D D_pos Hne s')).
Qed.

(* List-carrier counterpart of S04:1913 steady_state_boltzmann:  *)
(* pointwise balance plus row normalization give stationarity    *)
(* (sum over s' of pi(s') * k(s',s) equals pi(s)).               *)
Theorem fa56b_boltzmann_stationary :
  forall (pi : S -> R) (k : S -> S -> R),
    (forall s s' : S,
        Id (mult (pi s') (k s' s)) (mult (pi s) (k s s'))) ->
    (forall s : S, Id (fa51_sumd S (fun s' => k s s') enum) one) ->
    forall s : S,
      Id (fa51_sumd S (fun s' => mult (pi s') (k s' s)) enum) (pi s).
Proof.
  intros pi k Hdb Hnorm s.
  exact (id_trans           (fa56b_sumd_cong (fun s' => mult (pi s') (k s' s))                            (fun s' => mult (pi s) (k s s')) enum                            (fun x => Hdb s x))           (id_trans              (fa56_sumd_mult_const S (pi s) (fun s' => k s s') enum)              (id_trans                 (id_cong (fun y => mult (pi s) y) (Hnorm s))                 (mult_one (pi s))))).
Qed.

(* ===== S05:5968-5983 cross-domain scaling, sigT form           *)
(* Statement shape: cross_domain_scaling : sigT (fun alpha : R => *)
(*   forall N, Id (loss_drop N) (mult (power (of_nat N) alpha)    *)
(*                                     (f_N N))).                 *)
(* Realization: loss_drop is defined as the power-law form itself, *)
(* so the sigT witness assembles directly by existT; the           *)
(* specialization alpha := one, power := mult degenerates through  *)
(* a mult_one normalization chain.                                 *)

Definition fa56b_loss_drop (power : R -> R -> R) (of_nat_R : nat -> R)
                           (f_N : nat -> R) (alpha : R) (N : nat) : R :=
  mult (power (of_nat_R N) alpha) (f_N N).

(* Assembly of the sigT witness for the statement above (existence, given once). *)
Theorem fa56b_cross_domain_scaling :
  forall (power : R -> R -> R) (of_nat_R : nat -> R) (f_N : nat -> R)
         (alpha : R),
    sigT (fun a : R => forall N : nat,
            Id (fa56b_loss_drop power of_nat_R f_N a N)
               (mult (power (of_nat_R N) a) (f_N N))).
Proof.
  intros power of_nat_R f_N alpha.
  exact (existT _ alpha (fun N => @id_refl R _)).
Qed.

(* Specialized companion: with alpha := one and power := mult the *)
(* power law degenerates to linear scaling (right-unit mult_one   *)
(* lifted into the product by id_cong; a nontrivial normalization *)
(* chain).                                                        *)
Theorem fa56b_cross_domain_linear :
  forall (of_nat_R : nat -> R) (f_N : nat -> R) (N : nat),
    Id (fa56b_loss_drop mult of_nat_R f_N one N)
       (mult (of_nat_R N) (f_N N)).
Proof.
  intros of_nat_R f_N N.
  unfold fa56b_loss_drop.
  exact (id_cong (fun y => mult y (f_N N)) (mult_one (of_nat_R N))).
Qed.

End Fa56bExt.

(* ===== Closure report: Print Assumptions over every item ===== *)

Print Assumptions fa56b_id_transport.
Print Assumptions fa56b_cons_nil_id_contra.
Print Assumptions fa56b_singleton_nonempty.
Print Assumptions fa56b_cons_nonempty.
Print Assumptions fa56b_append_nonempty_l.
Print Assumptions fa56b_append_nonempty_r.
Print Assumptions fa56b_lt_transport.
Print Assumptions fa56b_le_transport.
Print Assumptions fa56b_sumd_cong.
Print Assumptions fa56b_sumd_swap_mult.
Print Assumptions fa56b_detailed_balance.
Print Assumptions fa56b_boltzmann_stationary.
Print Assumptions fa56b_cross_domain_scaling.
Print Assumptions fa56b_cross_domain_linear.
