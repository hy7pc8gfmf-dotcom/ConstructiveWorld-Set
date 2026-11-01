(* u5c_aux_natpow_discharge - premise-free discharge companions for the
   registered nat power bounds of the sqrt(2) closed-form separation family.
   Mission. Two unconditional Set-layer refinements (P' x 2):
     u5c_pow12' : forall k : nat, NatLe (12 * k * k) (2 ^ (k + 5))%nat
     u5c_pow4'  : forall k : nat, NatLe (4 * k * k) (2 ^ (k + 3))%nat
   Discharge basis: the (1 <= k)%nat premise of the premise-carrying forms is
   artificial - at k = 0 both conclusions hold trivially (12*0*0 = 0 <=
   2^5 = 32, 4*0*0 = 0 <= 2^3 = 8), so the unconditional statements hold on
   the whole domain. Honest interface note: the 64-bound premise (1 <= k)%nat
   is mathematically necessary (at k = 0, 2^5 = 32 < 64) and stays registered;
   the escape point n0 = den(q) + 3 >= 4 sits inside that premise domain.
   Non-trivial attainment: self-contained full-range induction, never invoking
   the premise-carrying forms: bases k = 0 and k = 1,2,3 close by pointwise
   computation; the k >= 4 step is preserved by (k+1)^2 <= 2k^2 (nia product
   split, lia linear close) over the induction invariant; the step rewrite
   reuses the definitional fold law 2^(S a + b) = 2 * 2^(a + b) (reflexivity).
   Dependencies. S01_BaseRing, S02_CauchyComplete (Id/NatLe carriers,
   NatLe_lift/NatLe_drop bridges), read-only; u5c_aux_natpow (nat power base
   library), read-only; Stdlib QArith.QArith, QArith.Qabs, ZArith.ZArith, Lia.
   The nat_scope reading of `_ ^ _` is supplied by this Require chain (a bare
   natpow + Lia Require was measured insufficient).
   References. S01_BaseRing.v NatLe_lift, NatLe_drop; u5c_aux_natpow.v
   u5c_pow12, u5c_pow4 (the premise-carrying family forms discharged here).
   Constructivity. Statements carry the Set-layer carrier NatLe; proofs lift
   to the Prop-face order via NatLe_lift, closing by induction with numeric
   bases and nia/lia on auxiliary bounds only; the fold law is asserted in
   eq-face by reflexivity; both lemmas close under the global context.
   Build. Rocq 9.1: rocq c -native-compiler no -q -Q . ""
   u5c_aux_natpow_discharge.v in the module directory (dependencies compiled
   alongside) after sourcing the toolchain environment. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import u5c_aux_natpow.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* P'-1: unconditional 12-square bound.                          *)
(* ============================================================ *)

(* 12k^2 <= 2^(k+5) for all k (including k = 0). Self-contained full-range
   induction: base k = 0 closes numerically, k = 1,2,3 close by pointwise
   computation, and the k >= 4 step preserves through the nia product split
   (k+1)^2 <= 2k^2 joined with the induction invariant. *)
Lemma u5c_pow12' : forall k : nat, NatLe (12 * k * k) (2 ^ (k + 5))%nat.
Proof.
  intro k.
  apply NatLe_lift.
  induction k as [| k IH].
  - cbn. lia.
  - destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + assert (Hsh : forall a b : nat,
                    (2 ^ (Datatypes.S a + b))%nat = (2 * 2 ^ (a + b))%nat)
        by (intros; reflexivity).
      rewrite !Hsh in IH.
      rewrite !Hsh.
      assert (E1 : (12 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (12 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

(* ============================================================ *)
(* P'-2: unconditional 4-square bound.                           *)
(* ============================================================ *)

(* 4k^2 <= 2^(k+3) for all k (including k = 0). Same full-range induction
   shape as the 12 bound: (k+3)^2 <= 2(k+2)^2 holds for all k >= 0 and
   preserves the step; bases close by pointwise computation. *)
Lemma u5c_pow4' : forall k : nat, NatLe (4 * k * k) (2 ^ (k + 3))%nat.
Proof.
  intro k.
  apply NatLe_lift.
  induction k as [| k IH].
  - cbn. lia.
  - destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + assert (Hsh : forall a b : nat,
                    (2 ^ (Datatypes.S a + b))%nat = (2 * 2 ^ (a + b))%nat)
        by (intros; reflexivity).
      rewrite !Hsh in IH.
      rewrite !Hsh.
      assert (E1 : (4 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (4 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

Print Assumptions u5c_pow12'.
Print Assumptions u5c_pow4'.
