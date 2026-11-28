(* ========================================================================= *)
(* Module   : sharp_const                                                   *)
(* Mission. Spectrum theorem for the sharpness constant of integer pair     *)
(*    threads: the pair-threading generator gp of a 2x2 integer matrix,     *)
(*    its adjacent determinants sdet (row 1, the constant carrier E) and    *)
(*    cross (mixed rows, the core G); identities cross_n = (ad-bc)^n G0,    *)
(*    E_n = b G_n, E'_n = -c G_n; closed forms sc_general (det=1) and       *)
(*    sc_general_alt (det=-1); explicit classes T=1 with B=1 (sc_T1,        *)
(*    |E|=1) and T=2 with B=a1, denominator of the first member (sc_T2);    *)
(*    the D=13 rotation block on row 2 (E'_n = 5(-1)^n); the Pell (D=m^2+1),*)
(*    D=3, D=6, D=13 family determinants recovered, plus seven numeric pins.*)
(* Dependencies. S01_BaseRing (Id, id_refl); fib_machine (powneg1,          *)
(*    powneg1_S, zabs_powneg1); pell_family (pellpair/qelpair, pellx/pelly, *)
(*    Id_eq/eq_Id); d3_family, d6_family, d13_family; Stdlib ZArith, Lia,   *)
(*    Extraction.                                                           *)
(* References. ConstructiveWorld-Main sharp_const.v (statement names kept;  *)
(*    statement-face Prop equalities replaced by the Set identity type Id). *)
(* Constructivity. Statement faces are Set-carried only: equalities via     *)
(*    Id, det premises via ZeqT := Id (Z.eqb a b) true (ZLeT precedent);    *)
(*    no Prop connective on any statement face. Proof bodies are            *)
(*    constructive Prop derivations on Z (ring) discharged through eq_Id    *)
(*    and bridged back by Id_eq/ZeqT_drop/ZeqT_lift, so Qed closes only     *)
(*    pure-Prop proof bodies of Set-carried statements (pell_family         *)
(*    precedent); all definitions transparent; vm_compute confined to the   *)
(*    seven numeric pins on closed terms; zero axioms, zero admits, zero    *)
(*    classical logic.                                                      *)
(* Build. rocq c -native-compiler no -q -Q <live root> "" sharp_const.v    *)
(* ========================================================================= *)

Require Import S01_BaseRing (Id, id_refl).
Require Import fib_machine.
Require Import pell_family.
Require Import d3_family.
Require Import d6_family.
Require Import d13_family.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Set-layer kit: decidable equality on Z as a Set-valued        *)
(* statement, in the style of ZLeT in pell_family.               *)
(* ============================================================ *)

Definition ZeqT (a b : Z) : Set := Id (Z.eqb a b) true.

Lemma ZeqT_drop : forall a b : Z, ZeqT a b -> (a = b)%Z.
Proof. intros a b H. exact (proj1 (Z.eqb_eq a b) (Id_eq _ _ H)). Defined.

Lemma ZeqT_lift : forall a b : Z, (a = b)%Z -> ZeqT a b.
Proof. intros a b H. exact (eq_Id _ _ (proj2 (Z.eqb_eq a b) H)). Defined.

(* ============================================================ *)
(* General matrix-stream layer: the gp generator, gx/gy streams, *)
(* the adjacent-row determinant sdet and the cross determinant.  *)
(* ============================================================ *)

(* gp: the pair-threading stream of the 2x2 integer matrix (a,b,c,d) --
   (x_{k+1}, y_{k+1}) = (a x_k + b y_k, c x_k + d y_k).  This is the
   common abstraction of the four pair carriers pellpair, d3pair,
   d6pair and d13pair (Section on specialization bridges). *)
Fixpoint gp (a b c d x0 y0 : Z) (n : nat) : Z * Z :=
  match n with
  | O => (x0, y0)
  | S k => match gp a b c d x0 y0 k with
           | pair x y => ((a * x + b * y)%Z, (c * x + d * y)%Z)
           end
  end.

Definition gx (a b c d x0 y0 : Z) (n : nat) : Z := fst (gp a b c d x0 y0 n).
Definition gy (a b c d x0 y0 : Z) (n : nat) : Z := snd (gp a b c d x0 y0 n).

(* sdet: the adjacent determinant of the first row of the iterates
   (the sharpness-constant carrier E_k). *)
Definition sdet (a b c d x0 y0 z0 w0 : Z) (n : nat) : Z :=
  (gx a b c d x0 y0 n * gx a b c d z0 w0 (S n)
    - gx a b c d x0 y0 (S n) * gx a b c d z0 w0 n)%Z.

(* cross: the companion determinant G of the mixed rows (the core
   carried along by the matrix determinant). *)
Definition cross (a b c d x0 y0 z0 w0 : Z) (n : nat) : Z :=
  (gx a b c d x0 y0 n * gy a b c d z0 w0 n
    - gy a b c d x0 y0 n * gx a b c d z0 w0 n)%Z.

Lemma gp_0 : forall a b c d x0 y0 : Z, Id (gp a b c d x0 y0 0) (x0, y0).
Proof. intros a b c d x0 y0. apply id_refl. Qed.

Lemma gx_0 : forall a b c d x0 y0 : Z, Id (gx a b c d x0 y0 0) x0.
Proof. intros a b c d x0 y0. apply id_refl. Qed.

Lemma gy_0 : forall a b c d x0 y0 : Z, Id (gy a b c d x0 y0 0) y0.
Proof. intros a b c d x0 y0. apply id_refl. Qed.

Lemma gp_unfold : forall (a b c d x0 y0 : Z) (n : nat),
  Id (gp a b c d x0 y0 (S n))
     ((a * fst (gp a b c d x0 y0 n) + b * snd (gp a b c d x0 y0 n))%Z,
      (c * fst (gp a b c d x0 y0 n) + d * snd (gp a b c d x0 y0 n))%Z).
Proof.
  intros a b c d x0 y0 n. cbn [gp]. destruct (gp a b c d x0 y0 n) as [u v].
  apply id_refl.
Qed.

Lemma gx_rec : forall (a b c d x0 y0 : Z) (n : nat),
  Id (gx a b c d x0 y0 (S n))
     (a * gx a b c d x0 y0 n + b * gy a b c d x0 y0 n)%Z.
Proof.
  intros a b c d x0 y0 n. apply eq_Id. unfold gx, gy.
  rewrite (Id_eq _ _ (gp_unfold a b c d x0 y0 n)). reflexivity.
Qed.

Lemma gy_rec : forall (a b c d x0 y0 : Z) (n : nat),
  Id (gy a b c d x0 y0 (S n))
     (c * gx a b c d x0 y0 n + d * gy a b c d x0 y0 n)%Z.
Proof.
  intros a b c d x0 y0 n. apply eq_Id. unfold gy, gx.
  rewrite (Id_eq _ _ (gp_unfold a b c d x0 y0 n)). reflexivity.
Qed.

(* ============================================================ *)
(* Spectrum theorems: the three identities, the closed forms for *)
(* det = 1 and det = -1, the two explicit classes, and the       *)
(* D = 13 rotation-block instance on the second row.             *)
(* ============================================================ *)

(* Identity 1 (step of the core): G_{n+1} = det * G_n -- the matrix
   determinant is multiplicative along the stream. *)
Lemma cross_step : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  Id (cross a b c d x0 y0 z0 w0 (S n))
     ((a * d - b * c) * cross a b c d x0 y0 z0 w0 n)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n. apply eq_Id. unfold cross.
  rewrite (Id_eq _ _ (gx_rec a b c d x0 y0 n)), (Id_eq _ _ (gy_rec a b c d x0 y0 n)),
          (Id_eq _ _ (gx_rec a b c d z0 w0 n)), (Id_eq _ _ (gy_rec a b c d z0 w0 n)).
  ring.
Qed.

(* Identity 2 (row-1 link): E_n = b * G_n -- the sharpness constant is
   the off-diagonal entry of the member row times the core. *)
Lemma sdet_cross : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  Id (sdet a b c d x0 y0 z0 w0 n) (b * cross a b c d x0 y0 z0 w0 n)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n. apply eq_Id. unfold sdet, cross.
  rewrite (Id_eq _ _ (gx_rec a b c d x0 y0 n)), (Id_eq _ _ (gx_rec a b c d z0 w0 n)).
  ring.
Qed.

(* Identity 3 (row-2 link): E'_n = -c * G_n. *)
Lemma sdet_row2 : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  Id (gy a b c d x0 y0 n * gy a b c d z0 w0 (S n)
      - gy a b c d x0 y0 (S n) * gy a b c d z0 w0 n)%Z
     ((- c) * cross a b c d x0 y0 z0 w0 n)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n. apply eq_Id. unfold cross.
  rewrite (Id_eq _ _ (gy_rec a b c d x0 y0 n)), (Id_eq _ _ (gy_rec a b c d z0 w0 n)).
  ring.
Qed.

(* The core is invariant along the stream for det = 1 and alternating
   for det = -1. *)
Lemma cross_det1 : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  ZeqT (a * d - b * c) 1%Z ->
  Id (cross a b c d x0 y0 z0 w0 n) (cross a b c d x0 y0 z0 w0 0).
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (Id_eq _ _ (cross_step a b c d x0 y0 z0 w0 k)),
            (ZeqT_drop _ _ Hdet), (Id_eq _ _ IH). ring.
Qed.

Lemma cross_detm1 : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  ZeqT (a * d - b * c) (-1)%Z ->
  Id (cross a b c d x0 y0 z0 w0 n)
     (powneg1 n * cross a b c d x0 y0 z0 w0 0)%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet. induction n as [|k IH].
  - apply eq_Id. cbn [powneg1]. ring.
  - apply eq_Id.
    rewrite (Id_eq _ _ (cross_step a b c d x0 y0 z0 w0 k)),
            (ZeqT_drop _ _ Hdet), (Id_eq _ _ IH), (Id_eq _ _ (powneg1_S k)). ring.
Qed.

(* Closed form for det = 1: E_n = b * G0 -- the sharpness constant is
   fixed by the off-diagonal entry and the seed core. *)
Theorem sc_general : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  ZeqT (a * d - b * c) 1%Z ->
  Id (sdet a b c d x0 y0 z0 w0 n) (b * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite (Id_eq _ _ (sdet_cross a b c d x0 y0 z0 w0 n)).
  rewrite (Id_eq _ _ (cross_det1 a b c d x0 y0 z0 w0 n Hdet)).
  apply eq_Id. unfold cross.
  rewrite (Id_eq _ _ (gx_0 a b c d x0 y0)), (Id_eq _ _ (gy_0 a b c d x0 y0)),
          (Id_eq _ _ (gx_0 a b c d z0 w0)), (Id_eq _ _ (gy_0 a b c d z0 w0)).
  ring.
Qed.

(* Closed form for det = -1: E_n = b * (-1)^n * G0. *)
Theorem sc_general_alt : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  ZeqT (a * d - b * c) (-1)%Z ->
  Id (sdet a b c d x0 y0 z0 w0 n)
     (b * powneg1 n * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite (Id_eq _ _ (sdet_cross a b c d x0 y0 z0 w0 n)).
  rewrite (Id_eq _ _ (cross_detm1 a b c d x0 y0 z0 w0 n Hdet)).
  apply eq_Id. unfold cross.
  rewrite (Id_eq _ _ (gx_0 a b c d x0 y0)), (Id_eq _ _ (gy_0 a b c d x0 y0)),
          (Id_eq _ _ (gx_0 a b c d z0 w0)), (Id_eq _ _ (gy_0 a b c d z0 w0)).
  ring.
Qed.

(* Closed form for det = 1, row-2 dual. *)
Theorem sc_row2_general : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  ZeqT (a * d - b * c) 1%Z ->
  Id (gy a b c d x0 y0 n * gy a b c d z0 w0 (S n)
      - gy a b c d x0 y0 (S n) * gy a b c d z0 w0 n)%Z
     ((- c) * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite (Id_eq _ _ (sdet_row2 a b c d x0 y0 z0 w0 n)).
  rewrite (Id_eq _ _ (cross_det1 a b c d x0 y0 z0 w0 n Hdet)).
  apply eq_Id. unfold cross.
  rewrite (Id_eq _ _ (gx_0 a b c d x0 y0)), (Id_eq _ _ (gy_0 a b c d x0 y0)),
          (Id_eq _ _ (gx_0 a b c d z0 w0)), (Id_eq _ _ (gy_0 a b c d z0 w0)).
  ring.
Qed.

(* Closed form for det = -1, row-2 dual (the D = 13 configuration). *)
Theorem sc_row2_general_alt : forall (a b c d x0 y0 z0 w0 : Z) (n : nat),
  ZeqT (a * d - b * c) (-1)%Z ->
  Id (gy a b c d x0 y0 n * gy a b c d z0 w0 (S n)
      - gy a b c d x0 y0 (S n) * gy a b c d z0 w0 n)%Z
     ((- c) * powneg1 n * (x0 * w0 - y0 * z0))%Z.
Proof.
  intros a b c d x0 y0 z0 w0 n Hdet.
  rewrite (Id_eq _ _ (sdet_row2 a b c d x0 y0 z0 w0 n)).
  rewrite (Id_eq _ _ (cross_detm1 a b c d x0 y0 z0 w0 n Hdet)).
  apply eq_Id. unfold cross.
  rewrite (Id_eq _ _ (gx_0 a b c d x0 y0)), (Id_eq _ _ (gy_0 a b c d x0 y0)),
          (Id_eq _ _ (gx_0 a b c d z0 w0)), (Id_eq _ _ (gy_0 a b c d z0 w0)).
  ring.
Qed.

(* Explicit class one (the D = m^2 + 1 family, matrix T(2m) = (2m,1;1,0),
   seeds (m,1) and (1,0)): the constant is B = 1 for the whole class,
   E_n = -(-1)^n = (-1)^{n+1}, the shape of the Pell determinant. *)
Theorem sc_T1 : forall (m : Z) (n : nat),
  Id (sdet (2 * m) 1 1 0 m 1 1 0 n) (powneg1 (S n)).
Proof.
  intros m n.
  assert (Hdet : ZeqT (2 * m * 0 - 1 * 1) (-1)%Z) by (apply ZeqT_lift; ring).
  pose proof (sc_general_alt (2 * m)%Z 1 1 0 m 1 1 0 n Hdet) as H.
  apply eq_Id. rewrite (Id_eq _ _ H), (Id_eq _ _ (powneg1_S n)). ring.
Qed.

(* The T = 1 sharpness constant has absolute value 1 on the whole class. *)
Theorem sc_T1_B1 : forall (m : Z) (n : nat),
  Id (Z.abs (sdet (2 * m) 1 1 0 m 1 1 0 n)) 1%Z.
Proof.
  intros m n. apply eq_Id.
  rewrite (Id_eq _ _ (sc_T1 m n)). exact (Id_eq _ _ (zabs_powneg1 (S n))).
Qed.

(* Explicit class two (matrix (a1*a2+1, a1; a2, 1), seeds (a1*p0+1, p0)
   and (a1, 1)): det = 1 and seed core G0 = 1, so the constant is
   B = a1 -- the denominator slot of the first convergent member
   (a1*p0+1)/a1. *)
Theorem sc_T2 : forall (a1 a2 p0 : Z) (n : nat),
  Id (sdet (a1 * a2 + 1) a1 a2 1 (a1 * p0 + 1) p0 a1 1 n) a1.
Proof.
  intros a1 a2 p0 n.
  assert (Hdet : ZeqT ((a1 * a2 + 1) * 1 - a1 * a2) 1%Z) by (apply ZeqT_lift; ring).
  pose proof (sc_general (a1 * a2 + 1)%Z a1 a2 1 (a1 * p0 + 1)%Z p0 a1 1 n Hdet) as H.
  apply eq_Id. rewrite (Id_eq _ _ H). ring.
Qed.

(* The T = 2 sharpness constant has absolute value |a1|. *)
Theorem sc_T2_Babs : forall (a1 a2 p0 : Z) (n : nat),
  Id (Z.abs (sdet (a1 * a2 + 1) a1 a2 1 (a1 * p0 + 1) p0 a1 1 n)) (Z.abs a1).
Proof.
  intros a1 a2 p0 n. apply eq_Id.
  rewrite (Id_eq _ _ (sc_T2 a1 a2 p0 n)). reflexivity.
Qed.

(* Rotation-block instance for D = 13 (matrix (33,20;5,3), seeds (3,1)
   and (1,0)), second row: E'_n = -5 * (-1)^n * (3*0 - 1*1) = 5 * (-1)^n;
   the constant 5 is the denominator of the first member 18/5. *)
Theorem sc_T13_row2 : forall n : nat,
  Id (gy 33 20 5 3 3 1 n * gy 33 20 5 3 1 0 (S n)
      - gy 33 20 5 3 3 1 (S n) * gy 33 20 5 3 1 0 n)%Z
     (5 * powneg1 n)%Z.
Proof.
  intro n.
  assert (Hdet : ZeqT (33 * 3 - 20 * 5) (-1)%Z) by (apply ZeqT_lift; ring).
  pose proof (sc_row2_general_alt 33 20 5 3 3 1 1 0 n Hdet) as H.
  apply eq_Id. rewrite (Id_eq _ _ H). ring.
Qed.

(* ============================================================ *)
(* Specialization layer: the four pair carriers are gp instances, *)
(* and their family determinants are instances of the general     *)
(* theorems.                                                      *)
(* ============================================================ *)

(* The Pell carrier (D = m^2 + 1): pellpair/qelpair = gp (2m,1;1,0). *)
Lemma pellpair_gp : forall (m : Z) (n : nat),
  Id (pellpair m n) (gp (2 * m) 1 1 0 m 1 n).
Proof.
  intros m n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (Id_eq _ _ (pellpair_unfold m k)),
            (Id_eq _ _ (gp_unfold (2 * m) 1 1 0 m 1 k)), (Id_eq _ _ IH).
    destruct (gp (2 * m) 1 1 0 m 1 k) as [u v]. f_equal; ring.
Qed.

Lemma qelpair_gp : forall (m : Z) (n : nat),
  Id (qelpair m n) (gp (2 * m) 1 1 0 1 0 n).
Proof.
  intros m n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (Id_eq _ _ (qelpair_unfold m k)),
            (Id_eq _ _ (gp_unfold (2 * m) 1 1 0 1 0 k)), (Id_eq _ _ IH).
    destruct (gp (2 * m) 1 1 0 1 0 k) as [u v]. f_equal; ring.
Qed.

Lemma pellx_gp : forall (m : Z) (k : nat),
  Id (pellx m (S k)) (gx (2 * m) 1 1 0 m 1 k).
Proof.
  intros m k. apply eq_Id. unfold pellx, gx.
  rewrite (Id_eq _ _ (pellpair_unfold m k)), (Id_eq _ _ (pellpair_gp m k)).
  reflexivity.
Qed.

Lemma pelly_gp : forall (m : Z) (k : nat),
  Id (pelly m (S k)) (gx (2 * m) 1 1 0 1 0 k).
Proof.
  intros m k. apply eq_Id. unfold pelly, gx.
  rewrite (Id_eq _ _ (qelpair_unfold m k)), (Id_eq _ _ (qelpair_gp m k)).
  reflexivity.
Qed.

(* The Pell family determinant is the T = 1 specialization. *)
Theorem sc_T1_recovers_pell_det : forall (m : Z) (n : nat),
  Id (pellx m (S n) * pelly m (S (S n)) - pellx m (S (S n)) * pelly m (S n))%Z
     (powneg1 (S n)).
Proof.
  intros m n.
  rewrite (Id_eq _ _ (pellx_gp m n)), (Id_eq _ _ (pellx_gp m (S n))),
          (Id_eq _ _ (pelly_gp m (S n))), (Id_eq _ _ (pelly_gp m n)).
  exact (sc_T1 m n).
Qed.

(* The D = 3 carrier: d3pair/e3pair = gp (3,1;2,1), a1 = 1. *)
Lemma d3pair_gp : forall n : nat, Id (d3pair n) (gp 3 1 2 1 2 1 n).
Proof.
  intro n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (d3pair_unfold k), (Id_eq _ _ (gp_unfold 3 1 2 1 2 1 k)),
            (Id_eq _ _ IH).
    destruct (gp 3 1 2 1 2 1 k) as [u v]. f_equal; ring.
Qed.

Lemma e3pair_gp : forall n : nat, Id (e3pair n) (gp 3 1 2 1 1 1 n).
Proof.
  intro n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (e3pair_unfold k), (Id_eq _ _ (gp_unfold 3 1 2 1 1 1 k)),
            (Id_eq _ _ IH).
    destruct (gp 3 1 2 1 1 1 k) as [u v]. f_equal; ring.
Qed.

(* The D = 3 family determinant is the T = 2 specialization at a1 = 1. *)
Theorem sc_T2_recovers_d3_det : forall n : nat,
  Id (d3x n * d3z (S n) - d3x (S n) * d3z n)%Z 1%Z.
Proof.
  intro n. unfold d3x, d3z.
  rewrite (Id_eq _ _ (d3pair_gp n)), (Id_eq _ _ (e3pair_gp n)),
          (Id_eq _ _ (d3pair_gp (S n))), (Id_eq _ _ (e3pair_gp (S n))).
  exact (sc_T2 1 2 1 n).
Qed.

(* The D = 6 carrier: d6pair/e6pair = gp (9,2;4,1), a1 = 2. *)
Lemma d6pair_gp : forall n : nat, Id (d6pair n) (gp 9 2 4 1 5 2 n).
Proof.
  intro n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (Id_eq _ _ (d6pair_unfold k)), (Id_eq _ _ (gp_unfold 9 2 4 1 5 2 k)),
            (Id_eq _ _ IH).
    destruct (gp 9 2 4 1 5 2 k) as [u v]. f_equal; ring.
Qed.

Lemma e6pair_gp : forall n : nat, Id (e6pair n) (gp 9 2 4 1 2 1 n).
Proof.
  intro n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (Id_eq _ _ (e6pair_unfold k)), (Id_eq _ _ (gp_unfold 9 2 4 1 2 1 k)),
            (Id_eq _ _ IH).
    destruct (gp 9 2 4 1 2 1 k) as [u v]. f_equal; ring.
Qed.

(* The D = 6 family determinant is the T = 2 specialization at a1 = 2. *)
Theorem sc_T2_recovers_d6_det : forall n : nat,
  Id (d6x n * d6z (S n) - d6x (S n) * d6z n)%Z 2%Z.
Proof.
  intro n. unfold d6x, d6z.
  rewrite (Id_eq _ _ (d6pair_gp n)), (Id_eq _ _ (e6pair_gp n)),
          (Id_eq _ _ (d6pair_gp (S n))), (Id_eq _ _ (e6pair_gp (S n))).
  exact (sc_T2 2 4 2 n).
Qed.

(* The D = 13 carrier: d13pair/e13pair = gp (33,20;5,3). *)
Lemma d13pair_gp : forall n : nat, Id (d13pair n) (gp 33 20 5 3 3 1 n).
Proof.
  intro n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (Id_eq _ _ (d13pair_unfold k)),
            (Id_eq _ _ (gp_unfold 33 20 5 3 3 1 k)), (Id_eq _ _ IH).
    destruct (gp 33 20 5 3 3 1 k) as [u v]. f_equal; ring.
Qed.

Lemma e13pair_gp : forall n : nat, Id (e13pair n) (gp 33 20 5 3 1 0 n).
Proof.
  intro n. induction n as [|k IH].
  - apply id_refl.
  - apply eq_Id.
    rewrite (Id_eq _ _ (e13pair_unfold k)),
            (Id_eq _ _ (gp_unfold 33 20 5 3 1 0 k)), (Id_eq _ _ IH).
    destruct (gp 33 20 5 3 1 0 k) as [u v]. f_equal; ring.
Qed.

(* The D = 13 family determinant is the second-row specialization. *)
Theorem sc_T5_recovers_d13_det : forall n : nat,
  Id (d13y n * d13w (S n) - d13y (S n) * d13w n)%Z (5 * powneg1 n)%Z.
Proof.
  intro n. unfold d13y, d13w.
  rewrite (Id_eq _ _ (d13pair_gp n)), (Id_eq _ _ (e13pair_gp n)),
          (Id_eq _ _ (d13pair_gp (S n))), (Id_eq _ _ (e13pair_gp (S n))).
  exact (sc_T13_row2 n).
Qed.

(* ============================================================ *)
(* Numeric pins (closed terms) and the assumption audit.         *)
(* ============================================================ *)

(* Pin 1 (T = 1 class, m = 2): E_5 = 1. *)
Lemma smoke_T1_m2 : Id (Z.eqb (sdet (2 * 2) 1 1 0 2 1 1 0 5) (powneg1 6)) true.
Proof. vm_compute. apply id_refl. Qed.

(* Pin 2 (T = 2 class, D = 3): E_4 = 1. *)
Lemma smoke_T2_d3 : Id (Z.eqb (sdet 3 1 2 1 2 1 1 1 4) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Pin 3 (T = 2 class, D = 6): E_4 = 2. *)
Lemma smoke_T2_d6 : Id (Z.eqb (sdet 9 2 4 1 5 2 2 1 4) 2%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Pin 4 (D = 13, second row): E'_0 = 5. *)
Lemma smoke_T13 :
  Id (Z.eqb (gy 33 20 5 3 3 1 0 * gy 33 20 5 3 1 0 1
             - gy 33 20 5 3 3 1 1 * gy 33 20 5 3 1 0 0)%Z 5%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Pin 5 (denominator slot, D = 6): the first member is 5/2. *)
Lemma smoke_fmden_d6 : Id (Z.eqb (gx 9 2 4 1 2 1 0) 2%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Pin 6 (T = 1 class, D = 10): the first member is 19/6. *)
Lemma smoke_pell_member :
  Id (Z.eqb (gx (2 * 3) 1 1 0 3 1 1) 19%Z, Z.eqb (gx (2 * 3) 1 1 0 1 0 1) 6%Z)
     (true, true).
Proof. vm_compute. apply id_refl. Qed.

(* Pin 7 (T = 1 class, D = 10): E_0 = -1. *)
Lemma smoke_T1_d10 :
  Id (Z.eqb (sdet (2 * 3) 1 1 0 3 1 1 0 0) (powneg1 1)) true.
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions ZeqT_drop.
Print Assumptions ZeqT_lift.
Print Assumptions gp_0.
Print Assumptions gx_0.
Print Assumptions gy_0.
Print Assumptions gp_unfold.
Print Assumptions gx_rec.
Print Assumptions gy_rec.
Print Assumptions cross_step.
Print Assumptions sdet_cross.
Print Assumptions sdet_row2.
Print Assumptions cross_det1.
Print Assumptions cross_detm1.
Print Assumptions sc_general.
Print Assumptions sc_general_alt.
Print Assumptions sc_row2_general.
Print Assumptions sc_row2_general_alt.
Print Assumptions sc_T1.
Print Assumptions sc_T1_B1.
Print Assumptions sc_T2.
Print Assumptions sc_T2_Babs.
Print Assumptions sc_T13_row2.
Print Assumptions pellpair_gp.
Print Assumptions qelpair_gp.
Print Assumptions pellx_gp.
Print Assumptions pelly_gp.
Print Assumptions sc_T1_recovers_pell_det.
Print Assumptions d3pair_gp.
Print Assumptions e3pair_gp.
Print Assumptions sc_T2_recovers_d3_det.
Print Assumptions d6pair_gp.
Print Assumptions e6pair_gp.
Print Assumptions sc_T2_recovers_d6_det.
Print Assumptions d13pair_gp.
Print Assumptions e13pair_gp.
Print Assumptions sc_T5_recovers_d13_det.
Print Assumptions smoke_T1_m2.
Print Assumptions smoke_T2_d3.
Print Assumptions smoke_T2_d6.
Print Assumptions smoke_T13.
Print Assumptions smoke_fmden_d6.
Print Assumptions smoke_pell_member.
Print Assumptions smoke_T1_d10.

From Stdlib Require Import Extraction.
Separate Extraction gp gx gy sdet cross
  smoke_T1_m2 smoke_T2_d3 smoke_T2_d6 smoke_T13 smoke_fmden_d6
  smoke_pell_member smoke_T1_d10.
