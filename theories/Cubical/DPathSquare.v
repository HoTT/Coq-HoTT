Require Import Basics.
Require Import Cubical.DPath.
Require Import Cubical.PathSquare.

Declare Scope dsquare_scope.
Delimit Scope dsquare_scope with dsquare.

Local Open Scope dpath_scope.

(* Dependent squares *)

Definition DPathSquare {A} (P : A -> Type) {a00 a10 a01 a11}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x p1x}
  (s : PathSquare px0 px1 p0x p1x) {b00 b10 b01 b11}
  (qx0 : DPath P px0 b00 b10) (qx1 : DPath P px1 b01 b11)
  (q0x : DPath P p0x b00 b01) (q1x : DPath P p1x b10 b11) : Type.
Proof.
  destruct s.
  exact (PathSquare qx0 qx1 q0x q1x).
Defined.

Definition ds_id {A} {P : A -> Type} {a00 b00}
  : DPathSquare P sq_id 1 1 1 1 (a00:=a00) (b00:=b00).
Proof.
  apply sq_id.
Defined.

Notation "1" := ds_id : dsquare_scope.

Section DPathSquareConstructors.

  (* Different ways of constructing dependent squares *)

  Context {A} {a0 a1 : A} {p : a0 = a1} {P : A -> Type}
    {b0 b1} (dp : DPath P p b0 b1).

  Definition ds_refl_h : DPathSquare P (sq_refl_h _) dp dp 1 1.
  Proof.
    destruct p.
    apply sq_refl_h.
  Defined.

  Definition ds_refl_v : DPathSquare P (sq_refl_v _) 1 1 dp dp.
  Proof.
    destruct p.
    apply sq_refl_v.
  Defined.

End DPathSquareConstructors.

(* We have an apD for DPathSquares *)
Definition ds_apD {A} {B : A -> Type} (f : forall a, B a) {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x p1x} (s : PathSquare px0 px1 p0x p1x)
  : DPathSquare B s (dp_apD f px0) (dp_apD f px1) (dp_apD f p0x) (dp_apD f p1x).
Proof.
  by destruct s.
Defined.

(* A DPathSquare over a constant family is given by just a square *)
Definition ds_const {A P : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11 : P}
  {qx0 : b00 = b10} {qx1 : b01 = b11} {q0x : b00 = b01} {q1x : b10 = b11}
  : PathSquare qx0 qx1 q0x q1x -> DPathSquare (fun _ => P) s (dp_const qx0)
      (dp_const qx1) (dp_const q0x) (dp_const q1x).
Proof.
  by destruct s.
Defined.

Global Instance isequiv_ds_const {A P : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11 : P}
  {qx0 : b00 = b10} {qx1 : b01 = b11} {q0x : b00 = b01} {q1x : b10 = b11}
  : IsEquiv (ds_const (s:=s) (qx0:=qx0) (qx1:=qx1) (q0x:=q0x) (q1x:=q1x)).
Proof.
  destruct s; exact _.
Defined.

(* Sometimes we want the DPathSquare to be typed differently *)
(* This could be achieved with some clever rewriting of squares and DPathSquares *)
(* It seems that writing it like this might get in the way, Cube.v has
   some examples of this. *)
Definition ds_const' {A P : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11 : P}
  {qx0 : DPath (fun _ => P) px0 b00 b10}
  {qx1 : DPath (fun _ => P) px1 b01 b11}
  {q0x : DPath (fun _ => P) p0x b00 b01}
  {q1x : DPath (fun _ => P) p1x b10 b11}
  : PathSquare (dp_const^-1 qx0) (dp_const^-1 qx1)
    (dp_const^-1 q0x) (dp_const^-1 q1x)
    -> DPathSquare (fun _ => P) s qx0 qx1 q0x q1x.
Proof.
  by destruct s.
Defined.

Global Instance isequiv_ds_const' {A P : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11 : P}
  {qx0 : DPath (fun _ => P) px0 b00 b10}
  {qx1 : DPath (fun _ => P) px1 b01 b11}
  {q0x : DPath (fun _ => P) p0x b00 b01}
  {q1x : DPath (fun _ => P) p1x b10 b11}
  : IsEquiv (ds_const' (s:=s) (qx0:=qx0) (qx1:=qx1) (q0x:=q0x) (q1x:=q1x)).
Proof.
  destruct s; exact _.
Defined.

(* dp_apD fits into a natural square *)
Definition dp_apD_nat {A} {P : A -> Type} (f g : forall x, P x) {x y : A}
  (p : x = y) (q : f == g)
  : DPathSquare P (sq_refl_h _) (dp_apD f p) (dp_apD g p) (q x) (q y).
Proof.
  destruct p.
  by apply sq_1G.
Defined.

Definition ds_G1 {A} (P : A -> Type) {a00 a10 }
  {px0 px1 : a00 = a10} {p : px0 = px1} {b00 b10}
  (qx0 : DPath P px0 b00 b10) (qx1 : DPath P px1 b00 b10)
  : DPath (fun x => DPath P x b00 b10) p qx0 qx1
      ->  DPathSquare P (sq_G1 p) qx0 qx1 1 1.
Proof.
  destruct p, px0.
  apply sq_G1.
Defined.

Global Instance isequiv_ds_G1 {A} (P : A -> Type) {a00 a10 }
  {px0 px1 : a00 = a10} {p : px0 = px1} {b00 b10}
  (qx0 : DPath P px0 b00 b10) (qx1 : DPath P px1 b00 b10)
  : IsEquiv (ds_G1 (p:=p) P qx0 qx1).
Proof.
  destruct p, px0.
  cbn in *.
  exact _.
Defined.
