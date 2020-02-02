Require Import Basics.
Require Import Types.
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

(* DPathSquares can be given by 2-dimensional DPaths *)
Definition equiv_ds_dpath {A} (P : A -> Type) {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  (s : px0 @ p1x = p0x @ px1) {b00 b10 b01 b11}
  {qx0 : DPath P px0 b00 b10} {qx1 : DPath P px1 b01 b11}
  {q0x : DPath P p0x b00 b01} {q1x : DPath P p1x b10 b11}
  : DPath (fun p => DPath P p b00 b11) s (qx0 @D q1x) (q0x @D qx1)
    <~> DPathSquare P (sq_path s) qx0 qx1 q0x q1x.
Proof.
  set (s' := sq_path s).
  rewrite <- (eissect sq_path s : sq_path^-1 s' = s).
  clearbody s'; clear s.
  destruct s'; cbn.
  apply equiv_sq_path.
Defined.

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
Definition dp_apD_nat {A} {P : A -> Type} {f g : forall x, P x} {x y : A}
  (q : f == g) (p : x = y)
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

(** A DPath in a path-type is naturally a DPathSquare.  *)

Definition equiv_sq_dp_D {A : Type} {B : A -> Type} (f g : forall a : A, B a)
  {x1 x2 : A} (p : x1 = x2) (q1 : f x1 = g x1) (q2 : f x2 = g x2)
  : DPathSquare B (sq_refl_h p) (dp_apD f p) (dp_apD g p) q1 q2
    <~> DPath (fun x : A => f x = g x) p q1 q2.
Proof.
  destruct p. cbn.
  exact (equiv_sq_1G^-1%equiv).
Defined.

(** Dependent Kan operations *)

Section Kan.

  Context {A : Type} {P : A -> Type} {a00 a10 a01 a11 : A}
          {px0 : a00 = a10} {px1 : a01 = a11} {p0x p1x}
          (s : PathSquare px0 px1 p0x p1x)
          {b00 : P a00} {b10 : P a10} {b01 : P a01} {b11 : P a11}.

  Definition ds_fill_l (qx1 : DPath P px1 b01 b11)
             (q0x : DPath P p0x b00 b01) (q1x : DPath P p1x b10 b11)
    : {qx0 : DPath P px0 b00 b10 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_l.
  Defined.

  Definition ds_fill_r (qx0 : DPath P px0 b00 b10)
             (q0x : DPath P p0x b00 b01) (q1x : DPath P p1x b10 b11)
    : {qx1 : DPath P px1 b01 b11 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_r.
  Defined.

  Definition ds_fill_t (qx0 : DPath P px0 b00 b10)
             (qx1 : DPath P px1 b01 b11) (q1x : DPath P p1x b10 b11)
    : {q0x : DPath P p0x b00 b01 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_t.
  Defined.

  Definition ds_fill_b (qx0 : DPath P px0 b00 b10)
             (qx1 : DPath P px1 b01 b11) (q0x : DPath P p0x b00 b01)
    : {q1x : DPath P p1x b10 b11 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_b.
  Defined.

End Kan.

(** Another equivalent formulation of a dependent square over reflexivity *)
Definition equiv_ds_transport_dpath {A} {a0 a1 : A} {p : a0 = a1}
           {P : A -> Type} {b00 b10 b01 b11}
           (qx0 : DPath P p b00 b10) (qx1 : DPath P p b01 b11)
           (q0x : b00 = b01) (q1x : b10 = b11)
  : DPathSquare P (sq_refl_h p) qx0 qx1 q0x q1x
    <~> transport (fun y => DPath P p y b11) q0x
          (transport (fun y => DPath P p b00 y) q1x
                     qx0) = qx1.
Proof.
  destruct p; cbn.
  refine (_ oE equiv_sq_path^-1).
  refine (equiv_concat_l _ _ oE _).
  { apply transport_paths_l. }
  refine (equiv_moveR_Vp _ _ _ oE _).
  refine (equiv_concat_l _ _).
  apply transport_paths_r.
Defined.
