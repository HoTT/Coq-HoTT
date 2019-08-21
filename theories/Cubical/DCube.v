Require Import Basics.
Require Import DPath.
Require Import Square.
Require Import DSquare.
Require Import Cube.

Declare Scope dcube_scope.
Delimit Scope dcube_scope with dcube.

(* In this file we define a dependent cube *)

(* Dependent cubes *)
Definition DCube {A} (B : A -> Type)
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110}
  {pi00 : x000 = x100} {pi10 : x010 = x110}
  {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111}
  {p00i : x000 = x001} {p01i : x010 = x011}
  {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : Square p0i0 p0i1 p00i p01i}
  {s1ii : Square p1i0 p1i1 p10i p11i}
  {sii0 : Square p0i0 p1i0 pi00 pi10}
  {sii1 : Square p0i1 p1i1 pi01 pi11}
  {si0i : Square p00i p10i pi00 pi01}
  {si1i : Square p01i p11i pi10 pi11}
  (cube : Cube s0ii s1ii sii0 sii1 si0i si1i)
  {b000 : B x000} {b010 : B x010} {b100 : B x100} {b110 : B x110}
  {b001 : B x001} {b011 : B x011} {b101 : B x101} {b111 : B x111 }
  {bp0i0 : DPath B p0i0 b000 b010} {bp1i0 : DPath B p1i0 b100 b110}
  {bpi00 : DPath B pi00 b000 b100} {bpi10 : DPath B pi10 b010 b110}
  {bp0i1 : DPath B p0i1 b001 b011} {bp1i1 : DPath B p1i1 b101 b111}
  {bpi01 : DPath B pi01 b001 b101} {bpi11 : DPath B pi11 b011 b111}
  {bp00i : DPath B p00i b000 b001} {bp01i : DPath B p01i b010 b011}
  {bp10i : DPath B p10i b100 b101} {bp11i : DPath B p11i b110 b111}
  (bs0ii : DSquare B s0ii bp0i0 bp0i1 bp00i bp01i)
  (bs1ii : DSquare B s1ii bp1i0 bp1i1 bp10i bp11i)
  (bsii0 : DSquare B sii0 bp0i0 bp1i0 bpi00 bpi10)
  (bsii1 : DSquare B sii1 bp0i1 bp1i1 bpi01 bpi11)
  (bsi0i : DSquare B si0i bp00i bp10i bpi00 bpi01)
  (bsi1i : DSquare B si1i bp01i bp11i bpi10 bpi11) : Type.
Proof.
  destruct cube.
  exact (Cube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i).
Defined.

Section DCubeConst.

  Definition dc_const' {A B : Type}
    {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110}
    {pi00 : x000 = x100} {pi10 : x010 = x110}
    {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111}
    {p00i : x000 = x001} {p01i : x010 = x011}
    {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : Square p0i0 p0i1 p00i p01i}
    {s1ii : Square p1i0 p1i1 p10i p11i}
    {sii0 : Square p0i0 p1i0 pi00 pi10}
    {sii1 : Square p0i1 p1i1 pi01 pi11}
    {si0i : Square p00i p10i pi00 pi01}
    {si1i : Square p01i p11i pi10 pi11}
    {cube : Cube s0ii s1ii sii0 sii1 si0i si1i}
    {b000 b010 b100 b110 b001 b011 b101 b111 : B}
    {bp0i0 : DPath (fun _ => B) p0i0 b000 b010}
    {bp1i0 : DPath (fun _ => B) p1i0 b100 b110}
    {bpi00 : DPath (fun _ => B) pi00 b000 b100}
    {bpi10 : DPath (fun _ => B) pi10 b010 b110}
    {bp0i1 : DPath (fun _ => B) p0i1 b001 b011}
    {bp1i1 : DPath (fun _ => B) p1i1 b101 b111}
    {bpi01 : DPath (fun _ => B) pi01 b001 b101}
    {bpi11 : DPath (fun _ => B) pi11 b011 b111}
    {bp00i : DPath (fun _ => B) p00i b000 b001}
    {bp01i : DPath (fun _ => B) p01i b010 b011}
    {bp10i : DPath (fun _ => B) p10i b100 b101}
    {bp11i : DPath (fun _ => B) p11i b110 b111}
    {bs0ii : DSquare (fun _ => B) s0ii bp0i0 bp0i1 bp00i bp01i}
    {bs1ii : DSquare (fun _ => B) s1ii bp1i0 bp1i1 bp10i bp11i}
    {bsii0 : DSquare (fun _ => B) sii0 bp0i0 bp1i0 bpi00 bpi10}
    {bsii1 : DSquare (fun _ => B) sii1 bp0i1 bp1i1 bpi01 bpi11}
    {bsi0i : DSquare (fun _ => B) si0i bp00i bp10i bpi00 bpi01}
    {bsi1i : DSquare (fun _ => B) si1i bp01i bp11i bpi10 bpi11}
    : Cube
      (ds_const'^-1 bs0ii) (ds_const'^-1 bs1ii) (ds_const'^-1 bsii0)
      (ds_const'^-1 bsii1) (ds_const'^-1 bsi0i) (ds_const'^-1 bsi1i)
    -> DCube (fun _ => B) cube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i.
  Proof.
    by destruct cube.
  Defined.

  Global Instance isequiv_dc_const' {A B : Type}
    {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110}
    {pi00 : x000 = x100} {pi10 : x010 = x110}
    {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111}
    {p00i : x000 = x001} {p01i : x010 = x011}
    {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : Square p0i0 p0i1 p00i p01i}
    {s1ii : Square p1i0 p1i1 p10i p11i}
    {sii0 : Square p0i0 p1i0 pi00 pi10}
    {sii1 : Square p0i1 p1i1 pi01 pi11}
    {si0i : Square p00i p10i pi00 pi01}
    {si1i : Square p01i p11i pi10 pi11}
    {cube : Cube s0ii s1ii sii0 sii1 si0i si1i}
    {b000 b010 b100 b110 b001 b011 b101 b111 : B}
    {bp0i0 : DPath (fun _ => B) p0i0 b000 b010}
    {bp1i0 : DPath (fun _ => B) p1i0 b100 b110}
    {bpi00 : DPath (fun _ => B) pi00 b000 b100}
    {bpi10 : DPath (fun _ => B) pi10 b010 b110}
    {bp0i1 : DPath (fun _ => B) p0i1 b001 b011}
    {bp1i1 : DPath (fun _ => B) p1i1 b101 b111}
    {bpi01 : DPath (fun _ => B) pi01 b001 b101}
    {bpi11 : DPath (fun _ => B) pi11 b011 b111}
    {bp00i : DPath (fun _ => B) p00i b000 b001}
    {bp01i : DPath (fun _ => B) p01i b010 b011}
    {bp10i : DPath (fun _ => B) p10i b100 b101}
    {bp11i : DPath (fun _ => B) p11i b110 b111}
    {bs0ii : DSquare (fun _ => B) s0ii bp0i0 bp0i1 bp00i bp01i}
    {bs1ii : DSquare (fun _ => B) s1ii bp1i0 bp1i1 bp10i bp11i}
    {bsii0 : DSquare (fun _ => B) sii0 bp0i0 bp1i0 bpi00 bpi10}
    {bsii1 : DSquare (fun _ => B) sii1 bp0i1 bp1i1 bpi01 bpi11}
    {bsi0i : DSquare (fun _ => B) si0i bp00i bp10i bpi00 bpi01}
    {bsi1i : DSquare (fun _ => B) si1i bp01i bp11i bpi10 bpi11}
    : IsEquiv (dc_const' (cube:=cube) (bs0ii:=bs0ii) (bs1ii:=bs1ii)
       (bsii0:=bsii0) (bsii1:=bsii1) (bsi0i:=bsi0i) (bsi1i:=bsi1i)).
  Proof.
    destruct cube; exact _.
  Qed.

  Definition dc_const {A B : Type}
    {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110}
    {pi00 : x000 = x100} {pi10 : x010 = x110}
    {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111}
    {p00i : x000 = x001} {p01i : x010 = x011}
    {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : Square p0i0 p0i1 p00i p01i}
    {s1ii : Square p1i0 p1i1 p10i p11i}
    {sii0 : Square p0i0 p1i0 pi00 pi10}
    {sii1 : Square p0i1 p1i1 pi01 pi11}
    {si0i : Square p00i p10i pi00 pi01}
    {si1i : Square p01i p11i pi10 pi11}
    {cube : Cube s0ii s1ii sii0 sii1 si0i si1i}
    {b000 b010 b100 b110 b001 b011 b101 b111 : B}
    {bp0i0 : b000 = b010} {bp1i0 : b100 = b110}
    {bpi00 : b000 = b100} {bpi10 : b010 = b110}
    {bp0i1 : b001 = b011} {bp1i1 : b101 = b111}
    {bpi01 : b001 = b101} {bpi11 : b011 = b111}
    {bp00i : b000 = b001} {bp01i : b010 = b011}
    {bp10i : b100 = b101} {bp11i : b110 = b111}
    {bs0ii : Square bp0i0 bp0i1 bp00i bp01i}
    {bs1ii : Square bp1i0 bp1i1 bp10i bp11i}
    {bsii0 : Square bp0i0 bp1i0 bpi00 bpi10}
    {bsii1 : Square bp0i1 bp1i1 bpi01 bpi11}
    {bsi0i : Square bp00i bp10i bpi00 bpi01}
    {bsi1i : Square bp01i bp11i bpi10 bpi11}
    : Cube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i
    -> DCube (fun _ => B) cube (ds_const bs0ii) (ds_const bs1ii) (ds_const bsii0)
       (ds_const bsii1) (ds_const bsi0i) (ds_const bsi1i).
  Proof.
    by destruct cube.
  Defined.

  Global Instance isequiv_dc_const {A B : Type}
    {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110}
    {pi00 : x000 = x100} {pi10 : x010 = x110}
    {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111}
    {p00i : x000 = x001} {p01i : x010 = x011}
    {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : Square p0i0 p0i1 p00i p01i}
    {s1ii : Square p1i0 p1i1 p10i p11i}
    {sii0 : Square p0i0 p1i0 pi00 pi10}
    {sii1 : Square p0i1 p1i1 pi01 pi11}
    {si0i : Square p00i p10i pi00 pi01}
    {si1i : Square p01i p11i pi10 pi11}
    {cube : Cube s0ii s1ii sii0 sii1 si0i si1i}
    {b000 b010 b100 b110 b001 b011 b101 b111 : B}
    {bp0i0 : b000 = b010} {bp1i0 : b100 = b110}
    {bpi00 : b000 = b100} {bpi10 : b010 = b110}
    {bp0i1 : b001 = b011} {bp1i1 : b101 = b111}
    {bpi01 : b001 = b101} {bpi11 : b011 = b111}
    {bp00i : b000 = b001} {bp01i : b010 = b011}
    {bp10i : b100 = b101} {bp11i : b110 = b111}
    {bs0ii : Square bp0i0 bp0i1 bp00i bp01i}
    {bs1ii : Square bp1i0 bp1i1 bp10i bp11i}
    {bsii0 : Square bp0i0 bp1i0 bpi00 bpi10}
    {bsii1 : Square bp0i1 bp1i1 bpi01 bpi11}
    {bsi0i : Square bp00i bp10i bpi00 bpi01}
    {bsi1i : Square bp01i bp11i bpi10 bpi11}
     : IsEquiv (dc_const (cube:=cube) (bs0ii:=bs0ii) (bs1ii:=bs1ii)
       (bsii0:=bsii0) (bsii1:=bsii1) (bsi0i:=bsi0i) (bsi1i:=bsi1i)).
  Proof.
    destruct cube; exact _.
  Defined.

End DCubeConst.