From HoTT Require Import Basics.
Require Import Cubical.DPath.
Require Import Cubical.PathSquare.
Require Import Cubical.DPathSquare.
Require Import Cubical.PathCube.

Declare Scope dcube_scope.
Delimit Scope dcube_scope with dcube.

(* In this file we define a dependent cube *)

(* Dependent cubes *)
Definition DPathCube {A} (B : A -> Type)
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110}
  {pi00 : x000 = x100} {pi10 : x010 = x110}
  {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111}
  {p00i : x000 = x001} {p01i : x010 = x011}
  {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i}
  {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10}
  {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01}
  {si1i : PathSquare p01i p11i pi10 pi11}
  (cube : PathCube s0ii s1ii sii0 sii1 si0i si1i)
  {b000 : B x000} {b010 : B x010} {b100 : B x100} {b110 : B x110}
  {b001 : B x001} {b011 : B x011} {b101 : B x101} {b111 : B x111 }
  {bp0i0 : DPath B p0i0 b000 b010} {bp1i0 : DPath B p1i0 b100 b110}
  {bpi00 : DPath B pi00 b000 b100} {bpi10 : DPath B pi10 b010 b110}
  {bp0i1 : DPath B p0i1 b001 b011} {bp1i1 : DPath B p1i1 b101 b111}
  {bpi01 : DPath B pi01 b001 b101} {bpi11 : DPath B pi11 b011 b111}
  {bp00i : DPath B p00i b000 b001} {bp01i : DPath B p01i b010 b011}
  {bp10i : DPath B p10i b100 b101} {bp11i : DPath B p11i b110 b111}
  (bs0ii : DPathSquare B s0ii bp0i0 bp0i1 bp00i bp01i)
  (bs1ii : DPathSquare B s1ii bp1i0 bp1i1 bp10i bp11i)
  (bsii0 : DPathSquare B sii0 bp0i0 bp1i0 bpi00 bpi10)
  (bsii1 : DPathSquare B sii1 bp0i1 bp1i1 bpi01 bpi11)
  (bsi0i : DPathSquare B si0i bp00i bp10i bpi00 bpi01)
  (bsi1i : DPathSquare B si1i bp01i bp11i bpi10 bpi11) : Type.
Proof.
  destruct cube.
  exact (PathCube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i).
Defined.

Definition equiv_dc_const' {A B : Type}
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110}
  {pi00 : x000 = x100} {pi10 : x010 = x110}
  {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111}
  {p00i : x000 = x001} {p01i : x010 = x011}
  {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i}
  {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10}
  {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01}
  {si1i : PathSquare p01i p11i pi10 pi11}
  {cube : PathCube s0ii s1ii sii0 sii1 si0i si1i}
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
  {bs0ii : DPathSquare (fun _ => B) s0ii bp0i0 bp0i1 bp00i bp01i}
  {bs1ii : DPathSquare (fun _ => B) s1ii bp1i0 bp1i1 bp10i bp11i}
  {bsii0 : DPathSquare (fun _ => B) sii0 bp0i0 bp1i0 bpi00 bpi10}
  {bsii1 : DPathSquare (fun _ => B) sii1 bp0i1 bp1i1 bpi01 bpi11}
  {bsi0i : DPathSquare (fun _ => B) si0i bp00i bp10i bpi00 bpi01}
  {bsi1i : DPathSquare (fun _ => B) si1i bp01i bp11i bpi10 bpi11}
  : PathCube
    (ds_const'^-1 bs0ii) (ds_const'^-1 bs1ii) (ds_const'^-1 bsii0)
    (ds_const'^-1 bsii1) (ds_const'^-1 bsi0i) (ds_const'^-1 bsi1i)
    <~> DPathCube (fun _ => B) cube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i.
Proof.
  by destruct cube.
Defined.

Notation dc_const' := equiv_dc_const'.

Definition equiv_dc_const {A B : Type}
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110}
  {pi00 : x000 = x100} {pi10 : x010 = x110}
  {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111}
  {p00i : x000 = x001} {p01i : x010 = x011}
  {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i}
  {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10}
  {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01}
  {si1i : PathSquare p01i p11i pi10 pi11}
  {cube : PathCube s0ii s1ii sii0 sii1 si0i si1i}
  {b000 b010 b100 b110 b001 b011 b101 b111 : B}
  {bp0i0 : b000 = b010} {bp1i0 : b100 = b110}
  {bpi00 : b000 = b100} {bpi10 : b010 = b110}
  {bp0i1 : b001 = b011} {bp1i1 : b101 = b111}
  {bpi01 : b001 = b101} {bpi11 : b011 = b111}
  {bp00i : b000 = b001} {bp01i : b010 = b011}
  {bp10i : b100 = b101} {bp11i : b110 = b111}
  {bs0ii : PathSquare bp0i0 bp0i1 bp00i bp01i}
  {bs1ii : PathSquare bp1i0 bp1i1 bp10i bp11i}
  {bsii0 : PathSquare bp0i0 bp1i0 bpi00 bpi10}
  {bsii1 : PathSquare bp0i1 bp1i1 bpi01 bpi11}
  {bsi0i : PathSquare bp00i bp10i bpi00 bpi01}
  {bsi1i : PathSquare bp01i bp11i bpi10 bpi11}
  : PathCube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i
  <~> DPathCube (fun _ => B) cube (ds_const bs0ii) (ds_const bs1ii) (ds_const bsii0)
     (ds_const bsii1) (ds_const bsi0i) (ds_const bsi1i).
Proof.
  by destruct cube.
Defined.

Notation dc_const := equiv_dc_const.

(** Dependent Kan fillers *)

Section Kan.
  Context {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {s1ii : PathSquare p1i0 p1i1 p10i p11i} {s0ii : PathSquare p0i0 p0i1 p00i p01i}
    {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
    {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
    (c : PathCube s0ii s1ii sii0 sii1 si0i si1i)
    {P : A -> Type} {y000 y010 y100 y110 y001 y011 y101 y111}
    {q0i0 : DPath P p0i0 y000 y010} {q1i0 : DPath P p1i0 y100 y110} {qi00 : DPath P pi00 y000 y100}
    {qi10 : DPath P pi10 y010 y110} {q0i1 : DPath P p0i1 y001 y011} {q1i1 : DPath P p1i1 y101 y111}
    {qi01 : DPath P pi01 y001 y101} {qi11 : DPath P pi11 y011 y111} {q00i : DPath P p00i y000 y001}
    {q01i : DPath P p01i y010 y011} {q10i : DPath P p10i y100 y101} {q11i : DPath P p11i y110 y111}.

  Definition dc_fill_left
    (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_left.
  Defined.

  Definition dc_fill_right
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_right.
  Defined.

  Definition dc_fill_top
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
                                                    (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_top.
  Defined.

  Definition dc_fill_bottom
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_bottom.
  Defined.

  Definition dc_fill_front
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
                                                    (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {ti0i : DPathSquare P si0i q00i q10i qi00 qi01 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_front.
  Defined.

  Definition dc_fill_back
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01)
    : {ti1i : DPathSquare P si1i q01i q11i qi10 qi11 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_back.
  Defined.

End Kan.
