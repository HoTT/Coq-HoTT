Require Import HoTT.Basics HoTT.Types.
Require Import DPath.

(* Squares *)

(* 
x00 ----pi0---- x01
 |               |
 |               |
p0i     ==>     p1i
 |               |
 |               |
x01-----pi1-----x11
 *)

(* We think of (and define) [Square p0i p1i pi0 pi1] as a
heterogeneous path from p0i to p1i over pi0 and pi1.  *)

Definition Square {A} {x00 x01 x10 x11 : A}
          (p0i : x00 = x01) (p1i : x10 = x11)
          (pi0 : x00 = x10) (pi1 : x01 = x11) : Type
  := dpath (fun xy:A*A => fst xy = snd xy) (path_prod' pi0 pi1) p0i p1i.

Definition sqG1 {A} {x0 x1 : A} {p p' : x0 = x1} (q : p = p')
  : Square p p' 1 1
  := q.

Definition sqid {A} {x0 x1 : A} (p : x0 = x1) : Square p p 1 1
  := sqG1 (idpath p).

Definition sq1G {A} {x0 x1 : A} {p p' : x0 = x1} (q : p = p')
  : Square 1 1 p p'.
Proof.
  destruct q, p; reflexivity.
Defined.

Definition sqid' {A} {x0 x1 : A} (p : x0 = x1) : Square 1 1 p p
  := sq1G (idpath p).

Definition sqCc {A} {x00 x01 x10 x11 x20 x21: A}
           {p0i : x00 = x01} {p1i : x10 = x11} {p2i : x20 = x21}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {pj0 : x10 = x20} {pj1 : x11 = x21}
  (s01 : Square p0i p1i pi0 pi1) (s12 : Square p1i p2i pj0 pj1)
  : Square p0i p2i (pi0 @ pj0) (pi1 @ pj1).
Proof.
  destruct pi0, pi1, pj0, pj1; exact (s01 @ s12).
Defined.

Definition sqGccc {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {p0i' : x00 = x01} (g0i : p0i' = p0i)
           (s : Square p0i p1i pi0 pi1)
  : Square p0i' p1i pi0 pi1.
Proof.
  destruct g0i; exact s.
Defined.

Definition sqcGcc {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {p1i' : x10 = x11} (g1i : p1i' = p1i)
           (s : Square p0i p1i pi0 pi1)
  : Square p0i p1i' pi0 pi1.
Proof.
  destruct g1i; exact s.
Defined.

Definition sqccGc {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {pi0' : x00 = x10} (gi0 : pi0 = pi0')
           (s : Square p0i p1i pi0 pi1)
  : Square p0i p1i pi0' pi1.
Proof.
  destruct gi0; exact s.
Defined.

Definition sqcccG {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {pi1' : x01 = x11} (gi1 : pi1 = pi1')
           (s : Square p0i p1i pi0 pi1)
  : Square p0i p1i pi0 pi1'.
Proof.
  destruct gi1; exact s.
Defined.

Definition sqtr {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           (s : Square p0i p1i pi0 pi1)
  : Square pi0 pi1 p0i p1i.
Proof.
  destruct pi0, pi1, s, p0i; reflexivity.
Defined.

Definition sqcC {A} {x00 x01 x10 x11 x02 x12: A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {p0j : x01 = x02} {p1j : x11 = x12}
           {pi0 : x00 = x10} {pi1 : x01 = x11} {pi2 : x02 = x12}
  (s01 : Square p0i p1i pi0 pi1) (s12 : Square p0j p1j pi1 pi2)
  : Square (p0i @ p0j) (p1i @ p1j) pi0 pi2
  := sqtr (sqCc (sqtr s01) (sqtr s12)).

Definition sqap {A} {B} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           (f : A -> B) (s : Square p0i p1i pi0 pi1)
  : Square (ap f p0i) (ap f p1i) (ap f pi0) (ap f pi1).
Proof.
  destruct pi0, pi1; exact (ap (ap f) s).
Defined.

Definition sqnat {A B} {f f' : A -> B} (h : f == f') {x y : A} (p : x = y)
  : Square (ap f p) (ap f' p) (h x) (h y).
Proof.
  destruct p; apply sq1G; reflexivity.
Defined.

Definition sqsx {A B C} (f : A -> B) {g : B -> C} {k : A -> C}
           (h : g o f == k) {x y : A} (p : x = y)
  : Square (h x) (h y) (ap g (ap f p)) (ap k p).
Proof.
  destruct p; apply sqG1; reflexivity.
Defined.

Definition sq_to_concat {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           (s : Square p0i p1i pi0 pi1)
  : p0i @ pi1 = pi0 @ p1i.
Proof.
  destruct pi0, pi1; cbn in *.
  destruct s, p0i; reflexivity.
Defined.
