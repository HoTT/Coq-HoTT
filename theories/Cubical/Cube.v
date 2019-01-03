Require Import HoTT.Basics HoTT.Types.
Require Import DPath Square.

(* 
x001----pi01----x101              x001----pi01----x101      
 |  \               \              |               |  \     
 |  p00i  ==si0i=>  p10i           |               |  p10i  
p0i1  \               \           p0i1 ==sii1=>   p1i1  \   
 |    x000----pi00----x100         |               |    x100
 |s0ii |               |    ===>   |               | s1ii|  
x011   |               |          x011----pi11----x111   |  
  \   p0i0  ==sii0=>  p1i0          \               \   p1i0
 p01i  |               |           p01i  ==si1i=>  p11i  |  
     \ |               |               \               \ |  
      x010----pi10----x110              x010----pi10----x110
 *)
Definition Cube {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
          {p0i0 : x000 = x010} {p1i0 : x100 = x110}
          {pi00 : x000 = x100} {pi10 : x010 = x110}
          {p0i1 : x001 = x011} {p1i1 : x101 = x111}
          {pi01 : x001 = x101} {pi11 : x011 = x111}
          {p00i : x000 = x001} {p01i : x010 = x011}
          {p10i : x100 = x101} {p11i : x110 = x111}
          (s0ii : Square p0i0 p0i1 p00i p01i)
          (s1ii : Square p1i0 p1i1 p10i p11i)
          (sii0 : Square p0i0 p1i0 pi00 pi10)
          (sii1 : Square p0i1 p1i1 pi01 pi11)
          (si0i : Square p00i p10i pi00 pi01)
          (si1i : Square p01i p11i pi10 pi11) : Type.
Proof.
  unshelve (refine (@dpath _ (fun bdry : { xs : (A*A)*(A*A) &
                                   ((fst (fst xs) = snd (fst xs))
                                    * (fst (snd xs) = snd (snd xs)))
                                   * ((fst (fst xs) = fst (snd xs))
                                      * (snd (fst xs) = snd (snd xs))) }
                 => Square (fst (snd (pr2 bdry))) (snd (snd (pr2 bdry)))
                           (fst (fst (pr2 bdry))) (snd (fst (pr2 bdry))))
                _ _ _ _ _)).
  - exists ((x000,x001),(x010,x011)); split; split; cbn; assumption.
  - exists ((x100,x101),(x110,x111)); split; split; cbn; assumption.
  - destruct pi00, pi01, pi10, pi11; cbn in *.
    destruct sii0, sii1, si0i, si1i; reflexivity.
  - assumption.
  - assumption.
Defined.

Definition sqsx_compose {X A B C} (i : X -> A)
           (f : A -> B) {g : B -> C} {k : A -> C}
           (h : g o f == k) {x y : X} (p : x = y)
  : Cube (sqsx (f o i) (fun x => h (i x)) p)
         (sqsx f h (ap i p))
         (sqid (h (i x))) (sqid (h (i y)))
         (ap (ap g) (ap_compose i f p)) (ap_compose i k p).
Proof.
  destruct p; reflexivity.
Defined.

Definition cubetr {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
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
          (c : Cube s0ii s1ii sii0 sii1 si0i si1i)
  : Cube sii0 sii1 s0ii s1ii (sqtr si0i) (sqtr si1i).
Proof.
  destruct pi00, pi01, pi10, pi11; cbn in *.
  destruct sii0, sii1, si0i, si1i; cbn in *.
  destruct c.
  destruct p00i, p01i; cbn in *.
  destruct s0ii; reflexivity.
Defined.


Definition cuberot {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
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
          (c : Cube s0ii s1ii sii0 sii1 si0i si1i)
  : Cube (sqtr sii0) (sqtr sii1) (sqtr si0i) (sqtr si1i) s0ii s1ii.
Proof.
  destruct pi00, pi01, pi10, pi11; cbn in *.
  destruct sii0, sii1, si0i, si1i; cbn in *.
  destruct c.
  destruct p00i, p01i; cbn in *.
  destruct s0ii; reflexivity.
Defined.
