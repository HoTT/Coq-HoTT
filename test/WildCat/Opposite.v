From HoTT Require Import Basics WildCat.Core WildCat.Opposite WildCat.Equiv
  WildCat.NatTrans WildCat.Bifunctor.

(** Opposites are definitionally involutive. *)
Definition test1 A : A = (A^op)^op :> Type := 1.
Definition test2 A `{x : IsGraph A} : x = @isgraph_op A^op (@isgraph_op A x) := 1.
Definition test3 A `{x : Is01Cat A} : x = @is01cat_op A^op _ (@is01cat_op A _ x) := 1.
Definition test4 A `{x : Is2Graph A} : x = @is2graph_op A^op _ (@is2graph_op A _ x) := 1.
Definition test5 A `{x : Is1Cat A} : x = @is1cat_op A^op _ _ _ (@is1cat_op A _ _ _ x) := 1.

(** [core] only partially commutes with taking the opposite category. *)
Definition core1 A `{HasEquivs A} : (core A)^op = core A^op :> Type := 1.
Definition core2 A `{HasEquivs A} : isgraph_op (A:=core A) = isgraph_core (A:=A^op) := 1.
Definition core3 A `{HasEquivs A} : is01cat_op (A:=core A) = is01cat_core (A:=A^op) := 1.
Definition core4 A `{HasEquivs A} : is2graph_op (A:=core A) = is2graph_core (A:=A^op) := 1.

(** The Opaque line reduces the time from 0.3s to 0.07s. *)
Opaque compose_catie_isretr.
Definition core5 A `{HasEquivs A} : is1cat_op (A:=core A) = is1cat_core (A:=A^op) := 1.

(** Opposite functors are definitionally involutive. *)
Definition test6 A B (F : A -> B) `{x : Is0Functor A B F}
  : @is0functor_op _ _ F _ _ (@is0functor_op _ _ F _ _ x) = x
  := 1.
Definition test7 A B (F : A -> B) `{x : Is1Functor A B F}
  : @is1functor_op _ _ F _ _ _ _ _ _ _ _ _(@is1functor_op _ _ F _ _ _ _ _ _ _ _ _ x) = x
  := 1.

(** Opposite bifunctors are definitionally involutive. *)
Definition test8 A B C (F : A -> B -> C) `{x : Is0Bifunctor A B C F}
  : @is0bifunctor_op _ _ _ F _ _ _ (@is0bifunctor_op _ _ _ F _ _ _ x) = x
  := 1.
Definition test9 A B C (F : A -> B -> C) `{x : Is1Bifunctor A B C F}
  : @is1bifunctor_op _ _ _ F _ _ _ _ _ _ _ _ _ _ _ _ _
    (@is1bifunctor_op _ _ _ F _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
  := 1.

(** Opposite natural transformations are *not* definitionally involutive. *)
Fail Definition test10 A `{Is01Cat A} B `{Is1Cat B} (F G : A -> B)
  `{!Is0Functor F, !Is0Functor G} (n : NatTrans F G)
  : nattrans_op (nattrans_op n) = n
  := 1.
