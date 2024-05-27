From HoTT Require Import Basics WildCat.Core WildCat.Opposite WildCat.Equiv
  WildCat.NatTrans WildCat.Bifunctor WildCat.Monoidal.

(** Opposites are definitionally involutive. *)
Succeed Definition t A : A = (A^op)^op :> Type := 1.
Succeed Definition t A `{x : IsGraph A} : x = @isgraph_op A^op (@isgraph_op A x) := 1.
Succeed Definition t A `{x : Is01Cat A} : x = @is01cat_op A^op _ (@is01cat_op A _ x) := 1.
Succeed Definition t A `{x : Is2Graph A} : x = @is2graph_op A^op _ (@is2graph_op A _ x) := 1.
Succeed Definition t A `{x : Is1Cat A} : x = @is1cat_op A^op _ _ _ (@is1cat_op A _ _ _ x) := 1.

(** [core] only partially commutes with taking the opposite category. *)
Succeed Definition t A `{HasEquivs A} : (core A)^op = core A^op :> Type := 1.
Succeed Definition t A `{HasEquivs A} : isgraph_op (A:=core A) = isgraph_core (A:=A^op) := 1.
Succeed Definition t A `{HasEquivs A} : is01cat_op (A:=core A) = is01cat_core (A:=A^op) := 1.
Succeed Definition t A `{HasEquivs A} : is2graph_op (A:=core A) = is2graph_core (A:=A^op) := 1.

(** The Opaque line reduces the time from 0.3s to 0.07s. *)
Opaque compose_catie_isretr.
Succeed Definition t A `{HasEquivs A} : is1cat_op (A:=core A) = is1cat_core (A:=A^op) := 1.

(** Opposite functors are definitionally involutive. *)
Succeed Definition t A B (F : A -> B) `{x : Is0Functor A B F}
  : @is0functor_op _ _ F _ _ (@is0functor_op _ _ F _ _ x) = x
  := 1.
Succeed Definition t A B (F : A -> B) `{x : Is1Functor A B F}
  : @is1functor_op _ _ F _ _ _ _ _ _ _ _ _ (@is1functor_op _ _ F _ _ _ _ _ _ _ _ _ x) = x
  := 1.

(** Opposite bifunctors are definitionally involutive. *)
Succeed Definition t A B C (F : A -> B -> C) `{x : Is0Bifunctor A B C F}
  : @is0bifunctor_op _ _ _ F _ _ _ (@is0bifunctor_op _ _ _ F _ _ _ x) = x
  := 1.
Succeed Definition t A B C (F : A -> B -> C) `{x : Is1Bifunctor A B C F}
  : @is1bifunctor_op _ _ _ F _ _ _ _ _ _ _ _ _ _ _ _ _
    (@is1bifunctor_op _ _ _ F _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
  := 1.

(** Opposite natural transformations are definitionally involutive. *)
Succeed Definition t A `{Is01Cat A} B `{Is1Cat B} (F G : A -> B)
  `{!Is0Functor F, !Is0Functor G} (n : NatTrans F G)
  : nattrans_op (nattrans_op n) = n
  := 1.

(** Opposite natural equivalences are definitionally involutive. *)
Succeed Definition t A `{Is01Cat A} B `{HasEquivs B} (F G : A -> B)
  `{!Is0Functor F, !Is0Functor G} (n : NatEquiv F G)
  : natequiv_op (natequiv_op n) = n
  := 1.

(** Opposite left unitors are *not* definitionally involutive. *)
Fail Definition t A `{HasEquivs A} (unit : A)
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (a : LeftUnitor F unit)
  : @left_unitor_op _ _ _ _ _ _ F unit _ _ (@left_unitor_op _ _ _ _ _ _ F unit _ _ a) = a
  := 1.

(** Opposite right unitors are *not* definitionally involutive. *)
Fail Definition t A `{HasEquivs A} (unit : A)
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (a : RightUnitor F unit)
  : @right_unitor_op _ _ _ _ _ _ F unit _ _ (@right_unitor_op _ _ _ _ _ _ F unit _ _ a) = a
  := 1.

(** Opposite associators are *not* definitionally involutive. *)
Fail Definition t A `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (a : Associator F)
  : @associator_op _ _ _ _ _ _ F _ _ (@associator_op _ _ _ _ _ _ F _ _ a) = a
  := 1.

(** Opposite braidings are definitionally involutive. *)
Succeed Definition t A `{HasEquivs A}
  (F : A -> A -> A) `{!Is0Bifunctor F, !Is1Bifunctor F} (a : Braiding F)
  : @braiding_op _ _ _ _ _ _ _ _ (@braiding_op _ _ _ _ _ _ _ _ a) = a
  := 1.
