(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.

(** ** Indexed product of categories *)

Global Instance isgraph_forall (A : Type) (B : A -> Type)
  `{forall a, IsGraph (B a)}
  : IsGraph (forall a, B a).
Proof.
  srapply Build_IsGraph.
  intros x y; exact (forall (a : A), x a $-> y a).
Defined.

Global Instance is01cat_forall (A : Type) (B : A -> Type)
  `{forall a, IsGraph (B a)} `{forall a, Is01Cat (B a)}
  : Is01Cat (forall a, B a).
Proof.
  srapply Build_Is01Cat.
  + intros x a; exact (Id (x a)).
  + intros x y z f g a; exact (f a $o g a).
Defined.

Global Instance is0gpd_forall (A : Type) (B : A -> Type)
  (* Apparently when there's a [forall] there, Coq can't automatically add the [Is01Cat] instance from the [Is0Gpd] instance. *)
  `{forall a, IsGraph (B a)} `{forall a, Is01Cat (B a)} `{forall a, Is0Gpd (B a)}
  : Is0Gpd (forall a, B a).
Proof.
  constructor.
  intros f g p a; exact ((p a)^$).
Defined.

Global Instance is1cat_forall (A : Type) (B : A -> Type)
  `{forall a, IsGraph (B a)} `{forall a, Is01Cat (B a)}
  `{forall a, Is1Cat (B a)}
  : Is1Cat (forall a, B a).
Proof.
  srapply Build_Is1Cat.
  + intros x y; srapply Build_IsGraph.
    intros f g; exact (forall a, f a $== g a).
  + intros x y; srapply Build_Is01Cat.
    - intros f a; apply Id.
    - intros f g h q p a; exact (p a $@ q a).
  + intros x y; srapply Build_Is0Gpd.
    intros f g p a; exact (gpd_rev (p a)).
  + intros x y z h; srapply Build_Is0Functor.
    intros f g p a.
    exact (h a $@L p a).
  + intros x y z h; srapply Build_Is0Functor.
    intros f g p a.
    exact (p a $@R h a).
  + intros w x y z f g h a; apply cat_assoc.
  + intros x y f a; apply cat_idl.
  + intros x y f a; apply cat_idr.
Defined.
