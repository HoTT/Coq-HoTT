(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.FunctorCat.
Require Import WildCat.Equiv.
Require Import WildCat.Induced.

(** * Wild categories of wild categories *)

(** ** The wild category of wild (0,1)-categories *)

(** The category of wild (0,1)-categories is simplest, but minimally coherent. *)
Record WildCat01 :=
{
  cat01_carrier : Type;
  cat01_is01cat : Is01Cat cat01_carrier;
}.

(* note for morgan: this allows us to consider WildCats as types. *)
Coercion cat01_carrier : WildCat01 >-> Sortclass.

Global Existing Instance cat01_is01cat.

Global Instance is01cat_wildcat01 : Is01Cat WildCat01.
Proof.
  srapply Build_Is01Cat.
  + intros A B; exact (Fun01 A B).
  + intros C. cbn in *.
    exists idmap; exact _.
  + intros A B C [G g] [F f].
    exists (G o F); exact _.
Defined.

(** In fact [WildCat01] is probably a (wild) 1-category and even a (1,2)-category, but we haven't shown that or even defined the latter. *)

(** ** The wild category of wild 1-categories *)

(** This should form a wild 2-category. *) 

Record WildCat :=
{
  cat_carrier : Type;
  cat_isgraph : IsGraph cat_carrier;
  cat_is01cat : Is01Cat cat_carrier;
  cat_is1cat : Is1Cat cat_carrier
}.

(* note for morgan: this allows us to consider WildCats as types. *)
Coercion cat_carrier : WildCat >-> Sortclass. 

Global Existing Instance cat_isgraph.
Global Existing Instance cat_is01cat.
Global Existing Instance cat_is1cat.

(** The proofs below are almost identical to those showing that WildCat01 is a (0,1)-category, but we use [Fun11] instead of [Fun01]. *)
Global Instance is01cat_wildcat : Is01Cat WildCat.
Proof.
  srapply Build_Is01Cat.
  + intros A B; exact (Fun11 A B).
  + intro A; rapply (Build_Fun11 idmap).
  + intros C D E [F ? ?] [G ? ?]; cbn in *.
    srapply (Build_Fun11 (F o G)).
Defined.

(** Now we show WildCat is a 2-category, with a 1-category structure on Fun02 given by natural transformations. *) 

Global Instance is1cat_wildcat : Is1Cat WildCat.
(** Proof.
  srapply Build_Is1Coh1Cat.
  + intros A B C D f g h.
  exact (Fun1 A B).
  + intros C. cbn in *.
  unfold Fun1. 
  exists (idmap). srapply Build_Is0Coh1Functor. intros a b. cbn.
  exact (idmap).
  + intros A B C; cbn in *; unfold Fun1.
  intros [G g] [F f]. 
  exists ( G o F). 
  srapply Build_Is0Coh1Functor.
  intros u v h. cbn in *.  exact (fmap G ( fmap F h)).
  Defined. *)
Admitted. 
