Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
(* Require Import WildCat.Induced. *)
Require Import WildCat.NatTrans.
Require Import WildCat.FunctorCat.
(* Require Import WildCat.TwoOneCat. *)

(** Categories of categories *)

(** Wild Categories *)
Record Cat1 := {
  cat1_type :> Type ;
  cat1_isgraph : IsGraph cat1_type ;
  cat1_is2graph : Is2Graph cat1_type ;
  cat1_is01cat : Is01Cat cat1_type ;
  cat1_is1cat : Is1Cat cat1_type ;
}.

Global Existing Instances
  cat1_isgraph
  cat1_is2graph
  cat1_is01cat
  cat1_is1cat.

Global Instance isgraph_cat1 : IsGraph Cat1
  := Build_IsGraph Cat1 (fun C D => Fun11 C D).

Global Instance is2graph_cat1 : Is2Graph Cat1
  := fun C D => isgraph_fun11.

Global Instance is01cat_cat1 : Is01Cat Cat1.
Proof.
  apply Build_Is01Cat.
  1: intros A; exact fun11_id.
  intros A B C f g; exact (fun11_compose f g).
Defined.

Global Instance is01cat_cat1_hom (a b : Cat1) : Is01Cat (a $-> b).
Proof.
  apply is01cat_fun11.
Defined.

