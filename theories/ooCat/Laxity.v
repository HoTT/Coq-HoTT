(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1.

Generalizable Variables m n p A B C.

(** ** Laxity *)

(** Various things in higher category theory, such as comma categories and natural transformations, can be lax, colax, or pseudo separately at all levels.  In keeping with our coinductive approach, we define such an infinite list of notions of laxity as a coinductive stream.  *)

Inductive Laxity :=
| colax : Laxity
| pseudo : Laxity
| lax : Laxity.

Notation oplax := colax (only parsing).

CoFixpoint all_pseudo : Stream Laxity := SCons pseudo all_pseudo.
Definition one_lax : Stream Laxity := SCons lax all_pseudo.
Definition one_colax : Stream Laxity := SCons colax all_pseudo.

(** It may seem backwards for [colax] to mean a morphism "forwards" and [lax] a morphism "backwards", but that's what matches the standard terminology for natural transformations. *)
Definition lHom (l : Laxity) `{HasEquivs n A} (a b : A) :=
  match l with
  | colax => (a $-> b)
  | pseudo => (a $<~> b)
  | lax => (b $-> a)
  end.

Definition lcat_id (l : Laxity) `{IsCat1 n A} (a : A)
  : lHom l a a
  := match l return lHom l a a with
  | colax => cat_id a
  | pseudo => cate_id a
  | lax => cat_id a
  end.
