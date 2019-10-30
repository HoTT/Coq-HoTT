(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import Truncations.
Require Import Factorization.
Require Import Algebra.ooGroup.
Import TrM.

Local Open Scope path_scope.

(** * Automorphism oo-Groups *)

(** To define the automorphism oo-group [Aut X], we have to construct its classifying space [BAut X]. *)

(** [BAut X] is the type of types that are merely equivalent to [X].  We put this in a module to make it local to this file; at the end of the file we'll redefine [BAut X] for export to be the classifying space of [Aut X] (which will be judgmentally, but not syntactically, equal to this definition.) *)
Module Import BAut.
  Definition BAut (X : Type) := { Z : Type & merely (Z = X) }.
End BAut.

(** Equivalently, [BAut X] is the (-1)-image of the classifying map [1 -> Type] of [X]. *)
Definition equiv_baut_image_unit X
: BAut X <~> image (Tr -1) (unit_name X).
Proof.
  unfold BAut, image; simpl.
  refine (equiv_functor_sigma' (equiv_idmap Type) _); intros Z; simpl.
  apply equiv_O_functor; unfold hfiber.
  refine ((equiv_contr_sigma _)^-1 oE _).
  apply equiv_path_inverse.
Defined.

(** Now we can define [Aut X], by proving that [BAut X] is connected. *)
Definition Aut (X : Type@{i}) : ooGroup@{j u a}.
Proof.
  refine (Build_ooGroup
            (Build_pType { Z : Type & merely (Z = X) } (X ; tr 1)) _).
  refine (conn_pointed_type (point _)); try exact _.
  pose (c := conn_map_compose (Tr -1)
                              (factor1 (image (Tr -1) (unit_name X)))
                              (equiv_baut_image_unit X)^-1).
  refine (conn_map_homotopic _ _ _ _ c); intros []; reflexivity.
Defined.

Definition BAut X : Type := classifying_space (Aut X).

(** The type [BAut X] is studied further in [Spaces.BAut] and its subdirectories. *)
