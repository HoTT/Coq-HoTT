(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import Truncations.
Require Import Factorization.
Require Import Algebra.ooGroup.

Local Open Scope path_scope.

(** * Automorphism oo-Groups *)

(** To define the automorphism oo-group [Aut X], we have to construct its classifying space [BAut X]. *)

(** [BAut X] is the type of types that are merely equivalent to [X]. *)
Definition BAut@{u v} (X : Type@{u}) : Type@{v}
  := sig@{v v} (fun Z => merely (paths@{v} Z X)).

Global Instance ispointed_baut {X : Type} : IsPointed (BAut X) := (X; tr 1).

(** Equivalently, [BAut X] is the (-1)-image of the classifying map [1 -> Type] of [X]. *)
Definition equiv_baut_image_unit X
: BAut X <~> image (Tr (-1)) (unit_name X).
Proof.
  unfold BAut, image; simpl.
  apply equiv_functor_sigma_id; intros Z; simpl.
  apply Trunc_functor_equiv; unfold hfiber.
  refine ((equiv_contr_sigma _)^-1 oE _).
  apply equiv_path_inverse.
Defined.

Global Instance isconnected_baut {X : Type}
  : IsConnected 0 (BAut X).
Proof.
  exists (tr (X; tr 1)).
  rapply Trunc_ind; intros [Z p].
  strip_truncations.
  apply (ap tr).
  rapply path_sigma_hprop.
  exact p^.
Defined.

(** Now we can define [Aut X], since [BAut X] is connected. *)
Definition Aut (X : Type) : ooGroup
  := Build_ooGroup (Build_pType (BAut X) _) _.

(** The type [BAut X] is studied further in [Spaces.BAut] and its subdirectories. *)
