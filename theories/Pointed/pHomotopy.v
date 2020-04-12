Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import WildCat.

Local Open Scope pointed_scope.

(** TODO: in various places we pointed_reduce. We should avoid doing so. *)

(** Some higher homotopies *)

Definition phomotopy_inverse_1 {A : pType} {P : pFam A} {f : pForall A P}
  : (phomotopy_refl f) ^* ==* phomotopy_refl f.
Proof.
  srapply Build_pHomotopy.
  + reflexivity.
  + pointed_reduce. reflexivity.
Defined.

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
Definition phomotopy_path_pp `{Funext} {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) ==* phomotopy_path p @* phomotopy_path q.
Proof.
  induction p. induction q. symmetry. apply phomotopy_compose_p1.
Defined.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
Proof.
  snrapply Build_pHomotopy; cbn.
  1: intros a; apply ap, p.
  pointed_reduce'.
  symmetry.
  simpl.
  refine (concat_p1 _ @ concat_p1 _ @ ap _ _).
  exact (concat_p1 _).
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h) : g o* f ==* h o* f.
Proof.
  snrapply Build_pHomotopy; cbn.
  1: intros a; apply p.
  pointed_reduce'.
  symmetry.
  refine (concat_p1 _ @ concat_1p _ @ concat_p1 _).
Defined.

(** ** Composition of pointed homotopies *)
Definition phomotopy_path2 `{Funext} {A : pType} {P : pFam A}
  {f g : pForall A P} {p p' : f = g} (q : p = p')
  : phomotopy_path p ==* phomotopy_path p'.
Proof.
  induction q. reflexivity.
Defined.

Infix "@*" := phomotopy_compose : pointed_scope.

(* pointed homotopy is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.

(** [phomotopy_path] sends inverses to inverses.*)
Definition phomotopy_path_V `{Funext} {A : pType} {P : pFam A}
  {f g : pForall A P} (p : f = g)
  : phomotopy_path (p^) ==* (phomotopy_path p)^*.
Proof.
  induction p. simpl. symmetry. apply phomotopy_inverse_1.
Defined.

Definition phomotopy_hcompose `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
 {p p' : f ==* g} {q q' : g ==* h} (r : p ==* p') (s : q ==* q') :
  p @* q ==* p' @* q'.
Proof.
  exact ((s $@R p) $@ (q' $@L r)).
Defined.

Reserved Infix "@@*" (at level 30).
Notation "p @@* q" := (phomotopy_hcompose p q).
