Require Import Basics.
Require Import Types.
Require Import Cone.
Require Import Cocone.
Require Import Diagram.
Require Import Graph.

(** * Constant diagram *)

Section ConstantDiagram.

  Context {G : Graph}.

  Definition diagram_const (C : Type) : Diagram G.
  Proof.
    serapply Build_Diagram.
    1: exact (fun _ => C).
    intros i j k.
    exact idmap.
  Defined.

  Definition diagram_const_functor {A B : Type} (f : A -> B)
    : DiagramMap (diagram_const A) (diagram_const B).
  Proof.
    serapply Build_DiagramMap.
    1: intro i; exact f.
    reflexivity.
  Defined.

  Definition diagram_const_functor_comp {A B C : Type}
    (f : A -> B) (g : B -> C)
    : diagram_const_functor (g o f)
    = diagram_comp (diagram_const_functor g) (diagram_const_functor f).
  Proof.
    reflexivity.
  Defined.

  Definition diagram_const_functor_idmap {A : Type}
    : diagram_const_functor (idmap : A -> A) = diagram_idmap (diagram_const A).
  Proof.
    reflexivity.
  Defined.

  Definition equiv_diagram_const_cocone `{Funext} (D : Diagram G) (X : Type)
    : DiagramMap D (diagram_const X) <~> Cocone D X.
  Proof.
    serapply equiv_adjointify.
    1,2: intros [? w]; econstructor.
    1,2: intros x y z z'; symmetry; revert x y z z'.
    1,2: exact w.
    1,2: intros[].
    1: serapply path_cocone.
    3: serapply path_DiagramMap.
    1,3: reflexivity.
    all: cbn; intros; hott_simpl.
  Defined.

  Definition equiv_diagram_const_cone `{Funext} (X : Type) (D : Diagram G)
    : DiagramMap (diagram_const X) D <~> Cone X D.
  Proof.
    serapply equiv_adjointify.
    1,2: intros [? w]; econstructor.
    1,2: exact w.
    1,2: intros[].
    1: serapply path_cone.
    3: serapply path_DiagramMap.
    1,3: reflexivity.
    all: cbn; intros; hott_simpl.
  Defined.

End ConstantDiagram.



