(** * Opposite Category *)
Require Import Category.Core Category.Objects.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope morphism_scope.
Local Open Scope category_scope.

(** ** Definition of [Cᵒᵖ] *)
Definition opposite (C : PreCategory) : PreCategory
  := @Build_PreCategory'
       C
       (fun s d => morphism C d s)
       (identity (C := C))
       (fun _ _ _ m1 m2 => m2 o m1)
       (fun _ _ _ _ _ _ _ => @associativity_sym _ _ _ _ _ _ _ _)
       (fun _ _ _ _ _ _ _ => @associativity _ _ _ _ _ _ _ _)
       (fun _ _ => @right_identity _ _ _)
       (fun _ _ => @left_identity _ _ _)
       (@identity_identity C)
       _.

Local Notation "C ^op" := (opposite C) : category_scope.

(** ** [ᵒᵖ] is judgmentally involutive *)
Definition opposite_involutive C : (C^op)^op = C := idpath.

(** ** Initial objects are opposite terminal objects, and vice versa *)
Section DualObjects.
  Variable C : PreCategory.

  Definition terminal_opposite_initial (x : C)
             `(H : IsTerminalObject C x)
  : IsInitialObject (C^op) x
    := fun x' => H x'.

  Definition initial_opposite_terminal (x : C)
             `(H : IsInitialObject C x)
  : IsTerminalObject (C^op) x
    := fun x' => H x'.
End DualObjects.

Module Export CategoryDualNotations.
  Notation "C ^op" := (opposite C) : category_scope.
End CategoryDualNotations.
