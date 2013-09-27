Require Export Category.Core Category.Objects.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Section category_opposite.
  Definition category_opposite (C : PreCategory) : PreCategory
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
End category_opposite.

Notation "C ^op" := (category_opposite C) (at level 3) : category_scope.

Section DualCategories.
  Lemma op_op_id C : (C^op)^op = C.
  Proof.
    destruct C; exact idpath.
  Defined.
End DualCategories.

Hint Rewrite @op_op_id : category.

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
