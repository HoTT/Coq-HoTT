(** * Identity functor *)
Require Import Category.Core Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section identity.
  (** There is an identity functor.  It does the obvious thing. *)
  Definition identity C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End identity.

Module Export FunctorIdentityNotations.
  Notation "1" := (identity _) : functor_scope.
End FunctorIdentityNotations.
