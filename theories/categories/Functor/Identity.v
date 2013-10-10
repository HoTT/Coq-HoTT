Require Import Category.Core Functor.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section identity.
  (** There is an identity functor.  It does the obvious thing. *)
  Definition identity C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End identity.

Module Export Notations.
  Notation "1" := (identity _) : functor_scope.
End Notations.
