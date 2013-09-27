Require Export Category.Core Functor.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section functor_identity.
  (** There is an identity functor.  It does the obvious thing. *)
  Definition functor_identity C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End functor_identity.

Notation "1" := (functor_identity _) : functor_scope.
