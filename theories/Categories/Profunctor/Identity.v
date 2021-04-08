(** * Identity profunctor *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.Category.Prod HoTT.Categories.Category.Dual HoTT.Categories.Functor.Prod.Core HoTT.Categories.SetCategory.Core HoTT.Categories.Profunctor.Core HoTT.Categories.HomFunctor.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope profunctor_scope.

Section identity.
  (** Quoting nCatLab:

      In particular the identity profunctor [Id : C ⇸ C] is represented by the identity functor and hence is given by the hom-functor [C(−,−) : Cᵒᵖ × C → Set]. *)

  Definition identity `{Funext} (C : PreCategory) : C -|-> C
    := hom_functor C.
End identity.

Module Export ProfunctorIdentityNotations.
  Notation "1" := (identity _) : profunctor_scope.
End ProfunctorIdentityNotations.
