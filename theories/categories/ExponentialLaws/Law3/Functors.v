(** * Functors between an exponential of a product and a product of exponentials *)
Require Import Category.Core Functor.Core FunctorCategory.Core Category.Prod.
Require Import Functor.Prod Functor.Composition.Core NaturalTransformation.Composition.Laws NaturalTransformation.Composition.Core.
Require Functor.Prod.Functorial.
Require Import Types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope functor_scope.

Local Notation fst_type := Coq.Init.Datatypes.fst.
Local Notation snd_type := Coq.Init.Datatypes.snd.
Local Notation pair_type := Coq.Init.Datatypes.pair.

Section law3.
  Context `{Funext}.
  Variables C1 C2 D : PreCategory.

  (** ** [(y × z)ⁿ → yⁿ × zⁿ] *)
  Definition functor
  : Functor (D -> C1 * C2) ((D -> C1) * (D -> C2))
    := Build_Functor
         (D -> C1 * C2) ((D -> C1) * (D -> C2))
         (fun H => (fst o H, snd o H)%core)
         (fun s d m => (fst oL m, snd oL m)%core)
         (fun _ _ _ _ _ => path_prod' (composition_of_whisker_l _ _ _)
                                      (composition_of_whisker_l _ _ _))
         (fun _ => path_prod' (whisker_l_right_identity _ _)
                              (whisker_l_right_identity _ _)).

  (** ** [yⁿ × zⁿ → (y × z)ⁿ] *)
  (** If we had [Require Functor.Functor.], we could just say [Functor.Prod.functor] here. *)
  Definition inverse
  : Functor ((D -> C1) * (D -> C2)) (D -> C1 * C2)
    := Functor.Prod.Functorial.functor _ _ _.
End law3.
