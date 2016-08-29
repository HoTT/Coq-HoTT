(** * Functoriality of the construction of adjunctions *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import Category.Dual.
Require Import FunctorCategory.Core.
Require Import Category.Sigma.OnObjects Category.Prod.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.Dual.
Require Import Adjoint.Functorial.Parts Adjoint.Functorial.Laws.
Require Import HoTT.Types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Section left.
  (** ** Non-dependent functor for left adjoints *)
  (** We'd need Π types (dependent functors) to include functoriality
      on the categories. *)
  Section nondep.
    Context `{Funext}.
    Variables C D : PreCategory.

    Definition left_functor_nondep
    : Functor (sigT_obj (D -> C) (fun G => { F : Functor C D & F -| G }))
              (sigT_obj ((C -> D)^op * (D -> C)) (fun FG => fst FG -| snd FG))
      := Build_Functor
           (sigT_obj (D -> C) (fun G => { F : Functor C D & F -| G }))
           (sigT_obj ((C -> D)^op * (D -> C)) (fun FG => fst FG -| snd FG))
           (fun GFA => ((GFA.2.1, GFA.1); GFA.2.2))
           (fun GFA G'F'A' m => (left_morphism_of_nondep GFA.2.2 G'F'A'.2.2 m, m))
           (fun s d d' m1 m2 => path_prod' (left_composition_of_nondep _ _ _ _ _) 1)
           (fun x => path_prod' (left_identity_of_nondep _) 1).
  End nondep.
End left.

Section right.
  (** ** Non-dependent functor for right adjoints *)
  (** We'd need Π types (dependent functors) to include functoriality
      on the categories. *)
  Section nondep.
    Context `{Funext}.
    Variables C D : PreCategory.

    (** TODO: Is there a nice way to write this functor as a
              composition of the above with some dualization functors?
              (I suspect there is.) *)
    Definition right_functor_nondep
    : Functor (sigT_obj (C -> D) (fun F => { G : Functor D C & F -| G }))
              (sigT_obj ((C -> D) * (D -> C)^op) (fun FG => fst FG -| snd FG))
      := Build_Functor
           (sigT_obj (C -> D) (fun F => { G : Functor D C & F -| G }))
           (sigT_obj ((C -> D) * (D -> C)^op) (fun FG => fst FG -| snd FG))
           (fun GFA => ((GFA.1, GFA.2.1); GFA.2.2))
           (fun GFA G'F'A' m => (m, right_morphism_of_nondep G'F'A'.2.2 GFA.2.2 m))
           (fun s d d' m1 m2 => path_prod' 1 (right_composition_of_nondep _ _ _ _ _))
           (fun x => path_prod' 1 (right_identity_of_nondep _)).
  End nondep.
End right.
