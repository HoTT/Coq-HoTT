Require Import Category.Core Functor.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Delimit Scope natural_transformation_scope with natural_transformation.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section NaturalTransformation.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely,
     given two functors [F : C -> D], [G : C -> D], a natural
     transformation [T: F -> G] is a collection of maps [T A : F A ->
     G A], one for each object [A] of [C], such that [(T B) ∘ (F m) =
     (G m) ∘ (T A)] for every map [m : A -> B] of [C]; that is, the
     following diagram is commutative:

<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
>>
     **)

  Record NaturalTransformation :=
    Build_NaturalTransformation' {
        components_of :> forall c, morphism D (F c) (G c);
        commutes : forall s d (m : morphism C s d),
                     components_of d o F _1 m = G _1 m o components_of s;
        (* We require the following symmetrized version so that for eta-expanded [T], we have [(T^op)^op = T] judgementally. *)
        commutes_sym : forall s d (m : C.(morphism) s d),
                         G _1 m o components_of s = components_of d o F _1 m
      }.

  Definition Build_NaturalTransformation CO COM
    := Build_NaturalTransformation'
         CO
         COM
         (fun _ _ _ => symmetry _ _ (COM _ _ _)).
End NaturalTransformation.

Bind Scope natural_transformation_scope with NaturalTransformation.

Create HintDb natural_transformation discriminated.

Arguments components_of {C D}%category {F G}%functor T%natural_transformation
          c%object : rename, simpl nomatch.
Arguments commutes [C D F G] T _ _ _ : rename.

Hint Resolve @commutes : category natural_transformation.
