(** * Adjunctions by units and counits *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Functor.Composition.Core Functor.Identity.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section Adjunction.
  (** ** Unit + UMP definition of adjunction *)
  (** Quoting from Awodey's "Category Theory":

      An adjunction between categories [C] and [D] consists of
      functors

      [F : C <-> D : G]

      and a natural transformation

      [T : 1_C -> G ∘ F]

      with the property:

      (o) For any [c : C], [d : D], and [f : c -> G d], there exists a
          unique [g : F c -> d] such that [f = (G g) ∘ (T c)] as
          indicated in

<<
                g
     F c ..................> d

                 G g
     G (F c) --------------> G d
       ^                    _
       |                    /|
       |                  /
       |                /
       |              /
       | T c        /
       |          /  f
       |        /
       |      /
       |    /
       |  /
        c
>>

     Terminology and notation:

     - [F] is called the left adjoint, [G] is called the right
       adjoint, and [T] is called the unit of the adjunction.

     - One sometimes writes [F -| G] for ``[F] is left and [G] right
       adjoint.''

     - The statement (o) is the UMP of the unit [T].

     Note that the situation [F ⊣ G] is a generalization of
     equivalence of categories, in that a pseudo-inverse is an
     adjoint. In that case, however, it is the relation between
     categories that one is interested in. Here, one is concerned with
     the relation between special functors. That is to say, it is not
     the relation on categories ``there exists an adjunction,'' but
     rather ``this functor has an adjoint'' that we are concerned
     with. *)

  Section unit.
    Variables C D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Definition AdjunctionUnit :=
      { T : NaturalTransformation 1 (G o F)
      | forall (c : C) (d : D) (f : morphism C c (G d)),
          Contr { g : morphism D (F c) d | G _1 g o T c = f }
      }.
  End unit.

  (** ** Counit + UMP definition of adjunction *)
  (**
     Paraphrasing and quoting from Awody's "Category Theory":

     An adjunction between categories [C] and [D] consists of functors

     [F : C <-> D : G]

     and a natural transformation

     [U : F ∘ G -> 1_D]

     with the property:

     (o) For any [c : C], [d : D], and [g : F c -> d], there exists a
         unique [f : c -> G d] such that [g = (U d) ∘ (F f)] as
         indicated in the diagram

<<
                f
     c ..................> G d

               F f
     F c --------------> F (G d)
      \                    |
        \                  |
          \                |
            \              |
              \            | U d
             g  \          |
                  \        |
                    \      |
                      \    |
                       _\| V
                          d
>>

    Terminology and notation:

    - The statement (o) is the UMP of the counit [U].
    *)
  Section counit.
    Variables C D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Definition AdjunctionCounit :=
      { U : NaturalTransformation (F o G) 1
      | forall (c : C) (d : D) (g : morphism D (F c) d),
          Contr { f : morphism C c (G d) | U d o F _1 f = g }
      }.
  End counit.

  (** The counit is just the dual of the unit.  We formalize this here
      so that we can use it to make coercions easier. *)

  Section unit_counit_op.
    Variables C D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Definition adjunction_counit__op__adjunction_unit (A : AdjunctionUnit G^op F^op)
    : AdjunctionCounit F G
      := existT
           (fun U : NaturalTransformation (F o G) 1 =>
              forall (c : C) (d : D) (g : morphism D (F c) d),
                Contr {f : morphism C c (G d)
                      | U d o F _1 f = g })
           (A.1^op)%natural_transformation
           (fun c d g => A.2 d c g).

    Definition adjunction_counit__op__adjunction_unit__inv (A : AdjunctionUnit G F)
    : AdjunctionCounit F^op G^op
      := existT
           (fun U : NaturalTransformation (F^op o G^op) 1
            => forall (c : C^op) (d : D^op) (g : morphism D^op ((F^op)%functor c) d),
                 Contr {f : morphism C^op c ((G^op)%functor d)
                       | U d o F^op _1 f = g })
           (A.1^op)%natural_transformation
           (fun c d g => A.2 d c g).

    Definition adjunction_unit__op__adjunction_counit (A : AdjunctionCounit G^op F^op)
    : AdjunctionUnit F G
      := existT
           (fun T : NaturalTransformation 1 (G o F) =>
              forall (c : C) (d : D) (f : morphism C c (G d)),
                Contr { g : morphism D (F c) d
                      | G _1 g o T c = f })
           (A.1^op)%natural_transformation
           (fun c d g => A.2 d c g).

    Definition adjunction_unit__op__adjunction_counit__inv (A : AdjunctionCounit G F)
    : AdjunctionUnit F^op G^op
      := existT
           (fun T : NaturalTransformation 1 (G^op o F^op)
            => forall (c : C^op) (d : D^op) (f : morphism C^op c ((G^op)%functor d)),
                 Contr {g : morphism D^op ((F^op)%functor c) d
                       | G^op _1 g o T c = f })
           (A.1^op)%natural_transformation
           (fun c d g => A.2 d c g).
  End unit_counit_op.

  (** ** Unit + Counit + Zig + Zag definition of adjunction *)
  (** Quoting Wikipedia on Adjoint Functors:

      A counit-unit adjunction between two categories [C] and [D]
      consists of two functors [F : C ← D] and [G : C → D] and two
      natural transformations

<<
      ε : FG → 1_C
      η : 1_D → GF
>>

      respectively called the counit and the unit of the adjunction
      (terminology from universal algebra), such that the compositions

<<
          F η            ε F
      F -------> F G F -------> F

          η G            G ε
      G -------> G F G -------> G
>>

      are the identity transformations [1_F] and [1_G] on [F] and [G]
      respectively.

      In this situation we say that ``[F] is left adjoint to [G]'' and
      ''[G] is right adjoint to [F]'', and may indicate this
      relationship by writing [(ε, η) : F ⊣ G], or simply [F ⊣ G].

      In equation form, the above conditions on (ε, η) are the
      counit-unit equations

<<
      1_F = ε F ∘ F η
      1_G = G ε ∘ η G
>>

      which mean that for each [X] in [C] and each [Y] in [D],

<<
      1_{FY} = ε_{FY} ∘ F(η_Y)
      1_{GX} = G(ε_X) ∘ η_{GX}
>>

      These equations are useful in reducing proofs about adjoint
      functors to algebraic manipulations.  They are sometimes called
      the ``zig-zag equations'' because of the appearance of the
      corresponding string diagrams.  A way to remember them is to
      first write down the nonsensical equation [1 = ε ∘ η] and then
      fill in either [F] or [G] in one of the two simple ways which
      make the compositions defined.

      Note: The use of the prefix ``co'' in counit here is not
      consistent with the terminology of limits and colimits, because
      a colimit satisfies an initial property whereas the counit
      morphisms will satisfy terminal properties, and dually.  The
      term unit here is borrowed from the theory of monads where it
      looks like the insertion of the identity 1 into a monoid.  *)

  Section unit_counit.
    Variables C D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    (*Local Reserved Notation "'ε'".
    Local Reserved Notation "'η'".*)

    (** Use the per-object version of the equations, so that we don't
        need the associator in the middle.  Also, explicitly simplify
        some of the types so that [rewrite] works better. *)
    Record AdjunctionUnitCounit :=
      {
        unit : NaturalTransformation (identity C) (G o F)
        (*where "'η'" := unit*);
        counit : NaturalTransformation (F o G) (identity D)
        (*where "'ε'" := counit*);
        unit_counit_equation_1
        : forall Y : C, (*ε (F Y) ∘ F ₁ (η Y) = identity (F Y);*)
            Category.Core.compose (C := D) (s := F Y) (d := F (G (F Y))) (d' := F Y)
                                  (counit (F Y))
                                  (F _1 (unit Y : morphism _ Y (G (F Y))))
            = 1;
        unit_counit_equation_2
        : forall X : D, (* G ₁ (ε X) ∘ η (G X) = identity (G X) *)
            Category.Core.compose (C := C) (s := G X) (d := G (F (G X))) (d' := G X)
                                  (G _1 (counit X : morphism _ (F (G X)) X))
                                  (unit (G X))
            = 1
      }.
  End unit_counit.
End Adjunction.

Declare Scope adjunction_scope.
Delimit Scope adjunction_scope with adjunction.

Bind Scope adjunction_scope with AdjunctionUnit.
Bind Scope adjunction_scope with AdjunctionCounit.
Bind Scope adjunction_scope with AdjunctionUnitCounit.

Arguments unit [C D]%category [F G]%functor _%adjunction / .
Arguments counit [C D]%category [F G]%functor _%adjunction / .
Arguments unit_counit_equation_1 [C D]%category [F G]%functor _%adjunction _%object.
Arguments unit_counit_equation_2 [C D]%category [F G]%functor _%adjunction _%object.
