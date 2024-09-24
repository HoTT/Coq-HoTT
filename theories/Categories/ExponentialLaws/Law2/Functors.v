(** * Exponential functors between products and sums in exponents *)
Require Import Functor.Core FunctorCategory.Core Functor.Identity NaturalTransformation.Core Category.Sum Category.Prod Functor.Sum Functor.Prod.Core NaturalTransformation.Sum Functor.Pointwise.Core NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Local Notation fst_type := Basics.Overture.fst.
Local Notation snd_type := Basics.Overture.snd.
Local Notation pair_type := Basics.Overture.pair.

Section law2.
  Context `{Funext}.
  Variables D C1 C2 : PreCategory.

  (** ** [yⁿ⁺ᵐ → yⁿ × yᵐ] *)
  Definition functor
  : Functor (C1 + C2 -> D) ((C1 -> D) * (C2 -> D))
    := pointwise (inl C1 C2) 1
       * pointwise (inr C1 C2) 1.

  (** ** [yⁿ × yᵐ → yⁿ⁺ᵐ] *)
  Definition inverse
  : Functor ((C1 -> D) * (C2 -> D)) (C1 + C2 -> D).
  Proof.
    refine (Build_Functor
              ((C1 -> D) * (C2 -> D)) (C1 + C2 -> D)
              (fun FG => fst FG + snd FG)%functor
              (fun _ _ m => fst_type m + snd_type m)%natural_transformation
              _
              _);
    simpl in *;
    abstract (
        repeat (intros [?|?] || intros [? ?]);
        simpl in *;
          apply path_natural_transformation; intros [?|?];
        reflexivity
      ).
  Defined.
End law2.
