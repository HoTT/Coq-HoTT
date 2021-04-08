(** * Exponential functors between products and sums in exponents *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.FunctorCategory.Core HoTT.Categories.Functor.Identity HoTT.Categories.NaturalTransformation.Core HoTT.Categories.NaturalTransformation.Paths HoTT.Categories.Functor.Composition.Core HoTT.Categories.Category.Sum HoTT.Categories.Category.Prod HoTT.Categories.Functor.Sum HoTT.Categories.Functor.Prod.Core HoTT.Categories.NaturalTransformation.Sum HoTT.Categories.Functor.Pointwise.Core HoTT.Categories.NaturalTransformation.Paths.
Require Import HoTT.Categories.InitialTerminalCategory.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Local Notation fst_type := Basics.Datatypes.fst.
Local Notation snd_type := Basics.Datatypes.snd.
Local Notation pair_type := Basics.Datatypes.pair.

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
