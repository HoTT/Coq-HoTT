(** * Functoriality of functor category construction *)
Require Import HoTT.Basics.
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.FunctorCategory.Core HoTT.Categories.Functor.Pointwise.Core HoTT.Categories.Functor.Pointwise.Properties HoTT.Categories.Category.Dual HoTT.Categories.Category.Prod HoTT.Categories.Cat.Core HoTT.Categories.ExponentialLaws.Law4.Functors.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope type_scope.

(** ** [(_ → _)] is a functor [catᵒᵖ × cat → cat] *)
Section functor.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (sub_pre_cat P HF).

  Hypothesis has_functor_categories : forall C D : cat, P (C.1 -> D.1).

  Local Open Scope category_scope.

  Definition functor_uncurried
  : object ((cat^op * cat) -> cat)
    := Eval cbv zeta in
        let object_of := (fun CD => (((fst CD).1 -> (snd CD).1);
                                     has_functor_categories (fst CD) (snd CD)))
        in Build_Functor
             (cat^op * cat) cat
             object_of
             (fun CD C'D' FG => pointwise (fst FG) (snd FG))
             (fun _ _ _ _ _ => Functor.Pointwise.Properties.composition_of _ _ _ _)
             (fun _ => Functor.Pointwise.Properties.identity_of _ _).

  Definition functor : object (cat^op -> (cat -> cat))
    := ExponentialLaws.Law4.Functors.inverse _ _ _ functor_uncurried.
End functor.
