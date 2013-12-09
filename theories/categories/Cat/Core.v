Require Import Category.Core Category.Objects InitialTerminalCategory Functor.Core Category.Strict Category.Univalent Functor.Paths.
Require Import Functor.Identity Functor.Composition.Core Functor.Composition.Laws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section sub_pre_cat.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  (** There is a precategory of precategories which satisfy the proposition P *)

  Definition sub_pre_cat : PreCategory
    := @Build_PreCategory
         { C : PreCategory | P C }
         (fun C D => Functor C.1 D.1)
         (fun C => identity C.1)
         (fun _ _ _ F G => F o G)
         (fun _ _ _ _ _ _ _ => associativity _ _ _)
         (fun _ _ _ => left_identity _)
         (fun _ _ _ => right_identity _)
         (fun s d => HF s.2 d.2).
End sub_pre_cat.

Arguments sub_pre_cat {_} P {_}, {_} P _.

Definition strict_cat `{Funext} : PreCategory
  := sub_pre_cat (fun C => IsStrictCategory C).

(*Definition Cat `{Funext} : PreCategory.
  refine (@sub_pre_cat _ (fun C => IsCategory C) _).
  *)

Section objects.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Lemma is_terminal_object__is_terminal_category
        `(IsTerminalCategory one)
        (HT : P one)
  : IsTerminalObject (sub_pre_cat P HF) (one; HT).
  Proof.
    typeclasses eauto.
  Defined.

  Lemma is_initial_object__is_initial_category
        `(IsInitialCategory zero)
        (HI : P zero)
  : IsInitialObject (sub_pre_cat P HF) (zero; HI).
  Proof.
    typeclasses eauto.
  Defined.
End objects.
