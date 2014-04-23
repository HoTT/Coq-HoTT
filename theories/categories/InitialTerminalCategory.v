(** * Initial and terminal categories *)
Require Import Category.Core Functor.Core NaturalTransformation.Core Functor.Paths NaturalTransformation.Paths.
Require Import NatCategory Contractible.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Module Export Core.
  Notation initial_category := (nat_category 0) (only parsing).
  Notation terminal_category := (nat_category 1) (only parsing).

  (** ** Terminal categories *)
  (** A precategory is terminal if its objects and morphisms are contractible types. *)
  Class IsTerminalCategory (C : PreCategory)
        `{Contr (object C)}
        `{forall s d, Contr (morphism C s d)} := {}.

  (** ** Initial categories *)
  (** An initial precategory is one whose objects have the recursion priniciple of the empty type *)
  Class IsInitialCategory (C : PreCategory)
    := initial_category_rect : forall P : Type, C -> P.

  Instance trunc_initial_category `{IsInitialCategory C}
  : IsHProp C
    := fun x y => initial_category_rect _ x.
  Instance trunc_initial_category_mor `{IsInitialCategory C} x y
  : Contr (morphism C x y)
    := initial_category_rect _ x.

  (** ** Default intitial ([0]) and terminal ([1]) precategories. *)
  Instance is_initial_category_0 : IsInitialCategory 0 := (fun T => @Empty_rect (fun _ => T)).
  Instance: IsTerminalCategory 1 | 0.
  Instance: Contr (object 1) | 0 := _.
  Instance: Contr (morphism 1 x y) | 0 := fun x y => _.
  Instance default_terminal C {H H1} : @IsTerminalCategory C H H1 | 10.

  Arguments initial_category_rect / .
  Arguments is_initial_category_0 / .
End Core.

(** ** Functors to and from initial and terminal categories *)
Module Functors.
  Section functors.
    Variable C : PreCategory.

    (** *** Functor to any terminal category *)
    Definition to_terminal `{@IsTerminalCategory one Hone Hone'}
    : Functor C one
      := Build_Functor
           C one
           (fun _ => center _)
           (fun _ _ _ => center _)
           (fun _ _ _ _ _ => contr _)
           (fun _ => contr _).

    (** *** Constant functor from any terminal category *)
    Definition from_terminal `{@IsTerminalCategory one Hone Hone'} (c : C)
    : Functor one C
      := Build_Functor
           one C
           (fun _ => c)
           (fun _ _ _ => identity c)
           (fun _ _ _ _ _ => symmetry _ _ (@identity_identity _ _))
           (fun _ => idpath).

    (** *** Functor from any initial category *)
    Definition from_initial `{@IsInitialCategory zero}
    : Functor zero C
      := Build_Functor
           zero C
           (fun x => initial_category_rect _ x)
           (fun x _ _ => initial_category_rect _ x)
           (fun x _ _ _ _ => initial_category_rect _ x)
           (fun x => initial_category_rect _ x).
  End functors.

  Local Arguments to_terminal / .
  Local Arguments from_terminal / .
  Local Arguments from_initial / .

  Definition to_1 C : Functor C 1
    := Eval simpl in to_terminal C.
  Definition from_1 C c : Functor 1 C
    := Eval simpl in from_terminal C c.
  Definition from_0 C : Functor 0 C
    := Eval simpl in from_initial C.

  Local Notation "! x" := (from_terminal _ x) (at level 3) : functor_scope.

  (** *** Uniqueness principles about initial and terminal categories and functors *)
  Section unique.
    Context `{Funext}.

    Global Instance trunc_initial_category_function
           `{@IsInitialCategory zero} T
    : Contr (zero -> T) :=
      let x := {| center x := initial_category_rect _ x |} in x.
    Proof.
      intro y.
      apply path_forall; intro x.
      apply (initial_category_rect _ x).
    Defined.

    Variable C : PreCategory.

    Global Instance trunc_initial_category
           `{@IsInitialCategory zero}
    : Contr (Functor zero C)
      := let x := {| center := from_initial C |} in x.
    Proof.
      abstract (
          intros; apply path_functor'_sig;
          (exists (center _));
          apply path_forall; intro x;
          apply (initial_category_rect _ x)
        ).
    Defined.

    Global Instance trunc_to_initial_category
           `{@IsInitialCategory zero}
    : IsHProp (Functor C zero).
    Proof.
      typeclasses eauto.
    Qed.

    Definition to_initial_category_empty
               `{@IsInitialCategory zero}
               (F : Functor C zero)
    : IsInitialCategory C
      := fun P x => initial_category_rect P (F x).

    Global Instance trunc_terminal_category
           `{@IsTerminalCategory one H0 H1}
    : Contr (Functor C one)
      := let x := {| center := to_terminal C |} in x.
    Proof.
      intros.
      exact (center _).
    Defined.
  End unique.

  Module Export InitialTerminalCategoryFunctorsNotations.
    Notation "! x" := (from_terminal _ x) : functor_scope.
  End InitialTerminalCategoryFunctorsNotations.
End Functors.

(** ** Natural transformations between functors from initial categories and to terminal categories *)
Module NaturalTransformations.
  Section NaturalTransformations.
    Variable C : PreCategory.

    Definition from_initial
               `{@IsInitialCategory zero} (F G : Functor zero C)
    : NaturalTransformation F G
      := Build_NaturalTransformation
           F G
           (fun x => initial_category_rect _ x)
           (fun x _ _ => initial_category_rect _ x).

    Global Instance trunc_from_initial
           `{Funext}
           `{@IsInitialCategory zero} (F G : Functor zero C)
    : Contr (NaturalTransformation F G)
      := let x := {| center := from_initial F G |}
         in x.
    Proof.
      abstract (
          intros;
          apply path_natural_transformation;
          intro x;
          exact (initial_category_rect _ x)
        ).
    Defined.

    Local Existing Instance Functors.to_initial_category_empty.

    Global Instance trunc_to_initial
           `{Funext}
           `{@IsInitialCategory zero}
           (F G : Functor zero C)
    : Contr (NaturalTransformation F G)
      := trunc_from_initial F G.

    Definition to_terminal
               `{@IsTerminalCategory one H0 H1} (F G : Functor C one)
    : NaturalTransformation F G
      := Build_NaturalTransformation
           F G
           (fun x => center _)
           (fun _ _ _ => path_contr _ _).

    Global Instance trunc_to_terminal
           `{Funext}
           `{@IsTerminalCategory one H0 H1} (F G : Functor C one)
    : Contr (NaturalTransformation F G)
      := let x := {| center := to_terminal F G |} in x.
    Proof.
      abstract (path_natural_transformation; exact (contr _)).
    Defined.
  End NaturalTransformations.
End NaturalTransformations.

Module Export Notations.
  Include Functors.InitialTerminalCategoryFunctorsNotations.
End Notations.
