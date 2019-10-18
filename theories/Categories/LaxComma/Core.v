(** * Lax Comma Category *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Pseudofunctors.
Require Import Cat.Core.
Require Functor.Identity.
Require Pseudofunctor.Identity.
Require Import Category.Strict.
Require Import Functor.Composition.Core.
Require Import NaturalTransformation.Paths NaturalTransformation.Composition.Core.
Require Import Category.Morphisms FunctorCategory.Core.
Require Import Pseudofunctor.Core.
Require Import NaturalTransformation.Composition.Laws.
Require Import FunctorCategory.Morphisms.
Require LaxComma.CoreLaws.
Require Import Trunc HoTT.Tactics Types.Paths Types.Sigma.
Local Set Warnings Append "-notation-overridden".
Require Import Basics.Notations.
Local Set Warnings Append "notation-overridden".

Import Functor.Identity.FunctorIdentityNotations.
Import Pseudofunctor.Identity.PseudofunctorIdentityNotations.
Import LaxComma.CoreLaws.LaxCommaCategory.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope morphism_scope.
Local Open Scope category_scope.

(** Quoting David Spivak:

    David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ∘ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]

     David: consider for yourself the case where [F : X --> X'] is
       identity ([X = X']) and (separately) the case where
       [α : G --> G ∘ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       *)

(** ** Definition of Lax Comma Category *)
Definition lax_comma_category `{Funext} A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           `{forall a b, IsHSet (Functor (S a) (T b))}
: PreCategory
  := @Build_PreCategory
       (@object _ _ _ S T)
       (@morphism _ _ _ S T)
       (@identity _ _ _ S T)
       (@compose _ _ _ S T)
       (@associativity _ _ _ S T)
       (@left_identity _ _ _ S T)
       (@right_identity _ _ _ S T)
       _.

Definition oplax_comma_category `{Funext} A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           `{forall a b, IsHSet (Functor (S a) (T b))}
: PreCategory
  := (lax_comma_category S T)^op.

Global Instance isstrict_lax_comma_category `{Funext} A B
       (S : Pseudofunctor A) (T : Pseudofunctor B)
       `{IsStrictCategory A, IsStrictCategory B}
       `{forall a b, IsHSet (Functor (S a) (T b))}
: IsStrictCategory (@lax_comma_category _ A B S T _).
Proof.
  typeclasses eauto.
Qed.

Global Instance isstrict_oplax_comma_category `{fs : Funext} A B S T HA HB H
: IsStrictCategory (@oplax_comma_category fs A B S T H)
  := @isstrict_lax_comma_category fs A B S T HA HB H.

(*  Section category.
    Context `{IsCategory A, IsCategory B}.
    (*Context `{Funext}. *)

    Definition comma_category_isotoid (x y : comma_category)
    : x ≅ y -> x = y.
    Proof.
      intro i.
      destruct i as [i [i' ? ?]].
      hnf in *.
      destruct i, i'.
      simpl in *.


    Global Instance comma_category_IsCategory `{IsCategory A, IsCategory B}
    : IsCategory comma_category.
    Proof.
      hnf.
      unfold IsStrictCategory in *.
      typeclasses eauto.
    Qed.
  End category.
 *)

(** ** Definition of Lax (Co)Slice Category *)
Section lax_slice_category.
  Context `{Funext}.
  Variables A a : PreCategory.
  Variable S : Pseudofunctor A.
  Context `{forall a0, IsHSet (Functor (S a0) a)}.
  Context `{forall a0, IsHSet (Functor a (S a0))}.

  Definition lax_slice_category : PreCategory := lax_comma_category S !a.
  Definition lax_coslice_category : PreCategory := lax_comma_category !a S.

  Definition oplax_slice_category : PreCategory := oplax_comma_category S !a.
  Definition oplax_coslice_category : PreCategory := oplax_comma_category !a S.

(** [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x -> F y]; [F ↓ x] has morphisms [F y -> x] *)
End lax_slice_category.

Arguments lax_slice_category {_} [A] a S {_}.
Arguments lax_coslice_category {_} [A] a S {_}.
Arguments oplax_slice_category {_} [A] a S {_}.
Arguments oplax_coslice_category {_} [A] a S {_}.

(** ** Definition of Lax (Co)Slice Category Over *)
Section lax_slice_category_over.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Variable a : PreCategory.
  Context `{forall a0 : cat, IsHSet (Functor a0.1 a)}.
  Context `{forall a0 : cat, IsHSet (Functor a a0.1)}.

  Definition lax_slice_category_over : PreCategory := @lax_slice_category _ cat a (Pseudofunctor.Identity.identity P) _.
  Definition lax_coslice_category_over : PreCategory := @lax_coslice_category _ cat a (Pseudofunctor.Identity.identity P) _.
  Definition oplax_slice_category_over : PreCategory := @oplax_slice_category _ cat a (Pseudofunctor.Identity.identity P) _.
  Definition oplax_coslice_category_over : PreCategory := @oplax_coslice_category _ cat a (Pseudofunctor.Identity.identity P) _.
End lax_slice_category_over.

Arguments lax_slice_category_over {_} P {HF} a {_}.
Arguments lax_coslice_category_over {_} P {HF} a {_}.
Arguments oplax_slice_category_over {_} P {HF} a {_}.
Arguments oplax_coslice_category_over {_} P {HF} a {_}.

(** ** Definition of Lax (Co)Slice Arrow Category *)
Section lax_arrow_category.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Definition lax_arrow_category : PreCategory := @lax_comma_category _ cat cat (Pseudofunctor.Identity.identity P) (Pseudofunctor.Identity.identity P) (fun C D => HF C.2 D.2).
  Definition oplax_arrow_category : PreCategory := @oplax_comma_category _ cat cat (Pseudofunctor.Identity.identity P) (Pseudofunctor.Identity.identity P) (fun C D => HF C.2 D.2).
End lax_arrow_category.

Arguments lax_arrow_category {_} P {_}.
Arguments oplax_arrow_category {_} P {_}.

Local Set Warnings Append "-notation-overridden". (* work around bug #5567, https://coq.inria.fr/bugs/show_bug.cgi?id=5567, notation-overridden,parsing should not trigger for only printing notations *)
Module Export LaxCommaCoreNotations.
  (** We play some games to get nice notations for lax comma categories. *)
  Section tc_notation_boiler_plate.
    Class LCC_Builder {A B C} (x : A) (y : B) (z : C) := lcc_builder_dummy : True.
    Definition get_LCC `{@LCC_Builder A B C x y z} : C := z.

    Global Arguments get_LCC / {A B C} x y {z} {_}.

    Global Instance LCC_comma `{Funext} A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           {_ : forall a b, IsHSet (Functor (S a) (T b))}
    : LCC_Builder S T (lax_comma_category S T) | 1000
      := I.

    Global Instance LCC_slice `{Funext} A x (F : Pseudofunctor A)
           `{forall a0, IsHSet (Functor (F a0) x)}
    : LCC_Builder F x (lax_slice_category x F) | 100
      := I.

    Global Instance LCC_coslice `{Funext} A x (F : Pseudofunctor A)
           `{forall a0, IsHSet (Functor x (F a0))}
    : LCC_Builder x F (lax_coslice_category x F) | 100
      := I.

    Global Instance LCC_slice_over `{Funext}
           P `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}
           a
           `{forall a0 : @sub_pre_cat _ P HF, IsHSet (Functor a0.1 a)}
    : LCC_Builder a (@sub_pre_cat _ P HF) (@lax_slice_category_over _ P HF a _) | 10
      := I.

    Global Instance LCC_coslice_over `{Funext}
           P `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}
           a
           `{forall a0 : @sub_pre_cat _ P HF, IsHSet (Functor a a0.1)}
    : LCC_Builder (@sub_pre_cat _ P HF) a (@lax_coslice_category_over _ P HF a _) | 10
      := I.

    Class OLCC_Builder {A B C} (x : A) (y : B) (z : C) := olcc_builder_dummy : True.

    Definition get_OLCC `{@OLCC_Builder A B C x y z} : C := z.

    Global Arguments get_OLCC / {A B C} x y {z} {_}.

    Global Instance OLCC_comma `{Funext} A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           {_ : forall a b, IsHSet (Functor (S a) (T b))}
    : OLCC_Builder S T (lax_comma_category S T) | 1000
      := I.

    Global Instance OLCC_slice `{Funext} A x (F : Pseudofunctor A)
           `{forall a0, IsHSet (Functor (F a0) x)}
    : OLCC_Builder F x (lax_slice_category x F) | 100
      := I.

    Global Instance OLCC_coslice `{Funext} A x (F : Pseudofunctor A)
           `{forall a0, IsHSet (Functor x (F a0))}
    : OLCC_Builder x F (lax_coslice_category x F) | 100
      := I.

    Global Instance OLCC_slice_over `{Funext}
           P `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}
           a
           `{forall a0 : @sub_pre_cat _ P HF, IsHSet (Functor a0.1 a)}
    : OLCC_Builder a (@sub_pre_cat _ P HF) (@lax_slice_category_over _ P HF a _) | 10
      := I.

    Global Instance OLCC_coslice_over `{Funext}
           P `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}
           a
           `{forall a0 : @sub_pre_cat _ P HF, IsHSet (Functor a a0.1)}
    : OLCC_Builder (@sub_pre_cat _ P HF) a (@lax_coslice_category_over _ P HF a _) | 10
      := I.
  End tc_notation_boiler_plate.

  (** We really want to use infix [⇓] and [⇑] for lax comma categories, but that's unicode.  Infix [,] might also be reasonable, but I can't seem to get it to work without destroying the [(_, _)] notation for ordered pairs.  So I settle for the ugly ASCII rendition [//] of [⇓] and [\\] for [⇑]. *)
  (** Set some notations for printing *)
  Notation "'CAT' // a" := (@lax_slice_category_over _ _ _ a _) : category_scope.
  Notation "a // 'CAT'" := (@lax_coslice_category_over _ _ _ a _) : category_scope.
  Notation "x // F" := (lax_coslice_category x F) (only printing) : category_scope.
  Notation "F // x" := (lax_slice_category x F) (only printing) : category_scope.
  Notation "S // T" := (lax_comma_category S T) (only printing) : category_scope.
  (** Set the notation for parsing; typeclasses will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
  Notation "S // T" := (get_LCC S T) : category_scope.

  Notation "'CAT' \\ a" := (@oplax_slice_category_over _ _ _ a _) : category_scope.
  Notation "a \\ 'CAT'" := (@oplax_coslice_category_over _ _ _ a _) : category_scope.
  Notation "x \\ F" := (oplax_coslice_category x F) (only printing) : category_scope.
  Notation "F \\ x" := (oplax_slice_category x F) (only printing) : category_scope.
  Notation "S \\ T" := (oplax_comma_category S T) (only printing) : category_scope.
  (** Set the notation for parsing; typeclasses will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
  Notation "S \\ T" := (get_OLCC S T) : category_scope.
End LaxCommaCoreNotations.
