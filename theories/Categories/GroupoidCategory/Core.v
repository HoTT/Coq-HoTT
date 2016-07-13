(** * Groupoids *)
Require Import Category.Core Category.Morphisms Category.Strict.
Require Import Trunc Types.Forall PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope category_scope.

(** A groupoid is a precategory where every morphism is an isomorphism.  Since 1-types are 1-groupoids, we can construct the category corresponding to the 1-groupoid of a 1-type. *)

(** ** Definition of what it means to be a groupoid *)
Class IsGroupoid (C : PreCategory)
  := isgroupoid : forall s d (m : morphism C s d),
                    IsIsomorphism m.

Global Instance trunc_isgroupoid `{Funext} C : IsHProp (IsGroupoid C)
  := trunc_forall.

(** We don't want access to all of the internals of a groupoid category at top level. *)
Module GroupoidCategoryInternals.
  Section groupoid_category.
    Variable X : Type.
    Context `{IsTrunc 1 X}.

    Local Notation morphism := (@paths X).

    Definition compose s d d' (m : morphism d d') (m' : morphism s d)
    : morphism s d'
      := transitivity m' m.

    Definition identity x : morphism x x
      := reflexivity _.

    Global Arguments compose [s d d'] m m' / .
    Global Arguments identity x / .
  End groupoid_category.
End GroupoidCategoryInternals.

(** ** Categorification of the groupoid of a 1-type *)
Definition groupoid_category X `{IsTrunc 1 X} : PreCategory.
Proof.
  refine (@Build_PreCategory X
                             (@paths X)
                             (@GroupoidCategoryInternals.identity X)
                             (@GroupoidCategoryInternals.compose X)
                             _
                             _
                             _
                             _);
  simpl; intros; path_induction; reflexivity.
Defined.

Arguments groupoid_category X {_}.

Global Instance isgroupoid_groupoid_category X `{IsTrunc 1 X}
: IsGroupoid (groupoid_category X).
 Proof.
  intros s d m; simpl in *.
  exact (Build_IsIsomorphism
           (groupoid_category X)
           s d
           m m^%path
           (concat_pV m)
           (concat_Vp m)).
Defined.

(** ** 0-types give rise to strict (groupoid) categories *)
Lemma isstrict_groupoid_category X `{IsHSet X}
: IsStrictCategory (groupoid_category X).
Proof.
  typeclasses eauto.
Defined.
