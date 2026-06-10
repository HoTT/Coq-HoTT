(** * Additive categories

    Semi-additive categories in which morphism addition admits inverses,
    so that hom-sets are abelian groups and composition is bilinear. *)

From HoTT Require Import Basics.Overture Basics.Tactics.
From HoTT.Classes.interfaces Require Import canonical_names abstract_algebra.
From HoTT.Classes.theory Require Import groups.
From HoTT.Categories Require Import Category.Core Functor.Core.
From HoTT.Categories.Functor Require Import Identity Composition.Core.
From HoTT.Categories.Additive Require Import ZeroObjects Biproducts SemiAdditive.
From HoTT.Algebra.AbGroups Require Import AbelianGroup.

Local Open Scope morphism_scope.

(** This lets us use "+", "-" and "0" notation for the commutative monoid
    structure on hom-sets defined in SemiAdditive.v. *)
Local Open Scope mc_add_scope.

(** ** Definition of additive category

    The commutative monoid structure on hom-sets of a semi-additive category
    is canonical, so an additive category only needs to assume that each
    morphism has an additive inverse. *)

Class AdditiveCategory := {
  additive_semiadditive :: SemiAdditiveCategory;

  additive_inverse :: forall (X Y : object additive_semiadditive),
    Inverse (morphism additive_semiadditive X Y);

  additive_inverse_l : forall {X Y : object additive_semiadditive}
    (f : morphism additive_semiadditive X Y),
    (- f) + f = 0;
}.

Coercion additive_semiadditive : AdditiveCategory >-> SemiAdditiveCategory.

(** ** Hom-sets are abelian groups *)

Section HomAbGroup.
  Context {A : AdditiveCategory} {X Y : object A}.

  (** The inverse law on the other side follows by commutativity. *)
  Definition additive_inverse_r (f : morphism A X Y)
    : f + (- f) = 0
    := morphism_addition_commutative f (- f) @ additive_inverse_l f.

  #[export] Instance isabgroup_morphisms : IsAbGroup (morphism A X Y).
  Proof.
    split.
    - split.
      + exact _.
      + exact additive_inverse_l.
      + exact additive_inverse_r.
    - exact _.
  Defined.

  (** The bundled abelian group of morphisms from [X] to [Y]. *)
  Definition abgroup_hom : AbGroup
    := Build_AbGroup' (morphism A X Y) _ _ _ _.

End HomAbGroup.

Arguments abgroup_hom {A} X Y.

(** ** Negation and composition *)

(** Additive inverses are unique. *)
Definition inverse_morphism_unique {A : AdditiveCategory} {X Y : object A}
  {f g : morphism A X Y} (H : g + f = 0)
  : g = - f
  := grp_moveL_1V (G:=abgroup_hom X Y) H.

(** Negation is compatible with precomposition. *)
Definition inverse_precompose {A : AdditiveCategory} {X Y W : object A}
  (f : morphism A X Y) (a : morphism A W X)
  : (- f) o a = - (f o a).
Proof.
  apply inverse_morphism_unique.
  lhs_V napply addition_precompose.
  refine (ap (fun g => g o a) (additive_inverse_l f) @ _).
  napply zero_morphism_left.
Qed.

(** Negation is compatible with postcomposition. *)
Definition inverse_postcompose {A : AdditiveCategory} {X Y W : object A}
  (a : morphism A Y W) (f : morphism A X Y)
  : a o (- f) = - (a o f).
Proof.
  apply inverse_morphism_unique.
  lhs_V napply addition_postcompose.
  refine (ap (fun g => a o g) (additive_inverse_l f) @ _).
  napply zero_morphism_right.
Qed.

(** ** Additive functors

    A functor between additive categories is additive when its action on
    each hom-set is a monoid homomorphism for the canonical addition.
    Such functors automatically preserve zero morphisms and negation. *)

Record AdditiveFunctor (A B : AdditiveCategory) := {
  add_functor :> Functor A B;

  addfunctor_monoid :: forall (X Y : object A),
    IsMonoidPreserving (@morphism_of _ _ add_functor X Y);
}.

Arguments add_functor {A B} F : rename.
Arguments addfunctor_monoid {A B} F X Y : rename.

Section AdditiveFunctorLaws.
  Context {A B : AdditiveCategory} (F : AdditiveFunctor A B)
    {X Y : object A}.

  (** Additive functors preserve addition of morphisms. *)
  Definition additive_functor_preserves_addition (f g : morphism A X Y)
    : morphism_of F (f + g) = morphism_of F f + morphism_of F g
    := preserves_sg_op f g.

  (** Additive functors preserve zero morphisms. *)
  Definition additive_functor_preserves_zero_morphisms
    : morphism_of F (zero_morphism X Y) = zero_morphism (F X) (F Y)
    := preserves_mon_unit.

  (** Additive functors preserve negation. *)
  Definition additive_functor_preserves_inverse (f : morphism A X Y)
    : morphism_of F (- f) = - morphism_of F f
    := preserves_inverse f.

End AdditiveFunctorLaws.

(** The identity functor is additive. *)
Definition id_additive_functor (A : AdditiveCategory)
  : AdditiveFunctor A A.
Proof.
  snapply Build_AdditiveFunctor.
  - exact 1%functor.
  - intros X Y.
    split.
    + intros f g.
      reflexivity.
    + reflexivity.
Defined.

(** Additive functors compose. *)
Definition compose_additive_functors {A B C : AdditiveCategory}
  (G : AdditiveFunctor B C) (F : AdditiveFunctor A B)
  : AdditiveFunctor A C.
Proof.
  snapply Build_AdditiveFunctor.
  - exact (G o F)%functor.
  - intros X Y.
    split.
    + intros f g.
      refine (ap (fun h => morphism_of G h) (preserves_sg_op f g) @ _).
      exact (preserves_sg_op _ _).
    + refine (ap (fun h => morphism_of G h) preserves_mon_unit @ _).
      exact preserves_mon_unit.
Defined.
