(** * Definition of a univalent/saturated precategory, or just "category" *)
Require Import Category.Core Category.Morphisms.
Require Import HoTT.Basics HoTT.Types HoTT.Tactics Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

(** A category is a precategory for which [idtoiso] is an equivalence. *)

Notation IsCategory C := (forall s d : object C, IsEquiv (@idtoiso C s d)).

Notation isotoid C s d := (@equiv_inv _ _ (@idtoiso C s d) _).

(** *** The objects of a category are a 1-type *)

Global Instance trunc_category `{IsCategory C} : IsTrunc 1 C | 10000.
Proof.
  intros ? ?.
  eapply trunc_equiv';
  [ symmetry;
    esplit;
    apply_hyp
  | ].
  typeclasses eauto.
Qed.

Record Category :=
  {
    precategory_of_category :> PreCategory;
    iscategory_precategory_of_category :> IsCategory precategory_of_category
  }.

Global Existing Instance iscategory_precategory_of_category.
