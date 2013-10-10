Require Import Category.Core Category.Morphisms.
Require Import HoTT.Tactics Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Notation IsCategory C := (forall s d : object C, IsEquiv (@idtoiso C s d)).

Notation isotoid C s d := (@equiv_inv _ _ (@idtoiso C s d) _).

Instance trunc_category `{IsCategory C} : IsTrunc 1 C | 10000.
Proof.
  intros ? ?.
  eapply trunc_equiv';
  [ apply symmetry;
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

Existing Instance iscategory_precategory_of_category.
