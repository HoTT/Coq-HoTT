(** * Definition of a univalent/saturated precategory *)
Require Import Category.Core Category.Morphisms.
Require Import HoTT.Tactics Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

(** A univalent category is a category for which [idtoiso] is an equivalence. *)

Notation IsUnivalentCategory C
  := (forall s d : object C, IsEquiv (@idtoiso C s d)).

Notation isotoid C s d := (@equiv_inv _ _ (@idtoiso C s d) _).

(** *** The objects of a univalent category are a 1-type *)

Global Instance trunc_category `{IsUnivalentCategory C} : IsTrunc 1 C | 10000.
Proof.
  intros ? ?.
  eapply trunc_equiv';
  [ symmetry;
    esplit;
    apply_hyp
  | ].
  typeclasses eauto.
Qed.

Record UnivalentCategory :=
  {
    unicat :> Category;
    isunivalentcat_unicat :> IsUnivalentCategory unicat
  }.

Global Existing Instance isunivalentcat_unicat.
