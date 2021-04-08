(** * Saturation of the Grothendieck Construction of a functor to Set *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core.
Require Import HoTT.Categories.Category.Univalent.
Require Import HoTT.Categories.Category.Morphisms.
Require Import HoTT.Categories.SetCategory.Core.
Require Import HoTT.Categories.Grothendieck.ToSet.Core HoTT.Categories.Grothendieck.ToSet.Morphisms.
Require Import HoTT.Basics.Equivalences HoTT.Basics.Trunc.
Require Import HoTT.Types.Universe HoTT.Types.Paths HoTT.Types.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Univalence}.

  Variable C : PreCategory.
  Context `{IsCategory C}.
  Variable F : Functor C set_cat.

  Definition category_isotoid_helper {s d} (a : c s = c d)
  : (transport (fun c : C => F c) a (x s) = x d)
      <~> (F _1 (idtoiso C a)) (x s) = x d.
  Proof.
    apply equiv_path.
    apply ap10, ap.
    destruct a; simpl.
    exact (ap10 (identity_of F _)^ _).
  Defined.

  Arguments category_isotoid_helper : simpl never.

  Definition category_isotoid {s d : category F}
  : s = d <~> (s <~=~> d)%category.
  Proof.
    refine (isequiv_sigma_category_isomorphism^-1 oE _ oE (equiv_ap' (issig_pair F)^-1 s d)).
    refine (_ oE (equiv_path_sigma _ _ _)^-1).
    simpl.
    simple refine (equiv_functor_sigma' _ _).
    { exists (@idtoiso C _ _).
      exact _. }
    { exact category_isotoid_helper. }
  Defined.

  Global Instance preservation : IsCategory (category F).
  Proof.
    intros s d.
    refine (@isequiv_homotopic _ _ category_isotoid (idtoiso (category F) (x:=s) (y:=d)) _ _).
    intro x.
    destruct x; apply path_isomorphic, path_sigma_hprop.
    reflexivity.
  Defined.
End Grothendieck.
