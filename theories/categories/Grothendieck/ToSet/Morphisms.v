(** * Classification of morphisms of the Grothendieck Construction of a functor to Set *)
Require Import Category.Core Functor.Core.
Require Import Category.Morphisms.
Require Import SetCategory.Core.
Require Import Grothendieck.ToSet.Core.
Require Import HoTT.Basics.Equivalences HoTT.Types.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.
  Context {C : PreCategory}
          {F : Functor C set_cat}.

  Definition isequiv_sigma_category_isomorphism {s d : category F}
  : (s <~=~> d)%category <~> { e : (s.(c) <~=~> d.(c))%category | (F _1 e s.(x) = d.(x))%category }.
  Proof.
    simple refine (equiv_adjointify _ _ _ _).
    { intro m.
      simple refine (_; _).
      { exists (m : morphism _ _ _).1.
        exists (m^-1).1.
        { exact (ap projT1 (@left_inverse _ _ _ m _)). }
        { exact (ap projT1 (@right_inverse _ _ _ m _)). } }
      { exact (m : morphism _ _ _).2. } }
    { intro m.
      exists (m.1 : morphism _ _ _ ; m.2).
      eexists (m.1^-1;
               ((ap (F _1 (m.1)^-1) m.2)^)
                 @ (ap10 ((((composition_of F _ _ _ _ _)^)
                             @ (ap (fun m => F _1 m) (@left_inverse _ _ _ m.1 _))
                             @ (identity_of F _))
                          : (F _1 (m.1 : morphism _ _ _)^-1) o F _1 m.1 = idmap) s.(x)));
        apply path_sigma_hprop.
      exact left_inverse.
      exact right_inverse. }
    { intro x; apply path_sigma_hprop; apply path_isomorphic.
      reflexivity. }
    { intro x; apply path_isomorphic; reflexivity. }
  Defined.
End Grothendieck.
