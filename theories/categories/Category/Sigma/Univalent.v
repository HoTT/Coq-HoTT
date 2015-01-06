(** * Lifting saturation from categories to sigma/subcategories *)
Require Import Category.Core Category.Morphisms.
Require Import Category.Univalent.
Require Import Category.Sigma.Core Category.Sigma.OnObjects Category.Sigma.OnMorphisms.
Require Import HoTT.Types.Sigma HoTT.Basics.Equivalences HoTT.Basics.Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation sigT_type := Coq.Init.Specif.sigT.
Local Notation pr1_type := Overture.pr1.

Local Open Scope morphism_scope.
Local Open Scope equiv_scope.
Local Open Scope function_scope.

(** ** Lift saturation to sigma on objects whenever the property is an hProp *)
Section onobjects.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Global Instance iscategory_sigT_obj `{forall a, IsHProp (Pobj a), A_cat : IsCategory A}
  : IsCategory (sigT_obj A Pobj).
  Proof.
    intros s d.
    refine (isequiv_homotopic
              ((issig_full_isomorphic (sigT_obj A Pobj) _ _ o (issig_full_isomorphic A _ _)^-1)
                 o (@idtoiso A s.1 d.1)
                 o pr1_path)
              _).
    intro x; destruct x.
    reflexivity.
  Defined.

  (** The converse is not true; consider [Pobj := fun _ => Empty]. *)
End onobjects.

(** TODO: Lift saturation to sigma on objects whenever the property is automatically and uniquely true of isomorphisms *)
(** To do this, we have to show that [IsCategory] respects equivalences on morphisms. *)
