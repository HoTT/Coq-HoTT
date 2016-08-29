(** * Indiscrete category *)
Require Import Category.Core Functor.Core Category.Strict Category.Univalent Category.Morphisms.
Require Import Types.Unit Trunc HoTT.Tactics Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

(** ** Definition of an indiscrete category *)
Module Export Core.
  Section indiscrete_category.
    (** The indiscrete category has exactly one morphism between any two
      objects. *)
    Variable X : Type.

    (** We define the symmetrized version of associaitivity differently
      so that the dual of an indiscrete category is convertible with
      the indiscrete category. *)

    Definition indiscrete_category : PreCategory
      := @Build_PreCategory' X
                             (fun _ _ => Unit)
                             (fun _ => tt)
                             (fun _ _ _ _ _ => tt)
                             (fun _ _ _ _ _ _ _ => idpath)
                             (fun _ _ _ _ _ _ _ => idpath)
                             (fun _ _ f => match f with tt => idpath end)
                             (fun _ _ f => match f with tt => idpath end)
                             (fun _ => idpath)
                             _.
  End indiscrete_category.

  (** *** Indiscrete categories are strict categories *)
  Definition isstrict_indiscrete_category `{H : IsHSet X}
  : IsStrictCategory (indiscrete_category X)
    := H.

  (** *** Indiscrete categories are (saturated/univalent) categories *)
  Global Instance iscategory_indiscrete_category `{H : IsHProp X}
  : IsCategory (indiscrete_category X).
  Proof.
    intros.

    eapply (isequiv_adjointify
              (idtoiso (indiscrete_category X) (x := s) (y := d))
              (fun _ => center _));
      abstract (
          repeat intro;
          destruct_head_hnf @Isomorphic;
          destruct_head_hnf @IsIsomorphism;
          destruct_head_hnf @Unit;
          path_induction_hammer
        ).
  Defined.
End Core.

(** ** Functors to an indiscrete category are given by their action on objects *)
Module Functors.
  Section to.
    Variable X : Type.
    Variable C : PreCategory.
    Variable objOf : C -> X.

    Definition to : Functor C (indiscrete_category X)
      := Build_Functor C (indiscrete_category X)
                       objOf
                       (fun _ _ _ => tt)
                       (fun _ _ _ _ _ => idpath)
                       (fun _ => idpath).
  End to.
End Functors.
