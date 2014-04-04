Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Morphisms NaturalTransformation.Paths.
Require Import SetCategory.Core.
Require Import FunextVarieties HSet HProp Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Lemma isisomorphism_set_cat_natural_transformation_paths
      `{fs : Funext, fs' : Funext, fs'' : Funext} (X : @set_cat fs) C D F G
      (T1 T2 : morphism (@set_cat fs) X (BuildhSet (@NaturalTransformation C D F G) (@trunc_natural_transformation fs'' _ _ _ _)))
      (H : forall x y, T1 x y = T2 x y)
      `{@IsIsomorphism (@set_cat fs) _ _ T1}
: @IsIsomorphism (@set_cat fs) _ _ T2.
Proof.
  exists (T1^-1)%morphism;
  abstract (
      first [ apply @iso_moveR_Vp
            | apply @iso_moveR_pV ];
      repeat first [ intro
                   | progress unfold Overture.compose
                   | solve [ auto
                           | symmetry; auto ]
                   | apply (@path_forall (@Funext_downward_closed fs'))
                   | path_natural_transformation ]
    ).
Defined.

Section equiv_iso_set_cat.
  (** Isomorphisms in [set_cat] and [prop_cat] are eqivalent to equivalences. *)
  Context `{fs : Funext, fs_extra : Funext}.

  Definition isiso_isequiv s d (m : morphism (@set_cat fs) s d)
             `{IsEquiv _ _ m}
  : IsIsomorphism m
    := Build_IsIsomorphism
         (@set_cat fs) s d
         m m^-1%equiv
         (@path_forall (@Funext_downward_closed fs_extra) _ _ _ _ (eissect _))
         (@path_forall (@Funext_downward_closed fs_extra) _ _ _ _ (eisretr _)).

  Definition isequiv_isiso s d (m : morphism (@set_cat fs) s d)
             `{IsIsomorphism _ _ _ m}
  : IsEquiv m
    := BuildIsEquiv
         _ _
         m m^-1%morphism
         (ap10 right_inverse)
         (ap10 left_inverse)
         (fun _ => allpath_hprop _ _).

  Definition iso_equiv (s d : @set_cat fs) (m : s <~> d)
  : s <~=~> d
    := Build_Isomorphic
         (@isiso_isequiv s d m m).

  Global Instance isequiv_isiso_isequiv s d
  : IsEquiv (@iso_equiv s d) | 0.
  Proof.
    refine (isequiv_adjointify
              (@iso_equiv s d)
              (fun m => BuildEquiv _ _ _ (@isequiv_isiso s d m m))
              _
              _);
    simpl in *;
    clear;
    abstract (
        intros [? ?]; simpl;
        unfold iso_equiv; simpl;
        apply ap;
        pose proof (@Funext_downward_closed fs_extra);
        apply allpath_hprop
      ).
  Defined.
End equiv_iso_set_cat.

Section equiv_iso_prop_cat.
  (** Isomorphisms in [set_cat] and [prop_cat] are eqivalent to equivalences. *)
  Context `{fs : Funext, fs_extra : Funext}.
  Let fs_extra' := @Funext_downward_closed fs_extra.

  Definition isiso_isequiv_prop s d (m : morphism (@prop_cat fs) s d)
             `{IsEquiv _ _ m}
  : IsIsomorphism m
    := Build_IsIsomorphism
         prop_cat s d
         m m^-1%equiv
         (@path_forall fs_extra' _ _ _ _ (eissect _))
         (@path_forall fs_extra' _ _ _ _ (eisretr _)).

  Definition isequiv_isiso_prop s d (m : morphism (@prop_cat fs) s d)
             `{IsIsomorphism _ _ _ m}
  : IsEquiv m
    := BuildIsEquiv
         _ _
         m m^-1%morphism
         (ap10 right_inverse)
         (ap10 left_inverse)
         (fun _ => allpath_hprop _ _).

  Definition iso_equiv_prop (s d : @prop_cat fs) (m : s <~> d)
  : s <~=~> d
    := Build_Isomorphic
         (@isiso_isequiv_prop s d m m).

  Global Instance isequiv_isiso_isequiv_prop s d
  : IsEquiv (@iso_equiv_prop s d) | 0.
  Proof.
    refine (isequiv_adjointify
              (@iso_equiv_prop s d)
              (fun m => BuildEquiv _ _ _ (@isequiv_isiso_prop s d m m))
              _
              _);
    simpl in *;
    clear;
    abstract (
        intros [? ?]; simpl;
        unfold iso_equiv_prop; simpl;
        apply ap;
        pose proof (@Funext_downward_closed fs_extra);
        apply allpath_hprop
      ).
  Defined.
End equiv_iso_prop_cat.
