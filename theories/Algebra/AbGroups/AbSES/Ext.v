Require Import Basics Types Pointed WildCat WildCat.Profunctor.
Require Import AbGroups.AbelianGroup AbSES.Core.
Require Import AbSES.Pullback AbSES.Pushout BaerSum.

(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup) := Tr 0 (AbSES B A).

Global Instance ispointed_ext {B A : AbGroup} : IsPointed (Ext B A) := tr (point _).

(** An extension [E : AbSES B A] is trivial in [Ext B A] if and only if [E] merely splits. *)
Proposition iff_ab_ext_trivial_split `{Univalence} {B A : AbGroup} (E : AbSES B A)
  : merely {s : GroupHomomorphism B E & (projection _) $o s == idmap}
           <~> (tr E = point (Ext B A)).
Proof.
  refine (equiv_path_Tr _ _ oE _).
  srapply equiv_iff_hprop;
    apply Trunc_functor;
    apply iff_abses_trivial_split.
Defined.

Definition Ext' (B A : AbGroup) := Tr 0 (AbSES' B A).

Global Instance isprofunctor_ext' `{Univalence}
  : IsProfunctor Ext' := isprofunctor_compose _ _.
