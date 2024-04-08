(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** * Induced wild categories *)

(** A map [A -> B] of types, where [B] is some type of wild category, induces the same level of structure on [A], via taking everything to be defined on the image.

This needs to be separate from Core because of HasEquivs usage.  We don't make these definitions Global Instances because we only want to apply them manually, but we make them Local Instances so that subsequent ones can pick up the previous ones automatically. *)

(** In most of the proofs, we only want to use [intro] on variables of type [A], so this will be handy. *)
Ltac intros_of_type A :=
  repeat match goal with |- forall (a : A), _ => intro a end.

Section Induced_category.
  Context {A B : Type} (f : A -> B).

  Local Instance isgraph_induced `{IsGraph B} : IsGraph A.
  Proof.
    nrapply Build_IsGraph.
    intros a1 a2. 
    exact (f a1 $-> f a2).
  Defined.

  Local Instance is01cat_induced `{Is01Cat B} : Is01Cat A.
  Proof.
    nrapply Build_Is01Cat; intros_of_type A; cbn.
    + apply Id.
    + apply cat_comp.
  Defined.

  Local Instance is0gpd_induced `{Is0Gpd B} : Is0Gpd A.
  Proof.
    nrapply Build_Is0Gpd; intros_of_type A; cbn.
    apply gpd_rev.
  Defined.

  (** The structure map along which we induce the category structure becomes a functor with respect to the induced structure. *)
  Local Instance is0functor_induced `{IsGraph B} : Is0Functor f.
  Proof.
    nrapply Build_Is0Functor; intros_of_type A; cbn.
    exact idmap.
  Defined.

  Local Instance is2graph_induced `{Is2Graph B} : Is2Graph A.
  Proof.
    constructor; cbn. apply isgraph_hom.
  Defined.

  Local Instance is1cat_induced `{Is1Cat B} : Is1Cat A.
  Proof.
    snrapply Build_Is1Cat; intros_of_type A; cbn.
    + rapply is01cat_hom.
    + nrapply is0gpd_hom.
    + rapply is0functor_postcomp.
    + rapply is0functor_precomp.
    + rapply cat_assoc.
    + rapply cat_idl.
    + rapply cat_idr.
  Defined.

  Local Instance is1functor_induced `{Is1Cat B} : Is1Functor f.
  Proof.
    srapply Build_Is1Functor; intros_of_type A; cbn.
    + intros g h. exact idmap.
    + exact (Id _).
    + intros g h. exact (Id _).
  Defined.

  Instance hasmorext_induced `{HasMorExt B} : HasMorExt A.
  Proof.
    constructor. intros_of_type A; cbn. rapply isequiv_Htpy_path.
  Defined.

  Definition hasequivs_induced `{HasEquivs B} : HasEquivs A.
  Proof.
    srapply Build_HasEquivs; intros a b; cbn.
    + exact (f a $<~> f b).
    + apply CatIsEquiv.
    + apply cate_fun.
    + apply cate_isequiv.
    + apply cate_buildequiv'.
    + nrapply cate_buildequiv_fun'.
    + apply cate_inv'.
    + nrapply cate_issect'.
    + nrapply cate_isretr'.
    + nrapply catie_adjointify'.
  Defined.

End Induced_category.
