(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** * Induced wild categories *)

(** A map A -> B of types where B is some type of category induces the same level of structure on A, via taking everything to be defined on the image.

This needs to be separate from Core because of HasEquivs usage.  We don't make these definitions Global Instances because we only want to apply them manually, but we make them Local Instances so that subsequent ones can pick up the previous ones automatically. *)

Section Induced_category.
  Context {A B : Type} (f : A -> B).

  Local Instance isgraph_induced `{IsGraph B} : IsGraph A.
  Proof.
    srapply Build_IsGraph.
    intros a1 a2. 
    exact (f a1 $-> f a2).
  Defined.

  Local Instance is01cat_induced `{Is01Cat B} : Is01Cat A.
  Proof.
    srapply Build_Is01Cat.
    + intro a. cbn in *. 
      exact (Id (f a)).
    + intros a b c; cbn in *; intros g1 g2.
      exact ( g1 $o g2).
  Defined.

  Local Instance is0gpd_induced `{Is0Gpd B} : Is0Gpd A.
  Proof.
    rapply Build_Is0Gpd.
    intros a b g; cbn in *; exact (g^$).
  Defined.

  (** The structure map along which we induce the category structure becomes a functor with respect to the induced structure *) 
  Local Instance is0functor_induced `{IsGraph B} : Is0Functor f.
  Proof.
    srapply Build_Is0Functor.
    intros a b. cbn in *. exact idmap.
  Defined.

  Local Instance is2graph_induced `{Is2Graph B} : Is2Graph A.
  Proof.
    intros a b.
    srapply Build_IsGraph.
    intros a1 a2.
    exact (fmap f a1 $-> fmap f a2).
  Defined.

  Local Instance is1cat_induced `{Is1Cat B} : Is1Cat A.
  Proof.
    srapply Build_Is1Cat;
      unfold isgraph_induced, is2graph_induced,
        is01cat_induced, is0functor_induced in *;
      cbn in *.
    + intros a b.
      rapply is01cat_hom.
    + intros a b.
      rapply is0gpd_hom.
    + intros a b c.
      rapply is0functor_postcomp.
    + intros a b c h.
      rapply is0functor_precomp.
    + intros a b c d u v w.
      rapply cat_assoc.
    + intros a b u.
      rapply cat_idl.
    + intros a b u.
      apply cat_idr.
  Defined.

  Local Instance is1functor_induced `{Is1Cat B} : Is1Functor f.
  Proof.
    srapply Build_Is1Functor.
    + intros a b g h. cbn in *. exact idmap.
    + intros a. cbn in *. exact (Id _).
    + intros a b c g h. cbn in *. exact (Id _). 
  Defined.

  Instance hasmorext_induced `{X : HasMorExt B} : HasMorExt A.
  Proof.
    constructor. intros. apply X.
  Defined.

  Definition hasequivs_induced `{HasEquivs B} : HasEquivs A.
  Proof.
    srapply Build_HasEquivs.
    + intros a b. exact (f a $<~> f b).
    + intros a b h. apply (CatIsEquiv' (f a) (f b)).
      exact (fmap f h).
    + intros a b; cbn in *. 
      intros g. exact( cate_fun g).
    + intros a b h; cbn in *. 
      exact (cate_isequiv' _ _ h ).
    + intros a b h; cbn in *. 
      exact ( cate_buildequiv' _ _ h).
    + intros a b h fe; cbn in *. 
      exact ( cate_buildequiv_fun' (f a) (f b) h fe) .
    + intros a b h; cbn in *.
      exact(cate_inv'  _ _ h ).
    + intros a b h; cbn in *.
      exact (cate_issect' _ _ h ).
    + intros a b h; cbn in *.
      exact (cate_isretr' _ _ _ ).
    + intros a b h g m n; cbn in *.  
      exact ( catie_adjointify' _ _ h g m n  ).
  Defined.

End Induced_category.
