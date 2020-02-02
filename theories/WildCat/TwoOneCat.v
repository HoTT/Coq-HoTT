Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Prod.
Require Import WildCat.NatTrans.

(** * Wild (2,1)-categories *)

Class Is21Cat (A : Type) `{Is1Cat A} :=
{
  is1cat_hom : forall (a b : A), Is1Cat (a $-> b) ;
  is1gpd_hom : forall (a b : A), Is1Gpd (a $-> b) ;
  is1functor_postcomp : forall (a b c : A) (g : b $-> c), Is1Functor (cat_postcomp a g) ;
  is1functor_precomp : forall (a b c : A) (f : a $-> b), Is1Functor (cat_precomp c f) ;

  (** Naturality of the associator in each variable separately *)
  is1natural_cat_assoc_l : forall (a b c d : A) (f : a $-> b) (g : b $-> c),
      Is1Natural (cat_precomp d f o cat_precomp d g) (cat_precomp d (g $o f))
                 (cat_assoc f g);
  is1natural_cat_assoc_m : forall (a b c d : A) (f : a $-> b) (h : c $-> d),
      Is1Natural (cat_precomp d f o cat_postcomp b h) (cat_postcomp a h o cat_precomp c f)
                 (fun g => cat_assoc f g h);
  is1natural_cat_assoc_r : forall (a b c d : A) (g : b $-> c) (h : c $-> d),
      Is1Natural (cat_postcomp a (h $o g)) (cat_postcomp a h o cat_postcomp a g)
                 (fun f => cat_assoc f g h);

  (** Naturality of the unitors *)
  is1natural_cat_idl : forall (a b : A),
      Is1Natural (cat_postcomp a (Id b)) idmap
                 cat_idl ;

  is1natural_cat_idr : forall (a b : A),
      Is1Natural (cat_precomp b (Id a)) idmap
                 cat_idr;

  (** *** Coherence *)
  cat_pentagon : forall (a b c d e : A)
                        (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e),
      (k $@L cat_assoc f g h) $o (cat_assoc f (h $o g) k) $o (cat_assoc g h k $@R f)
      $== (cat_assoc (g $o f) h k) $o (cat_assoc f g (k $o h)) ;

  cat_tril : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      (g $@L cat_idl f) $o (cat_assoc f (Id b) g) $== (cat_idr g $@R f)
}.

Global Existing Instance is1cat_hom.
Global Existing Instance is1gpd_hom.
Global Existing Instance is1functor_precomp.
Global Existing Instance is1functor_postcomp.
Global Existing Instance is1natural_cat_assoc_l.
Global Existing Instance is1natural_cat_assoc_m.
Global Existing Instance is1natural_cat_assoc_r.
Global Existing Instance is1natural_cat_idl.
Global Existing Instance is1natural_cat_idr.
