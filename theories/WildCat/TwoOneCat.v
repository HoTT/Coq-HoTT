Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Square.
Require Import WildCat.Prod.
Require Import WildCat.NatTrans.

(** * Wild (2,1)-categories *)

Definition cat_comp_lassoc {A : Type} `{Is1Cat A} (a b c d : A)
  : (a $-> b) * (b $-> c) * (c $-> d) -> a $-> d.
Proof.
  intros [[f g] h].
  exact ((h $o g) $o f).
Defined.

Definition cat_comp_rassoc {A : Type} `{Is1Cat A} (a b c d : A)
  : (a $-> b) * (b $-> c) * (c $-> d) -> a $-> d.
Proof.
  intros [[f g] h].
  exact (h $o (g $o f)).
Defined.

Global Instance is01cat_cat_assoc_dom {A : Type} `{Is1Cat A}
       {a b c d : A} : Is01Cat ((a $-> b) * (b $-> c) * (c $-> d)).
Proof.
  rapply is01cat_prod.
Defined.

Global Instance is0functor_cat_comp_lassoc
       {A : Type} `{Is1Cat A}
       {a b c d : A} : Is0Functor (cat_comp_lassoc a b c d).
Proof.
  apply Build_Is0Functor.
  intros [[f g] h] [[f' g'] h'] [[al be] ga] ;
    exact (fmap11 cat_comp (fmap11 cat_comp ga be) al).
Defined.

Global Instance is0functor_cat_comp_rassoc
       {A : Type} `{Is1Cat A}
       {a b c d : A} : Is0Functor (cat_comp_rassoc a b c d).
Proof.
  apply Build_Is0Functor.
  intros [[f g] h] [[f' g'] h'] [[al be] ga] ;
    exact (fmap11 cat_comp ga (fmap11 cat_comp be al)).
Defined.


Definition cat_comp_idl {A : Type} `{Is1Cat A} (a b : A)
  : (a $-> b) -> (a $-> b)
  := fun (f : a $-> b) => Id b $o f.

Global Instance is0functor_cat_comp_idl {A : Type} `{Is1Cat A} (a b : A)
  : Is0Functor (cat_comp_idl a b).
Proof.
  apply Build_Is0Functor.
  intros f g p; unfold cat_comp_idl; cbn.
  exact (Id b $@L p).
Defined.



Definition cat_comp_idr {A : Type} `{Is1Cat A} (a b : A)
  : (a $-> b) -> (a $-> b)
  := fun (f : a $-> b) => f $o Id a.

Global Instance is0functor_cat_comp_idr {A : Type} `{Is1Cat A} (a b : A)
  : Is0Functor (cat_comp_idr a b).
Proof.
  apply Build_Is0Functor.
  intros f g p; unfold cat_comp_idr; cbn.
  exact (p $@R Id a).
Defined.


Definition cat_assoc_transformation {A : Type} `{Is1Cat A} {a b c d : A}
  : (cat_comp_lassoc a b c d) $=> (cat_comp_rassoc a b c d).
Proof.
  intros [[f g] h] ; exact (cat_assoc f g h).
Defined.

Definition cat_idl_transformation {A : Type} `{Is1Cat A} {a b : A}
  : cat_comp_idl a b $=> idmap.
Proof.
  intro f ; exact (cat_idl f).
Defined.


Definition cat_idr_transformation {A : Type} `{Is1Cat A} {a b : A}
  : cat_comp_idr a b $=> idmap.
Proof.
  intro f ; exact (cat_idr f).
Defined.

Class Is21Cat (A : Type) `{Is1Cat A} :=
{
  is1cat_hom : forall (a b : A), Is1Cat (a $-> b) ;
  is1gpd_hom : forall (a b : A), Is1Gpd (a $-> b) ;
  is1functor_comp : forall (a b c : A),
      Is1Functor (uncurry (@cat_comp A _ a b c)) ;

  (** *** Associator *)
  is1natural_cat_assoc : forall (a b c d : A),
      Is1Natural (cat_comp_lassoc a b c d) (cat_comp_rassoc a b c d)
                 cat_assoc_transformation ;

  (** *** Unitors *)
  is1natural_cat_idl : forall (a b : A),
      Is1Natural (cat_comp_idl a b) idmap
                 cat_idl_transformation;

  is1natural_cat_idr : forall (a b : A),
      Is1Natural (cat_comp_idr a b) idmap
                 cat_idr_transformation;

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
Global Existing Instance is1functor_comp.
Global Existing Instance is1natural_cat_assoc.
Global Existing Instance is1natural_cat_idl.
Global Existing Instance is1natural_cat_idr.