Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.Prod.
Require Import WildCat.Bifunctor.

Declare Scope twocat.
Notation "f $=> g" := (Hom (A:=Hom _ _) f g) : twocat.
Local Open Scope twocat.

(** * Wild (2,1)-categories *)

(** This file introduces two basic 2-dimensional structures, (2,1)-categories and bicategories. Bicategories classically have 0-cells, 1-cells and 2-cells; our presentation includes 3-cells expressing coherence relations between 2-cells, that would classically be expressed as truncated equalities. The paradigmatic example of a bicategory is the bicategory of categories, functors and natural transformations. Other common bicategories are the bicategory of sets and spans, the bicategory of rings and ring bimodules, and the bicategory of categories and profunctors. A (2,1)-category is a bicategory where all 2-cells are invertible; a (2,1)-category can also be seen as an ordinary category extended with coherence conditions on 2-cells, expressed as 3-cells. *)

(** ** Wild 1-categorical structures *)

(** We start by introducing the common core of the theory of 1-categories and the theory of bicategories. A wild 1-bicategory is like a wild 1-category, but without the requirement that the 2-cells are invertible in general. The theory of 1-bicategories is the fragment of the theory of bicategories containing all 0-cells, 1-cells and 2-cells, but subject to no coherence conditions between 2-cells (which would require 3-cells to express.) *)
Class Is1Bicat (A : Type) `{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01bicat_hom :: forall (a b : A), Is01Cat (a $-> b) ;
  is0functor_bicat_postcomp :: forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_bicat_precomp :: forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  bicat_assoc : forall {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $=> h $o (g $o f);
  bicat_assoc_opp : forall {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $=> (h $o g) $o f;
  bicat_idl : forall {a b : A} (f : a $-> b), Id b $o f $=> f;
  bicat_idl_opp : forall {a b : A} (f : a $-> b), f $=> Id b $o f;
  bicat_idr : forall {a b : A} (f : a $-> b), f $o Id a $=> f;
  bicat_idr_opp : forall {a b : A} (f : a $-> b), f $=> f $o Id a;
}.

(** A wild 1-category is precisely a wild 1-bicategory such that the 2-cells are invertible. *)
Definition is1cat_is1bicat (A : Type) `{Is1Bicat A}
  (p : forall a b : A, Is0Gpd (Hom a b))
  : Is1Cat A.
Proof.
  rapply Build_Is1Cat.
  - exact (@bicat_assoc _ _ _ _ _).
  - exact (@bicat_assoc_opp _ _ _ _ _).
  - exact (@bicat_idl _ _ _ _ _).
  - exact (@bicat_idr _ _ _ _ _).
Defined.

(** Conversely, forgetting the inverses of 2-cells, one recovers a 1-bicategory from a 1-category. *)
Definition is1bicat_is1cat (A : Type) `{Is1Cat A}
  : Is1Bicat A.
Proof.
  rapply Build_Is1Bicat.
  - exact (@cat_assoc _ _ _ _ _).
  - exact (@cat_assoc_opp _ _ _ _ _).
  - exact (@cat_idl _ _ _ _ _).
  - intros a b f. symmetry. apply cat_idl.
  - exact (@cat_idr _ _ _ _ _).
  - intros a b f. symmetry. apply cat_idr.
Defined.

Notation "p $@R h" := (fmap (cat_precomp _ h) p) : twocat.
Notation "h $@L p" := (fmap (cat_postcomp _ h) p) : twocat.
Notation "a $| b" := (cat_comp (A:=Hom _ _) b a) : twocat.

Instance is0bifunctor_bicat_comp (A : Type) `{Is1Bicat A} (a b c : A)
  : Is0Bifunctor (cat_comp (a:=a) (b:=b) (c:=c))
  := Build_Is0Bifunctor'' _.

Instance Is0Functor_swap (A: Type) `{Is1Bicat A} (a b c : A)
  : Is0Functor (fun '(f,g) => cat_comp (a:=a) (b:=b) (c:=c) g f).
Proof.
  change (fun p => snd p $o fst p) with (fun p => (flip (cat_comp (a:=a) (b:=b) (c:=c)) (fst p) (snd p))).
  rapply (is0functor_bifunctor_uncurried (flip (cat_comp))).
  rapply is0bifunctor_flip.
Defined.

Notation "alpha $@@ beta" := (fmap11 cat_comp beta alpha) : twocat.

Instance Is0Functor_left_assoc (A: Type) `{Is1Bicat A} (a b c d : A):
  Is0Functor (fun p : (a $-> b) * (b $-> c) * (c $-> d) =>
                let '(f,g,h) := p in (h $o g) $o f).
Proof.
  simpl.
  constructor.
  intros ? ? [[alpha beta] gamma].
  exact (alpha $@@ (beta $@@ gamma)).
Defined.

Instance Is0Functor_right_assoc (A: Type) `{Is1Bicat A} (a b c d : A):
  Is0Functor (fun p : (a $-> b) * (b $-> c) * (c $-> d) =>
                let '(f,g,h) := p in h $o (g $o f)).
Proof.
  simpl.
  constructor.
  intros ? ? [[alpha beta] gamma].
  exact ((alpha $@@ beta) $@@ gamma).
Defined.

(** The full structure of a bicategory, incorporating all appropriate coherence conditions. *)
Class IsBicat (A : Type) `{H: Is1Bicat A} `{!Is3Graph A} :=
{
  is1cat_hom :: forall (a b : A), Is1Cat (a $-> b) ;
  is1functor_postcomp :: forall (a b c : A) (g : b $-> c), Is1Functor (cat_postcomp a g) ;
  is1functor_precomp :: forall (a b c : A) (f : a $-> b), Is1Functor (cat_precomp c f) ;
  bifunctor_coh_comp : forall {a b c : A} {f f' : a $-> b}  {g g' : b $-> c}
    (p : f $=> f') (p' : g $=> g'),
    (p' $@R f) $| (g' $@L p) $== (g $@L p) $| (p' $@R f');
  isnatural_bicat_assoc :: forall {a b c d : A},
    Is1Natural
      (fun '(f,g,h) => (h $o g) $o f)
      (fun '(f,g,h) => h $o (g $o f))
      (fun '(f,g,h) => bicat_assoc (Is1Bicat:=H) (a:=a) (b:=b) (c:=c) (d:=d) f g h);
  areinv_bicat_assoc :: forall {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d),
    AreInverse (bicat_assoc f g h) (bicat_assoc_opp f g h);
  areinv_bicat_idl :: forall {a b : A} (f : a $-> b),
    AreInverse (bicat_idl f) (bicat_idl_opp f);
  areinv_bicat_idr :: forall {a b : A} (f : a $-> b),
    AreInverse (bicat_idr f) (bicat_idr_opp f);
  isnatural_bicat_idl :: forall {a b : A}, Is1Natural _ _ (bicat_idl (a:=a) (b:=b));
  isnatural_bicat_idr :: forall {a b : A}, Is1Natural _ _ (bicat_idr (a:=a) (b:=b));
  bicat_pentagon : forall {a b c d e : A}
                     (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e),
      (k $@L bicat_assoc f g h) $o (bicat_assoc f (h $o g) k) $o (bicat_assoc g h k $@R f)
      $== (bicat_assoc (g $o f) h k) $o (bicat_assoc f g (k $o h)) ;
  bicat_tril : forall {a b c : A} (f : a $-> b) (g : b $-> c),
      (g $@L bicat_idl f) $o (bicat_assoc f (Id b) g) $== (bicat_idr g $@R f)
}.

(** A (2,1)-category is a bicategory such that all 2-cells have a unique inverse. Here we have chosen to define (2,1)-categories as extending the theory of bicategories, but the theory of (2,1)-categories also extends the theory of 1-categories with coherence conditions on 2-cells. TODO: Give a constructor to upgrade a 1-category to a (2,1)-category by adding appropriate coherence conditions. *)
Class Is21Cat (A : Type) `{IsBicat A} :=
{
  is0gpd_hom :: forall (a b : A), Is0Gpd (a $-> b) ;
  is1gpd_hom :: forall (a b : A), Is1Gpd (a $-> b) ;
}.

(** *** Whiskering functoriality *)

Definition cat_postwhisker_pp {A} `{IsBicat A} {a b c : A}
  {f g h : a $-> b} (k : b $-> c) (p : f $=> g) (q : g $=> h)
  : k $@L (p $| q) $== (k $@L p) $| (k $@L q)
  := fmap_comp _ _ _.

Definition cat_prewhisker_pp {A} `{IsBicat A} {a b c : A}
  {f g h : b $-> c} (k : a $-> b) (p : f $=> g) (q : g $=> h)
  : (p $| q) $@R k $== (p $@R k) $| (q $@R k)
  := fmap_comp _ _ _.

Instance is1bifunctor_bicat_comp {A: Type} `{IsBicat A} {a b c : A} :
  Is1Bifunctor (cat_comp (a:=a) (b:=b) (c:=c)).
Proof.
  rapply Build_Is1Bifunctor''.
  intros.
  apply bifunctor_coh_comp.
Defined.

(** *** Exchange law *)

Definition cat_exchange {A : Type} `{IsBicat A} {a b c : A}
  {f f' f'' : a $-> b} {g g' g'' : b $-> c}
  (p : f $=> f') (q : f' $=> f'') (r : g $=> g') (s : g' $=> g'')
  : (p $| q) $@@ (r $| s) $== (p $@@ r) $| (q $@@ s)
  := fmap11_comp _ _ _ _ _.
