Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.

(** * Wild (2,1)-categories *)

Class Is21Cat (A : Type) `{Is1Cat A, !Is3Graph A} :=
{
  is1cat_hom : forall (a b : A), Is1Cat (a $-> b) ;
  is1gpd_hom : forall (a b : A), Is1Gpd (a $-> b) ;
  is1functor_postcomp : forall (a b c : A) (g : b $-> c), Is1Functor (cat_postcomp a g) ;
  is1functor_precomp : forall (a b c : A) (f : a $-> b), Is1Functor (cat_precomp c f) ;
  bifunctor_coh_comp : forall {a b c : A} {f f' : a $-> b}  {g g' : b $-> c}
    (p : f $== f') (p' : g $== g'),
    (p' $@R f) $@ (g' $@L p) $== (g $@L p) $@ (p' $@R f') ;

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

  (** Coherence *)
  cat_pentagon : forall (a b c d e : A)
                        (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e),
      (k $@L cat_assoc f g h) $o (cat_assoc f (h $o g) k) $o (cat_assoc g h k $@R f)
      $== (cat_assoc (g $o f) h k) $o (cat_assoc f g (k $o h)) ;

  cat_tril : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      (g $@L cat_idl f) $o (cat_assoc f (Id b) g) $== (cat_idr g $@R f)
}.

Existing Instance is1cat_hom.
Existing Instance is1gpd_hom.
Existing Instance is1functor_precomp.
Existing Instance is1functor_postcomp.
Existing Instance is1natural_cat_assoc_l.
Existing Instance is1natural_cat_assoc_m.
Existing Instance is1natural_cat_assoc_r.
Existing Instance is1natural_cat_idl.
Existing Instance is1natural_cat_idr.

(** *** Whiskering functoriality *)

Definition cat_postwhisker_pp {A} `{Is21Cat A} {a b c : A}
  {f g h : a $-> b} (k : b $-> c) (p : f $== g) (q : g $== h)
  : k $@L (p $@ q) $== (k $@L p) $@ (k $@L q)
  := fmap_comp _ _ _.

Definition cat_prewhisker_pp {A} `{Is21Cat A} {a b c : A}
  {f g h : b $-> c} (k : a $-> b) (p : f $== g) (q : g $== h)
  : (p $@ q) $@R k $== (p $@R k) $@ (q $@R k)
  := fmap_comp _ _ _.

(** *** Exchange law *)

Definition cat_exchange {A : Type} `{Is21Cat A} {a b c : A}
  {f f' f'' : a $-> b} {g g' g'' : b $-> c}
  (p : f $== f') (q : f' $== f'') (r : g $== g') (s : g' $== g'')
  : (p $@ q) $@@ (r $@ s) $== (p $@@ r) $@ (q $@@ s).
Proof.
  unfold "$@@".
  (** We use the distributivity of [$@R] and [$@L] in a (2,1)-category (since they are functors) to see that we have the same data on both sides of the 3-morphism. *)
  nrefine ((_ $@L cat_prewhisker_pp _ _ _ ) $@ _).
  nrefine ((cat_postwhisker_pp _ _ _ $@R _) $@ _).
  (** Now we reassociate and whisker on the left and right. *)
  nrefine (cat_assoc _ _ _ $@ _).
  refine (_ $@ (cat_assoc _ _ _)^$).
  nrefine (_ $@L _).
  refine (_ $@ cat_assoc _ _ _).
  refine ((cat_assoc _ _ _)^$ $@ _).
  nrefine (_ $@R _).
  (** Finally we are left with the bifunctoriality condition for left and right whiskering which is part of the data of the (2,1)-cat. *)
  apply bifunctor_coh_comp.
Defined.
