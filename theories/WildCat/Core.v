(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.

(** * Wild categories, functors, and transformations *)

(** ** Directed graphs *)

Class IsGraph (A : Type) :=
{
  Hom : A -> A -> Type
}.

Notation "a $-> b" := (Hom a b).

(** ** 0-categorical structures *)

(** A wild (0,1)-category has 1-morphisms and operations on them, but no coherence. *)
Class Is01Cat (A : Type) := Build_Is01Cat'
{
  isgraph_1cat : IsGraph A;
  Id  : forall (a : A), a $-> a;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Global Existing Instance isgraph_1cat.
Arguments cat_comp {A _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).

Definition Build_Is01Cat A
           (Hom' : A -> A -> Type)
           (Id'  : forall (a : A), Hom' a a)
           (cat_comp' : forall (a b c : A), Hom' b c -> Hom' a b -> Hom' a c)
  : Is01Cat A
  := Build_Is01Cat' A (Build_IsGraph A Hom') Id' cat_comp'.

(** A wild 0-groupoid is a wild (0,1)-category whose morphisms can be reversed.  This is also known as a setoid. *)
Class Is0Gpd (A : Type) `{Is01Cat A} :=
  { gpd_rev : forall {a b : A}, (a $-> b) -> (b $-> a) }.

Definition GpdHom {A} `{Is0Gpd A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).

Global Instance reflexive_GpdHom {A} `{Is0Gpd A}
  : Reflexive GpdHom
  := fun a => Id a.

Definition gpd_comp {A} `{Is0Gpd A} {a b c : A}
  : (a $== b) -> (b $== c) -> (a $== c)
  := fun p q => q $o p.
Infix "$@" := gpd_comp.

Global Instance transitive_GpdHom {A} `{Is0Gpd A}
  : Transitive GpdHom
  := fun a b c f g => f $@ g.

Notation "p ^$" := (gpd_rev p).

Global Instance symmetric_GpdHom {A} `{Is0Gpd A}
  : Symmetric GpdHom
  := fun a b f => f^$.

Definition GpdHom_path {A} `{Is0Gpd A} {a b : A} (p : a = b)
  : a $== b.
Proof.
  destruct p; apply Id.
Defined.

(** A 0-functor acts on morphisms, but satisfies no axioms. *)
Class Is0Functor {A B : Type} `{IsGraph A} `{IsGraph B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments fmap {_ _ _ _} F {_ _ _} f.

(** Products preserve (0,1)-categories. *)
Global Instance isgraph_prod A B `{IsGraph A} `{IsGraph B}
  : IsGraph (A * B)
  := Build_IsGraph (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)).

Global Instance is01cat_prod A B `{Is01Cat A} `{Is01Cat B}
  : Is01Cat (A * B).
Proof.
  refine (Build_Is01Cat (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)) _ _).
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

(** To avoid having to define a separate notion of "two-variable functor", we define two-variable functors in uncurried form.  The following definition applies such a two-variable functor, with a currying built in. *)
Definition fmap11 {A B C : Type} `{IsGraph A} `{IsGraph B} `{IsGraph C}
  (F : A -> B -> C) {H2 : Is0Functor (uncurry F)}
  {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2)
  : F a1 b1 $-> F a2 b2
  := @fmap _ _ _ _ (uncurry F) H2 (a1, b1) (a2, b2) (f1, f2).


(** ** Wild 1-categorical structures *)

(** A wild 1-category (a.k.a. (1,1)-category) has its hom-types enhanced to 0-groupoids, its composition operations to 0-functors, and its composition associative and unital up to these 2-cells. *)
Class Is1Cat (A : Type) `{Is01Cat A} :=
{
  is01cat_hom : forall (a b : A), Is01Cat (a $-> b) ;
  isgpd_hom : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_comp : forall (a b c : A), Is0Functor (uncurry (@cat_comp A _ a b c)) ;
  cat_assoc : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_idl : forall a b (f : a $-> b), Id b $o f $== f;
  cat_idr : forall a b (f : a $-> b), f $o Id a $== f;
}.
Global Existing Instance is01cat_hom.
Global Existing Instance isgpd_hom.
Global Existing Instance is0functor_comp.
Arguments cat_assoc {_ _ _ _ _ _ _} f g h.
Arguments cat_idl {_ _ _ _ _} f.
Arguments cat_idr {_ _ _ _ _} f.

Definition cat_assoc_opp {A : Type} `{Is1Cat A}
           {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : h $o (g $o f) $== (h $o g) $o f
  := (cat_assoc f g h)^$.

Definition Comp2 {A} `{Is1Cat A} {a b c : A}
           {f g : a $-> b} {h k : b $-> c}
           (q : h $-> k) (p : f $-> g)
  : (h $o f $-> k $o g)
  := fmap11 cat_comp q p.

Infix "$o@" := Comp2.

Definition WhiskerL_Htpy {A} `{Is1Cat A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $== g)
  : h $o f $== h $o g
  := (Id h) $o@ p.
Notation "h $@L p" := (WhiskerL_Htpy h p).

Definition WhiskerR_Htpy {A} `{Is1Cat A} {a b c : A}
           {f g : b $-> c} (p : f $== g) (h : a $-> b)
  : f $o h $== g $o h
  := p $o@ (Id h).
Notation "p $@R h" := (WhiskerR_Htpy p h).

(** Often, the coherences are actually equalities rather than homotopies. *)
Class Is1Cat_Strong (A : Type) `{Is01Cat A} := 
{
  is01cat_hom_strong : forall (a b : A), Is01Cat (a $-> b) ;
  isgpd_hom_strong : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_comp_strong : forall (a b c : A), Is0Functor (uncurry (@cat_comp A _ a b c)) ;
  cat_assoc_strong : forall (a b c d : A)
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f);
  cat_idl_strong : forall (a b : A) (f : a $-> b), Id b $o f = f;
  cat_idr_strong : forall (a b : A) (f : a $-> b), f $o Id a = f;
}.

Arguments cat_assoc_strong {_ _ _ _ _ _ _} f g h.
Arguments cat_idl_strong {_ _ _ _ _} f.
Arguments cat_idr_strong {_ _ _ _ _} f.

Definition cat_assoc_opp_strong {A : Type} `{Is1Cat_Strong A}
           {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : h $o (g $o f) = (h $o g) $o f
  := (cat_assoc_strong f g h)^.

Global Instance is1cat_is1cat_strong (A : Type) `{Is1Cat_Strong A}
  : Is1Cat A.
Proof.
  srefine (Build_Is1Cat A _ _ _ _ _ _ _).
  all:intros a b.
  - apply is01cat_hom_strong.
  - apply isgpd_hom_strong.
  - apply is0functor_comp_strong.
  - intros; apply GpdHom_path, cat_assoc_strong.
  - intros; apply GpdHom_path, cat_idl_strong.
  - intros; apply GpdHom_path, cat_idr_strong.
Defined.

(** Generalizing function extensionality, "Morphism extensionality" states that homwise [GpdHom_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is1Cat A} :=
  { isequiv_Htpy_path : forall a b f g, IsEquiv (@GpdHom_path (a $-> b) _ _ f g) }.
Global Existing Instance isequiv_Htpy_path.

Definition path_hom {A} `{HasMorExt A} {a b : A} {f g : a $-> b} (p : f $== g) : f = g
  := GpdHom_path^-1 p.

(** A 1-functor acts on 2-cells (satisfying no axioms) and also preserves composition and identities up to a 2-cell. *)
Class Is1Functor {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (* The [!] tells Coq to use typeclass search to find the [IsGraph] parameters of [Is0Functor] instead of assuming additional copies of them. *)
      (F : A -> B) `{!Is0Functor F} :=
{
  fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) ;
  fmap_id : forall a, fmap F (Id a) $== Id (F a);
  fmap_comp : forall a b c (f : a $-> b) (g : b $-> c),
    fmap F (g $o f) $== fmap F g $o fmap F f;
}.

Arguments fmap2 {A B _ _ _ _} F {_ _ _ _ _ _} p.
Arguments fmap_id {A B _ _ _ _} F {_ _} a.
Arguments fmap_comp {A B _ _ _ _} F {_ _ _ _ _} f g.


(** ** Natural transformations *)

Definition Transformation {A B : Type} `{IsGraph B} (F : A -> B) (G : A -> B)
  := forall (a : A), F a $-> G a.

Notation "F $=> G" := (Transformation F G).

(** A 1-natural transformation is natural up to a 2-cell, so its domain must be a 1-category. *)
Class Is1Natural {A B : Type} `{IsGraph A} `{Is1Cat B}
      (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
      (alpha : F $=> G) :=
{
  isnat : forall a b (f : a $-> b),
    alpha b $o fmap F f $== fmap G f $o alpha a;
}.

Arguments isnat {_ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

Definition isnat_opp {A B : Type} `{IsGraph A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      (alpha : F $=> G) `{!Is1Natural F G alpha}
      {a b : A} (f : a $-> b)
  : fmap G f $o alpha a $== alpha b $o fmap F f
  := (isnat alpha f)^$.

Definition id_transformation {A B : Type} `{Is01Cat B} (F : A -> B)
  : F $=> F
  := fun a => Id (F a).

Global Instance is1natural_id {A B : Type} `{IsGraph A} `{Is1Cat B}
       (F : A -> B) `{!Is0Functor F}
  : Is1Natural F F (id_transformation F).
Proof.
  apply Build_Is1Natural; intros a b f; cbn.
  refine (cat_idl (fmap F f) $@ (cat_idr (fmap F f))^$).
Defined.

Definition comp_transformation {A B : Type} `{Is01Cat B}
           {F G K : A -> B} (gamma : G $=> K) (alpha : F $=> G)
  : F $=> K
  := fun a => gamma a $o alpha a.

Global Instance is1natural_comp {A B : Type} `{IsGraph A} `{Is1Cat B}
       {F G K : A -> B} `{!Is0Functor F} `{!Is0Functor G} `{!Is0Functor K}
       (gamma : G $=> K) `{!Is1Natural G K gamma}
       (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural F K (comp_transformation gamma alpha).
Proof.
  apply Build_Is1Natural; intros a b f; cbn.
  refine (cat_assoc _ _ _ $@ _).
  refine ((gamma b $@L isnat alpha f) $@ _).
  refine (cat_assoc_opp _ _ _ $@ _).
  refine ((isnat gamma f) $@R alpha a $@ _).
  exact (cat_assoc _ _ _).
Defined.  

(** Modifying a transformation to something pointwise equal preserves naturality. *)
Definition is1natural_homotopic {A B : Type} `{Is01Cat A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      {alpha : F $=> G} (gamma : F $=> G) `{!Is1Natural F G gamma}
      (p : forall a, alpha a $== gamma a)
  : Is1Natural F G alpha.
Proof.
  refine (Build_Is1Natural _ _ _ _ _ F _ G _ alpha _); intros a b f.
  refine ((p b $@R fmap F f) $@ _).
  refine (_ $@ (fmap G f $@L (p a)^$)).
  apply (isnat gamma).
Defined.

(** Identity functor *)

Section IdentityFunctor.

  Context {A : Type} `{Is1Cat A}.

  Global Instance is0functor_idmap : Is0Functor idmap.
  Proof.
    by apply Build_Is0Functor.
  Defined.

  Global Instance is1functor_idmap : Is1Functor idmap.
  Proof.
    by apply Build_Is1Functor.
  Defined.

End IdentityFunctor.

(** Constant functor *)

Section ConstantFunctor.

  Context {A B : Type}.

  Global Instance is0coh1functor_const
    `{IsGraph A} `{Is01Cat B} (x : B)
    : Is0Functor (fun _ : A => x).
  Proof.
    serapply Build_Is0Functor.
    intros a b f; apply Id.
  Defined.

  Global Instance is1functor_const
         `{Is1Cat A} `{Is1Cat B} (x : B)
    : Is1Functor (fun _ : A => x).
  Proof.
    serapply Build_Is1Functor.
    - intros a b f g p; apply Id.
    - intro; apply Id.
    - intros a b c f g. cbn.
      symmetry.
      apply cat_idl.
  Defined.

End ConstantFunctor.

(** Composite functors *)

Section CompositeFunctor.

  Context {A B C : Type} `{Is1Cat A} `{Is1Cat B} `{Is1Cat C}
          (F : A -> B) `{!Is0Functor F, !Is1Functor F}
          (G : B -> C) `{!Is0Functor G, !Is1Functor G}.

  Global Instance is0functor_compose : Is0Functor (G o F).
  Proof.
    srapply Build_Is0Functor.
    intros a b f; exact (fmap G (fmap F f)).
  Defined.

  Global Instance is1functor_compose : Is1Functor (G o F).
  Proof.
    srapply Build_Is1Functor.
    - intros a b f g p; exact (fmap2 G (fmap2 F p)).
    - intros a; exact (fmap2 G (fmap_id F a) $@ fmap_id G (F a)).
    - intros a b c f g.
      refine (fmap2 G (fmap_comp F f g) $@ _).
      exact (fmap_comp G (fmap F f) (fmap F g)).
  Defined.

End CompositeFunctor.

(** More products *)

Global Instance is0gpd_prod A B `{Is0Gpd A} `{Is0Gpd B}
 : Is0Gpd (A * B).
Proof. 
  serapply Build_Is0Gpd.
  intros [x1 x2] [y1 y2] [f1 f2].
  cbn in *.
  exact ( (f1^$, f2^$) ).
Defined.

Global Instance is1cat_prod A B `{Is1Cat A} `{Is1Cat B}
  : Is1Cat (A * B).
Proof.
  serapply (Build_Is1Cat).
  - intros [x1 x2] [y1 y2].
    rapply is01cat_prod.
  - intros [x1 x2] [y1 y2].
    apply is0gpd_prod.
    + cbn.
      apply isgpd_hom.
    + cbn.
      apply isgpd_hom.
  - intros [x1 x2] [y1 y2] [z1 z2].
    serapply Build_Is0Functor.  
    intros f g. unfold uncurry.
    destruct f as [[f11 f12] [f21 f22]].
    destruct g as [[g11 g12] [g21 g22]]. cbn in *. 
    intros a. destruct a as [[a11 a12][a21 a22]].
    exact ( a11 $o@ a21, a12 $o@ a22).
  - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2].
    cbn in *. 
    exact(cat_assoc f1 g1 h1, cat_assoc f2 g2 h2).
  - intros [a1 a2] [b1 b2] [f1 f2].
    cbn in *.
    exact (cat_idl _, cat_idl _).
  - intros [a1 a2] [b1 b2] [g1 g2].
    cbn in *.
    exact (cat_idr _, cat_idr _). 
Defined. 

(** ** Wild 1-groupoids *)

Class Is1Gpd (A : Type) `{Is1Cat A, !Is0Gpd A} :=
{ 
  gpd_issect : forall {a b : A} (f : a $-> b), f^$ $o f $== Id a ;
  gpd_isretr : forall {a b : A} (f : a $-> b), f $o f^$ $== Id b ;
}.

(** Wild (2,1)-categories *)

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

Definition cat_assoc_transformation {A : Type} `{Is1Cat A} {a b c d : A}
  : (cat_comp_lassoc a b c d) $=> (cat_comp_rassoc a b c d).
Proof.
  intros [[f g] h] ; exact (cat_assoc f g h).
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

Definition cat_idl_transformation {A : Type} `{Is1Cat A} {a b : A}
  : cat_comp_idl a b $=> idmap.
Proof.
  intro f ; exact (cat_idl f).
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
