(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.

(** * Equivalences in wild categories *)

(** We could define equivalences in any wild 2-category as bi-invertible maps, or in a wild 3-category as half-adjoint equivalences.  However, in concrete cases there is often an equivalent definition of equivalences that we want to use instead, and the important property we need is that it's logically equivalent to (quasi-)isomorphism. *)

Class HasEquivs (A : Type) `{Is1Cat A} :=
{
  CatEquiv' : A -> A -> Type where "a $<~> b" := (CatEquiv' a b);
  CatIsEquiv' : forall a b, (a $-> b) -> Type;
  cate_fun' : forall a b, (a $<~> b) -> (a $-> b);
  cate_isequiv' : forall a b (f : a $<~> b), CatIsEquiv' a b (cate_fun' a b f);
  cate_buildequiv' : forall a b (f : a $-> b), CatIsEquiv' a b f -> CatEquiv' a b;
  cate_buildequiv_fun' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
      cate_fun' a b (cate_buildequiv' a b f fe) $== f;
  cate_inv' : forall a b (f : a $-> b), CatIsEquiv' a b f -> (b $-> a);
  cate_issect' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
    cate_inv' _ _ f fe $o f $== Id a;
  cate_isretr' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
      f $o cate_inv' _ _ f fe $== Id b;
  catie_adjointify' : forall a b (f : a $-> b) (g : b $-> a)
    (r : f $o g $== Id b) (s : g $o f $== Id a), CatIsEquiv' a b f;
}.

(** Since apparently a field of a record can't be the source of a coercion (Coq complains about the uniform inheritance condition, although as officially stated that condition appears to be satisfied), we redefine all the fields of [HasEquivs]. *)

Definition CatEquiv {A} `{HasEquivs A} (a b : A)
  := @CatEquiv' A _ _ _ a b.

Notation "a $<~> b" := (CatEquiv a b).
Arguments CatEquiv : simpl never.

Definition cate_fun {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : a $-> b
  := @cate_fun' A _ _ _ a b f.

Coercion cate_fun : CatEquiv >-> Hom.

(* Being an equivalence should be a typeclass, but we have to redefine it.  (Apparently [Existing Class] doesn't work.) *)
Class CatIsEquiv {A} `{HasEquivs A} {a b : A} (f : a $-> b)
  := catisequiv : CatIsEquiv' a b f.

Global Instance cate_isequiv {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : CatIsEquiv f
  := cate_isequiv' a b f.

Definition Build_CatEquiv {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : a $<~> b
  := cate_buildequiv' a b f fe.

Definition cate_buildequiv_fun {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : cate_fun (Build_CatEquiv f) $== f
  := cate_buildequiv_fun' a b f fe.

Definition catie_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $== Id b) (s : g $o f $== Id a)
  : CatIsEquiv f
  := catie_adjointify' a b f g r s.

Definition cate_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $== Id b) (s : g $o f $== Id a)
  : a $<~> b
  := @Build_CatEquiv _ _ _ _ a b f (catie_adjointify f g r s).

(** This one we define to construct the whole inverse equivalence. *)
Definition cate_inv {A} `{HasEquivs A} {a b : A} (f : a $-> b) {fe : CatIsEquiv f}
  : b $<~> a.
Proof.
  simple refine (cate_adjointify _ _ _ _).
  - exact (@cate_inv' A _ _ _ a b f fe).
  - exact f.
  - exact (@cate_issect' A _ _ _ a b f fe).
  - exact (@cate_isretr' A _ _ _ a b f fe).
Defined.

Notation "f ^-1$" := (cate_inv f).

Definition cate_issect {A} `{HasEquivs A} {a b} (f : a $-> b) {fe : CatIsEquiv f}
  : f^-1$ $o f $== Id a.
Proof.
  refine (_ $@ @cate_issect' A _ _ _ a b f fe).
  refine (_ $@R f).
  apply cate_buildequiv_fun'.
Defined.

Definition cate_isretr {A} `{HasEquivs A} {a b} (f : a $-> b) {fe : CatIsEquiv f}
  : f $o f^-1$ $== Id b.
Proof.
  refine (_ $@ @cate_isretr' A _ _ _ a b f fe).
  refine (f $@L _).
  apply cate_buildequiv_fun'.
Defined.

(** The identity morphism is an equivalence *)
Global Instance catie_id {A} `{HasEquivs A} (a : A)
  : CatIsEquiv (Id a)
  := catie_adjointify (Id a) (Id a) (cat_idl (Id a)) (cat_idl (Id a)).

Definition id_cate {A} `{HasEquivs A} (a : A)
  : a $<~> a
  := Build_CatEquiv (Id a).

Global Instance reflexive_cate {A} `{HasEquivs A}
  : Reflexive (@CatEquiv A _ _ _)
  := id_cate.

Global Instance symmetric_cate {A} `{HasEquivs A}
  : Symmetric (@CatEquiv A _ _ _)
  := fun a b f => cate_inv f.

(** Equivalences can be composed. *)
Definition compose_cate {A} `{HasEquivs A} {a b c : A}
  (g : b $<~> c) (f : a $<~> b) : a $<~> c.
Proof.
  refine (cate_adjointify (g $o f) (f^-1$ $o g^-1$) _ _).
  - refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L cat_assoc_opp _ _ _) $@ _).
    refine ((_ $@L (cate_isretr _ $@R _)) $@ _).
    refine ((_ $@L cat_idl _) $@ _).
    apply cate_isretr.
  - refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L cat_assoc_opp _ _ _) $@ _).
    refine ((_ $@L (cate_issect _ $@R _)) $@ _).
    refine ((_ $@L cat_idl _) $@ _).
    apply cate_issect.
Defined.

Notation "g $oE f" := (compose_cate g f).

Definition compose_cate_fun {A} `{HasEquivs A}
           {a b c : A} (g : b $<~> c) (f : a $<~> b)
  : cate_fun (g $oE f) $== g $o f.
Proof.
  apply cate_buildequiv_fun.
Defined.

Definition compose_cate_funinv {A} `{HasEquivs A}
           {a b c : A} (g : b $<~> c) (f : a $<~> b)
  : g $o f $== cate_fun (g $oE f).
Proof.
  apply gpd_rev.
  apply cate_buildequiv_fun.
Defined.

Definition id_cate_fun {A} `{HasEquivs A} (a : A) 
  : cate_fun (id_cate a) $== Id a.
Proof.
  apply cate_buildequiv_fun.
Defined.

Definition compose_cate_assoc {A} `{HasEquivs A}
           {a b c d : A} (f : a $<~> b) (g : b $<~> c) (h : c $<~> d)
  : cate_fun ((h $oE g) $oE f) $== cate_fun (h $oE (g $oE f)).
Proof.
  refine (compose_cate_fun _ f $@ _ $@ cat_assoc f g h $@ _ $@
                           compose_cate_funinv h _).
  - refine (compose_cate_fun h g $@R _).
  - refine (_ $@L compose_cate_funinv g f).
Defined.

Definition compose_cate_idl {A} `{HasEquivs A}
           {a b : A} (f : a $<~> b)
  : cate_fun (id_cate b $oE f) $== cate_fun f.
Proof.
  refine (compose_cate_fun _ f $@ _ $@ cat_idl f).
  refine (cate_buildequiv_fun _ $@R _).
Defined.

Definition compose_cate_idr {A} `{HasEquivs A}
           {a b : A} (f : a $<~> b)
  : cate_fun (f $oE id_cate a) $== cate_fun f.
Proof.
  refine (compose_cate_fun f _ $@ _ $@ cat_idr f).
  refine (_ $@L cate_buildequiv_fun _).
Defined.

Global Instance transitive_cate {A} `{HasEquivs A}
  : Transitive (@CatEquiv A _ _ _)
  := fun a b c f g => g $oE f.

(** Any sufficiently coherent functor preserves equivalences.  *)
Global Instance iemap {A B : Type} `{HasEquivs A} `{HasEquivs B}
       (F : A -> B) `{!Is0Functor F, !Is1Functor F}
       {a b : A} (f : a $-> b) {fe : CatIsEquiv f}
  : CatIsEquiv (fmap F f).
Proof.
  refine (catie_adjointify (fmap F f) (fmap F f^-1$) _ _).
  - refine ((fmap_comp F f^-1$ f)^$ $@ fmap2 F (cate_isretr _) $@ fmap_id F _).
  - refine ((fmap_comp F f f^-1$)^$ $@ fmap2 F (cate_issect _) $@ fmap_id F _).
Defined.

Definition emap {A B : Type} `{HasEquivs A} `{HasEquivs B}
           (F : A -> B) `{!Is0Functor F, !Is1Functor F}
           {a b : A} (f : a $<~> b)
  : F a $<~> F b
  := Build_CatEquiv (fmap F f).

(** When we have equivalences, we can define what it means for a category to be univalent. *)
Definition cat_equiv_path {A : Type} `{HasEquivs A} (a b : A)
  : (a = b) -> (a $<~> b).
Proof.
  intros []; reflexivity.
Defined.

Class IsUnivalent1Cat (A : Type) `{HasEquivs A}
  := { isequiv_cat_equiv_path : forall a b, IsEquiv (@cat_equiv_path A _ _ _ a b) }.
Global Existing Instance isequiv_cat_equiv_path.

Definition cat_path_equiv {A : Type} `{IsUnivalent1Cat A} (a b : A)
  : (a $<~> b) -> (a = b)
  := (cat_equiv_path a b)^-1.

(** ** Core of a 1-category *)

Record core (A : Type) := { uncore : A }.
Arguments uncore {A} c.

Global Instance is01cat_core {A : Type} `{HasEquivs A}
  : Is01Cat (core A).
Proof.
  srapply Build_Is01Cat ; cbv.
  - intros a b ; exact (uncore a $<~> uncore b).
  - intros; apply id_cate.
  - intros a b c ; apply compose_cate.
Defined.

Global Instance is01cat_core_hom {A : Type} `{HasEquivs A} (a b : core A)
  : Is01Cat (a $-> b).
Proof.
  srapply Build_Is01Cat.
  - intros f g ; exact (cate_fun f $== cate_fun g).
  - intro f ; apply Id.
  - intros f g h ; apply cat_comp.
Defined.

Global Instance is0gpd_core_hom {A : Type} `{HasEquivs A} (a b : core A)
  : Is0Gpd (a $-> b).
Proof.
  apply Build_Is0Gpd.
  intros f g ; cbv.
  apply gpd_rev.
Defined.

Global Instance is0functor_core_postcomp {A : Type} `{HasEquivs A}
       (a b c : core A) (h : b $-> c) :
  Is0Functor (cat_postcomp a h).
Proof.
  apply Build_Is0Functor.
  intros f g al; cbn in h.
  exact (compose_cate_fun h f
           $@ (h $@L al)
           $@ (compose_cate_fun h g)^$).
Defined.

Global Instance is0functor_core_precomp {A : Type} `{HasEquivs A}
       (a b c : core A) (h : a $-> b) :
  Is0Functor (cat_precomp c h).
Proof.
  apply Build_Is0Functor.
  intros f g al; cbn in h.
  exact (compose_cate_fun f h
           $@ (al $@R h)
           $@ (compose_cate_fun g h)^$).
Defined.

Global Instance is1cat_core {A : Type} `{HasEquivs A}
  : Is1Cat (core A).
Proof.
  rapply Build_Is1Cat.
  - intros; apply compose_cate_assoc.
  - intros; apply compose_cate_idl.
  - intros; apply compose_cate_idr.
Defined.

Global Instance is0gpd_core {A : Type} `{HasEquivs A}
  : Is0Gpd (core A).
Proof.
  apply Build_Is0Gpd.
  intros a b f; cbn in *; exact (f^-1$).
Defined.

Global Instance is1gpd_core {A : Type} `{HasEquivs A}
  : Is1Gpd (core A).
Proof.
  apply Build_Is1Gpd; cbn ; intros a b f;
    refine (compose_cate_fun _ _ $@ _ $@ (id_cate_fun _)^$).
  - apply cate_issect.
  - apply cate_isretr.
Defined.
