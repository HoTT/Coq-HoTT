(* -*- mode: coq; mode: visual-line -*-  *)
From Coq Require Setoids.Setoid Classes.CMorphisms
  Classes.CRelationClasses.
Require Import Basics WildCat.Core.
Import CMorphisms.ProperNotations.


  (** Every Transitive crelation gives rise to a binary morphism on [impl],
   contravariant in the first argument, covariant in the second. *)
  
(* #[export] Instance trans_contra_co_type_morphism {A : Type} *)
(*   {R : Relation A} `(Transitive A R) *)
(*   : CMorphisms.Proper (R --> R ++> CRelationClasses.arrow) R. *)
(* Proof with auto. *)
(*   intros x y X x0 y0 X0 X1. *)
(*   transitivity x... *)
(*   transitivity x0... *)
(* Defined. *)
Print CMorphisms.ProperProxy.
(* #[export] Instance paths_proper_proxy {A : Type} {a : A} *)
(*   : CMorphisms.ProperProxy (@paths A) a := reflexivity a. *)


#[export] Instance reflexive_proper_proxy {A : Type}
  {R : Relation A} `(Reflexive A R) (x : A)
  : CMorphisms.ProperProxy R x := reflexivity x.

(* forall (x y : A), x $== y -> forall (a b : A), a $== b -> y $== b -> x $==a *)
#[export] Instance IsProper_GpdHom_from {A : Type} `{Is0Gpd A}
  : CMorphisms.Proper
      (GpdHom ==>
         GpdHom ==>
         CRelationClasses.flip CRelationClasses.arrow) GpdHom.
Proof.
  intros x y eq_xy a b eq_ab eq_yb.
  exact (transitivity eq_xy (transitivity eq_yb
                              (symmetry _ _ eq_ab))).
Defined.

(* forall (x y : A), x $== y -> forall (a b : A), a $== b -> x $== a -> y $== b *)
#[export] Instance IsProper_GpdHom_to {A : Type} `{Is0Gpd A}
  : CMorphisms.Proper
      (GpdHom ==>
         GpdHom ==>
         CRelationClasses.arrow) GpdHom.
Proof.
  intros x y eq_xy a b eq_ab eq_yb.
  unshelve refine (transitivity _ eq_ab).
  unshelve refine (transitivity _ eq_yb).
  exact (symmetry _ _ eq_xy).
Defined.

(* forall a : A, x $== y -> a $== x -> a $== y *)
#[export] Instance IsProper_GpdHom_to_a {A : Type} `{Is0Gpd A}
  {a : A}
  : CMorphisms.Proper
      (GpdHom ==>
         CRelationClasses.arrow) (GpdHom a).
Proof.
  intros x y eq_xy eq_ax.
  now transitivity x.
Defined.

(* forall a : A, x $== y -> a $== y -> a $== x *)
#[export] Instance IsProper_GpdHom_from_a {A : Type} `{Is0Gpd A}
  {a : A}
  : CMorphisms.Proper
      (GpdHom ==>
         CRelationClasses.flip CRelationClasses.arrow) (GpdHom a).
Proof.
  intros x y eq_xy eq_ay.
  exact (transitivity eq_ay (symmetry _ _ eq_xy)).
Defined.

Locate "_ --> _".
Open Scope signatureT_scope.

#[export] Instance symmetry_flip {A B: Type} {f : A -> B}
  {R : Relation A} {R' : Relation B} `{Symmetric _ R}
  (H0 : CMorphisms.Proper (R ++> R') f)
  : CMorphisms.Proper (R --> R') f.
Proof.
  intros a b Rab.
  apply H0. unfold CRelationClasses.flip. symmetry. exact Rab.
Defined.

#[export] Instance symmetric_flip_snd {A B C: Type} {R : Relation A}
  {R' : Relation B} {R'' : Relation C} `{Symmetric _ R'}
  (f : A -> B -> C) (H1 : CMorphisms.Proper (R ++> R' ++> R'') f)
  : CMorphisms.Proper (R ++> R' --> R'') f.
Proof.
  intros a b Rab x y R'yx. apply H1; [ assumption | symmetry; assumption ].
Defined.  

Goal forall (A : Type) `(H : Is0Gpd A) (a b c : A),
    a $== b -> b $== c -> a $== c.
Proof.
  intros A ? ? ? a b c eq_ab eq_bc.
  rewrite eq_ab, <- eq_bc.
Abort.
Goal forall (A : Type) `(H : Is0Gpd A) (a b c : A),
    a $== b -> b $== c -> a $== c.
Proof.
  intros A ? ? ? a b c eq_ab eq_bc.
  symmetry.
  rewrite eq_ab, <- eq_bc.
  rewrite eq_bc.
  rewrite <- eq_bc.
Abort.

#[export] Instance IsProper_fmap {A B: Type} `{Is1Cat A} `{Is1Cat A} (F : A -> B) `{Is1Functor _ _ F} (a b : A)
  : CMorphisms.Proper (GpdHom ==> GpdHom) (@fmap _ _ _ _ F _ a b) := fun _ _ eq => fmap2 F eq.

Goal forall (A B : Type) (F : A -> B) `{Is1Functor _ _ F} (a b : A) (f g : a $-> b), f $== g -> fmap F f $== fmap F g.
Proof.
  do 17 intro.
  intro eq_fg.
  rewrite eq_fg.
  Abort.
    Check @cat_comp.
#[export] Instance IsProper_catcomp_g {A : Type} `{Is1Cat A} {a b c : A} (g : b $-> c)
      : CMorphisms.Proper (GpdHom ==> GpdHom) (@cat_comp _ _ _ a b c g).
Proof.
  intros f1 f2.
  apply (is0functor_postcomp a b c g ).
Defined.
                  
Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f1 f2 : a $-> b) (g : b $-> c), f1 $== f2 -> g $o f1 $== g $o f2.
Proof.
  do 11 intro.
  intro eq.
  rewrite <- eq.
  rewrite eq.
Abort.

#[export] Instance IsProper_catcomp {A : Type} `{Is1Cat A} {a b c : A}
  : CMorphisms.Proper (GpdHom ==> GpdHom ==> GpdHom) (@cat_comp _ _ _ a b c).
Proof.
  intros g1 g2 eq_g f1 f2 eq_f.
  rewrite eq_f.
  apply (is0functor_precomp a b c f2).
  exact eq_g.
Defined.

Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f : a $-> b) (g1 g2 : b $-> c), g1 $== g2 -> g1 $o f $== g2 $o f.
Proof.
  do 11 intro.
  intro eq.
  rewrite <- eq.
  rewrite eq.
  rewrite <- eq.
  Abort.

Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f1 f2 : a $-> b) (g1 g2 : b $-> c), g1 $== g2 -> f1 $== f2 -> g1 $o f1 $== g2 $o f2.
Proof.
  do 12 intro.
  intros eq_g eq_f.
  rewrite eq_g.
  rewrite <- eq_f.
  rewrite eq_f.
  rewrite <- eq_g.
Abort.


Require Import WildCat.Bifunctor WildCat.Prod.

#[export] Instance Is1Functor_uncurry_bifunctor {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C)
  `{forall a, Is0Functor (F a)}
  `{forall a, Is1Functor (F a)} 
  `{forall b, Is0Functor (Forall.flip F b)}
  `{forall b, Is1Functor (Forall.flip F b)}  
  `{@IsBifunctor A B C _ _ _ _ _ _ F _ _} 
  : Is1Functor (uncurry F).
Proof.
  nrapply Build_Is1Functor.
  - intros [a1 a2] [b1 b2] [f1 f2] [g1 g2] [eq_fg1 eq_fg2];
      cbn in f1, f2, g1, g2, eq_fg1, eq_fg2; cbn.
    rewrite eq_fg1, eq_fg2.
    reflexivity.
  - intros [a b]; cbn.
    (* rewrite fmap_id generates an extra goal. Not sure how to get typeclass resolution to figure this out automatically. *)
    rewrite (fmap_id _).
    rewrite (fmap_id _).
    rewrite cat_idl.
    reflexivity.
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 f2] [g1 g2];
      cbn in f1, f2, g1, g2.
    cbn.
    rewrite (fmap_comp _).
    rewrite (fmap_comp _).
    rewrite cat_assoc.
    rewrite <- (cat_assoc _ (fmap (F a1) g2)).
    rewrite <- (isbifunctor F f1 g2).
    rewrite ! cat_assoc.
    reflexivity.
Defined.
    
