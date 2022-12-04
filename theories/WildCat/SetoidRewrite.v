(* -*- mode: coq; mode: visual-line -*-  *)

(* Init.Tactics contains the definition of the Coq stdlib typeclass_inferences database. It must be imported before Basics.Overture. *)
From Coq Require Init.Tactics.
Require Import Basics.
From Coq Require Setoids.Setoid Classes.CMorphisms
  Classes.CRelationClasses.
Require Import WildCat.Core.
Import CMorphisms.ProperNotations.

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

#[export] Instance IsProper_fmap {A B: Type} `{Is1Cat A}
  `{Is1Cat A} (F : A -> B) `{Is1Functor _ _ F} (a b : A)
  : CMorphisms.Proper (GpdHom ==> GpdHom) (@fmap _ _ _ _ F _ a b) := fun _ _ eq => fmap2 F eq.

#[export] Instance IsProper_catcomp_g {A : Type} `{Is1Cat A}
  {a b c : A} (g : b $-> c)
  : CMorphisms.Proper (GpdHom ==> GpdHom) (@cat_comp _ _ _ a b c g).
Proof.
  intros f1 f2.
  apply (is0functor_postcomp a b c g ).
Defined.
                  
#[export] Instance IsProper_catcomp {A : Type} `{Is1Cat A}
  {a b c : A}
  : CMorphisms.Proper (GpdHom ==> GpdHom ==> GpdHom)
      (@cat_comp _ _ _ a b c).
Proof.
  intros g1 g2 eq_g f1 f2 eq_f.
  rewrite eq_f.
  apply (is0functor_precomp a b c f2).
  exact eq_g.
Defined.

Require Import WildCat.Bifunctor WildCat.Prod.

#[export] Instance gpd_hom_to_hom_proper {A B: Type} `{Is0Gpd A} 
  {R : Relation B} (F : A -> B)
  `{CMorphisms.Proper _ (GpdHom ==> R) F}
  : CMorphisms.Proper (Hom ==> R) F.
Proof.
  intros a b eq_ab; apply H2; exact eq_ab.
Defined.

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
      cbn in f1, f2, g1, g2, eq_fg1, eq_fg2. cbn.
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




Require Import WildCat.NatTrans WildCat.Equiv.


#[export] Instance gpd_hom_is_proper1 {A : Type} `{Is0Gpd A}
 : CMorphisms.Proper
     (Hom ==> Hom ==> CRelationClasses.arrow) Hom.
Proof.
  intros x y eq_xy a b eq_ab f.
  refine (transitivity _ eq_ab).
  refine (transitivity _ f).
  symmetry; exact eq_xy.
Defined.

#[export] Instance transitive_hom {A : Type} `{Is01Cat A} {x : A}
 : CMorphisms.Proper
     (Hom ==> CRelationClasses.arrow) (Hom x).
Proof.
  intros y z g f.
  exact (g $o f).
Defined.

Proposition IsEpic_HasSection {A} `{Is1Cat A}
  {a b : A} (f : a $-> b) :
  SectionOf f -> Epic f.
Proof.
  intros section c g h eq_gf_hf.
  destruct section as [right_inverse is_section].
  apply (is0functor_precomp _ _ _ right_inverse) in eq_gf_hf;
    unfold cat_precomp in eq_gf_hf.
  rewrite 2 cat_assoc, is_section, 2 cat_idr in eq_gf_hf.
  exact eq_gf_hf.
Defined.

Proposition IsMonic_HasRetraction {A} `{Is1Cat A}
  {b c : A} (f : b $-> c) :
  RetractionOf f -> Monic f.
Proof.
  intros retraction a g h eq_fg_fh.
  destruct retraction as [left_inverse is_retraction].
  apply (is0functor_postcomp _ _ _ left_inverse) in eq_fg_fh;
    unfold cat_postcomp in eq_fg_fh.
  rewrite <- 2 cat_assoc, is_retraction, 2 cat_idl in eq_fg_fh.
  assumption.
Defined.

Proposition nat_equiv_faithful {A B : Type}
  {F G : A -> B} `{Is1Functor _ _ F}
  `{!Is0Functor G, !Is1Functor G} 
  `{!HasEquivs B} (tau : NatEquiv F G)
  : Faithful F -> Faithful G.
Proof.
  intros faithful_F x y f g eq_Gf_Gg.
  apply (@fmap _ _ _ _ _ (is0functor_precomp _
       _ _ (cat_equiv_natequiv F G tau x))) in eq_Gf_Gg.
  cbn in eq_Gf_Gg.
  unfold cat_precomp in eq_Gf_Gg.
  rewrite <- is1natural_natequiv in eq_Gf_Gg.
  rewrite <- is1natural_natequiv in eq_Gf_Gg.
  apply faithful_F.
  assert (X : RetractionOf (tau y)). {
    unshelve eapply Build_RetractionOf.
    - exact ((tau y)^-1$).
    - exact (cate_issect _ ).
  }
  apply IsMonic_HasRetraction in X.
  apply X in eq_Gf_Gg. assumption.
Defined.

