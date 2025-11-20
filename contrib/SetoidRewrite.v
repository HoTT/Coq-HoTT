(** * Typeclass instances to allow rewriting in categories *)

(** The file using the setoid rewriting machinery from the Coq standard library to allow rewriting in wild-categories.  Examples are given later in the file. *)

(** Init.Tactics contains the definition of the Coq stdlib typeclass_inferences database.  It must be imported before Basics.Overture.  Otherwise, the typeclasses hintdb is cleared, breaking typeclass inference.  Because of this, this file also needs to be the first file Require'd in any file that uses it.  Moreover, if Foo Requires this file, then Foo must also be the first file Require'd in any file that Requires Foo, and so on.  In the long term it would be good if this could be avoided. *)

#[warnings="-deprecated-from-Coq"]
From Coq Require Init.Tactics.
From HoTT Require Import Basics.Overture Basics.Tactics.
From HoTT Require Import Types.Forall.
#[warnings="-deprecated-from-Coq"]
From Coq Require Setoids.Setoid.
Import CMorphisms.ProperNotations.
From HoTT Require Import WildCat.Core
  WildCat.NatTrans WildCat.Equiv.

(** ** Setoid rewriting *)

#[export] Instance reflexive_proper_proxy {A : Type}
  {R : Relation A} `(Reflexive A R) (x : A)
  : CMorphisms.ProperProxy R x := reflexivity x.

(** forall (x y : A), x $== y -> forall (a b : A), a $== b -> y $== b -> x $==a *)
#[export] Instance IsProper_GpdHom_from {A : Type} `{Is0Gpd A}
  : CMorphisms.Proper
      (GpdHom ==>
         GpdHom ==>
         CRelationClasses.flip CRelationClasses.arrow) GpdHom.
Proof.
  intros x y eq_xy a b eq_ab eq_yb.
  exact (transitivity eq_xy (transitivity eq_yb
                              (symmetry _ _ eq_ab))).
  (* We could also just write:
    exact (eq_xy $@ eq_yb $@ eq_ab^$).
  The advantage of the above proof is that it works for other transitive and symmetric relations. *)
Defined.

(** forall (x y : A), x $== y -> forall (a b : A), a $== b -> x $== a -> y $== b *)
#[export] Instance IsProper_GpdHom_to {A : Type} `{Is0Gpd A}
  : CMorphisms.Proper
      (GpdHom ==>
         GpdHom ==>
         CRelationClasses.arrow) GpdHom.
Proof.
  intros x y eq_xy a b eq_ab eq_xa.
  refine (transitivity _ eq_ab).
  refine (transitivity _ eq_xa).
  exact (symmetry _ _ eq_xy).
Defined.

(** forall a : A, x $== y -> a $== x -> a $== y *)
#[export] Instance IsProper_GpdHom_to_a {A : Type} `{Is0Gpd A}
  {a : A}
  : CMorphisms.Proper
      (GpdHom ==>
         CRelationClasses.arrow) (GpdHom a).
Proof.
  intros x y eq_xy eq_ax.
  by transitivity x.
Defined.

(** forall a : A, x $== y -> a $== y -> a $== x *)
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

#[export] Instance symmetry_flip {A B : Type} {f : A -> B}
  {R : Relation A} {R' : Relation B} `{Symmetric _ R}
  (H0 : CMorphisms.Proper (R ++> R') f)
  : CMorphisms.Proper (R --> R') f.
Proof.
  intros a b Rba; unfold CRelationClasses.flip in Rba.
  apply H0. symmetry. exact Rba.
Defined.

#[export] Instance symmetric_flip_snd {A B C : Type} {R : Relation A}
  {R' : Relation B} {R'' : Relation C} `{Symmetric _ R'}
  (f : A -> B -> C) (H1 : CMorphisms.Proper (R ++> R' ++> R'') f)
  : CMorphisms.Proper (R ++> R' --> R'') f.
Proof.
  intros a b Rab x y R'yx. apply H1; [ assumption | symmetry; assumption ].
Defined.

#[export] Instance IsProper_fmap {A B : Type}
  (F : A -> B) `{Is1Functor _ _ F} (a b : A)
  : CMorphisms.Proper (GpdHom ==> GpdHom) (@fmap _ _ _ _ F _ a b)
  := fun _ _ => fmap2 F.

#[export] Instance IsProper_catcomp_g {A : Type} `{Is1Cat A}
  {a b c : A} (g : b $-> c)
  : CMorphisms.Proper (GpdHom ==> GpdHom) (@cat_comp _ _ _ a b c g)
  := fun _ _ => cat_postwhisker g.

#[export] Instance IsProper_catcomp {A : Type} `{Is1Cat A}
  {a b c : A}
  : CMorphisms.Proper (GpdHom ==> GpdHom ==> GpdHom)
      (@cat_comp _ _ _ a b c).
Proof.
  intros g1 g2 eq_g f1 f2 eq_f.
  exact (cat_comp2 eq_f eq_g).
Defined.

#[export] Instance gpd_hom_to_hom_proper {A B : Type} `{Is0Gpd A}
  {R : Relation B} (F : A -> B)
  {H2 : CMorphisms.Proper (GpdHom ==> R) F}
  : CMorphisms.Proper (Hom ==> R) F.
Proof.
  intros a b eq_ab; apply H2; exact eq_ab.
Defined.

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
      (Hom ==> CRelationClasses.arrow) (Hom x)
  := fun y z => cat_comp.

(** ** Examples of setoid rewriting *)

(** Rewriting works in hypotheses. *)
Proposition IsEpic_HasSection {A} `{Is1Cat A}
  {a b : A} (f : a $-> b) :
  SectionOf f -> Epic f.
Proof.
  intros [right_inverse is_section] c g h eq_gf_hf.
  apply (fmap (cat_precomp _ right_inverse)) in eq_gf_hf;
    unfold cat_precomp in eq_gf_hf.
  rewrite 2 cat_assoc, is_section, 2 cat_idr in eq_gf_hf.
  exact eq_gf_hf.
Defined.

(** A different approach, working in the goal. *)
Proposition IsMonic_HasRetraction {A} `{Is1Cat A}
  {b c : A} (f : b $-> c) :
  RetractionOf f -> Monic f.
Proof.
  intros [left_inverse is_retraction] a g h eq_fg_fh.
  rewrite <- (cat_idl g), <- (cat_idl h).
  rewrite <- is_retraction.
  rewrite 2 cat_assoc.
  exact (_ $@L eq_fg_fh).
Defined.

Proposition nat_equiv_faithful {A B : Type}
  {F G : A -> B} `{Is1Functor _ _ F}
  `{!Is0Functor G, !Is1Functor G}
  `{!HasEquivs B} (tau : NatEquiv F G)
  : Faithful F -> Faithful G.
Proof.
  intros faithful_F x y f g eq_Gf_Gg.
  apply faithful_F.
  apply (cate_monic_equiv (tau y)).
  rewrite 2 (isnat tau).
  by apply cat_prewhisker.
Defined.

Section SetoidRewriteTests.
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

  Goal forall (A B : Type) (F : A -> B) `{Is1Functor _ _ F} (a b : A) (f g : a $-> b), f $== g -> fmap F f $== fmap F g.
  Proof.
    do 17 intro.
    intro eq_fg.
    rewrite eq_fg.
  Abort.

  Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f1 f2 : a $-> b) (g : b $-> c), f1 $== f2 -> g $o f1 $== g $o f2.
  Proof.
    do 11 intro.
    intro eq.
    rewrite <- eq.
    rewrite eq.
  Abort.

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
End SetoidRewriteTests.
