(** * Typeclass instances to allow rewriting in wild categories *)

(** This file uses the setoid rewriting machinery from the Coq standard library to allow rewriting in wild-categories.  Examples are given in test/WildCat/SetoidRewrite.v. *)

(** Init.Tactics contains the definition of the Coq stdlib typeclass_inferences database.  With Coq 8.x, it must be imported before Basics.Overture.  Otherwise, the typeclasses hintdb is cleared, breaking typeclass inference.  Because of this, this file also needs to be the first file Require'd in any file that uses it.  Moreover, if Foo Requires this file, then Foo must also be the first file Require'd in any file that Requires Foo, and so on.  Once we assume Rocq 9.0 as our minimum, these comments can be removed. *)

#[warnings="-deprecated-from-Coq"]
From Coq Require Init.Tactics.
From HoTT Require Import Basics.Overture Basics.Tactics.
#[warnings="-deprecated-from-Coq"]
From Coq Require Setoids.Setoid.
Import CMorphisms.ProperNotations.
From HoTT Require Import WildCat.Core.

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
  (* Add the next line to the start of any proof to see what it means: *)
  unfold "==>", CMorphisms.Proper, CRelationClasses.arrow, CRelationClasses.flip in *.
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

(** forall a x y : A, x $== y -> a $== x -> a $== y *)
#[export] Instance IsProper_GpdHom_to_a {A : Type} `{Is0Gpd A}
  {a : A}
  : CMorphisms.Proper
      (GpdHom ==>
         CRelationClasses.arrow) (GpdHom a).
Proof.
  intros x y eq_xy eq_ax.
  by transitivity x.
Defined.

(** forall a x y : A, x $== y -> a $== y -> a $== x *)
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

(** If [R] is symmetric and [R x y -> R' (f x) (f y)], then [R y x -> R' (f x) (f y)]. *)
#[export] Instance symmetry_flip {A B : Type} {f : A -> B}
  {R : Relation A} {R' : Relation B} `{Symmetric _ R}
  (H0 : CMorphisms.Proper (R ++> R') f)
  : CMorphisms.Proper (R --> R') f.
Proof.
  intros a b Rba; unfold CRelationClasses.flip in Rba.
  apply H0. symmetry. exact Rba.
Defined.

(** If [R'] is symmetric and [R x y -> R' x' y' -> R'' (f x x') (f y y')], then [R x y -> R' y' x' -> R'' (f x x') (f y y')]. *)
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

#[export] Instance IsProper_Hom {A : Type} `{Is0Gpd A}
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
