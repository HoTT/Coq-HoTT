Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core WildCat.Prod WildCat.Equiv.

(** * Bifunctors between WildCats *)

Class Is0Bifunctor {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C)
  := {
    bifunctor_is0functor01 :: forall a, Is0Functor (F a);
    bifunctor_is0functor10 :: forall b, Is0Functor (flip F b);
  }.

Class Is1Bifunctor {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F}
  := {
    bifunctor_is1functor01 :: forall a : A, Is1Functor (F a);
    bifunctor_is1functor10 :: forall b : B, Is1Functor (flip F b);
    bifunctor_isbifunctor : forall a0 a1 (f : a0 $-> a1) b0 b1 (g : b0 $-> b1),
      fmap (F _) g $o fmap (flip F _) f $== fmap (flip F _) f $o fmap (F _) g
  }.

Arguments bifunctor_isbifunctor {A B C} {_ _ _ _ _ _ _ _ _ _ _ _}
  F {_ _} {a0 a1} f {b0 b1} g.

(** Functors from product categories are (uncurried) bifunctors. *)
Global Instance is0bifunctor_functor_uncurried {A B C : Type}
  `{Is01Cat A, Is01Cat B, IsGraph C} (F : A * B -> C) `{!Is0Functor F}
  : Is0Bifunctor (fun a b => F (a, b)).
Proof.
  rapply Build_Is0Bifunctor.
Defined.

Global Instance is1bifunctor_functor_uncurried {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F}
  : Is1Bifunctor (fun a b => F (a, b)).
Proof.
  apply Build_Is1Bifunctor.
  1,2: exact _.
  intros a b f c d g; cbn.
  refine ((fmap_comp F _ _)^$ $@ _ $@ fmap_comp F _ _).
  rapply (fmap2 F).
  refine (cat_idl f $@ (cat_idr f)^$, _).
  exact (cat_idr g $@ (cat_idl g)^$).
Defined.

(** It is often simplest to create a bifunctor [A -> B -> C] by constructing a functor from the product category [A * B]. *)
Definition Build_Is0Bifunctor' {A B C : Type} `{Is01Cat A, Is01Cat B, IsGraph C}
  (F : A -> B -> C) `{!Is0Functor (uncurry F)}
  : Is0Bifunctor F
  := is0bifunctor_functor_uncurried (uncurry F).

Definition Build_Is1Bifunctor' {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Functor (uncurry F), !Is1Functor (uncurry F)}
  : Is1Bifunctor F
  := is1bifunctor_functor_uncurried (uncurry F).

(** [fmap] in the first argument *)
Definition fmap10 {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : (F a0 b) $-> (F a1 b)
  := fmap (flip F b) f.

(** [fmap] in the second argument *)
Definition fmap01 {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C) `{!Is0Bifunctor F} (a : A) {b0 b1 : B} (g : b0 $-> b1)
  : F a b0 $-> F a b1
  := fmap (F a) g.

(** There are two ways to [fmap] in both arguments of a bifunctor. The bifunctor coherence condition ([bifunctor_isbifunctor]) states precisely that these two routes agree. *)
Definition fmap11 {A B C : Type} `{IsGraph A, IsGraph B, Is01Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1)
  {b0 b1 : B} (g : b0 $-> b1)
  : F a0 b0 $-> F a1 b1
  := fmap (F _) g $o fmap (flip F _) f.

Definition fmap11' {A B C : Type} `{IsGraph A, IsGraph B, Is01Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1)
  {b0 b1 : B} (g : b0 $-> b1)
  : F a0 b0 $-> F a1 b1
  := fmap (flip F _) f $o fmap (F _) g.

Definition fmap22 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} {f : a0 $-> a1} {f' : a0 $-> a1}
  {b0 b1 : B} {g : b0 $-> b1} {g' : b0 $-> b1}
  (p : f $== f') (q : g $== g')
  : fmap11 F f g $== fmap11 F f' g'
  := fmap2 (flip F _) p $@@ fmap2 (F _) q.

Global Instance iemap11 {A B C : Type} `{HasEquivs A, HasEquivs B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $<~> a1) {b0 b1 : B} (g : b0 $<~> b1)
  : CatIsEquiv (fmap11 F f g).
Proof.
  rapply compose_catie'.
  exact (iemap (flip F _) f).
Defined.

Definition emap11 {A B C : Type} `{HasEquivs A, HasEquivs B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $<~> a1) {b0 b1 : B} (g : b0 $<~> b1)
  : F a0 b0 $<~> F a1 b1
  := Build_CatEquiv (fmap11 F f g).

(** Any 0-bifunctor [A -> B -> C] can be made into a functor from the product category [A * B -> C] in two ways. *)
Global Instance is0functor_uncurry_bifunctor {A B C : Type}
  `{IsGraph A, IsGraph B, Is01Cat C} (F : A -> B -> C) `{!Is0Bifunctor F}
  : Is0Functor (uncurry F).
Proof.
  nrapply Build_Is0Functor.
  intros a b [f g].
  exact (fmap11 F f g).
Defined.

(** Any 1-bifunctor defines a canonical functor from the product category. *)
Global Instance is1functor_uncurry_bifunctor {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C} (F : A -> B -> C)
  `{!Is0Bifunctor F, !Is1Bifunctor F}
  : Is1Functor (uncurry F).
Proof.
  nrapply Build_Is1Functor.
  - intros x y f g [p q].
    exact (fmap22 F p q).
  - intros x.
    refine (fmap_id (flip F _) _ $@@ fmap_id (F _) _ $@ _).
    apply cat_idl.
  - intros x y z f g.
    refine (fmap_comp (flip F _) _ _ $@@ fmap_comp (F _) _ _ $@ _ ).
    nrefine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
    nrefine (cat_assoc _ _ _ $@R _ $@ _ $@ (cat_assoc_opp _ _ _ $@R _)).
    exact (_ $@L bifunctor_isbifunctor F _ _ $@R _).
Defined.

(** ** Composition of bifunctors *)

(** There are 4 different ways to compose a functor with a bifunctor. *)

(** Restricting a functor along a bifunctor yields a bifunctor. *)
Global Instance is0bifunctor_postcompose {A B C D : Type}
  `{IsGraph A, IsGraph B, IsGraph C, IsGraph D}
  (F : A -> B -> C) {bf : Is0Bifunctor F}
  (G : C -> D) `{!Is0Functor G}
  : Is0Bifunctor (fun a b => G (F a b)).
Proof.
  rapply Build_Is0Bifunctor.
Defined.

Global Instance is1bifunctor_postcompose {A B C D : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{!Is0Bifunctor F} {bf : Is1Bifunctor F}
  : Is1Bifunctor (fun a b => G (F a b)).
Proof.
  nrapply Build_Is1Bifunctor.
  1,2: exact _.
  intros a0 a1 f b0 b1 g.
  refine ((fmap_comp G _ _)^$ $@ _ $@ fmap_comp G _ _).
  rapply fmap2.
  exact (bifunctor_isbifunctor F f g).
Defined.

Global Instance is0bifunctor_precompose {A B C D : Type}
  `{IsGraph A, IsGraph B, IsGraph C, IsGraph D}
  (G : A -> B) (F : B -> C -> D) `{!Is0Functor G, !Is0Bifunctor F}
  : Is0Bifunctor (fun a b => F (G a) b).
Proof.
  rapply Build_Is0Bifunctor.
  intros c.
  change (Is0Functor (flip F c o G)).
  exact _.
Defined.

Global Instance is0bifunctor_precompose' {A B C D : Type}
  `{IsGraph A, IsGraph B, IsGraph C, IsGraph D}
  (G : A -> C) (F : B -> C -> D) `{!Is0Functor G, !Is0Bifunctor F}
  : Is0Bifunctor (fun a b => F a (G b)).
Proof.
  rapply Build_Is0Bifunctor.
  intros a.
  change (Is0Functor (flip F (G a))).
  exact _.
Defined.

Global Instance is1bifunctor_precompose {A B C D : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D}
  (G : A -> B) (F : B -> C -> D)
  `{!Is0Functor G, !Is1Functor G, !Is0Bifunctor F, !Is1Bifunctor F}
  : Is1Bifunctor (fun a b => F (G a) b).
Proof.
  nrapply Build_Is1Bifunctor.
  - exact _.
  - unfold flip.
    change (forall c, Is1Functor (flip F c o G)).
    exact _.
  - intros ? ? ?; apply (bifunctor_isbifunctor F).
Defined.

Global Instance is1bifunctor_precompose' {A B C D : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D}
  (G : A -> C) (F : B -> C -> D)
  `{!Is0Functor G, !Is1Functor G, !Is0Bifunctor F, !Is1Bifunctor F}
  : Is1Bifunctor (fun b a => F b (G a)).
Proof.
  nrapply Build_Is1Bifunctor.
  - exact _.
  - unfold flip.
    change (forall a, Is1Functor (fun b => F b (G a))).
    exact _.
  - intros a a' f b b' g.
    simpl.
    apply (bifunctor_isbifunctor F).
Defined.

Global Instance is0functor_uncurry_uncurry_left {A B C D E}
  (F : A -> B -> C) (G : C -> D -> E)
  `{Is01Cat A, Is01Cat B, Is01Cat C, Is01Cat D, Is01Cat E,
    !Is0Bifunctor F, !Is0Bifunctor G}
  : Is0Functor (uncurry (uncurry (fun x y z => G (F x y) z))).
Proof.
  rapply is0functor_uncurry_bifunctor.
Defined.

Global Instance is0functor_uncurry_uncurry_right {A B C D E}
  (F : A -> B -> D) (G : C -> D -> E)
  `{Is01Cat A, Is01Cat B, Is01Cat C, Is01Cat D, Is01Cat E,
    !Is0Bifunctor F, !Is0Bifunctor G}
  : Is0Functor (uncurry (uncurry (fun x y z => G x (F y z)))).
Proof.
  apply is0functor_uncurry_bifunctor.
  nrapply Build_Is0Bifunctor.
  1: exact _.
  intros b.
  change (Is0Functor (uncurry (fun x y => G x (F y b)))).
  apply is0functor_uncurry_bifunctor.
  apply (is0bifunctor_precompose' (flip F b) G).
Defined.
