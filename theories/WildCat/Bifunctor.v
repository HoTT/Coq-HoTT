Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core WildCat.Prod WildCat.Equiv WildCat.NatTrans WildCat.Square.

(** * Bifunctors between WildCats *)

(** ** Definition *)

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

(** ** Bifunctor lemmas *)

(** *** 1-functorial action *)

(** [fmap] in the first argument. *)
Definition fmap10 {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : (F a0 b) $-> (F a1 b)
  := fmap (flip F b) f.

(** [fmap] in the second argument. *)
Definition fmap01 {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C) `{!Is0Bifunctor F} (a : A) {b0 b1 : B} (g : b0 $-> b1)
  : F a b0 $-> F a b1
  := fmap (F a) g.

(** [fmap] in both arguments. Note that we made a choice in the order in which to compose, but the bifunctor coherence condition says that both ways agree. *)
Definition fmap11 {A B C : Type} `{IsGraph A, IsGraph B, Is01Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1)
  {b0 b1 : B} (g : b0 $-> b1)
  : F a0 b0 $-> F a1 b1
  := fmap01 F _ g $o fmap10 F f _.

(** [fmap11] but with the other choice. *)
Definition fmap11' {A B C : Type} `{IsGraph A, IsGraph B, Is01Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1)
  {b0 b1 : B} (g : b0 $-> b1)
  : F a0 b0 $-> F a1 b1
  := fmap10 F f _ $o fmap01 F _ g.

(** *** Coherence *)

(** The bifunctor coherence condition becomes a 2-cell between the two choices for [fmap11]. *)
Definition fmap11_coh {A B C : Type}
  (F : A -> B -> C) `{Is1Bifunctor A B C F}
  {a0 a1 : A} (f : a0 $-> a1) {b0 b1 : B} (g : b0 $-> b1)
  : fmap11 F f g $== fmap11' F f g.
Proof.
  rapply bifunctor_isbifunctor.
Defined.

(** [fmap11] with right map the identity gives [fmap10]. *)
Definition fmap10_is_fmap11 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : fmap11 F f (Id b) $== fmap10 F f b
  := (fmap_id _ _ $@R _) $@ cat_idl _.

(** [fmap11] with left map the identity gives [fmap01]. *)
Definition fmap01_is_fmap11 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (a : A) {b0 b1 : B} (g : b0 $-> b1)
  : fmap11 F (Id a) g $== fmap01 F a g
  := (_ $@L fmap_id _ _) $@ cat_idr _.

(** 2-functorial action *)

Definition fmap02 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (a : A) {b0 b1 : B} {g g' : b0 $-> b1} (q : g $== g')
  : fmap01 F a g $== fmap01 F a g'
  := fmap2 (F a) q.

Definition fmap12 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $-> a1) {b0 b1 : B} {g g' : b0 $-> b1} (q : g $== g')
  : fmap11 F f g $== fmap11 F f g'
  := fmap02 F _ q $@R _.

Definition fmap20 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} {f f' : a0 $-> a1} (p : f $== f') (b : B)
  : fmap10 F f b $== fmap10 F f' b
  := fmap2 (flip F b) p.

Definition fmap21 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} {f f' : a0 $-> a1} (p : f $== f') {b0 b1 : B} (g : b0 $-> b1)
  : fmap11 F f g $== fmap11 F f' g
  := _ $@L fmap20 F p _.

Definition fmap22 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} {f f' : a0 $-> a1} (p : f $== f')
  {b0 b1 : B} {g g' : b0 $-> b1} (q : g $== g')
  : fmap11 F f g $== fmap11 F f' g'
  := fmap20 F p b0 $@@ fmap02 F a1 q.

(** *** Identity preservation *)

Definition fmap01_id {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F} (a : A) (b : B)
  : fmap01 F a (Id b) $== Id (F a b)
  := fmap_id (F a) b.

Definition fmap10_id {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F} (a : A) (b : B)
  : fmap10 F (Id a) b $== Id (F a b)
  := fmap_id (flip F b) a.

Definition fmap11_id {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F} (a : A) (b : B)
  : fmap11 F (Id a) (Id b) $== Id (F a b).
Proof.
  refine ((_ $@@ _) $@ cat_idr _).
  1,2: rapply fmap_id.
Defined.

(** *** Composition preservation *)

Definition fmap01_comp {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (a : A) {b0 b1 b2 : B} (g : b1 $-> b2) (f : b0 $-> b1)
  : fmap01 F a (g $o f) $== fmap01 F a g $o fmap01 F a f
  := fmap_comp (F a) f g.

Definition fmap10_comp {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 a2 : A} (g : a1 $-> a2) (f : a0 $-> a1) (b : B)
  : fmap10 F (g $o f) b $== fmap10 F g b $o fmap10 F f b
  := fmap_comp (flip F b) f g.

Definition fmap11_comp {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 a2 : A} (g : a1 $-> a2) (f : a0 $-> a1)
  {b0 b1 b2 : B} (k : b1 $-> b2) (h : b0 $-> b1)
  : fmap11 F (g $o f) (k $o h) $== fmap11 F g k $o fmap11 F f h.
Proof.
  refine ((fmap10_comp F _ _ _ $@@ fmap01_comp F _ _ _) $@ _).
  refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
  refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ cat_assoc _ _ _).
  rapply fmap11_coh.
Defined.

(** *** Equivalence preservation *)

Global Instance iemap10 {A B C : Type} `{HasEquivs A, Is1Cat B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $<~> a1) (b : B)
  : CatIsEquiv (fmap10 F f b)
  := iemap (flip F b) f.

Global Instance iemap01 {A B C : Type} `{Is1Cat A, HasEquivs B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (a : A) {b0 b1 : B} (g : b0 $<~> b1)
  : CatIsEquiv (fmap01 F a g)
  := iemap (F a) g.

Global Instance iemap11 {A B C : Type} `{HasEquivs A, HasEquivs B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $<~> a1) {b0 b1 : B} (g : b0 $<~> b1)
  : CatIsEquiv (fmap11 F f g)
  := compose_catie' _ _.

Definition emap10 {A B C : Type} `{HasEquivs A, Is1Cat B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $<~> a1) (b : B)
  : F a0 b $<~> F a1 b
  := Build_CatEquiv (fmap10 F f b).

Definition emap01 {A B C : Type} `{Is1Cat A, HasEquivs B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (a : A) {b0 b1 : B} (g : b0 $<~> b1)
  : F a b0 $<~> F a b1
  := Build_CatEquiv (fmap01 F a g).

Definition emap11 {A B C : Type} `{HasEquivs A, HasEquivs B, HasEquivs C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $<~> a1) {b0 b1 : B} (g : b0 $<~> b1)
  : F a0 b0 $<~> F a1 b1
  := Build_CatEquiv (fmap11 F f g).

(** *** Uncurrying *)

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

(** ** Flipping bifunctors *)

Definition is0bifunctor_flip {A B C : Type}
  (F : A -> B -> C) `{Is0Bifunctor A B C F} : Is0Bifunctor (flip F).
Proof.
  snrapply Build_Is0Bifunctor; exact _.
Defined.
Hint Immediate is0bifunctor_flip : typeclass_instances.

Definition is1bifunctor_flip {A B C : Type}
  (F : A -> B -> C) `{Is1Bifunctor A B C F} : Is1Bifunctor (flip F).
Proof.
  snrapply Build_Is1Bifunctor.
  1,2: exact _.
  intros a0 a1 f b0 b1 g.
  symmetry.
  rapply bifunctor_isbifunctor.
Defined.
Hint Immediate is1bifunctor_flip : typeclass_instances.

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

(** ** Natural transformations between bifunctors *)

(** We can show that an uncurried natural transformation between uncurried bifunctors by composing the naturality square in each variable. *)
Global Instance is1natural_uncurry {A B C : Type}
  `{IsGraph A, IsGraph B, Is1Cat C}
  (F : A -> B -> C)
  `{!Is0Bifunctor F}
  (G : A -> B -> C)
  `{!Is0Bifunctor G}
  (alpha : uncurry F $=> uncurry G)
  (nat_l : forall b, Is1Natural (flip F b) (flip G b) (fun x : A => alpha (x, b)))
  (nat_r : forall a, Is1Natural (F a) (G a) (fun y : B => alpha (a, y)))
  : Is1Natural (uncurry F) (uncurry G) alpha.
Proof.
  intros [a b] [a' b'] [f f']; cbn in *.
  change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
  unfold fmap11.
  exact (hconcat (nat_l _ _ _ f) (nat_r _ _ _ f')).
Defined.
