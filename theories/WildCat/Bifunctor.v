Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core WildCat.Prod.

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

(* fmap in the first argument *)
Definition fmap10 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : (F a0 b) $-> (F a1 b)
  := fmap (flip F b) f.

(* fmap in the second argument *)
Definition fmap01 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F} (a : A) {b0 b1 : B} (g : b0 $-> b1)
  : F a b0 $-> F a b1
  := fmap (F a) g.

(** Restricting a functor along a bifunctor yields a bifunctor. *)
Global Instance is0bifunctor_compose {A B C D : Type}
  `{IsGraph A, IsGraph B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) `{bf : !Is0Bifunctor F}
  (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  : Is0Bifunctor (fun a b => G (F a b)).
Proof.
  rapply Build_Is0Bifunctor.
Defined.

Global Instance is1bifunctor_compose {A B C D : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{!Is0Bifunctor F, bf : !Is1Bifunctor F}
  : Is1Bifunctor (fun a b => G (F a b)).
Proof.
  nrapply Build_Is1Bifunctor.
  - intros x; nrapply Build_Is1Functor.
    + intros a b f g p.
      exact (fmap2 G (fmap2 (F x) p)).
    + intros b.
      refine (fmap2 G (fmap_id (F x) b) $@ _).
      exact (fmap_id G _).
    + intros a b c f g.
      refine (fmap2 G (fmap_comp (F x) f g) $@ _).
      exact (fmap_comp G _ _).
  - intros y; nrapply Build_Is1Functor.
    + intros a b f g p.
      exact (fmap2 G (fmap2 (flip F y) p)).
    + intros a.
      refine (fmap2 G (fmap_id (flip F y) a) $@ _).
      exact (fmap_id G _).
    + intros a b c f g.
      refine (fmap2 G (fmap_comp (flip F y) f g) $@ _).
      exact (fmap_comp G _ _).
  - intros a0 a1 f b0 b1 g.
    refine ((fmap_comp G _ _)^$ $@ _ $@ fmap_comp G _ _).
    rapply fmap2.
    exact (bifunctor_isbifunctor F f g).
Defined.

(*TODO: does the comment below imply (incorrectly) that [Is0Bifunctor] ensures the two routes agree?*)
(** Any 0-bifunctor [A -> B -> C] can be made into a functor from the product category [A * B -> C] in two ways. The bifunctor coherence condition ([bifunctor_isbifunctor]) states precisely that these two routes agree. *)
Global Instance is0functor_uncurry_bifunctor {A B C : Type}
  `{IsGraph A, IsGraph B, Is1Cat C} (F : A -> B -> C) `{!Is0Bifunctor F}
  : Is0Functor (uncurry F).
Proof.
  nrapply Build_Is0Functor.
  intros [a b] [c d] [f g].
  exact (fmap (flip F d) f $o fmap (F a) g).
Defined.

(** Any 1-bifunctor defines a canonical functor from the product category. *)
Global Instance is1functor_uncurry_bifunctor {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C} (F : A -> B -> C)
  `{!Is0Bifunctor F, !Is1Bifunctor F}
  : Is1Functor (uncurry F).
Proof.
  nrapply Build_Is1Functor.
  - intros x y f g [p q].
    refine (fmap2 (flip F _) p $@R _ $@ _).
    exact (_ $@L fmap2 (F _) q).
  - intros x.
    refine (fmap_id (flip F _) _ $@R _ $@ _).
    refine (_ $@L fmap_id (F _) _ $@ cat_idl _).
  - intros x y z f g.
    refine (fmap_comp (flip F _) _ _ $@R _ $@ _).
    refine (_ $@L fmap_comp (F _) _ _  $@ _).
    refine (cat_assoc_opp _ _ _ $@ _ $@ cat_assoc _ _ _).
    refine (cat_assoc _ _ _ $@R _ $@ _ $@ (cat_assoc_opp _ _ _ $@R _)).
    exact (_ $@L (bifunctor_isbifunctor F _ _)^$ $@R _).
Defined.
