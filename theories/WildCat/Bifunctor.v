Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core WildCat.Opposite WildCat.Universe WildCat.Prod.

(** * Bifunctors between WildCats *)

Class IsBifunctor {A B C : Type} `{IsGraph A, IsGraph B, Is1Cat C}
  (F : A -> B -> C)
  := {
    bifunctor_isfunctor_10 : forall a, Is0Functor (F a);
    bifunctor_isfunctor_01 : forall b, Is0Functor (flip F b);
    bifunctor_isbifunctor : forall a0 a1 (f : a0 $-> a1) b0 b1 (g : b0 $-> b1),
      fmap (F _) g $o fmap (flip F _) f $== fmap (flip F _) f $o fmap (F _) g
  }.

#[export] Existing Instance bifunctor_isfunctor_10.
#[export] Existing Instance bifunctor_isfunctor_01.
Arguments bifunctor_isbifunctor {A B C} {_ _ _ _ _ _}
  F {_} {a0 a1} f {b0 b1} g.

Class Is1Bifunctor {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!IsBifunctor F}
  := {
    bifunctor_is1functor_10 :: forall a : A, Is1Functor (F a);
    bifunctor_is1functor_01 :: forall b : B, Is1Functor (flip F b);
  }.

Definition bifunctor_hom {C : Type} `{IsGraph C}
  : C^op -> C -> Type := @Hom C _.

Local Instance is0functor_hom01 {C : Type} `{Is1Cat C}
  : forall c, Is0Functor (bifunctor_hom c).
Proof.
  intro c; srapply Build_Is0Functor.
  rapply cat_postcomp.
Defined.

Local Instance is0functor_hom10 {C : Type} `{Is1Cat C}
  : forall c, Is0Functor (flip bifunctor_hom c).
Proof.
  intro c; srapply Build_Is0Functor.
  intros ? ? f; cbn.
  rapply cat_precomp.
  exact f.
Defined.

(** [Hom] is a bifunctor whenever [C] is a strong 1-category. *)
Global Instance isbifunctor_hom {C : Type} `{Is1Cat_Strong C}
  : IsBifunctor (bifunctor_hom (C:=C)).
Proof.
  srapply Build_IsBifunctor.
  intros ? ? f ? ? g x; cbn.
  unfold cat_precomp, cat_postcomp.
  symmetry; apply cat_assoc_strong.
Defined.

Definition fmap01 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A -> B -> C) `{!IsBifunctor F}
  (a : A) {b0 b1 : B} (g : b0 $-> b1)
  : F a b0 $-> F a b1 := fmap (F a) g.

Definition fmap10 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A -> B -> C) `{!IsBifunctor F}
  {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : (F a0 b) $-> (F a1 b) := fmap (flip F b) f.

Global Instance isbifunctor_compose {A B C D : Type}
  `{IsGraph A, IsGraph B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{P : !IsBifunctor F}
  : IsBifunctor (fun a b => G (F a b)).
Proof.
  srapply Build_IsBifunctor.
  intros ? ? f ? ? g; cbn.
  refine ((fmap_comp G _ _)^$ $@ _ $@ fmap_comp G _ _).
  rapply fmap2.
  apply P.
Defined.

Global Instance is1bifunctor_compose {A B C D : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{!IsBifunctor F, !Is1Bifunctor F}
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
Defined.

(** There are two possible ways to define this, which will only agree in the event that F is a bifunctor. *)
#[export] Instance Is0Functor_uncurry_bifunctor {A B C : Type}
  `{IsGraph A, IsGraph B, Is1Cat C}
  (F : A -> B -> C)
  `{forall a, Is0Functor (F a), forall b, Is0Functor (flip F b)}
  : Is0Functor (uncurry F).
Proof.
  srapply Build_Is0Functor.
  intros [a1 b1] [a2 b2] [f g]; cbn in f, g.
  unfold uncurry; cbn.
  exact ((fmap (flip F b2) f) $o (fmap (F a1) g)).
Defined.

(** *** (Uncurried) Bifunctors are functorial in each argument. *)

Global Instance is0functor_bifunctor01 {A B C : Type}
  `{Is01Cat A} `{IsGraph B} `{IsGraph C}
  (F : A * B -> C) `{!Is0Functor F} (a : A)
  : Is0Functor (fun b => F (a, b)).
Proof.
  apply Build_Is0Functor.
  intros x y f.
  rapply (fmap F).
  exact (Id a, f).
Defined.

Global Instance is1functor_bifunctor01 {A B C : Type}
  `{Is1Cat A} `{Is1Cat B} `{Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F} (a : A)
  : Is1Functor (fun b => F (a, b)).
Proof.
  apply Build_Is1Functor.
  - intros x y f g p.
    rapply (fmap2 F).
    exact (Id _, p).
  - intros b.
    exact (fmap_id F (a, b)).
  - intros x y z f g.
    refine (_ $@ _).
    2: rapply (fmap_comp F).
    rapply (fmap2 F).
    exact ((cat_idl (Id a))^$, Id _).
Defined.

Global Instance is0functor_bifunctor10 {A B C : Type}
  `{IsGraph A} `{Is01Cat B} `{IsGraph C}
  (F : A * B -> C) `{!Is0Functor F} (b : B)
  : Is0Functor (fun a => F (a, b)).
Proof.
  apply Build_Is0Functor.
  intros x y f.
  rapply (fmap F).
  exact (f, Id b).
Defined.

Global Instance is1functor_bifunctor10 {A B C : Type}
  `{Is1Cat A} `{Is1Cat B} `{Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F} (b : B)
  : Is1Functor (fun a => F (a, b)).
Proof.
  apply Build_Is1Functor.
  - intros x y f g p.
    rapply (fmap2 F).
    exact (p, Id _).
  - intros a.
    exact (fmap_id F (a, b)).
  - intros x y z f g.
    refine (_ $@ _).
    2: rapply (fmap_comp F).
    rapply (fmap2 F).
    exact (Id _, (cat_idl _)^$).
Defined.
