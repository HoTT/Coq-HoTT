Require Import Basics Types.
Require Import WildCat.Core WildCat.Opposite WildCat.Universe WildCat.Prod.

(** * Bifunctors between WildCats *)

Class IsBifunctor {A B C : Type} `{IsGraph A, IsGraph B, Is1Cat C}
  (bifunctor_map : A -> B -> C)
  := {
    bifunctor_isfunctor_10 : forall a, Is0Functor (bifunctor_map a);
    bifunctor_isfunctor_01 :
    forall b, Is0Functor (flip bifunctor_map b);
    bifunctor_isbifunctor :
    forall a0 a1 (f : a0 $-> a1) b0 b1 (g : b0 $-> b1),
      fmap (bifunctor_map _) g $o fmap (flip bifunctor_map _) f $==
        fmap (flip bifunctor_map _) f $o fmap (bifunctor_map _) g
  }.

#[export] Existing Instance bifunctor_isfunctor_10.
#[export] Existing Instance bifunctor_isfunctor_01.

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
  unshelve nrapply Build_IsBifunctor; try (typeclasses eauto).
  intros ? ? f ? ? g x; cbn.
  unfold cat_precomp, cat_postcomp.
  symmetry; apply cat_assoc_strong.
Defined.

Definition fmap01 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A -> B -> C) `{IsBifunctor _ _ _ F}
  (a : A) {b0 b1 : B} (g : b0 $-> b1)
  : F a b0 $-> F a b1 := fmap (F a) g.

Definition fmap10 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A -> B -> C) `{IsBifunctor _ _ _ F}
  {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : (F a0 b) $-> (F a1 b) := fmap (flip F b) f.

Global Instance isbifunctor_compose {A B C D : Type}
  `{IsGraph A, IsGraph B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{P : !IsBifunctor F}
  : IsBifunctor (fun a b => G (F a b)).
Proof.
  unshelve nrapply Build_IsBifunctor; try (typeclasses eauto).
  intros ? ? f ? ? g; cbn.
  refine ((fmap_comp G _ _)^$ $@ _ $@ fmap_comp G _ _).
  rapply fmap2.
  apply P.
Defined.

(** There are two possible ways to define this, which will only agree in the event that F is a bifunctor. *)
#[export] Instance Is0Functor_uncurry_bifunctor {A B C : Type}
  `{IsGraph A, IsGraph B, Is1Cat C}
  (F : A -> B -> C)
  `{forall a, Is0Functor (F a), forall b, Is0Functor (flip F b)}
  : Is0Functor (uncurry F).
Proof.
  nrapply Build_Is0Functor.
  intros [a1 b1] [a2 b2] [f g]; cbn in f, g.
  unfold uncurry; cbn.
  exact ((fmap (flip F b2) f) $o (fmap (F a1) g)).
Defined.
