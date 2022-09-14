Require Import Basics Types.
Require Import WildCat.Core WildCat.Opposite WildCat.Universe.

(** * Bifunctors between WildCats *)

Definition swap {A B C : Type} (F : A -> B -> C)
  : B -> A -> C := (fun b a => F a b).

Class IsBifunctor {A B C : Type} `{IsGraph A, IsGraph B, Is1Cat C}
  (F : A -> B -> C) `{forall a, Is0Functor (F a), forall b, Is0Functor (swap F b)}
  := isbifunctor : forall a0 a1, forall f : a0 $-> a1, forall b0 b1, forall g : b0 $-> b1,
      fmap (F _) g $o fmap (swap F _) f $== fmap (swap F _) f $o fmap (F _) g.

Arguments isbifunctor {_ _ _ _ _ _ _ _ _} F {_ _ _ _ _} f {_ _} g.

Definition bifunctor_hom {C : Type} `{IsGraph C}
  : C^op -> C -> Type := @Hom C _.

Local Instance is0functor_hom01 {C : Type} `{Is1Cat C}
  : forall c, Is0Functor (bifunctor_hom c).
Proof.
  intro c; srapply Build_Is0Functor.
  rapply cat_postcomp.
Defined.

Local Instance is0functor_hom10 {C : Type} `{Is1Cat C}
  : forall c, Is0Functor (swap bifunctor_hom c).
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
  intros ? ? f ? ? g x; cbn.
  unfold cat_precomp, cat_postcomp.
  symmetry; apply cat_assoc_strong.
Defined.

Definition fmap01 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C} (F : A -> B -> C)
  `{forall a, Is0Functor (F a), forall b, Is0Functor (swap F b), !IsBifunctor F}
  (a : A) {b0 b1 : B} (g : b0 $-> b1) : F a b0 $-> F a b1 := fmap (F a) g.

Definition fmap10 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C} (F : A -> B -> C)
  `{forall a, Is0Functor (F a), forall b, Is0Functor (swap F b), !IsBifunctor F}
  {a0 a1 : A} (f : a0 $-> a1) (b : B) : (F a0 b) $-> (F a1 b) := fmap (swap F b) f.

Global Instance isbifunctor_compose {A B C D : Type}
  `{IsGraph A, IsGraph B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{forall a, Is0Functor (F a), forall b, Is0Functor (fun a => F a b), P : !IsBifunctor F}
  : IsBifunctor (fun a b => G (F a b)).
Proof.
  intros ? ? f ? ? g; cbn.
  refine ((fmap_comp G _ _)^$ $@ _ $@ fmap_comp G _ _).
  rapply fmap2.
  apply P.
Defined.
