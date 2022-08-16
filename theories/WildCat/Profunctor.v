Require Import Basics Types.
Require Import WildCat.Core WildCat.Opposite WildCat.Universe.

Declare Scope profunctor_scope.
Local Open Scope profunctor_scope.

(** * Enriched profunctors between WildCats *)

Definition swap {A B C : Type} (F : A -> B -> C)
  : B -> A -> C := (fun b a => F a b).

Class IsProfunctor {A B C : Type} `{IsGraph A, IsGraph B, Is1Cat C}
  (F : A^op -> B -> C) `{forall a, Is0Functor (F a), forall b, Is0Functor (swap F b)}
  := isprofunctor : forall a0 a1, forall f : a1 $-> a0, forall b0 b1, forall g : b0 $-> b1,
      fmap (F a0) g $o fmap (swap F b0) f $== fmap (swap F b1) f $o fmap (F a1) g.

Arguments isprofunctor {_ _ _ _ _ _ _ _ _} F {_ _ _ _ _} f {_ _} g.

Definition profunctor_hom {C : Type} `{IsGraph C}
  : C^op -> C -> Type := @Hom C _.

(* jarl: if [is0functor_postcomp] and [is0functor_precomp] were packaged differently, this would be automatic. *)
Local Instance is0functor_hom01 {C : Type} `{Is1Cat C}
  : forall c, Is0Functor (profunctor_hom c).
Proof.
  intro c; srapply Build_Is0Functor.
  rapply cat_postcomp.
Defined.

Local Instance is0functor_hom10 {C : Type} `{Is1Cat C}
  : forall c, Is0Functor (swap profunctor_hom c).
Proof.
  intro c; srapply Build_Is0Functor.
  intros ? ? f; cbn.
  rapply cat_precomp.
  exact f.
Defined.

(** [Hom] is a profunctor whenever [C] is a strong 1-category. *)
Global Instance isprofunctor_hom {C : Type} `{Is1Cat_Strong C}
  : IsProfunctor (profunctor_hom (C:=C)).
Proof.
  intros ? ? f ? ? g x; cbn.
  unfold cat_precomp, cat_postcomp.
  symmetry; apply cat_assoc_strong.
Defined.

Definition fmap01 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A^op -> B -> C)
  `{forall a, Is0Functor (F a), forall b, Is0Functor (swap F b), !IsProfunctor F}
  (a : A^op) {b0 b1 : B} (g : b0 $-> b1)
  : F a b0 $-> F a b1 := fmap (F a) g.

Definition fmap10 {A B C : Type} `{Is01Cat A, Is01Cat B, Is1Cat C}
  (F : A^op -> B -> C)
  `{forall a, Is0Functor (F a), forall b, Is0Functor (swap F b), !IsProfunctor F}
  {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : Hom (F a1 b) (F a0 b).
Proof.
  refine (fmap (swap F b) _).
  exact f.
Defined.

(** We can compose a functor with a profunctor to get a profunctor. *)
Global Instance isprofunctor_compose {A B C D : Type}
  `{IsGraph A, IsGraph B, Is1Cat C, Is1Cat D}
  (F : A^op -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{forall a, Is0Functor (F a), forall b, Is0Functor (fun a => F a b), P : !IsProfunctor F}
  : IsProfunctor (fun a b => G (F a b)).
Proof.
  intros ? ? f ? ? g; cbn.
  refine ((fmap_comp G _ _)^$ $@ _ $@ fmap_comp G _ _).
  rapply fmap2.
  apply P.
Defined.
