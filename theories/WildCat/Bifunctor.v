Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall Types.Prod.
Require Import WildCat.Core WildCat.Prod WildCat.Equiv WildCat.NatTrans
  WildCat.Square WildCat.Opposite.

(** * Bifunctors between WildCats *)

(** ** Definition *)

(** We choose to store redundant information in the class, so that depending on how an instance is constructed, we will get the expected implementations of [fmap10], [fmap01] and [fmap11]. *)
Class Is0Bifunctor {A B C : Type}
  `{IsGraph A, IsGraph B, IsGraph C} (F : A -> B -> C) := {
  is0functor_bifunctor_uncurried :: Is0Functor (uncurry F);
  is0functor01_bifunctor :: forall a, Is0Functor (F a);
  is0functor10_bifunctor :: forall b, Is0Functor (flip F b);
}.

Arguments Is0Bifunctor {A B C _ _ _} F.
Arguments is0functor_bifunctor_uncurried {A B C _ _ _} F {_}.
Arguments is0functor01_bifunctor {A B C _ _ _} F {_} a : rename.
Arguments is0functor10_bifunctor {A B C _ _ _} F {_} b : rename.

(** We provide two alternate constructors, allowing the user to provide just the first field or the last two fields. *)
Definition Build_Is0Bifunctor' {A B C : Type}
  `{Is01Cat A, Is01Cat B, IsGraph C} (F : A -> B -> C)
  `{!Is0Functor (uncurry F)}
  : Is0Bifunctor F.
Proof.
  snrapply Build_Is0Bifunctor.
  - exact _.
  - exact (is0functor_functor_uncurried01 (uncurry F)).
  - exact (is0functor_functor_uncurried10 (uncurry F)).
Defined.

Definition Build_Is0Bifunctor'' {A B C : Type}
  `{IsGraph A, IsGraph B, Is01Cat C} (F : A -> B -> C)
  `{!forall a, Is0Functor (F a), !forall b, Is0Functor (flip F b)}
  : Is0Bifunctor F.
Proof.
  (* The first condition follows from [is0functor_prod_is0functor]. *)
  nrapply Build_Is0Bifunctor; exact _.
Defined.

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

(** [fmap] in both arguments. *)
Definition fmap11 {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C) `{!Is0Bifunctor F} {a0 a1 : A} (f : a0 $-> a1)
  {b0 b1 : B} (g : b0 $-> b1)
  : F a0 b0 $-> F a1 b1
  := fmap_pair (uncurry F) f g.

(** As with [Is0Bifunctor], we store redundant information.  In addition, we store the proofs that they are consistent with each other. *)
Class Is1Bifunctor {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C} (F : A -> B -> C) `{!Is0Bifunctor F} := {

  is1functor_bifunctor_uncurried :: Is1Functor (uncurry F);
  is1functor01_bifunctor :: forall a, Is1Functor (F a);
  is1functor10_bifunctor :: forall b, Is1Functor (flip F b);

  fmap11_is_fmap01_fmap10 {a0 a1} (f : a0 $-> a1) {b0 b1} (g : b0 $-> b1)
    : fmap11 F f g $== fmap01 F a1 g $o fmap10 F f b0;
  fmap11_is_fmap10_fmap01 {a0 a1} (f : a0 $-> a1) {b0 b1} (g : b0 $-> b1)
    : fmap11 F f g $== fmap10 F f b1 $o fmap01 F a0 g;
}.

Arguments Is1Bifunctor {A B C _ _ _ _ _ _ _ _ _ _ _ _} F {Is0Bifunctor} : rename.
Arguments Build_Is1Bifunctor {A B C _ _ _ _ _ _ _ _ _ _ _ _} F {_} _ _ _ _ _.
Arguments is1functor_bifunctor_uncurried {A B C _ _ _ _ _ _ _ _ _ _ _ _} F {_ _}.
Arguments is1functor01_bifunctor {A B C _ _ _ _ _ _ _ _ _ _ _ _} F {_ _} a : rename.
Arguments is1functor10_bifunctor {A B C _ _ _ _ _ _ _ _ _ _ _ _} F {_ _} b : rename.
Arguments fmap11_is_fmap01_fmap10 {A B C _ _ _ _ _ _ _ _ _ _ _ _} F
  {Is0Bifunctor Is1Bifunctor} {a0 a1} f {b0 b1} g : rename.
Arguments fmap11_is_fmap10_fmap01 {A B C _ _ _ _ _ _ _ _ _ _ _ _} F
  {Is0Bifunctor Is1Bifunctor} {a0 a1} f {b0 b1} g : rename.

(** We again provide two alternate constructors. *)
Definition Build_Is1Bifunctor' {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C} (F : A -> B -> C)
  `{!Is0Functor (uncurry F), !Is1Functor (uncurry F)}
  : Is1Bifunctor (Is0Bifunctor := Build_Is0Bifunctor' F) F.
Proof.
  snrapply Build_Is1Bifunctor.
  - exact _.
  - exact (is1functor_functor_uncurried01 (uncurry F)).
  - exact (is1functor_functor_uncurried10 (uncurry F)).
  - intros a0 a1 f b0 b1 g.
    refine (_^$ $@ fmap_pair_comp (uncurry F) f (Id b0) (Id a1) g).
    exact (fmap2_pair (uncurry F) (cat_idl _) (cat_idr _)).
  - intros a0 a1 f b0 b1 g.
    refine (_^$ $@ fmap_pair_comp (uncurry F) (Id a0) g f (Id b1)).
    exact (fmap2_pair (uncurry F) (cat_idr _) (cat_idl _)).
Defined.

Definition Build_Is1Bifunctor'' {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C} (F : A -> B -> C)
  `{!forall a, Is0Functor (F a), !forall b, Is0Functor (flip F b)}
  (Is0Bifunctor_F := Build_Is0Bifunctor'' F)
  `{!forall a, Is1Functor (F a), !forall b, Is1Functor (flip F b)}
  (bifunctor_coh : forall a0 a1 (f : a0 $-> a1) b0 b1 (g : b0 $-> b1),
    fmap01 F a1 g $o fmap10 F f b0 $== fmap10 F f b1 $o fmap01 F a0 g)
  : Is1Bifunctor F.
Proof.
  snrapply Build_Is1Bifunctor.
  - exact _. (* [is1functor_prod_is1functor]. *)
  - exact _.
  - exact _.
  - intros a0 a1 f b0 b1 g.
    exact (bifunctor_coh a0 a1 f b0 b1 g)^$.
  - reflexivity.
Defined.

(** ** Bifunctor lemmas *)

(** *** Coherence *)

Definition bifunctor_coh {A B C : Type}
  (F : A -> B -> C) `{Is1Bifunctor A B C F}
  {a0 a1 : A} (f : a0 $-> a1) {b0 b1 : B} (g : b0 $-> b1)
  : fmap01 F a1 g $o fmap10 F f b0 $== fmap10 F f b1 $o fmap01 F a0 g
  := (fmap11_is_fmap01_fmap10 _ _ _)^$ $@ fmap11_is_fmap10_fmap01 _ _ _.

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
  := fmap2_pair (uncurry F) (Id _) q.

Definition fmap20 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} {f f' : a0 $-> a1} (p : f $== f') (b : B)
  : fmap10 F f b $== fmap10 F f' b
  := fmap2 (flip F b) p.

Definition fmap21 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} {f f' : a0 $-> a1} (p : f $== f') {b0 b1 : B} (g : b0 $-> b1)
  : fmap11 F f g $== fmap11 F f' g
  := fmap2_pair (uncurry F) p (Id _).

Definition fmap22 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} {f f' : a0 $-> a1} (p : f $== f')
  {b0 b1 : B} {g g' : b0 $-> b1} (q : g $== g')
  : fmap11 F f g $== fmap11 F f' g'
  := fmap2_pair (uncurry F) p q.

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
  : fmap11 F (Id a) (Id b) $== Id (F a b)
  := fmap_id (uncurry F) (a, b).

(** [fmap11] with left map the identity gives [fmap01]. *)
Definition fmap01_is_fmap11 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (a : A) {b0 b1 : B} (g : b0 $-> b1)
  : fmap11 F (Id a) g $== fmap01 F a g
  := fmap11_is_fmap01_fmap10 _ _ _ $@ (_ $@L fmap10_id _ _ _) $@ cat_idr _.

(** [fmap11] with right map the identity gives [fmap10]. *)
Definition fmap10_is_fmap11 {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a0 a1 : A} (f : a0 $-> a1) (b : B)
  : fmap11 F f (Id b) $== fmap10 F f b
  := fmap11_is_fmap01_fmap10 _ _ _ $@ (fmap01_id _ _ _ $@R _) $@ cat_idl _.

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
  : fmap11 F (g $o f) (k $o h) $== fmap11 F g k $o fmap11 F f h
  := fmap_pair_comp (uncurry F) _ _ _ _.

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
  := iemap (uncurry F) (a := (a0, b0)) (b := (_, _)) (f, g).

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

(** ** Flipping bifunctors *)

Definition is0bifunctor_flip {A B C : Type}
  (F : A -> B -> C) `{Is01Cat A, Is01Cat B, Is01Cat C, !Is0Bifunctor F}
  : Is0Bifunctor (flip F).
Proof.
  snrapply Build_Is0Bifunctor.
  - change (Is0Functor (uncurry F o equiv_prod_symm _ _)).
    exact _.
  - exact _.
  - exact _.
Defined.
Hint Immediate is0bifunctor_flip : typeclass_instances.

Definition is1bifunctor_flip {A B C : Type}
(F : A -> B -> C) `{H : Is1Bifunctor A B C F}
  : Is1Bifunctor (flip F).
Proof.
  snrapply Build_Is1Bifunctor.
  - change (Is1Functor (uncurry F o equiv_prod_symm _ _)).
    exact _.
  - exact _.
  - exact _.
  - intros b0 b1 g a0 a1 f.
    exact (fmap11_is_fmap10_fmap01 F f g).
  - intros b0 b1 g a0 a1 f.
    exact (fmap11_is_fmap01_fmap10 F f g).
Defined.
Hint Immediate is1bifunctor_flip : typeclass_instances.

(** ** Composition of bifunctors *)

(** There are 4 different ways to compose a functor with a bifunctor. *)

(** Restricting a functor along a bifunctor yields a bifunctor. *)
Global Instance is0bifunctor_postcompose {A B C D : Type}
  `{IsGraph A, IsGraph B, IsGraph C, IsGraph D}
  (F : A -> B -> C) {bf : Is0Bifunctor F}
  (G : C -> D) `{!Is0Functor G}
  : Is0Bifunctor (fun a b => G (F a b)) | 10
  := {}.

Global Instance is1bifunctor_postcompose {A B C D : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D}
  (F : A -> B -> C) (G : C -> D) `{!Is0Functor G, !Is1Functor G}
  `{!Is0Bifunctor F} {bf : Is1Bifunctor F}
  : Is1Bifunctor (fun a b => G (F a b)) | 10.
Proof.
  snrapply Build_Is1Bifunctor.
  1-3: exact _.
  - intros a0 a1 f b0 b1 g.
    exact (fmap2 G (fmap11_is_fmap01_fmap10 F f g) $@ fmap_comp G _ _).
  - intros a0 a1 f b0 b1 g.
    exact (fmap2 G (fmap11_is_fmap10_fmap01 F f g) $@ fmap_comp G _ _).
Defined.

Global Instance is0bifunctor_precompose {A B C D E : Type}
  `{IsGraph A, IsGraph B, IsGraph C, IsGraph D, IsGraph E}
  (G : A -> B) (K : E -> C) (F : B -> C -> D)
  `{!Is0Functor G, !Is0Bifunctor F, !Is0Functor K}
  : Is0Bifunctor (fun a b => F (G a) (K b)) | 10.
Proof.
  snrapply Build_Is0Bifunctor.
  - change (Is0Functor (uncurry F o functor_prod G K)).
    exact _.
  - exact _.
  - intros e.
    change (Is0Functor (flip F (K e) o G)).
    exact _.
Defined.

Global Instance is1bifunctor_precompose {A B C D E : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D, Is1Cat E}
  (G : A -> B) (K : E -> C) (F : B -> C -> D)
  `{!Is0Functor G, !Is1Functor G, !Is0Bifunctor F, !Is1Bifunctor F,
    !Is0Functor K, !Is1Functor K}
  : Is1Bifunctor (fun a b => F (G a) (K b)) | 10.
Proof.
  snrapply Build_Is1Bifunctor.
  - change (Is1Functor (uncurry F o functor_prod G K)).
    exact _.
  - exact _.
  - intros e.
    change (Is1Functor (flip F (K e) o G)).
    exact _.
  - intros a0 a1 f b0 b1 g.
    exact (fmap11_is_fmap01_fmap10 F (fmap G f) (fmap K g)).
  - intros a0 a1 f b0 b1 g.
    exact (fmap11_is_fmap10_fmap01 F (fmap G f) (fmap K g)).
Defined.

Global Instance is0functor_uncurry_uncurry_left {A B C D E}
  (F : A -> B -> C) (G : C -> D -> E)
  `{IsGraph A, IsGraph B, IsGraph C, IsGraph D, IsGraph E,
    !Is0Bifunctor F, !Is0Bifunctor G}
  : Is0Functor (uncurry (uncurry (fun x y z => G (F x y) z))).
Proof.
  exact _.
Defined.

Global Instance is1functor_uncurry_uncurry_left {A B C D E}
  (F : A -> B -> C) (G : C -> D -> E)
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D, Is1Cat E,
    !Is0Bifunctor F, !Is1Bifunctor F, !Is0Bifunctor G, !Is1Bifunctor G}
  : Is1Functor (uncurry (uncurry (fun x y z => G (F x y) z))).
Proof.
  exact _.
Defined.

Global Instance is0functor_uncurry_uncurry_right {A B C D E}
  (F : A -> B -> D) (G : C -> D -> E)
  `{IsGraph A, IsGraph B, IsGraph C, IsGraph D, IsGraph E,
    !Is0Bifunctor F, !Is0Bifunctor G}
  : Is0Functor (uncurry (uncurry (fun x y z => G x (F y z)))).
Proof.
  snrapply Build_Is0Functor.
  intros cab cab' [[h f] g].
  exact (fmap11 G h (fmap11 F f g)).
Defined.

Global Instance is1functor_uncurry_uncurry_right {A B C D E}
  (F : A -> B -> D) (G : C -> D -> E)
  `{Is1Cat A, Is1Cat B, Is1Cat C, Is1Cat D, Is1Cat E,
    !Is0Bifunctor F, !Is1Bifunctor F, !Is0Bifunctor G, !Is1Bifunctor G}
  : Is1Functor (uncurry (uncurry (fun x y z => G x (F y z)))).
Proof.
  snrapply Build_Is1Functor.
  - intros cab cab' [[h f] g] [[h' f'] g'] [[q p] r].
    exact (fmap22 G q (fmap22 F p r)).
  - intros cab.
    exact (fmap12 G _ (fmap11_id F _ _) $@ fmap11_id G _ _).
  - intros cab cab' cab'' [[h f] g] [[h' f'] g'].
    exact (fmap12 G _ (fmap11_comp F _ _ _ _) $@ fmap11_comp G _ _ _ _).
Defined.  

Definition fmap11_square {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  {a00 a20 a02 a22 : A} {f10 : a00 $-> a20} {f12 : a02 $-> a22}
  {f01 : a00 $-> a02} {f21 : a20 $-> a22}
  {b00 b20 b02 b22 : B} {g10 : b00 $-> b20} {g12 : b02 $-> b22}
  {g01 : b00 $-> b02} {g21 : b20 $-> b22}
  (p : Square f01 f21 f10 f12) (q : Square g01 g21 g10 g12)
  : Square (fmap11 F f01 g01) (fmap11 F f21 g21) (fmap11 F f10 g10) (fmap11 F f12 g12)
  := (fmap11_comp F _ _ _ _)^$ $@ fmap22 F p q $@ fmap11_comp F _ _ _ _.

(** ** Natural transformations between bifunctors *)

(** We can show that an uncurried natural transformation between uncurried bifunctors by composing the naturality square in each variable. *)
Global Instance is1natural_uncurry {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B -> C) `{!Is0Bifunctor F, !Is1Bifunctor F}
  (G : A -> B -> C) `{!Is0Bifunctor G, !Is1Bifunctor G}
  (alpha : uncurry F $=> uncurry G)
  (nat_l : forall b, Is1Natural (flip F b) (flip G b) (fun x : A => alpha (x, b)))
  (nat_r : forall a, Is1Natural (F a) (G a) (fun y : B => alpha (a, y)))
  : Is1Natural (uncurry F) (uncurry G) alpha.
Proof.
  intros [a b] [a' b'] [f f']; cbn in *.
  change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
  nrapply vconcatL.
  1: rapply (fmap11_is_fmap01_fmap10 F).
  nrapply vconcatR.
  2: rapply (fmap11_is_fmap01_fmap10 G).
  exact (hconcat (nat_l _ _ _ f) (nat_r _ _ _ f')).
Defined.

(** Flipping a natural transformation between bifunctors. *)
Definition nattrans_flip {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  {F : A -> B -> C} `{!Is0Bifunctor F, !Is1Bifunctor F}
  {G : A -> B -> C} `{!Is0Bifunctor G, !Is1Bifunctor G}
  : NatTrans (uncurry F) (uncurry G)
    -> NatTrans (uncurry (flip F)) (uncurry (flip G)).
Proof.
  intros [alpha nat].
  snrapply Build_NatTrans.
  - exact (alpha o equiv_prod_symm _ _).
  - intros [b a] [b' a'] [g f].
    exact (nat (a, b) (a', b') (f, g)).
Defined.

(** ** Opposite Bifunctors *)

(** There are a few more combinations we can do for this, such as profunctors, but we will leave those for later. *)

Global Instance is0bifunctor_op A B C (F : A -> B -> C) `{Is0Bifunctor A B C F}
  : Is0Bifunctor (F : A^op -> B^op -> C^op).
Proof.
  snrapply Build_Is0Bifunctor.
  - exact (is0functor_op _ _ (uncurry F)).
  - intros a.
    nrapply is0functor_op.
    exact (is0functor01_bifunctor F a).
  - intros b.
    nrapply is0functor_op.
    exact (is0functor10_bifunctor F b).
Defined.

Global Instance is1bifunctor_op A B C (F : A -> B -> C) `{Is1Bifunctor A B C F}
  : Is1Bifunctor (F : A^op -> B^op -> C^op).
Proof.
  snrapply Build_Is1Bifunctor.
  - exact (is1functor_op _ _ (uncurry F)).
  - intros a.
    nrapply is1functor_op.
    exact (is1functor01_bifunctor F a).
  - intros b.
    nrapply is1functor_op.
    exact (is1functor10_bifunctor F b).
  - intros a0 a1 f b0 b1 g; cbn in f, g.
    exact (fmap11_is_fmap10_fmap01 F f g).
  - intros a0 a1 f b0 b1 g; cbn in f, g.
    exact (fmap11_is_fmap01_fmap10 F f g).
Defined.

Global Instance is0bifunctor_op' A B C (F : A^op -> B^op -> C^op)
  `{IsGraph A, IsGraph B, IsGraph C, Fop : !Is0Bifunctor (F : A^op -> B^op -> C^op)}
  : Is0Bifunctor (F : A -> B -> C)
  := is0bifunctor_op A^op B^op C^op F.

Global Instance is1bifunctor_op' A B C (F : A^op -> B^op -> C^op)
  `{Is1Cat A, Is1Cat B, Is1Cat C,
    !Is0Bifunctor (F : A^op -> B^op -> C^op), !Is1Bifunctor (F : A^op -> B^op -> C^op)}
  : Is1Bifunctor (F : A -> B -> C)
  := is1bifunctor_op A^op B^op C^op F.
