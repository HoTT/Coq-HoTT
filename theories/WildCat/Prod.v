(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** * More about product categories *)

(** Product categories inherit equivalences *)

Global Instance hasequivs_prod A B `{HasEquivs A} `{HasEquivs B}
  : HasEquivs (A * B).
Proof.
  srefine (Build_HasEquivs (A * B) _ _
             (fun a b => (fst a $<~> fst b) * (snd a $<~> snd b))
             _ _ _ _ _ _ _ _ _).
  1:intros a b f; exact (CatIsEquiv (fst f) * CatIsEquiv (snd f)).
  all:cbn; intros a b f.
  - split; [ exact (fst f) | exact (snd f) ].
  - split; exact _.
  - intros [fe1 fe2]; split.
    + exact (Build_CatEquiv (fst f)).
    + exact (Build_CatEquiv (snd f)).
  - intros [fe1 fe2]; cbn; split; apply cate_buildequiv_fun.
  - intros [fe1 fe2]; split; [ exact ((fst f)^-1$) | exact ((snd f)^-1$) ].
  - intros [fe1 fe2]; split; apply cate_issect.
  - intros [fe1 fe2]; split; apply cate_isretr.
  - intros g r s; split.
    + exact (catie_adjointify (fst f) (fst g) (fst r) (fst s)).
    + exact (catie_adjointify (snd f) (snd g) (snd r) (snd s)).
Defined.

Global Instance isequivs_prod A B `{HasEquivs A} `{HasEquivs B}
       {a1 a2 : A} {b1 b2 : B} {f : a1 $-> a2} {g : b1 $-> b2}
       {ef : CatIsEquiv f} {eg : CatIsEquiv g}
  : @CatIsEquiv (A*B) _ _ _ (a1,b1) (a2,b2) (f,g) := (ef,eg).

(** More coherent two-variable functors. *)

Definition fmap22 {A B C : Type} `{Is1Cat A} `{Is1Cat B} `{Is1Cat C}
  (F : A -> B -> C) `{!Is0Functor (uncurry F), !Is1Functor (uncurry F)}
  {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2) (g1 : a1 $-> a2) (g2 : b1 $-> b2)
  (alpha : f1 $== g1) (beta : f2 $== g2)
  : (fmap11 F f1 f2) $== (fmap11 F g1 g2)
  := @fmap2 _ _ _ _ _ _ (uncurry F) _ _ (a1, b1) (a2, b2) (f1, f2) (g1, g2) (alpha, beta).

Global Instance iemap11 {A B C : Type} `{HasEquivs A} `{HasEquivs B} `{HasEquivs C}
           (F : A -> B -> C) `{!Is0Functor (uncurry F), !Is1Functor (uncurry F)}
           {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2)
           {f1e : CatIsEquiv f1} {f2e : CatIsEquiv f2}
  : CatIsEquiv (fmap11 F f1 f2)
  := @iemap _ _ _ _ _ _ _ _ (uncurry F) _ _ (a1, b1) (a2, b2) (f1, f2) _.

Definition emap11 {A B C : Type} `{HasEquivs A} `{HasEquivs B} `{HasEquivs C}
           (F : A -> B -> C) `{!Is0Functor (uncurry F), !Is1Functor (uncurry F)}
           {a1 a2 : A} {b1 b2 : B} (fe1 : a1 $<~> a2)
           (fe2 : b1 $<~> b2) : (F a1 b1) $<~> (F a2 b2)
  := @emap _ _ _ _ _ _ _ _ (uncurry F) _ _ (a1, b1) (a2, b2) (fe1, fe2).
