(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.

(** ** Indexed sum of categories *)

Section Sigma.

  Context (A : Type) (B : A -> Type)
    `{forall a, IsGraph (B a)}
    `{forall a, Is01Cat (B a)}
    `{forall a, Is0Gpd (B a)}.

Global Instance isgraph_sigma : IsGraph (sig B).
Proof.
  srapply Build_IsGraph.
  intros [x u] [y v].
  exact {p : x = y & p # u $-> v}.
Defined.

Global Instance is01cat_sigma : Is01Cat (sig B).
Proof.
  srapply Build_Is01Cat.
  + intros [x u].
    exists idpath. exact (Id u).
  + intros [x u] [y v] [z w] [q g] [p f].
    exists (p @ q).
    destruct p, q; cbn in *. 
    exact (g $o f).
Defined.

Global Instance is0gpd_sigma : Is0Gpd (sig B).
Proof.
  constructor.
  intros [x u] [y v] [p f].
  exists (p^).
  destruct p; cbn in *.
  exact (f^$).
Defined.

End Sigma.

Global Instance is0functor_sigma {A : Type} (B C : A -> Type)
       `{forall a, IsGraph (B a)} `{forall a, IsGraph (C a)}
       `{forall a, Is01Cat (B a)} `{forall a, Is01Cat (C a)}
       (F : forall a, B a -> C a) {ff : forall a, Is0Functor (F a)}
  : Is0Functor (fun (x:sig B) => (x.1 ; F x.1 x.2)).
Proof.
  constructor; intros [a1 b1] [a2 b2] [p f]; cbn.
  exists p.
  destruct p; cbn in *.
  exact (fmap (F a1) f).
Defined.
