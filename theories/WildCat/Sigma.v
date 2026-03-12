Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.

(** * Indexed sum of categories *)

(** We define a wild category structure on [sig B] where [B : A -> Type] is a family of wild categories.  In this construction, we implicitly regard [A] as a wild category using its path groupoid structure.  We only handle the case where each [B a] is a 0-groupoid, for now. *)

Section Sigma.

  Context (A : Type) (B : A -> Type)
    `{forall a, IsGraph (B a)}
    `{forall a, Is01Cat (B a)}
    `{forall a, Is0Gpd (B a)}.

#[export] Instance isgraph_sigma : IsGraph (sig B).
Proof.
  srapply Build_IsGraph.
  intros [x u] [y v].
  exact {p : x = y & p # u $-> v}.
Defined.

#[export] Instance is01cat_sigma : Is01Cat (sig B).
Proof.
  srapply Build_Is01Cat.
  + intros [x u].
    exists idpath. exact (Id u).
  + intros [x u] [y v] [z w] [q g] [p f].
    exists (p @ q).
    destruct p, q; cbn in *. 
    exact (g $o f).
Defined.

#[export] Instance is0gpd_sigma : Is0Gpd (sig B).
Proof.
  constructor.
  intros [x u] [y v] [p f].
  exists (p^).
  destruct p; cbn in *.
  exact (f^$).
Defined.

End Sigma.

Instance is0functor_functor_sigma_id {A : Type} (B C : A -> Type)
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
