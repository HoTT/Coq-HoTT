Require Import Basics Types.
Require Import WildCat.Core WildCat.Prod WildCat.Bifunctor WildCat.Equiv WildCat.NatTrans.

Section Monoidal.
  Context (C : Type).
  Context `{Is1Cat C}.
  Context `{HasEquivs C}.
  Context (tensor : C -> C -> C).
  Context `{forall a, Is0Functor (tensor a)}.
  Context `{forall b, Is0Functor (flip tensor b)}.
  Context `{@IsBifunctor _ _ _ _ _ _ _ _ _ tensor _ _}.

  Definition left_assoc : C * C * C -> C :=
    fun abc => let (ab,c) := abc in
               let (a, b) := ab in
               tensor (tensor a b) c.
  
  Definition right_assoc : C * C * C -> C :=
    fun abc => let (ab,c) := abc in
               let (a, b) := ab in
               tensor a (tensor b c).  

  #[export] Instance Is0Functor_right_assoc
    : Is0Functor right_assoc.
  Proof using Type*.
    nrapply Build_Is0Functor.
    intros [[a1 b1] c1] [[a2 b2] c2] [[f g] h];
      cbn in f, g, h.
    exact (fmap11 tensor f (fmap11 tensor g h)).
  Defined.
    
  #[export] Instance Is0Functor_left_assoc : Is0Functor left_assoc.
  Proof using Type*.
    nrapply Build_Is0Functor.
    intros [[a1 b1] c1] [[a2 b2] c2] [[f g] h];
      cbn in f, g, h.
    exact (fmap11 tensor (fmap11 tensor f g) h).
  Defined.

  (* Left to right is the convention in Mac Lane. *)
  Definition Associator := NatEquiv right_assoc left_assoc.
  
