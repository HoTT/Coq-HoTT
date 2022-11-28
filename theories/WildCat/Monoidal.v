Require Import WildCat.SetoidRewrite Basics Types.
Require Import WildCat.Core WildCat.Prod
  WildCat.Bifunctor WildCat.Equiv WildCat.NatTrans.
  

Section Monoidal.
  Context (C : Type).
  Context `{Is1Cat C}.
  Context `{HasEquivs C}.
  Context (tensor : C -> C -> C).
  Context `{forall a, Is0Functor (tensor a)}.
  Context `{forall b, Is0Functor (flip tensor b)}.
  Context `{@IsBifunctor _ _ _ _ _ _ _ _ _ tensor _ _}.

  Definition left_assoc : C -> C -> C -> C :=
    fun a b => tensor (tensor a b).
  
  Definition right_assoc : C -> C -> C -> C :=
    fun a b c => tensor a (tensor b c).

  Let right_assoc' := uncurry (uncurry (right_assoc)).
  Let left_assoc' := uncurry (uncurry (left_assoc)).
  
  #[export] Instance Is0Functor_right_assoc
    : Is0Functor right_assoc'.
  Proof using Type*.
    nrapply Build_Is0Functor.
    intros [[a1 b1] c1] [[a2 b2] c2] [[f g] h];
      cbn in f, g, h.
    exact (fmap11 tensor f (fmap11 tensor g h)).
  Defined.
    
  #[export] Instance Is0Functor_left_assoc : Is0Functor left_assoc'.
  Proof using Type*.
    nrapply Build_Is0Functor.
    intros [[a1 b1] c1] [[a2 b2] c2] [[f g] h];
      cbn in f, g, h.
    exact (fmap11 tensor (fmap11 tensor f g) h).
  Defined.

  (* Left to right is the convention in Mac Lane. *)
  Class Associator := assoc : NatEquiv right_assoc' left_assoc'.
  (* Definition curried_associator `{Associator} := *)
  (*   fun a b c => assoc (a, b, c). *)
  (* Coercion curried_associator : Associator >-> Funclass. *)

  Notation "a ⊗ b" := (tensor a b).
  
  Definition PentagonLaw `{Associator} (a b c d : C) :=
    (assoc (a ⊗ b, c, d)) $o (assoc (a, b, c ⊗ d)) $==
      (fmap (flip tensor d) (assoc (a, b, c)))  
      $o assoc (a, b ⊗ c, d) $o (fmap (tensor a) (assoc (b, c, d))).
    
  Context (I : C).
  
  Class LeftUnitor := left_unitor : NatEquiv (tensor I) idmap.

  Class RightUnitor := right_unitor : NatEquiv (flip tensor I) idmap.

  Definition TriangleLaw {assoc : Associator}
    `{LeftUnitor} `{RightUnitor} (a c : C)
    :=  fmap (tensor a) (left_unitor c)
    $== fmap (flip tensor c) (right_unitor a) $o assoc (a, I, c).
               
  Class MonoidalStructure
    `{forall a, Is1Functor (tensor a)}
    `{forall b, Is1Functor (flip tensor b)}
    {assoc : Associator}
    {left_unitor : LeftUnitor}
    {right_unitor : RightUnitor}
    := {
      pentagon_law : forall a b c d : C, PentagonLaw a b c d;
      triangle_law : forall a c : C, TriangleLaw a c
    }.

  Proposition left_unitor_associator_coherence `{M : MonoidalStructure} (x y : C)
    : fmap (flip tensor y) (left_unitor x) $o
        assoc (I, x ,y) $== left_unitor (x ⊗ y).
  Proof.
    assert (tensor_I_faithful : Faithful (tensor I)). {
      apply (nat_equiv_faithful
               (natequiv_inverse _ _ left_unitor) _).
    }
    
    
  Proposition left_right_unitor_agree `{M : MonoidalStructure}
    : cate_fun (left_unitor I) $== cate_fun (right_unitor I).
  Proof.
    Abort.
    
  
End Monoidal.
