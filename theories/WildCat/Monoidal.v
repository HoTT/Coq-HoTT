Require Import Basics.Utf8 Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core WildCat.Prod WildCat.Bifunctor
  WildCat.Equiv WildCat.NatTrans.

Section Monoidal.
  Context (C : Type).
  Context `{Is1Cat C}.
  Context `{HasEquivs C}.
  Context (tensor : C -> C -> C).
  Context `{!Is0Bifunctor tensor}.

  Definition left_assoc : C -> C -> C -> C :=
    fun a b c => tensor (tensor a b) c.
  
  Definition right_assoc : C -> C -> C -> C :=
    fun a b c => tensor a (tensor b c).

  Let right_assoc' := uncurry (uncurry (right_assoc)).
  Let left_assoc' := uncurry (uncurry (left_assoc)).
  
  #[export] Instance Is0Functor_right_assoc
    : Is0Functor right_assoc'.
  Proof.
    srapply Build_Is0Functor.
    intros [[a1 b1] c1] [[a2 b2] c2] [[f g] h];
      cbn in f, g, h.
    exact (fmap11 tensor f (fmap11 tensor g h)).
  Defined.

  #[export] Instance Is0Functor_left_assoc : Is0Functor left_assoc'.
  Proof.
    srapply Build_Is0Functor.
    intros [[a1 b1] c1] [[a2 b2] c2] [[f g] h];
      cbn in f, g, h.
    exact (fmap11 tensor (fmap11 tensor f g) h).
  Defined.

  (* Left to right is the convention in Mac Lane. *)
  Class Associator := assoc : NatEquiv right_assoc' left_assoc'.

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

  (** TODO *)
  Proposition left_unitor_associator_coherence
    `{M : MonoidalStructure} (x y : C)
    : fmap (flip tensor y) (left_unitor x) $o
        assoc (I, x ,y) $== left_unitor (x ⊗ y).
  Proof.
    Abort.
    
  (** TODO *)
  Proposition left_right_unitor_agree `{M : MonoidalStructure}
    : cate_fun (left_unitor I) $== cate_fun (right_unitor I).
  Proof.
    Abort.
    
End Monoidal.
