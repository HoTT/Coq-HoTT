Require Import Basics.Overture.
Require Import WildCat.Core WildCat.Equiv WildCat.Prod
  WildCat.NatTrans WildCat.Bifunctor.

Class Associator (A : Type) (Hom : A -> A -> Type)
  `{forall a b, IsGraph (Hom a b)}
  `{forall a b, Is2Graph (Hom a b)}
  `{forall a b, Is01Cat (Hom a b)}
  `{forall a b, Is1Cat (Hom a b)}
  `{forall a b, HasEquivs (Hom a b)}
  (F : forall {a b c}, Hom a b -> Hom b c -> Hom a c)
  `{forall a b c, Is0Bifunctor (@F a b c)}
  `{forall a b c, Is1Bifunctor (@F a b c)}
  := bicat_associator_uncurried :
    forall {a b c d : A},
      NatEquiv
      (fun '(f, g, h) => @F a b d f (F g h))
      (fun '(f, g, h) => @F a c d (F f g) h).

Definition associator {A : Type} {Hom : A -> A -> Type}
  {F : forall {a b c}, Hom a b -> Hom b c -> Hom a c}
  `{alpha : Associator A Hom (@F)}
  : forall {a b c d : A} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    F f (F g h) $<~> F (F f g) h :=
  fun _ _ _ _ f g h => bicat_associator_uncurried (f, g, h).

Class PentagonIdentity (A : Type) (Hom : A -> A -> Type)
  (F : forall {a b c}, Hom a b -> Hom b c -> Hom a c)
  `{alpha : Associator A Hom (@F)}
  := pentagonator :
    forall (a b c d e : A) (f : Hom a b) (g : Hom b c)
           (h : Hom c d) (k : Hom d e),
      (associator (F f g) h k) $o (associator f g (F h k))  $==
        fmap10 F (associator f g h) k $o associator f (F g h) k
        $o fmap01 F f (associator g h k).

Class LeftUnitor (A : Type) (Hom : A -> A -> Type)
  `{forall a b, IsGraph (Hom a b)}
  `{forall a b, Is2Graph (Hom a b)}
  `{forall a b, Is01Cat (Hom a b)}
  `{forall a b, Is1Cat (Hom a b)}
  `{forall a b, HasEquivs (Hom a b)}
  (F : forall {a b c}, Hom a b -> Hom b c -> Hom a c)
  (I : forall a, Hom a a)
  `{forall a b c, Is0Bifunctor (@F a b c)}
  `{forall a b c, Is1Bifunctor (@F a b c)}
  := bicat_left_unitor_uncurried :
    forall a b : A,
      NatEquiv (fun f => @F a b b f (I b)) (fun f => f).

Definition left_unitor {A : Type} {Hom: A ->  A -> Type} {F I}
  `{LeftUnitor A Hom F I} : forall {a b : A} (f : Hom a b),
    F a b b f (I b) $<~> f := 
  fun a b f => bicat_left_unitor_uncurried a b f.

Class RightUnitor (A : Type) (Hom : A -> A -> Type)
  `{forall a b, IsGraph (Hom a b)}
  `{forall a b, Is2Graph (Hom a b)}
  `{forall a b, Is01Cat (Hom a b)}
  `{forall a b, Is1Cat (Hom a b)}
  `{forall a b, HasEquivs (Hom a b)}
  (F : forall {a b c}, Hom a b -> Hom b c -> Hom a c)
  (I : forall a, Hom a a)
  `{forall a b c, Is0Bifunctor (@F a b c)}
  `{forall a b c, Is1Bifunctor (@F a b c)}
  := bicat_right_unitor_uncurried :
    forall a b : A,
      NatEquiv
      (fun f => @F a a b (I a) f)
      (fun f => f).

Definition right_unitor {A : Type} {Hom: A ->  A -> Type} {F I}
  `{RightUnitor A Hom F I} : forall {a b : A} (f : Hom a b),
    F a a b (I a) f $<~> f := 
  fun a b f => bicat_right_unitor_uncurried a b f.

Print Implicit fmap01.
Print Implicit right_unitor.

Check (fun (A : Type) (Hom : A -> A -> Type)
  (F : forall {a b c}, Hom a b -> Hom b c -> Hom a c)
  `(alpha : Associator A Hom (@F))
  (I : forall a, Hom a a)
  `(!LeftUnitor A Hom (@F) I)
  `(!RightUnitor A Hom (@F) I)
    (a b c: A) (f : Hom a b) (g : Hom b c) =>
      (fmap10 F (right_unitor f) g) ).

Class TriangleIdentity (A : Type) (Hom : A -> A -> Type)
  (F : forall {a b c}, Hom a b -> Hom b c -> Hom a c)
  `{alpha : Associator A Hom (@F)}
  (I : forall a, Hom a a)
  `{!LeftUnitor A Hom (@F) I}
  `{!RightUnitor A Hom (@F) I}
  := triangulator :
    forall (a b c: A) (f : Hom a b) (g : Hom b c),
      fmap10 F (left_unitor f) g $o associator f (I b) g $==
             fmap01 F f (right_unitor g).

Class IsBicat (A : Type) `{IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_homcat : forall (a b : A), Is01Cat (a $-> b) ;
  is2graph_homcat: forall (a b : A), Is2Graph (a $-> b) ;
  is1cat_homcat : forall (a b : A), Is1Cat (a $-> b) ;
  is0bifunctor_homcat : forall (a b c :A),
    Is0Bifunctor (@cat_comp _ _ _ a b c);
  is1bifunctor_homcat : forall (a b c :A),
    Is1Bifunctor (@cat_comp _ _ _ a b c);
  has_equivs_homcat : forall (a b : A), HasEquivs (Hom a b);
  bicat_assoc : Associator A (@Hom A _)
                  (fun a b c g f => @cat_comp A _ _ a b c f g);
  bicat_idl : LeftUnitor A (@Hom A _)
                (fun a b c g f => @cat_comp A _ _ a b c f g)
                (@Id A _ _);
  bicat_idr : RightUnitor A (@Hom A _)
                (fun a b c g f => @cat_comp A _ _ a b c f g)
                (@Id A _ _);
  bicat_pentagon : PentagonIdentity A (@Hom A _)
                     (fun a b c g f => @cat_comp A _ _ a b c f g);
  bicat_triangle : TriangleIdentity A (@Hom A _)
                     (fun a b c g f => @cat_comp A _ _ a b c f g)
                     (@Id A _ _)
}.
