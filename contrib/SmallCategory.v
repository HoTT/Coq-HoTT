Require Import Basics.Overture.
Require Import Basics.Trunc.
Require Import Basics.PathGroupoids.

Require Import Types.Universe.
Require Import Types.Paths.
Require Import Types.Sigma.

Require Import ExcludedMiddle.
Require Import Spaces.Card.
Require Import HIT.Truncations.
Require Import HSet.

Require Import Category.Core.
Require Import Category.Strict.
Require Import Functor.Core.
Require Import Limits.Core.

Import TrM.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Section Small_Category.

  Context `{Univalence}.

  (* A small category is a strict category *)
  Context (C : PreCategory).
  Context `{IsStrictCategory C}.

  (* Cardinality of a small category *)
  Definition CatCard : Card := tr (BuildhSet {X:C & {Y:C & morphism _ X Y }}).

  Context (k : Card).

  (* A k-small category is a small category with object set 
     cardinality less than k *)
  Definition IskSmall : hProp := lt_card CatCard k.

  (* Type of k-small Categories *)
  Record kSmallCategory := {
    k_small_cat :> StrictCategory;
    k_small : IskSmall
  }.

  (* A diagram is k-small if its indexing category is *)
  Definition Diagram_IskSmall {D : PreCategory} (F : Functor C D) 
    : hProp := IskSmall.

  (* Type of k-small C-diagrams in a category D *)
  Record kSmallDiagram (D : PreCategory) := {
    F :> Functor C D;
    isks : Diagram_IskSmall F
  }.

  (* k-Completeness - D has all limits over k-small diagrams *)
  Definition kComplete (D : PreCategory) := 
    forall (F : kSmallDiagram D), exists L, @IsLimit _ _ _ F L.

  (* k-Cocompleteness - D has all colimits under k-small diagrams *)
  Definition kCoComplete (D : PreCategory) :=
    forall (F : kSmallDiagram D), exists L, @IsColimit _ _ _ F L.

End Small_Category.

(* A category is thin if its morphism type is a hprop *)
Definition IsThinCat (C : PreCategory) :=
  forall (x y : C), IsHProp (morphism _ x y).

(* Type of thin categories *)
Record ThinCat := {
  thin_cat :> PreCategory;
  thin : IsThinCat thin_cat;
}.

Lemma exp_card_leq `{Univalence} {a b : Card} (e : leq_card a b) (c : Card) :
    leq_card (exp_card c a) (exp_card c b).
  Proof.
    revert e; strip_truncations.
    intro; strip_truncations.
    apply tr; simpl in *.
    induction e as [e_i e_isinj].
    srefine (_; _); simpl.
    + refine (fun f => e_i o f).
    + unfold isinj in e_isinj.
      intros f g. intro.
      simpl. unfold isinj.
    Admitted.
    
Section Freyd.
  Context `{Univalence}.
  Context `{ExcludedMiddle}.

(**
  Prop 3.7.3 Category theory in context, Riehl

  Any k-small category C that admits all k-small limits or all k-small 
  colimits is a preorder.

  Preorder means is a thin category.

  Assume there are two parallel non-equal morphisms f,g : X -> Y in C,
  then |C(X,Y)| >= 2. Let l be the cardinality of C, then we have
  |C(X,Y)|^l = |C(X,Y^l)| >= 2^l where Y^l is the power object indexed
  by l. However this is absurd since by Cantor's theorem 2^l > l = |Mor C|.
  And C(X,Y^l) is a subset of Mor C. Considering copowers gives a dual 
  construction for the second part.
 
 **)


  Context (C : PreCategory).
  Context `{IsStrictCategory C}.

  Context (k : Card).
  Context `{IskSmall C k}.
  Context {h : kComplete _ k C}.

  Theorem Freyd : IsThinCat C.
  Proof.
    set (l := CatCard C).
    intros x y f g.
    srapply (BuildContr).
    + destruct (LEM (f = g)).
      * admit.
      * apply p.
      * set (s := exp_card_leq (@bool_leq_at_least_two _ _ f g n) l).
        admit.
  Admitted.

End Freyd.