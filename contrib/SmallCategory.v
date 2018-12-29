Require Import HoTT.Basics HoTT.Types.
Require Import Category.Core Category.Strict.
Require Import Functor.
Require Import Limits.Core.
Require Import Spaces.Card.
Require Import HIT.Truncations.
Require Import ExcludedMiddle.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section Small_Category.

Context `{Univalence}.

(* A small category is a strict category *)

(* Cardinality of a small category *)
Definition CatCard (C : StrictCategory) : Card := 
  tr (BuildhSet (exists (X Y : C), C.(morphism) X Y)).

(* A k-small category is a small category with object set 
   cardinality less than k *)
Definition IsSmall (k : Card) (C : StrictCategory): hProp :=
  lt_card (CatCard C) k.

Record kSmallCategory (k : Card) := {
  C :> StrictCategory;
  k_small : IsSmall k C
}.

Context {C : PreCategory}.
Context {strc : IsStrictCategory C}.

Definition DiagramIskSmall {D : PreCategory} (k : Card) (F : Functor C D) : hProp
 := IsSmall k (Build_StrictCategory C strc).

Record kSmallDiagram (k : Card) (D : PreCategory) := {
  F :> Functor C D;
  isks : DiagramIskSmall k F
}.

(** k-Completeness **)
Definition HaskLimits (k : Card) (D : PreCategory) := 
  forall (F : kSmallDiagram k D), exists L, @IsLimit _ D C F L.

(** k-Cocompleteness **)
Definition HaskColimits (k : Card) (D : PreCategory) :=
  forall (F : kSmallDiagram k D), exists L, @IsColimit _ D C F L.

End Small_Category.

Definition IsThin (C : PreCategory) :=
  forall (x y : C), IsHProp(C.(morphism) x y).

Record ThinCat := {
  thin_cat :> StrictCategory;
  thin : IsThin thin_cat;
}.



Section freyd.

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

Proposition Freyd_preorder_limit 
  (k : Card) (C : kSmallCategory k) {h : HaskLimits k C} : 
    IsThin C.
Proof.
  remember (CatCard C) as l eqn:p.
  intros X Y f g; srapply (BuildContr).
  + pose (ab := (f <> g)).
Admitted.

End freyd.