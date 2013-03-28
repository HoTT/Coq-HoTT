Require Import Overture PathGroupoids Equivalences Trunc HSet.

Module Export CummulativeHierarchy.

Local Inductive V : Type :=
  | vset : forall (A : Type), (A -> V) -> V.

Axiom veq :
  forall {A B : Type} (f : A -> V) (g : B -> V),
    



Module Export CummulativeHierarchy.