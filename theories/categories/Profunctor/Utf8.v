Require Import Profunctor.Core.
Require Export Profunctor.Notations.

Notation "x ⇸ y" := (Profunctor x y)
                      (at level 99, right associativity, y at level 200)
                    : type_scope.
