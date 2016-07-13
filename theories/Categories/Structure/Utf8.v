Require Import Structure.Core.
Require Export Structure.Notations.

Notation "a ≤_{ x } b" := (a <=_{ x } b)%long_structure (at level 70, no associativity) : long_structure_scope.
Notation "a ≤ b" := (a <= b)%structure (at level 70, no associativity) : structure_scope.
