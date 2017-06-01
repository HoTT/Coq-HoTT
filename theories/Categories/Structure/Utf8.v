Require Import Structure.Core.
Require Export Structure.Notations.
Require Import Basics.Utf8.

Notation "a ≤_{ x } b" := (a <=_{ x } b)%long_structure : long_structure_scope.
Notation "a ≤ b" := (a <= b)%structure : structure_scope.
