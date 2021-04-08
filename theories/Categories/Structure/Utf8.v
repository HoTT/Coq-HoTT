Require Import HoTT.Categories.Structure.Core.
Require Export HoTT.Categories.Structure.Notations.
Require Import HoTT.Basics.Utf8.

Notation "a ≤_{ x } b" := (a <=_{ x } b)%long_structure : long_structure_scope.
Notation "a ≤ b" := (a <= b)%structure : structure_scope.
