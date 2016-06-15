(* Require Import HoTT.Basics HoTT.Types.Bool.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.implementations.list.
Require Import HoTTClasses.tactics.fakeord.

Section content.

(* [C] is the scalar semiring: Z when working on rings,
   N on semirings, other sometimes. *)
Context `{SemiRing C}.

(* [V] is the type of variables, ie we are defining polynomials [C[V]]. *)
Context `{FakeOrdered V}.

Inductive Pol :=
  | Pconst : C -> Pol
  | PX : Pol -> V -> positive -> Pol -> Pol.

(* Pconst c = c
   PX P v i Q = P * v^i + Q *)


End content. *)