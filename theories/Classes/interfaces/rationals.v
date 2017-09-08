Require Import HoTT.Types.Universe.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.integers.

(* Universes:
  - i universe of origin type
  - j universe of target types
  - k universe of applied apart of target types
  - l universe of Field property of target types 
*)
Class RationalsToField@{i j k l} (A : Type@{i}) :=
  rationals_to_field : forall (B : Type@{j}) `{Field@{j l k} B}
    `{!FieldCharacteristic B 0}, A -> B.

Arguments rationals_to_field A {_} B {_ _ _ _ _ _ _ _ _} _.


(* The Rationals are the initial field of characteristic 0. *)

Class Rationals A {Aap : Apart A} {Aplus Amult Azero Aone Aneg Arecip Ale Alt}
  `{U : !RationalsToField A} :=
  { rationals_field :> @DecField A Aplus Amult Azero Aone Aneg Arecip
  ; rationals_order :> FullPseudoSemiRingOrder Ale Alt
  ; rationals_to_field_mor :> forall `{Field B} `{!FieldCharacteristic B 0},
    SemiRingPreserving (rationals_to_field A B)
  ; rationals_initial : forall `{Field B} `{!FieldCharacteristic B 0}
    {h : A -> B} `{!SemiRingPreserving h} x,
    rationals_to_field A B x = h x }.
