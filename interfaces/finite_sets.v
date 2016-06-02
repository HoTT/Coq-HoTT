Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders.

(*
We define finite sets as the initial join semi lattice over a decidable type.

An important aspect of our interface is the possibility to make fast
implementations. Therefore it is important that various properties of the
carrier set can be used to create an implementation. Examples of
implementations are:
* Finite sets as unordered lists.
* Finite sets as AVLs (here we need order).
* Finite sets of positives as trees with boolean nodes.
The above examples already illustrate that it is very inconvenient to
fix the properties of the carrier right now. Instead we use the following
type class:
*)

Class SetType (A : Type) := set_type: Type.
Arguments set_type _ {SetType}.
(* We can't make this type transparent to typeclass resolution. *)

(*
The key idea is that an implementation can let instances of this class depend
on any specific properties it likes.

For convenience we define some notations to hide nasty details.
*)
Notation EmptySet A := (Bottom (set_type A)).
Notation "∅" := (@bottom (set_type _) _) : mc_scope.
Notation SetJoin A := (Join (set_type A)).
Notation SetMeet A := (Meet (set_type A)).
Notation SetDifference A := (Difference (set_type A)).
Notation SetSingleton A := (Singleton A (set_type A)).
Notation SetLe A := (Le (set_type A)).
Notation SetContains A := (Contains A (set_type A)).

Class FSetExtend A `{t : SetType A} :=
  fset_extend `{Join B} `{Bottom B} : (A → B) → set_type A → B.

Class FSet A `{At : SetType A}
   `{Aempty : EmptySet A} `{Ajoin : SetJoin A} `{Asingle : SetSingleton A}
   `{∀ a₁ a₂ : A, Decision (a₁ = a₂)} `{U : !FSetExtend A} :=
 { fset_bounded_sl :> BoundedJoinSemiLattice (set_type A)
  ; fset_extend_mor `{BoundedJoinSemiLattice B} {f : A → B} :>
      BoundedJoinSemiLattice_Morphism (fset_extend f)
  ; fset_extend_correct `{BoundedJoinSemiLattice B}  (f : A → B) :
      f = fset_extend f ∘ singleton
  ; fset_extend_unique `{Join B} `{Bottom B} (f : A → B)
      (h : set_type A → B) `{!BoundedJoinSemiLattice_Morphism h}
       : f = h ∘ singleton → h = fset_extend f }.

Definition fset_map `(f : A → B) `{SetType A} `{SetType B}
  `{EmptySet B} `{SetJoin B} `{SetSingleton B} `{U : !FSetExtend A}
  : set_type A → set_type B
  := fset_extend (singleton ∘ f).

(*
Next we describe the order and set inclusion. Constructing a
JoinSemiLatticeOrder might be quite inconvenient since we have used the
algebraic definition of a lattice in FSet. However, an implementation can
freely use orders.lattices.alt_Build_JoinSemiLatticeOrder.
*)

Class FSetContainsSpec A `{At : SetType A}
     `{SetLe A} `{SetContains A} `{Ajoin : SetJoin A} `{Asingle : SetSingleton A} :=
  { fset_join_sl_order :> JoinSemiLatticeOrder (≤)
  ; fset_in_singleton_le : ∀ x X, x ∈ X ↔ {{ x }} ≤ X }.

(*
Unfortunately, properties as meet and the differences cannot be uniquely
defined in an algebraic way, therefore we just use set inclusion.
*)
Class FullFSet A {car conAle Acontains Aempty Ajoin Asingle U Adec}
  `{Adiff : SetDifference A} `{Ameet : SetMeet A} :=
  { full_fset_fset :> @FSet A car Aempty Ajoin Asingle U Adec
  ; full_fset_contains :> @FSetContainsSpec A car conAle Acontains Ajoin Asingle
  ; fset_in_meet : ∀ X Y x, x ∈ X ⊓ Y ↔ (x ∈ X ∧ x ∈ Y)
  ; fset_in_difference : ∀ X Y x, x ∈ X∖ Y ↔ (x ∈ X ∧ x ∉ Y) }.
