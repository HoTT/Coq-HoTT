Require Import HoTT.Types.Universe.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.implementations.field_of_fractions
  HoTTClasses.theory.integers.

(* Without this the class Rationals needs an instance of Funext/Univalence,
   then if we assume 2 instances they get separate Funext/Univalence instances
   unless we do annoying annotations ala
   [`{@Rationals preexisting_funext preexisting_univalence Q Qplus Qmult ...}] *)
Require Export HoTT.FunextAxiom.
Require Export HoTT.UnivalenceAxiom.

Section rationals_to_frac.
  Context (A : Type).

  Class RationalsToFrac := rationals_to_frac : ∀ B `{Integers B}, A →
    FracField.F B.
End rationals_to_frac.

(*
We specify the Rationals as a field that contains the integers and can be embedded
into the field of integers fractions. Since we do not want to fix a specific integer
representation in this interface, we quantify over all integer implementations.
However, when constructing an instance of the rationals it is generally inconvenient
to prove that the required properties hold for all possible integer implementations.
Therefore we provide a way (theory.rationals.alt_Build_Rationals) to construct
a rationals implementation if the required properties hold for some specific
implementation of the integers.
*)

Class Rationals A {plus mult zero one neg recip} `{U : !RationalsToFrac A} :=
  { rationals_field:> @DecField A plus mult zero one neg recip
  ; rationals_frac :> ∀ `{Integers Z}, Injective (rationals_to_frac A Z)
  ; rationals_frac_mor :> ∀ `{Integers Z}, SemiRingPreserving (rationals_to_frac A Z)
  ; rationals_embed_ints :> ∀ `{Integers Z}, Injective (integers_to_ring Z A) }.
