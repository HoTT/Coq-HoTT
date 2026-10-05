(** * Regression tests for global inductive cumulativity *)

Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Universes.TruncType.
Require Import HoTT.Modalities.ReflectiveSubuniverse.
Require Import HoTT.Modalities.Accessible HoTT.Modalities.Localization.
Require Import HoTT.Algebra.Universal.Algebra.
Require Import HoTT.Algebra.Universal.Homomorphism.

(** Importing the library makes new records cumulative, too. *)
Record CumulativeRecord@{i} := { cumulative_carrier : Type@{i} }.

Definition lift_record@{i j | i < j}
  (X : CumulativeRecord@{i}) : CumulativeRecord@{j} := X.

Definition lift_generators@{a b | a < b}
  (f : LocalGenerators@{a}) : LocalGenerators@{b} := f.

(** The generators need not have the same size as the localized universe. *)
Definition locality@{a i j | a <= j, i <= j}
  (f : LocalGenerators@{a}) (X : Type@{i}) : Type@{j}
  := IsLocal_Internal.IsLocal@{i j a} f X.

Definition larger_localization@{a i | a < i}
  (f : LocalGenerators@{a}) : ReflectiveSubuniverse@{i} := Loc@{a i} f.

Definition lift_accessible@{a i j | a <= i, a < j}
  (O : Subuniverse@{i}) (acc : IsAccRSU@{a i} O)
  : ReflectiveSubuniverse@{j} := @lift_accrsu@{a i j} O acc.

(** Instance search must not change the universe of [TruncType]. *)
Definition truncated_universe@{i j | i < j} `{Univalence}
  (n : trunc_index) : IsTrunc_internal@{j} (TruncType@{i} n) n.+1 := _.

Definition hprop_function_space@{a i j | a <= j, i < j}
  `{Univalence} (X : Type@{a})
  : IsTrunc_internal@{j} (X -> HProp@{i}) 0.
Proof.
  rapply istrunc_arrow@{a j j}.
Defined.

(** Identity and composition also work for algebras with differently sized carriers. *)
Section Algebras.
  Universes us uo ur ua ub uc ut.
  Constraint ur <= ut, ua <= ut, ub <= ut, uc <= ut.
  Context {sigma : Signature@{us uo ur}}
    (A : Algebra@{us uo ur ua ut} sigma)
    (B : Algebra@{us uo ur ub ut} sigma)
    (C : Algebra@{us uo ur uc ut} sigma).

  Definition identity_hom@{}
    : Homomorphism@{us uo ur ua ut ua ut ut} A A := homomorphism_id A.

  Definition compose_homs@{}
    (g : Homomorphism@{us uo ur ub ut uc ut ut} B C)
    (f : Homomorphism@{us uo ur ua ut ub ut ut} A B)
    : Homomorphism@{us uo ur ua ut uc ut ut} A C
    := homomorphism_compose g f.
End Algebras.
