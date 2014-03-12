(** A convenience file that loads most of the HoTT library.
    You can use it with "Require Import HoTT" in your files.
    But please do not use it in the HoTT library itself, or
    you are likely going to create a dependency loop. *)

Require Export Overture.
Require Export PathGroupoids.
Require Export Conjugation.
Require Export Contractible.
Require Export Equivalences.
Require Export Trunc.
Require Export FunextVarieties.
Require Export Pointed.
Require Export HProp.
Require Export HSet.
Require Export Fibrations.
Require Export EquivalenceVarieties.
Require Export Misc.
Require Export Functorish.

Require Export types.Unit.
Require Export types.Paths.
Require Export types.Forall.
Require Export types.Empty.
Require Export types.Bool.
Require Export types.Arrow.
Require Export types.Prod.
Require Export types.Record.
Require Export types.Sigma.
Require Export types.Sum.
Require Export types.Universe.
Require Export types.ObjectClassifier.
Require Export types.UniverseLevel.

Require Export hit.Interval.
Require Export hit.Truncations.
Require Export hit.Flattening.
Require Export hit.Circle.
Require Export hit.Suspension.
Require Export hit.Spheres.
Require Export hit.minus1Trunc.
Require Export hit.epi.
Require Export hit.unique_choice.
Require Export hit.iso.
Require Export hit.quotient.

Require Export HoTT.Tactics.
