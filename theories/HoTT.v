(** A convenience file that loads most of the HoTT library.
    You can use it with "Require Import HoTT" in your files.
    But please do not use it in the HoTT library itself, or
    you are likely going to create a dependency loop. *)

Require Export HoTT.Basics.

Require Export HoTT.Types.

Require Export Fibrations.
Require Export Conjugation.
Require Export HProp.
Require Export HSet.
Require Export EquivalenceVarieties.
Require Export Extensions.
Require Export Misc.
Require Export Functorish.
Require Export Factorization.
Require Export ObjectClassifier.
Require Export TruncType.
Require Export NullHomotopy.
Require Export Idempotents.

Require Export hit.Interval.
Require Export hit.Truncations.
Require Export hit.Connectedness.
Require Export hit.Flattening.
Require Export hit.Circle.
Require Export hit.Suspension.
Require Export hit.Spheres.
Require Export hit.Pushout.
Require Export hit.epi.
Require Export hit.unique_choice.
Require Export hit.iso.
Require Export hit.quotient.
Require Export hit.V.
Require Export hit.Join.

Require Export Modalities.ReflectiveSubuniverse.
Require Export Modalities.Modality.
Require Export Modalities.Accessible.
Require Export Modalities.Notnot.
Require Export Modalities.Identity.
Require Export Modalities.Localization.
Require Export Modalities.Nullification.
Require Export Modalities.Open.
Require Export Modalities.Closed.

Require Export HoTT.Tactics.

(** We do _not_ export [UnivalenceAxiom], [FunextAxiom], [UnivalenceImpliesFunext], or [hit.IntervalImpliesFunext] from this file; thus importing it does not prevent you from tracking usage of [Univalence] and [Funext] theorem-by-theorem in the same way that the library does.  If you want any of those files, you should import them separately. *)
