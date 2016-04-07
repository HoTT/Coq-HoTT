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
Require Export EquivGroupoids.
Require Export EquivalenceVarieties.
Require Export Extensions.
Require Export Misc.
Require Export Functorish.
Require Export Factorization.
Require Export Constant.
Require Export ObjectClassifier.
Require Export TruncType.
Require Export Pointed.
Require Export DProp.
Require Export NullHomotopy.
Require Export Idempotents.
Require Export Pullback.

Require Export hit.Interval.
Require Export hit.Truncations.
Require Export hit.Connectedness.
Require Export hit.Coeq.
Require Export hit.Flattening.
Require Export hit.Circle.
Require Export hit.FreeIntQuotient.
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
Require Export Modalities.Lex.
Require Export Modalities.Topological.
Require Export Modalities.Notnot.
Require Export Modalities.Identity.
Require Export Modalities.Localization.
Require Export Modalities.Nullification.
Require Export Modalities.Open.
Require Export Modalities.Closed.
Require Export Modalities.Fracture.

Require Export Comodalities.CoreflectiveSubuniverse.

Require Export Spaces.Nat.
Require Export Spaces.Int.
Require Export Spaces.Cantor.
Require Export Spaces.BAut.
Require Export Spaces.BAut.Cantor.
Require Export Spaces.Finite.
Require Export Spaces.BAut.Bool.
Require Export Spaces.BAut.Bool.IncoherentIdempotent.
Require Export Spaces.No.

Require Export Algebra.ooGroup.
Require Export Algebra.Aut.
Require Export Algebra.ooAction.

Require Export Spectra.Spectrum.

Require Export HoTT.Tactics.
Require Export HoTT.Tactics.EvalIn.
Require Export HoTT.Tactics.BinderApply.
Require Export HoTT.Tactics.RewriteModuloAssociativity.
Require Export HoTT.Tactics.EquivalenceInduction.

(** We do _not_ export [UnivalenceAxiom], [FunextAxiom], [UnivalenceImpliesFunext], [hit.IntervalImpliesFunext], nor [hit.TruncImpliesFunext] from this file; thus importing it does not prevent you from tracking usage of [Univalence] and [Funext] theorem-by-theorem in the same way that the library does.  If you want any of those files, you should import them separately. *)
