(** A convenience file that loads most of the HoTT library.
    You can use it with "Require Import HoTT" in your files.
    But please do not use it in the HoTT library itself, or
    you are likely going to create a dependency loop. *)

Require Export HoTT.Basics.

Require Export HoTT.Types.

Require Export HoTT.Cubical.

Require Export Fibrations.
Require Export Conjugation.
Require Export HProp.
Require Export HSet.
Require Export EquivGroupoids.
Require Export EquivalenceVarieties.
Require Export FunextVarieties.
Require Export UnivalenceVarieties.
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
Require Export ExcludedMiddle.
Require Export BoundedSearch.

Require Export PropResizing.PropResizing.
(* Don't export the rest of [PropResizing] *)

Require Export Homotopy.HomotopyGroup.

Require Export HIT.Suspension.
Require Export HIT.Interval.
Require Export HIT.Truncations.
Require Export HIT.Connectedness.
Require Export HIT.Coeq.
Require Export HIT.Flattening.
Require Export HIT.Circle.
Require Export HIT.FreeIntQuotient.
Require Export HIT.Spheres.
Require Export HIT.Pushout.
Require Export HIT.SpanPushout.
Require Export HIT.SetCone.
Require Export HIT.epi.
Require Export HIT.unique_choice.
Require Export HIT.iso.
Require Export HIT.quotient.
Require Export HIT.V.
Require Export HIT.Join.

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
Require Export Spaces.BAut.Rigid.
Require Export Spaces.No.
Require Export Spaces.Universe.

Require Export Algebra.ooGroup.
Require Export Algebra.Aut.
Require Export Algebra.ooAction.

Require Export Homotopy.HomotopyGroup.
Require Export Homotopy.Pi1S1.
Require Export Homotopy.BlakersMassey.

Require Export Spectra.Spectrum.

Require Export HoTT.Tactics.
Require Export HoTT.Tactics.EvalIn.
Require Export HoTT.Tactics.BinderApply.
Require Export HoTT.Tactics.RewriteModuloAssociativity.
Require Export HoTT.Tactics.EquivalenceInduction.

(** We do _not_ export [UnivalenceAxiom], [FunextAxiom], [UnivalenceImpliesFunext], [HIT.IntervalImpliesFunext], nor [HIT.TruncImpliesFunext] from this file; thus importing it does not prevent you from tracking usage of [Univalence] and [Funext] theorem-by-theorem in the same way that the library does.  If you want any of those files, you should import them separately. *)
