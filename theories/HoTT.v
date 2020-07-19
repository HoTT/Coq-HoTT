(** A convenience file that loads most of the HoTT library.
    You can use it with "Require Import HoTT" in your files.
    But please do not use it in the HoTT library itself, or
    you are likely going to create a dependency loop. *)

Require Export HoTT.Basics.
Require Export HoTT.Types.
Require Export HoTT.WildCat.
Require Export HoTT.Cubical.
Require Export HoTT.Pointed.
Require Export HoTT.Truncations.

Require Export HoTT.HFiber.
Require Export HoTT.HProp.
Require Export HoTT.HSet.
Require Export HoTT.EquivGroupoids.

Require Export HoTT.Equiv.BiInv.
Require Export HoTT.Equiv.PathSplit.
Require Export HoTT.Equiv.Relational.

Require Export HoTT.Extensions.
Require Export HoTT.Misc.
Require Export HoTT.PathAny.

Require Export HoTT.Functorish.
Require Export HoTT.Factorization.
Require Export HoTT.Constant.
Require Export HoTT.ObjectClassifier.
Require Export HoTT.TruncType.

Require Export HoTT.DProp.
Require Export HoTT.NullHomotopy.
Require Export HoTT.Idempotents.
Require Export HoTT.ExcludedMiddle.
Require Export HoTT.BoundedSearch.

Require Export HoTT.PropResizing.PropResizing.
(* Don't export the rest of [PropResizing] *)

Require Export HoTT.HIT.Interval.
Require Export HoTT.HIT.Coeq.
Require Export HoTT.HIT.Flattening.
Require Export HoTT.HIT.FreeIntQuotient.
Require Export HoTT.HIT.SetCone.
Require Export HoTT.HIT.epi.
Require Export HoTT.HIT.unique_choice.
Require Export HoTT.HIT.iso.
Require Export HoTT.HIT.quotient.
Require Export HoTT.HIT.V.

Require Export HoTT.Diagrams.Graph.
Require Export HoTT.Diagrams.Diagram.
Require Export HoTT.Diagrams.Cone.
Require Export HoTT.Diagrams.Cocone.
Require Export HoTT.Diagrams.DDiagram.
Require Export HoTT.Diagrams.ConstantDiagram.
Require Export HoTT.Diagrams.CommutativeSquares.
Require Export HoTT.Diagrams.Sequence.
Require Export HoTT.Diagrams.Span.
Require Export HoTT.Diagrams.ParallelPair.

Require Export HoTT.Limits.Pullback.
Require Export HoTT.Limits.Equalizer.
Require Export HoTT.Limits.Limit.

Require Export HoTT.Colimits.Pushout.
Require Export HoTT.Colimits.SpanPushout.
Require Export HoTT.Colimits.Quotient.
Require Export HoTT.Colimits.MappingCylinder.
Require Export HoTT.Colimits.Colimit.
Require Export HoTT.Colimits.Colimit_Pushout.
Require Export HoTT.Colimits.Colimit_Coequalizer.
Require Export HoTT.Colimits.Colimit_Flattening.
Require Export HoTT.Colimits.Colimit_Prod.
Require Export HoTT.Colimits.Colimit_Pushout_Flattening.
Require Export HoTT.Colimits.Colimit_Sigma.

Require Export HoTT.Modalities.ReflectiveSubuniverse.
Require Export HoTT.Modalities.Modality.
Require Export HoTT.Modalities.Accessible.
Require Export HoTT.Modalities.Notnot.
Require Export HoTT.Modalities.Identity.
Require Export HoTT.Modalities.Localization.
Require Export HoTT.Modalities.Nullification.
Require Export HoTT.Modalities.Descent.
Require Export HoTT.Modalities.Separated.
Require Export HoTT.Modalities.Lex.
Require Export HoTT.Modalities.Topological.
Require Export HoTT.Modalities.Open.
Require Export HoTT.Modalities.Closed.
Require Export HoTT.Modalities.Fracture.

Require Export HoTT.Modalities.CoreflectiveSubuniverse.

Require Export HoTT.Spaces.Nat.
Require Export HoTT.Spaces.Int.
Require Export HoTT.Spaces.Pos.

Require Export HoTT.Spaces.Cantor.

Require Export HoTT.Spaces.Circle.
Require Export HoTT.Spaces.TwoSphere.
Require Export HoTT.Spaces.Spheres.

Require Export HoTT.Spaces.BAut.
Require Export HoTT.Spaces.BAut.Cantor.
Require Export HoTT.Spaces.BAut.Bool.
Require Export HoTT.Spaces.BAut.Bool.IncoherentIdempotent.
Require Export HoTT.Spaces.BAut.Rigid.

Require Export HoTT.Spaces.Finite.

Require Export HoTT.Spaces.No.
Require Export HoTT.Spaces.Universe.

Require Export HoTT.Spaces.Torus.Torus.
Require Export HoTT.Spaces.Torus.TorusEquivCircles.
Require Export HoTT.Spaces.Torus.TorusHomotopy.

Require Export HoTT.Algebra.ooGroup.
Require Export HoTT.Algebra.Aut.
Require Export HoTT.Algebra.ooAction.
Require Export HoTT.Algebra.AbGroups.
Require Export HoTT.Algebra.Groups.

Require Export HoTT.Homotopy.HomotopyGroup.
Require Export HoTT.Homotopy.Pi1S1.
Require Export HoTT.Homotopy.WhiteheadsPrinciple.
Require Export HoTT.Homotopy.BlakersMassey.
Require Export HoTT.Homotopy.Freudenthal.
Require Export HoTT.Homotopy.Suspension.
Require Export HoTT.Homotopy.Smash.
Require Export HoTT.Homotopy.Wedge.
Require Export HoTT.Homotopy.Join.
Require Export HoTT.Homotopy.HSpace.
Require Export HoTT.Homotopy.ClassifyingSpace.

Require Export HoTT.Spectra.Spectrum.

Require Export HoTT.Tactics.
Require Export HoTT.Tactics.BinderApply.
Require Export HoTT.Tactics.EquivalenceInduction.
Require Export HoTT.Tactics.EvalIn.
Require Export HoTT.Tactics.Nameless.
Require Export HoTT.Tactics.RewriteModuloAssociativity.

(** We do _not_ export [UnivalenceAxiom], [FunextAxiom], or any of the files in [Metatheory] from this file.  Thus, importing this file does not prevent you from tracking usage of [Univalence] and [Funext] theorem-by-theorem in the same way that the library does.  If you want any of those files, you should import them separately. *)

(** We check that UnivalenceAxiom, FunextAxiom aren't being leaked. This is so that these can be imported seperately. *)
Fail Check HoTT.UnivalenceAxiom.univalence_axiom.
Fail Check HoTT.FunextAxiom.funext_axiom.
