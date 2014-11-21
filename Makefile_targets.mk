# This file defined the targets of the Makefile.  If you add another
# file, add it to the appropriate variable here.  The order of files
# here determines their order in the TOC.  It is preferable to list a
# file after all of its dependencies, and to group similar files.  If
# in doubt, put your new files at the end of the CORE_VFILES list, as
# "$(srcdir)/theories/<new files>.v" (no quotes).  Don't forget to add
# a '\' to the end of the line before it, or, if you place it in the
# middle, to the end of the line that you added.

STD_VFILES = \
	$(SRCCOQLIB)/theories/Init/Notations.v \
	$(SRCCOQLIB)/theories/Init/Logic.v \
	$(SRCCOQLIB)/theories/Init/Datatypes.v \
	$(SRCCOQLIB)/theories/Init/Logic_Type.v \
	$(SRCCOQLIB)/theories/Init/Peano.v \
	$(SRCCOQLIB)/theories/Init/Tactics.v \
	$(SRCCOQLIB)/theories/Init/Specif.v \
	$(SRCCOQLIB)/theories/Init/Prelude.v \
	$(SRCCOQLIB)/theories/Bool/Bool.v \
	$(SRCCOQLIB)/theories/Unicode/Utf8_core.v \
	$(SRCCOQLIB)/theories/Unicode/Utf8.v \
	$(SRCCOQLIB)/theories/Program/Tactics.v

CORE_VFILES = \
	$(srcdir)/theories/Basics/Overture.v \
	$(srcdir)/theories/Basics/UniverseLevel.v \
	$(srcdir)/theories/Basics/PathGroupoids.v \
	$(srcdir)/theories/Basics/Contractible.v \
	$(srcdir)/theories/Basics/Equivalences.v \
	$(srcdir)/theories/Basics/Trunc.v \
	$(srcdir)/theories/Basics/FunextVarieties.v \
	$(srcdir)/theories/Basics/Pointed.v \
	$(srcdir)/theories/Basics.v \
	$(srcdir)/theories/Types/Paths.v \
	$(srcdir)/theories/Types/Unit.v \
	$(srcdir)/theories/Types/Forall.v \
	$(srcdir)/theories/Types/Arrow.v \
	$(srcdir)/theories/Types/Sigma.v \
	$(srcdir)/theories/Types/Prod.v \
	$(srcdir)/theories/Types/Record.v \
	$(srcdir)/theories/Types/Empty.v \
	$(srcdir)/theories/Types/Bool.v \
	$(srcdir)/theories/Types/Sum.v \
	$(srcdir)/theories/Types/Equiv.v \
	$(srcdir)/theories/Types/Universe.v \
	$(srcdir)/theories/Types/Nat.v \
	$(srcdir)/theories/Types.v \
	$(srcdir)/theories/Fibrations.v \
	$(srcdir)/theories/Conjugation.v \
	$(srcdir)/theories/HProp.v \
	$(srcdir)/theories/EquivalenceVarieties.v \
	$(srcdir)/theories/Extensions.v \
	$(srcdir)/theories/HSet.v \
	$(srcdir)/theories/UnivalenceImpliesFunext.v \
	$(srcdir)/theories/Tactics.v \
	$(srcdir)/theories/Tactics/RewriteModuloAssociativity.v \
	$(srcdir)/theories/Tactics/BinderApply.v \
	$(srcdir)/theories/TruncType.v \
	$(srcdir)/theories/Functorish.v \
	$(srcdir)/theories/FunextAxiom.v \
	$(srcdir)/theories/UnivalenceAxiom.v \
	$(srcdir)/theories/ObjectClassifier.v \
	$(srcdir)/theories/NullHomotopy.v \
	$(srcdir)/theories/Factorization.v \
	$(srcdir)/theories/Modalities/ReflectiveSubuniverse.v \
	$(srcdir)/theories/Modalities/Modality.v \
	$(srcdir)/theories/Modalities/Accessible.v \
	$(srcdir)/theories/Modalities/Notnot.v \
	$(srcdir)/theories/Modalities/Identity.v \
	$(srcdir)/theories/Modalities/Localization.v \
	$(srcdir)/theories/Modalities/Nullification.v \
	$(srcdir)/theories/Modalities/Open.v \
	$(srcdir)/theories/Modalities/Closed.v \
	$(srcdir)/theories/hit/Circle.v \
	$(srcdir)/theories/hit/Truncations.v \
	$(srcdir)/theories/hit/Connectedness.v \
	$(srcdir)/theories/hit/Flattening.v \
	$(srcdir)/theories/hit/Interval.v \
	$(srcdir)/theories/hit/IntervalImpliesFunext.v \
	$(srcdir)/theories/hit/Suspension.v \
	$(srcdir)/theories/hit/Spheres.v \
	$(srcdir)/theories/hit/TwoSphere.v \
	$(srcdir)/theories/hit/epi.v \
	$(srcdir)/theories/hit/unique_choice.v \
	$(srcdir)/theories/hit/quotient.v \
	$(srcdir)/theories/hit/iso.v \
	$(srcdir)/theories/hit/Pushout.v \
	$(srcdir)/theories/hit/Join.v \
	$(srcdir)/theories/hit/V.v \
	$(srcdir)/theories/Misc.v \
	$(srcdir)/theories/Utf8.v \
	$(srcdir)/theories/HoTT.v \
	$(srcdir)/theories/Tests.v

CATEGORY_VFILES = \
	$(srcdir)/theories/categories.v \
	\
	$(srcdir)/theories/categories/Category.v \
	$(srcdir)/theories/categories/Functor.v \
	$(srcdir)/theories/categories/NaturalTransformation.v \
	\
	$(srcdir)/theories/categories/Category/Core.v \
	$(srcdir)/theories/categories/Functor/Core.v \
	$(srcdir)/theories/categories/NaturalTransformation/Core.v \
	\
	$(srcdir)/theories/categories/Category/Morphisms.v \
	$(srcdir)/theories/categories/Category/Strict.v \
	$(srcdir)/theories/categories/Category/Univalent.v \
	$(srcdir)/theories/categories/Category/Objects.v \
	$(srcdir)/theories/categories/Category/Dual.v \
	$(srcdir)/theories/categories/Category/Prod.v \
	$(srcdir)/theories/categories/Category/Pi.v \
	$(srcdir)/theories/categories/Category/Sum.v \
	$(srcdir)/theories/categories/Category/Sigma.v \
	$(srcdir)/theories/categories/Category/Sigma/Core.v \
	\
	$(srcdir)/theories/categories/Functor/Composition.v \
	$(srcdir)/theories/categories/Functor/Composition/Core.v \
	$(srcdir)/theories/categories/Functor/Identity.v \
	$(srcdir)/theories/categories/Functor/Paths.v \
	\
	$(srcdir)/theories/categories/Category/Sigma/OnMorphisms.v \
	$(srcdir)/theories/categories/Category/Sigma/OnObjects.v \
	$(srcdir)/theories/categories/Category/Subcategory.v \
	$(srcdir)/theories/categories/Category/Subcategory/Full.v \
	$(srcdir)/theories/categories/Category/Subcategory/Wide.v \
	$(srcdir)/theories/categories/Category/Notations.v \
	$(srcdir)/theories/categories/Category/Utf8.v \
	\
	$(srcdir)/theories/categories/Functor/Prod.v \
	$(srcdir)/theories/categories/Functor/Dual.v \
	\
	$(srcdir)/theories/categories/SetCategory.v \
	$(srcdir)/theories/categories/SetCategory/Core.v \
	$(srcdir)/theories/categories/SetCategory/Morphisms.v \
	$(srcdir)/theories/categories/SetCategory/Functors.v \
	$(srcdir)/theories/categories/SetCategory/Functors/SetProp.v \
	\
	$(srcdir)/theories/categories/FundamentalPreGroupoidCategory.v \
	$(srcdir)/theories/categories/HomotopyPreCategory.v \
	\
	$(srcdir)/theories/categories/HomFunctor.v \
	$(srcdir)/theories/categories/Functor/Attributes.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Paths.v \
	$(srcdir)/theories/categories/NaturalTransformation/Identity.v \
	$(srcdir)/theories/categories/NaturalTransformation/Composition.v \
	$(srcdir)/theories/categories/NaturalTransformation/Composition/Core.v \
	$(srcdir)/theories/categories/NaturalTransformation/Composition/Laws.v \
	\
	$(srcdir)/theories/categories/FunctorCategory.v \
	$(srcdir)/theories/categories/FunctorCategory/Core.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Composition/Functorial.v \
	\
	$(srcdir)/theories/categories/ExponentialLaws.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law0.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law1.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law1/Functors.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law1/Law.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law2.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law2/Functors.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law2/Law.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law3.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law3/Functors.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law3/Law.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law4.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law4/Functors.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law4/Law.v \
	$(srcdir)/theories/categories/ExponentialLaws/Tactics.v \
	\
	$(srcdir)/theories/categories/Functor/Composition/Functorial.v \
	$(srcdir)/theories/categories/Functor/Composition/Functorial/Core.v \
	$(srcdir)/theories/categories/Functor/Composition/Functorial/Attributes.v \
	$(srcdir)/theories/categories/Functor/Composition/Laws.v \
	\
	$(srcdir)/theories/categories/Functor/Sum.v \
	$(srcdir)/theories/categories/Functor/Pointwise.v \
	$(srcdir)/theories/categories/Functor/Prod/Core.v \
	$(srcdir)/theories/categories/Functor/Prod/Universal.v \
	\
	$(srcdir)/theories/categories/GroupoidCategory.v \
	$(srcdir)/theories/categories/GroupoidCategory/Core.v \
	\
	$(srcdir)/theories/categories/CategoryOfGroupoids.v \
	\
	$(srcdir)/theories/categories/DiscreteCategory.v \
	\
	$(srcdir)/theories/categories/IndiscreteCategory.v \
	\
	$(srcdir)/theories/categories/NatCategory.v \
	\
	$(srcdir)/theories/categories/InitialTerminalCategory.v \
	$(srcdir)/theories/categories/InitialTerminalCategory/Core.v \
	$(srcdir)/theories/categories/InitialTerminalCategory/Functors.v \
	$(srcdir)/theories/categories/InitialTerminalCategory/NaturalTransformations.v \
	$(srcdir)/theories/categories/InitialTerminalCategory/Pseudofunctors.v \
	$(srcdir)/theories/categories/InitialTerminalCategory/Notations.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Prod.v \
	\
	$(srcdir)/theories/categories/Functor/Prod/Functorial.v \
	$(srcdir)/theories/categories/Functor/Pointwise/Core.v \
	$(srcdir)/theories/categories/Functor/Pointwise/Properties.v \
	$(srcdir)/theories/categories/Functor/Notations.v \
	$(srcdir)/theories/categories/Functor/Utf8.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Dual.v \
	$(srcdir)/theories/categories/NaturalTransformation/Sum.v \
	$(srcdir)/theories/categories/NaturalTransformation/Pointwise.v \
	\
	$(srcdir)/theories/categories/FunctorCategory/Dual.v \
	$(srcdir)/theories/categories/FunctorCategory/Morphisms.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Isomorphisms.v \
	$(srcdir)/theories/categories/NaturalTransformation/Notations.v \
	$(srcdir)/theories/categories/NaturalTransformation/Utf8.v \
	\
	$(srcdir)/theories/categories/Structure.v \
	$(srcdir)/theories/categories/Structure/Core.v \
	$(srcdir)/theories/categories/Structure/IdentityPrinciple.v \
	$(srcdir)/theories/categories/Structure/Notations.v \
	$(srcdir)/theories/categories/Structure/Utf8.v \
	\
	$(srcdir)/theories/categories/CategoryOfSections.v \
	$(srcdir)/theories/categories/CategoryOfSections/Core.v \
	\
	$(srcdir)/theories/categories/Profunctor/Core.v \
	$(srcdir)/theories/categories/Profunctor/Identity.v \
	\
	$(srcdir)/theories/categories/Comma.v \
	$(srcdir)/theories/categories/Comma/Core.v \
	\
	$(srcdir)/theories/categories/Adjoint.v \
	$(srcdir)/theories/categories/Adjoint/UnitCounit.v \
	$(srcdir)/theories/categories/Adjoint/Core.v \
	$(srcdir)/theories/categories/Adjoint/Paths.v \
	$(srcdir)/theories/categories/Adjoint/Identity.v \
	$(srcdir)/theories/categories/Adjoint/Composition.v \
	$(srcdir)/theories/categories/Adjoint/Composition/Core.v \
	$(srcdir)/theories/categories/Adjoint/Composition/LawsTactic.v \
	$(srcdir)/theories/categories/Adjoint/Composition/AssociativityLaw.v \
	$(srcdir)/theories/categories/Adjoint/Composition/IdentityLaws.v \
	$(srcdir)/theories/categories/Adjoint/Dual.v \
	$(srcdir)/theories/categories/Adjoint/UnitCounitCoercions.v \
	$(srcdir)/theories/categories/Adjoint/UniversalMorphisms.v \
	$(srcdir)/theories/categories/Adjoint/Hom.v \
	$(srcdir)/theories/categories/Adjoint/HomCoercions.v \
	$(srcdir)/theories/categories/Adjoint/Pointwise.v \
	$(srcdir)/theories/categories/Adjoint/Notations.v \
	$(srcdir)/theories/categories/Adjoint/Utf8.v \
	\
	$(srcdir)/theories/categories/Cat.v \
	$(srcdir)/theories/categories/Cat/Core.v \
	\
	$(srcdir)/theories/categories/DualFunctor.v \
	\
	$(srcdir)/theories/categories/FunctorCategory/Functorial.v \
	$(srcdir)/theories/categories/FunctorCategory/Notations.v \
	$(srcdir)/theories/categories/FunctorCategory/Utf8.v \
	\
	$(srcdir)/theories/categories/ProductLaws.v \
	\
	$(srcdir)/theories/categories/GroupoidCategory/Morphisms.v \
	\
	$(srcdir)/theories/categories/Profunctor.v \
	$(srcdir)/theories/categories/Profunctor/Representable.v \
	$(srcdir)/theories/categories/Profunctor/Notations.v \
	$(srcdir)/theories/categories/Profunctor/Utf8.v \
	\
	$(srcdir)/theories/categories/Yoneda.v \
	\
	$(srcdir)/theories/categories/Cat/Morphisms.v \
	\
	$(srcdir)/theories/categories/Comma/Dual.v \
	$(srcdir)/theories/categories/Comma/Projection.v \
	$(srcdir)/theories/categories/Comma/InducedFunctors.v \
	$(srcdir)/theories/categories/Comma/ProjectionFunctors.v \
	$(srcdir)/theories/categories/Comma/Functorial.v \
	$(srcdir)/theories/categories/Comma/Notations.v \
	$(srcdir)/theories/categories/Comma/Utf8.v \
	\
	$(srcdir)/theories/categories/Pseudofunctor.v \
	$(srcdir)/theories/categories/Pseudofunctor/Core.v \
	$(srcdir)/theories/categories/Pseudofunctor/RewriteLaws.v \
	$(srcdir)/theories/categories/Pseudofunctor/FromFunctor.v \
	$(srcdir)/theories/categories/Pseudofunctor/Identity.v \
	\
	$(srcdir)/theories/categories/PseudonaturalTransformation.v \
	$(srcdir)/theories/categories/PseudonaturalTransformation/Core.v \
	\
	$(srcdir)/theories/categories/LaxComma.v \
	$(srcdir)/theories/categories/LaxComma/Core.v \
	$(srcdir)/theories/categories/LaxComma/CoreParts.v \
	$(srcdir)/theories/categories/LaxComma/CoreLaws.v \
	$(srcdir)/theories/categories/LaxComma/Notations.v \
	$(srcdir)/theories/categories/LaxComma/Utf8.v \
	\
	$(srcdir)/theories/categories/Grothendieck.v \
	$(srcdir)/theories/categories/Grothendieck/ToSet.v \
	$(srcdir)/theories/categories/Grothendieck/PseudofunctorToCat.v \
	$(srcdir)/theories/categories/Grothendieck/ToCat.v \
	\
	$(srcdir)/theories/categories/DependentProduct.v \
	\
	$(srcdir)/theories/categories/UniversalProperties.v \
	\
	$(srcdir)/theories/categories/KanExtensions.v \
	$(srcdir)/theories/categories/KanExtensions/Core.v \
	$(srcdir)/theories/categories/KanExtensions/Functors.v \
	\
	$(srcdir)/theories/categories/Limits.v \
	$(srcdir)/theories/categories/Limits/Core.v \
	$(srcdir)/theories/categories/Limits/Functors.v \
	\
	$(srcdir)/theories/categories/Notations.v \
	$(srcdir)/theories/categories/Utf8.v

CONTRIB_VFILES = \
	$(srcdir)/contrib/HoTTBook.v \
	$(srcdir)/contrib/HoTTBookExercises.v \
	$(srcdir)/contrib/Freudenthal.v
