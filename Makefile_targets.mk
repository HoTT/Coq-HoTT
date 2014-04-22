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
	$(SRCCOQLIB)/theories/Program/Tactics.v

CORE_VFILES = \
	$(srcdir)/theories/Overture.v \
	$(srcdir)/theories/PathGroupoids.v \
	$(srcdir)/theories/Conjugation.v \
	$(srcdir)/theories/Contractible.v \
	$(srcdir)/theories/Equivalences.v \
	$(srcdir)/theories/types/Paths.v \
	$(srcdir)/theories/types/Unit.v \
	$(srcdir)/theories/Trunc.v \
	$(srcdir)/theories/types/Forall.v \
	$(srcdir)/theories/types/Arrow.v \
	$(srcdir)/theories/types/Sigma.v \
	$(srcdir)/theories/types/Prod.v \
	$(srcdir)/theories/types/Record.v \
	$(srcdir)/theories/types/Empty.v \
	$(srcdir)/theories/HProp.v \
	$(srcdir)/theories/EquivalenceVarieties.v \
	$(srcdir)/theories/Fibrations.v \
	$(srcdir)/theories/types/UniverseLevel.v \
	$(srcdir)/theories/FunextVarieties.v \
	$(srcdir)/theories/HSet.v \
	$(srcdir)/theories/types/Bool.v \
	$(srcdir)/theories/types/Sum.v \
	$(srcdir)/theories/types/Universe.v \
	$(srcdir)/theories/UnivalenceImpliesFunext.v \
	$(srcdir)/theories/Pointed.v \
	$(srcdir)/theories/Tactics.v \
	$(srcdir)/theories/HoTT.v \
	$(srcdir)/theories/Misc.v \
	$(srcdir)/theories/TruncType.v \
	$(srcdir)/theories/Functorish.v \
	$(srcdir)/theories/FunextAxiom.v \
	$(srcdir)/theories/UnivalenceAxiom.v \
	$(srcdir)/theories/Modality.v \
	$(srcdir)/theories/hit/Circle.v \
	$(srcdir)/theories/hit/Truncations.v \
	$(srcdir)/theories/hit/Connectedness.v \
	$(srcdir)/theories/hit/Flattening.v \
	$(srcdir)/theories/hit/Interval.v \
	$(srcdir)/theories/hit/Suspension.v \
	$(srcdir)/theories/hit/Spheres.v \
	$(srcdir)/theories/hit/TwoSphere.v \
	$(srcdir)/theories/hit/minus1Trunc.v \
	$(srcdir)/theories/hit/epi.v \
	$(srcdir)/theories/hit/unique_choice.v \
	$(srcdir)/theories/hit/quotient.v \
	$(srcdir)/theories/hit/iso.v \
	$(srcdir)/theories/types/ObjectClassifier.v

CATEGORY_VFILES = \
	$(srcdir)/theories/categories/categories.v \
	\
	$(srcdir)/theories/categories/Category/Category.v \
	$(srcdir)/theories/categories/Functor/Functor.v \
	$(srcdir)/theories/categories/NaturalTransformation/NaturalTransformation.v \
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
	$(srcdir)/theories/categories/Category/Sum.v \
	$(srcdir)/theories/categories/Category/Sigma/Core.v \
	\
	$(srcdir)/theories/categories/Functor/Composition/Composition.v \
	$(srcdir)/theories/categories/Functor/Composition/Core.v \
	$(srcdir)/theories/categories/Functor/Identity.v \
	$(srcdir)/theories/categories/Functor/Paths.v \
	\
	$(srcdir)/theories/categories/Category/Sigma/Sigma.v \
	$(srcdir)/theories/categories/Category/Sigma/OnMorphisms.v \
	$(srcdir)/theories/categories/Category/Sigma/OnObjects.v \
	$(srcdir)/theories/categories/Category/Subcategory/Subcategory.v \
	$(srcdir)/theories/categories/Category/Subcategory/Full.v \
	$(srcdir)/theories/categories/Category/Subcategory/Wide.v \
	$(srcdir)/theories/categories/Category/Notations.v \
	$(srcdir)/theories/categories/Category/Utf8.v \
	\
	$(srcdir)/theories/categories/Functor/Prod.v \
	$(srcdir)/theories/categories/Functor/Dual.v \
	\
	$(srcdir)/theories/categories/SetCategory/SetCategory.v \
	$(srcdir)/theories/categories/SetCategory/Core.v \
	$(srcdir)/theories/categories/SetCategory/Morphisms.v \
	$(srcdir)/theories/categories/SetCategory/Functors/Functors.v \
	\
	$(srcdir)/theories/categories/FundamentalPreGroupoidCategory.v \
	$(srcdir)/theories/categories/HomotopyPreCategory.v \
	\
	$(srcdir)/theories/categories/HomFunctor.v \
	$(srcdir)/theories/categories/Functor/Attributes.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Paths.v \
	$(srcdir)/theories/categories/NaturalTransformation/Identity.v \
	$(srcdir)/theories/categories/NaturalTransformation/Composition/Composition.v \
	$(srcdir)/theories/categories/NaturalTransformation/Composition/Core.v \
	$(srcdir)/theories/categories/NaturalTransformation/Composition/Laws.v \
	\
	$(srcdir)/theories/categories/FunctorCategory/FunctorCategory.v \
	$(srcdir)/theories/categories/FunctorCategory/Core.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Composition/Functorial.v \
	\
	$(srcdir)/theories/categories/ExponentialLaws/ExponentialLaws.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law0.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law1/Law1.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law1/Functors.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law1/Law.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law2/Law2.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law2/Functors.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law3/Law3.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law3/Functors.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law4/Law4.v \
	$(srcdir)/theories/categories/ExponentialLaws/Law4/Functors.v \
	\
	$(srcdir)/theories/categories/Functor/Composition/Functorial.v \
	$(srcdir)/theories/categories/Functor/Composition/Functorial/Core.v \
	$(srcdir)/theories/categories/Functor/Composition/Functorial/Attributes.v \
	$(srcdir)/theories/categories/Functor/Composition/Laws.v \
	\
	$(srcdir)/theories/categories/Functor/Sum.v \
	$(srcdir)/theories/categories/Functor/Pointwise.v \
	$(srcdir)/theories/categories/Functor/Prod/Prod.v \
	$(srcdir)/theories/categories/Functor/Prod/Universal.v \
	\
	$(srcdir)/theories/categories/GroupoidCategory/GroupoidCategory.v \
	$(srcdir)/theories/categories/GroupoidCategory/Core.v \
	\
	$(srcdir)/theories/categories/DiscreteCategory.v \
	\
	$(srcdir)/theories/categories/IndiscreteCategory.v \
	\
	$(srcdir)/theories/categories/NatCategory.v \
	\
	$(srcdir)/theories/categories/InitialTerminalCategory.v \
	\
	$(srcdir)/theories/categories/NaturalTransformation/Prod.v \
	\
	$(srcdir)/theories/categories/Functor/Prod/Functorial.v \
	$(srcdir)/theories/categories/Functor/Pointwise/Pointwise.v \
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
	$(srcdir)/theories/categories/Structure/Core.v \
	$(srcdir)/theories/categories/Structure/IdentityPrinciple.v \
	$(srcdir)/theories/categories/Structure/Notations.v \
	$(srcdir)/theories/categories/Structure/Utf8.v \
	$(srcdir)/theories/categories/Structure/Structure.v \
	\
	$(srcdir)/theories/categories/CategoryOfSections/Core.v \
	$(srcdir)/theories/categories/CategoryOfSections/CategoryOfSections.v \
	\
	$(srcdir)/theories/categories/Profunctor/Core.v \
	$(srcdir)/theories/categories/Profunctor/Identity.v \
	\
	$(srcdir)/theories/categories/Comma/Comma.v \
	$(srcdir)/theories/categories/Comma/Core.v \
	\
	$(srcdir)/theories/categories/Adjoint/Adjoint.v \
	$(srcdir)/theories/categories/Adjoint/UnitCounit.v \
	$(srcdir)/theories/categories/Adjoint/Core.v \
	$(srcdir)/theories/categories/Adjoint/Composition/Core.v \
	$(srcdir)/theories/categories/Adjoint/Paths.v \
	$(srcdir)/theories/categories/Adjoint/Identity.v \
	$(srcdir)/theories/categories/Adjoint/Composition/Composition.v \
	$(srcdir)/theories/categories/Adjoint/Composition/LawsTactic.v \
	$(srcdir)/theories/categories/Adjoint/Composition/AssociativityLaw.v \
	$(srcdir)/theories/categories/Adjoint/Composition/IdentityLaws.v \
	$(srcdir)/theories/categories/Adjoint/Dual.v \
	$(srcdir)/theories/categories/Adjoint/UnitCounitCoercions.v \
	$(srcdir)/theories/categories/Adjoint/UniversalMorphisms.v \
	$(srcdir)/theories/categories/Adjoint/Hom.v \
	$(srcdir)/theories/categories/Adjoint/HomCoercions.v \
	$(srcdir)/theories/categories/Adjoint/Notations.v \
	$(srcdir)/theories/categories/Adjoint/Utf8.v \
	\
	$(srcdir)/theories/categories/Cat/Cat.v \
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
	$(srcdir)/theories/categories/Profunctor/Profunctor.v \
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
	$(srcdir)/theories/categories/Comma/Notations.v \
	$(srcdir)/theories/categories/Comma/Utf8.v \
	\
	$(srcdir)/theories/categories/Pseudofunctor/Pseudofunctor.v \
	$(srcdir)/theories/categories/Pseudofunctor/Core.v \
	$(srcdir)/theories/categories/Pseudofunctor/FromFunctor.v \
	\
	$(srcdir)/theories/categories/Grothendieck/Grothendieck.v \
	$(srcdir)/theories/categories/Grothendieck/ToSet.v \
	$(srcdir)/theories/categories/Grothendieck/PseudofunctorToCat.v \
	$(srcdir)/theories/categories/Grothendieck/ToCat.v \
	\
	$(srcdir)/theories/categories/DependentProduct.v \
	\
	$(srcdir)/theories/categories/UniversalProperties.v \
	\
	$(srcdir)/theories/categories/KanExtensions/KanExtensions.v \
	$(srcdir)/theories/categories/KanExtensions/Core.v \
	$(srcdir)/theories/categories/KanExtensions/Functors.v \
	\
	$(srcdir)/theories/categories/Limits/Limits.v \
	$(srcdir)/theories/categories/Limits/Core.v \
	$(srcdir)/theories/categories/Limits/Functors.v \
	\
	$(srcdir)/theories/categories/Notations.v \
	$(srcdir)/theories/categories/Utf8.v

CONTRIB_VFILES = \
	$(srcdir)/contrib/HoTTBook.v \
	$(srcdir)/contrib/HoTTBookExercises.v
