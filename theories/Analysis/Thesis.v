(** * Index of Booij's thesis *)

(** This file lists, in thesis order, the numbered items of Chapters 3–8 of A. B. Booij, _Analysis in Univalent Type Theory_ (PhD thesis, University of Birmingham, 2020) that have been formalized, each as a [Check] of the results that formalize it. It defines nothing; it fails to build if a listed result is renamed or removed. See [BLUEPRINT.md] for the plan and for the items that are not formalized yet. *)

From HoTT Require Import Basics.Overture Basics.Classes.
From HoTT.Classes.interfaces Require Import canonical_names orders rationals archimedean cauchy.
From HoTT.Cubical Require Import DPath.
From HoTT.Modalities Require Import ReflectiveSubuniverse.
From HoTT.Misc Require Import BoundedSearch.
From HoTT.Classes.orders Require Import archimedean rationals.
From HoTT.DomainTheory Require Import Dcpo Constructions FixedPoints.
From HoTT.Analysis Require Import IntervalObject Locator MetricSpace BanachFixedPoint CauchyCompleteness CauchyReals CauchyStructure LocatorDigits LiftsToLocators IntermediateValue.

(** ** Chapter 3: Fixpoints in dcpos *)

(** Definition 3.1.1. Reflexive, irreflexive, symmetric, antisymmetric, transitive and cotransitive relations. *)
Check Reflexive.
Check Irreflexive.
Check Symmetric.
Check AntiSymmetric.
Check Transitive.
Check CoTransitive.

(** Definition 3.1.3. Preorders and partial orders. *)
Check PreOrder.
Check PartialOrder.

(** Definition 3.1.4. Inflationary endomaps, which are monotone ([OrderPreserving]) and increasing (called [IsInflationary] here, following TypeTopology); semidirected and directed families, and subsets as families indexed by their total space; suprema; dcpos and subdcpos, at a universe level [v] of index types given by universe polymorphism. A partial order in which every directed subset has a supremum is a dcpo. *)
Check OrderPreserving.
Check IsInflationary.
Check IsSemidirected.
Check IsDirected.
Check IsSup.
Check IsDcpo.
Check @isdcpo_from_subsets.
Check IsSubdcpo.

(** Lemma 3.1.5. The elements of a subdcpo form a dcpo under the restricted order. *)
Check @isdcpo_sig.

(** Lemma 3.1.6. Functions into a dcpo form a dcpo under the pointwise order. *)
Check @partialorder_pointwise.
Check @isdcpo_pointwise.

(** Lemma 3.1.7. Assuming propositional resizing, the subsets [A -> HProp@{i}] of a type [A] in universe [i] form a dcpo under inclusion, with index types in any universe, in particular at level [i+1]: propositions form such a dcpo under implication, and the subsets are its pointwise order. *)
Check @isdcpo_hprop.
Check @isdcpo_pointwise.

(** Proposition 3.2.1. The monotone inflationary endomaps of a dcpo whose carrier and order live in the universe of index types form a subdcpo of the endomaps, which as a family indexed by itself is directed, so that it has a top element; its values are common fixed points of all monotone inflationary endomaps. *)
Check @issubdcpo_inflationary.
Check @isdirected_inflationary.
Check @top_inflationary.
Check @top_inflationary_greatest.
Check @top_inflationary_fixed_point.

(** Corollary 3.2.2. A point of a subdcpo closed under an inflationary endomap gives a fixed point of it, without propositional resizing. *)
Check @fixed_point_subdcpo.

(** Theorem 3.2.3. Pataraia's theorem: assuming propositional resizing, a monotone endomap of a dcpo with a bottom element has a least fixed point. *)
Check @least_fixed_point.

(** ** Chapter 4: Real numbers *)

(** Definition 4.1.8. Lattices. *)
Check LatticeOrder.

(** Lemma 4.1.12. An ordered field is a constructive field. *)
Check @ordered_field_field.

(** Lemma 4.3.3. There is a unique morphism of ordered fields from the rationals to an ordered field, and it preserves and reflects the strict order. *)
Check rationals_to_field.
Check rationals_initial.
Check strictly_order_preserving_rationals_to_field.
Check strictly_order_reflecting_rationals_to_field.
Check issemiringstrongpreserving_rationals_to_field.

(** Remark 4.3.4. The morphism from the rationals to an ordered field is an embedding. *)
Check isinjective_rationals_to_field.
Check isembedding_rationals_to_field.

(** Definition 4.3.5. Archimedean ordered fields. *)
Check ArchimedeanProperty.

(** Definition 4.4.1. Modulus of Cauchy convergence. *)
Check CauchyModulus.

(** Definition 4.4.2. Limit of a sequence. *)
Check IsLimit.

(** Definition 4.4.4. Cauchy complete ordered fields. *)
Check IsComplete.

(** Lemma 4.4.5. In an Archimedean ordered field, limits of sequences are unique, so the type of limits of a sequence is a proposition. *)
Check limit_unique.
Check ishprop_limit.

(** Corollary 4.4.6. A limit that merely exists can be computed. *)
Check limit_merely.

(** Corollary 4.4.7. If a limit can be computed from a modulus of Cauchy convergence, it can be computed from the mere existence of a modulus; in particular in a Cauchy complete Archimedean ordered field. *)
Check limit_merely_modulus.
Check limit_complete.

(** Definition 4.4.9. The Cauchy reals: rational sequences with a modulus of Cauchy convergence, quotiented by the relation identifying [x] and [y] when [|x (M (e / 4)) - y (N (e / 4))| < e] for all [e], where [M] and [N] are their moduli. *)
Check CauchySequence.
Check cauchy_related.
Check CauchyReals.

(** Definition 4.5.2. Premetrics: families of relations indexed by the positive rationals, valued in propositions. *)
Check IsPremetric.

(** Definition 4.5.3. Moduli of Cauchy convergence of sequences in a premetric space. *)
Check MetricCauchyModulus.

(** Definition 4.5.4. Limits of sequences in a premetric space. *)
Check IsMetricLimit.

(** Definition 4.5.5. Cauchy approximations. *)
Check IsCauchyApproximation.
Check CauchyApproximation.

(** Definition 4.5.7. Limits of Cauchy approximations, and Cauchy complete premetric spaces. *)
Check IsApproximationLimit.
Check CauchyComplete.

(** Definition 4.5.8. Cauchy structures and their morphisms. *)
Check CauchyStructure.
Check CauchyStructureHom.

(** Remark 4.5.9. A morphism of Cauchy structures, indeed any map preserving closeness, acts on Cauchy approximations; identity maps are morphisms, and morphisms compose. *)
Check @map_cauchy_approximation.
Check cshom_idmap.
Check @cshom_compose.

(** Lemma 4.5.10. In an Archimedean ordered field with [u] and [v] being [e]-close when [|u - v| < e], a limit [u] of a Cauchy approximation [x] satisfies [|x d - u| ≤ d]. *)
Check field_close.
Check @isapproximationlimit_le.

(** Corollary 4.5.11. A Cauchy complete Archimedean ordered field is Cauchy complete as a premetric space, and has a canonical Cauchy structure. *)
Check @cauchycomplete_field.
Check @cauchy_structure_field.

(** Definition 4.5.17. Dependent identifications. *)
Check DPath.

(** ** Chapter 5: Universal properties of real numbers *)

(** Definition 5.3.1. Cancellative midpoint algebras: sets with an idempotent, commutative, medial and cancellative binary operation. *)
Check Midpoint.
Check Medial.
Check IsCancellativeMidpointAlgebra.

(** Definition 5.3.2. Convex bodies: cancellative midpoint algebras with an iteration operator. *)
Check @IsIterationOperator.
Check IterationOperator.
Check IsConvexBody.

(** Lemma 5.3.3. Any two iteration operators are equal, so having one is a proposition. *)
Check @path_iteration_operator.
Check @ishprop_iterationoperator.

(** Theorem 5.3.4. An iteration operator is equivalently the contractibility, for every sequence [x], of the type of sequences [a] with [a i = m(x i, a i.+1)] for all [i]. *)
Check @equiv_iteration_operator_contr_iterated_midpoints.

(** Definition 5.3.5. Bipointed convex bodies and their homomorphisms. *)
Check BipointedConvexBody.
Check @IsConvexBodyHom.
Check ConvexBodyHom.

(** Definition 5.3.6. Interval objects: homotopy-initial bipointed convex bodies. *)
Check IsIntervalObject.

(** Remark 5.3.7. Contractibility of the type of homomorphisms of bipointed convex bodies means existence of a homomorphism and pointwise uniqueness. *)
Check @contr_convexbodyhom_iff.

(** ** Chapter 6: Locators *)

(** Definition 6.1.1. Locators. *)
Check locator.

(** Lemma 6.1.3. Assuming excluded middle, every real has a locator. *)
Check all_reals_locators.

(** Lemma 6.4.2. A locator is equivalently a decidable [locatesRight] with its two properties. *)
Check @equiv_locator_locator'.

(** Definition 6.4.4. [locatesRight] and [locatesLeft]. *)
Check locates_right.
Check locates_left.

(** Lemma 6.4.6. What a locator must locate. *)
Check nltqx_locates_left.
Check nltxr_locates_right.

(** Theorem 6.5.1. Bounded search: from [exists n, P n] with [P] decidable we get [{n & P n}]. *)
Check minimal_n.

(** Corollary 6.5.4. Bounded search over a type equivalent to [nat]. *)
Check minimal_n_alt_type.

(** Lemma 6.6.1. A real with a locator has rational bounds. *)
Check lower_bound.
Check upper_bound.

(** Lemma 6.6.3. A real with a locator has arbitrarily tight rational bounds. *)
Check tight_bound.

(** Lemma 6.7.1. Characterizations of [-x], [x + y], [x y], reciprocals, [min] and [max] in terms of the strict order with rationals. *)
Check char_minus_left.
Check char_minus_right.
Check char_plus_left.
Check char_plus_right.
Check char_times_left.
Check char_times_right.
Check char_recip_pos_left.
Check char_recip_pos_right.
Check char_recip_neg_left.
Check char_recip_neg_right.
Check char_meet_left.
Check char_meet_right.
Check char_join_left.
Check char_join_right.

(** Lemma 6.7.3. For reals with locators, [x < y] gives a rational between them. *)
Check archimedean_structure.

(** Corollary 6.7.4. For reals [x < y] with locators and a rational [s], we can choose [x < s] or [s < y]. *)
Check locator_cotransitive_rational.

(** Theorem 6.7.6. If [x] and [y] have locators, then so do [-x], [x + y], [x y], [x⁻¹] (for [x # 0]), [min(x, y)] and [max(x, y)]. *)
Check locator_minus.
Check locator_plus.
Check locator_times.
Check locator_recip.
Check locator_meet.
Check locator_join.

(** Lemma 6.8.1. A limit of a sequence with modulus whose terms have locators has a locator. *)
Check locator_limit.

(** Definition 6.9.2. Signed-digit representations: an integer and a sequence of signed digits whose partial sums converge to the given real. Here in base [1 + d] with digits from [- d] to [d], for an arbitrary model [Z] of the integers; the thesis's decimal case is [d = 9]. *)
Check digit_weight.
Check digit_sum.
Check SignedDigits.

(** Lemma 6.9.4. A real with a locator lies within distance [1] of an integer, which we can find using an integer part of rationals. *)
Check integer_floor.
Check integer_bound.

(** Theorem 6.9.5. Locators and signed-digit representations are interdefinable. *)
Check locator_signed_digits.
Check signed_digits_locator.

(** Definition 6.9.6. An element of a Cauchy complete Archimedean ordered field is a Cauchy real when it is merely in the image of the canonical map from the Cauchy reals, which sends a sequence to its limit and commutes with the inclusions of the rationals; equivalently, when it is merely the limit of a rational sequence with a modulus. *)
Check cauchy_reals_to_field.
Check rationals_to_cauchy_reals.
Check cauchy_reals_to_field_rationals.
Check IsCauchyReal.
Check iscauchyreal_iff_limit.

(** Theorem 6.9.7. Merely having a locator, merely having a signed-digit representation, merely being the limit of a rational sequence with a modulus, and being a Cauchy real are equivalent. Constructively, a signed-digit representation gives such a sequence, and such a sequence gives a locator for its limit. *)
Check merely_locator_iff_signed_digits.
Check merely_locator_iff_limit.
Check iscauchyreal_iff_limit.
Check cauchy_sequence_signed_digits.
Check locator_cauchy_sequence.

(** Remark 6.9.8. A locator can be truncated as a whole, pointwise, or in its values: the first implies the second, which is equivalent to the third because the order on the rationals is decidable, using that a function from a decidable type into a truncation can be brought inside it. The third holds for every element by cotransitivity of the order. *)
Check merely_locator_pointwise.
Check pointwise_locator_iff_located.
Check @O_decidable_arrow.
Check cotransitive.

(** ** Chapter 7: Some constructive analysis with locators *)

(** Definition 7.1.1. A function lifts to locators if it is equipped with a map from locators for [x] to locators for [f x]. *)
Check LiftsToLocators.

(** Definition 7.1.4. Continuity at a point, and pointwise continuity. *)
Check IsContinuousAt.
Check IsPointwiseContinuous.

(** Definition 7.1.5. A modulus of uniform continuity on an interval [[a, b]]: a modulus of uniform continuity for the restriction to the interval. *)
Check UniformModulusOn.

(** Lemma 7.1.7. If all constant functions lift to locators, then every element has a locator. *)
Check locator_lifts_constant.

(** Lemma 7.1.8. Assuming excluded middle, a function which is not continuous lifts to locators. *)
Check step_function.
Check lifts_step_function.
Check not_iscontinuousat_step_function.

(** Theorem 7.3.1. Approximate intermediate value theorem: a function which is pointwise continuous on [[a, b]] with [f a < 0 < f b] merely takes values arbitrarily close to [0]; if it lifts to locators and [a] and [b] have locators, we can find such a point with a locator. The thesis claims that the limit of Frank's interpolating bisection is such a point, which can fail; the proof shows that the limit or one of the midpoints is. *)
Check approximate_ivt.
Check approximate_ivt_locator.

(** Definition 7.3.2. Locally nonconstant functions. *)
Check IsLocallyNonconstant.

(** Lemma 7.3.4. For a continuous, locally nonconstant function which lifts to locators, and [x < y] and [t] with locators, we can find a rational [r] with [x < r < y] and [f r] apart from [t]. *)
Check locally_nonconstant_rational.

(** Theorem 7.3.5. Exact intermediate value theorem: a continuous, locally nonconstant function which lifts to locators, with [f a ≤ 0 ≤ f b] for [a < b] with locators, has a root in [[a, b]] with a locator. *)
Check exact_ivt.

(** ** Chapter 8: Metric spaces *)

(** Definition 8.1.1. Pseudometrics and metrics, with values in the nonnegative elements of an ordered field. *)
Check IsPseudoMetric.
Check IsMetric.

(** Lemma 8.1.3. The Euclidean distance [|x - y|] is a metric. *)
Check @ismetric_abs_minus.

(** Lemma 8.1.5. Two limits of a sequence in a pseudometric space have distance zero; in a metric space limits are unique. Here [x] and [y] are [e]-close when their distance is less than [e], which defines moduli of Cauchy convergence and limits. *)
Check metric_close.
Check MetricCauchyModulus.
Check IsMetricLimit.
Check @metric_limit_distance_zero.
Check @metric_limit_unique.

(** Definition 8.1.6. Cauchy completeness: a limit operator for sequences with a modulus of Cauchy convergence. *)
Check MetricCauchyComplete.

(** Definition 8.1.7. Moduli of uniform continuity, with the identity and composition. *)
Check IsUniformModulus.
Check @isuniformmodulus_idmap.
Check @isuniformmodulus_compose.

(** Lemma 8.1.8. A uniformly continuous map with modulus [w] sends a sequence with modulus [M] to one with modulus [M o w]. *)
Check @metriccauchymodulus_uniform.

(** Definition 8.1.9. Maps preserving limits. *)
Check PreservesMetricLimits.

(** Lemma 8.1.10. Uniformly continuous maps preserve limits. *)
Check @preservesmetriclimits_uniform.

(** Definition 8.3.1. Lipschitz constants. *)
Check IsLipschitz.

(** Lemma 8.3.2. A positive rational Lipschitz constant [c] gives the modulus of uniform continuity [e / c]. *)
Check @isuniformmodulus_lipschitz.

(** Corollary 8.3.3. A positive Lipschitz constant in the ordered field merely gives a modulus of uniform continuity. *)
Check @merely_isuniformmodulus_lipschitz.

(** Lemma 8.3.4. For a Lipschitz constant [c < 1], pseudo-fixed points are unique up to distance zero. *)
Check @pseudo_fixed_point_unique.

(** Corollary 8.3.5. In a metric space, for a Lipschitz constant [c < 1], the type of fixed points is a proposition. *)
Check @ishprop_fixed_point.

(** Remark 8.3.6. It suffices that such a Lipschitz constant merely exists. *)
Check @ishprop_fixed_point_merely.

(** Lemma 8.3.7. For a rational [0 < c < 1], a logarithm-like function giving for each positive rational [q] an exponent [n] with [c^n < q]. *)
Check @rational_log.

(** Lemma 8.3.8. For a rational Lipschitz constant [0 < c < 1] and [d (T x0) x0 ≤ C], the iterates of [T] at [x0] have the modulus of Cauchy convergence [log_c (e (1 - c) / C)]. *)
Check @iterates_modulus.
Check @metriccauchymodulus_iterates.

(** Theorem 8.3.11. Banach's fixed point theorem: in a Cauchy complete pseudometric space, a map with a rational Lipschitz constant [0 < c < 1] has a pseudo-fixed point, unique up to distance zero. *)
Check @banach_fixed_point.
