(** * Index of Booij's thesis *)

(** This file lists, in thesis order, the numbered items of Chapters 3–8 of A. B. Booij, _Analysis in Univalent Type Theory_ (PhD thesis, University of Birmingham, 2020) that have been formalized, each as a [Check] of the results that formalize it. It defines nothing; it fails to build if a listed result is renamed or removed. See [BLUEPRINT.md] for the plan and for the items that are not formalized yet. *)

From HoTT Require Import Basics.Overture Basics.Classes.
From HoTT.Classes.interfaces Require Import canonical_names orders rationals archimedean cauchy.
From HoTT.Cubical Require Import DPath.
From HoTT.Misc Require Import BoundedSearch.
From HoTT.Classes.orders Require Import archimedean rationals.
From HoTT.Analysis Require Import Dcpo IntervalObject Locator MetricSpace.

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

(** Definition 3.1.4. Inflationary endomaps; semidirected and directed subsets; joins; dcpos and subdcpos, at a universe level [i] given by universe polymorphism. *)
Check IsInflationary.
Check IsSemidirected.
Check IsDirected.
Check IsJoin.
Check IsDcpo.
Check IsSubdcpo.

(** Lemma 3.1.5. The elements of a subdcpo form a dcpo under the restricted order. *)
Check @isdcpo_sig.

(** Lemma 3.1.6. Functions into a dcpo form a dcpo under the pointwise order. *)
Check @partialorder_pointwise.
Check @isdcpo_pointwise.

(** Lemma 3.1.7. Assuming propositional resizing, the subsets [A -> HProp@{i}] of a type [A] in universe [i] form a dcpo at level [i+1] under inclusion: propositions form such a dcpo under implication, and the subsets are its pointwise order. *)
Check @isdcpo_hprop.
Check @isdcpo_pointwise.

(** Proposition 3.2.1. The inflationary endomaps of a dcpo form a subdcpo of the endomaps, which as a subset of itself is directed, so that it has a top element; its values are common fixed points of all inflationary endomaps. *)
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
