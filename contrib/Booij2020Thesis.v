(** * Analysis in Univalent Type Theory: the formalization *)

(** This file links the numbered results of Chapters 3–8 of A. B. Booij, _Analysis in Univalent Type Theory_ (PhD thesis, University of Birmingham, 2020) with their formalizations in the HoTT library and in [HoTT_Contrib]. You can look up definitions and theorems by their number in the thesis: the formalization of Lemma 6.6.1 is [Booij2020Thesis_6_6_1], and an item formalized by several results has one definition per result, [Booij2020Thesis_6_6_1_item_i], [Booij2020Thesis_6_6_1_item_ii], and so on. Use [Print] or [About] on these names to find the results they stand for.

Every numbered item of these chapters has an entry. An item that has not been formalized (an example, a remark without formal content, a conjecture, or a result that has not been done yet) has an entry with a comment saying so instead of definitions. [BLUEPRINT.md] in the root of the repository lists every numbered item of these chapters, with its status, its dependencies, and how the formalization differs from the thesis. *)

(*  NOTES FOR THE DEVELOPERS:

    This file is kept in the format of [HoTTBook.v], without a script that maintains it. Each entry starts with a marker line, a comment line with many = signs followed by the item number; then comes a heading with the kind and number of the item and a short statement in words.

    1. Keep the entries in the order of the thesis, one per numbered item.

    2. Each entry defines [Booij2020Thesis_X_Y_Z], or [Booij2020Thesis_X_Y_Z_item_i], [Booij2020Thesis_X_Y_Z_item_ii], ... for an item with several parts, as an alias of the results that formalize it. Use the existing name of a result rather than adding a new definition for the index.

    3. An item that is not formalized gets an entry with no definitions: after the heading and the short statement in words comes a plain comment starting with "Not formalized:" and saying briefly why or what it would need (e.g. "Not formalized: an example." or "Not formalized: needs the interval object of Section 5.1."), or "Conjecture." for a conjecture. Replace the comment by definitions once the item is formalized. Numbered displayed equations do not get entries of their own; they are covered by the entry of the item that contains them.

    4. Make entries independent of each other, and import everything before the first entry.

    5. Thesis numbers appear only here and in [BLUEPRINT.md]: the formalizations themselves describe the mathematics.
*)

From HoTT Require Import Basics.Overture Basics.Classes.
From HoTT.Classes.interfaces Require Import canonical_names abstract_algebra orders rationals archimedean cauchy.
From HoTT.Classes.theory Require Import apartness rings fields.
From HoTT.Cubical Require Import DPath.
From HoTT.Modalities Require Import ReflectiveSubuniverse.
From HoTT.Misc Require Import BoundedSearch CompactTypes.
From HoTT.Classes.orders Require Import archimedean rationals maps.
From HoTT.DomainTheory Require Import Dcpo Constructions FixedPoints.
From HoTT.Analysis Require Import Locator.
From HoTT_Contrib.Analysis Require Import
  IntervalObject MetricSpace BanachFixedPoint CauchyCompleteness CauchyReals CauchyStructure
  DedekindReals LocatorDigits LiftsToLocators IntermediateValue HoTTBookReals RealsInclusions
  FunctionSpace Integral PicardLindelof LocatorCuts EuclideanReals.


(* END OF PREAMBLE *)
(* ================================================== 3.1.1 *)
(** Definition 3.1.1 *)

(** Reflexive, irreflexive, symmetric, antisymmetric, transitive and cotransitive relations. *)
Definition Booij2020Thesis_3_1_1_item_i := @Reflexive.
Definition Booij2020Thesis_3_1_1_item_ii := @Irreflexive.
Definition Booij2020Thesis_3_1_1_item_iii := @Symmetric.
Definition Booij2020Thesis_3_1_1_item_iv := @AntiSymmetric.
Definition Booij2020Thesis_3_1_1_item_v := @Transitive.
Definition Booij2020Thesis_3_1_1_item_vi := @CoTransitive.

(* ================================================== 3.1.2 *)
(** Remark 3.1.2 *)

(** Cotransitivity is also known as weak linearity or the approximate splitting principle. *)
(* Not formalized: a remark on terminology. *)

(* ================================================== 3.1.3 *)
(** Definition 3.1.3 *)

(** Preorders and partial orders. *)
Definition Booij2020Thesis_3_1_3_item_i := @PreOrder.
Definition Booij2020Thesis_3_1_3_item_ii := @PartialOrder.

(* ================================================== 3.1.4 *)
(** Definition 3.1.4 *)

(** Inflationary endomaps, semidirected and directed families, suprema, dcpos and subdcpos. *)
Definition Booij2020Thesis_3_1_4_item_i := @OrderPreserving.
Definition Booij2020Thesis_3_1_4_item_ii := @IsInflationary.
Definition Booij2020Thesis_3_1_4_item_iii := @IsSemidirected.
Definition Booij2020Thesis_3_1_4_item_iv := @IsDirected.
Definition Booij2020Thesis_3_1_4_item_v := @IsSup.
Definition Booij2020Thesis_3_1_4_item_vi := @IsDcpo.
Definition Booij2020Thesis_3_1_4_item_vii := @isdcpo_from_subsets.
Definition Booij2020Thesis_3_1_4_item_viii := @IsSubdcpo.

(* ================================================== 3.1.5 *)
(** Lemma 3.1.5 *)

(** The elements of a subdcpo form a dcpo under the restricted order. *)
Definition Booij2020Thesis_3_1_5 := @isdcpo_sig.

(* ================================================== 3.1.6 *)
(** Lemma 3.1.6 *)

(** Functions into a dcpo form a dcpo under the pointwise order. *)
Definition Booij2020Thesis_3_1_6_item_i := @partialorder_pointwise.
Definition Booij2020Thesis_3_1_6_item_ii := @isdcpo_pointwise.

(* ================================================== 3.1.7 *)
(** Lemma 3.1.7 *)

(** Assuming propositional resizing, the subsets of a type form a dcpo under inclusion. *)
Definition Booij2020Thesis_3_1_7_item_i := @isdcpo_hprop.
Definition Booij2020Thesis_3_1_7_item_ii := @isdcpo_pointwise.

(* ================================================== 3.2.1 *)
(** Proposition 3.2.1 *)

(** The monotone inflationary endomaps of a dcpo form a directed subdcpo of the endomaps, with a top element whose values are common fixed points. *)
Definition Booij2020Thesis_3_2_1_item_i := @issubdcpo_inflationary.
Definition Booij2020Thesis_3_2_1_item_ii := @isdirected_inflationary.
Definition Booij2020Thesis_3_2_1_item_iii := @top_inflationary.
Definition Booij2020Thesis_3_2_1_item_iv := @top_inflationary_greatest.
Definition Booij2020Thesis_3_2_1_item_v := @top_inflationary_fixed_point.

(* ================================================== 3.2.2 *)
(** Corollary 3.2.2 *)

(** A point of a subdcpo closed under an inflationary endomap gives a fixed point of it, without propositional resizing. *)
Definition Booij2020Thesis_3_2_2 := @fixed_point_subdcpo.

(* ================================================== 3.2.3 *)
(** Theorem 3.2.3 *)

(** Pataraia's theorem: assuming propositional resizing, a monotone endomap of a dcpo with a bottom element has a least fixed point. *)
Definition Booij2020Thesis_3_2_3 := @least_fixed_point.

(* ================================================== 4.1.1 *)
(** Remark 4.1.1 *)

(** In a commutative ring that is a set, multiplicative inverses are unique, so the mere existence of inverses of nonzero elements is equivalent to their structured existence. *)
(* Not formalized: uniqueness of multiplicative inverses is not stated as a lemma. *)

(* ================================================== 4.1.2 *)
(** Definition 4.1.2 *)

(** Classical fields: commutative rings in which every element different from [0] has a multiplicative inverse. [IsDecField] is stronger: it asks for a total reciprocal with [/0 = 0], which needs decidability of [x = 0], and for [1 <> 0]. *)
Definition Booij2020Thesis_4_1_2 := @IsDecField.

(* ================================================== 4.1.3 *)
(** Remark 4.1.3 *)

(** Uniqueness of additive and multiplicative inverses gives the negation and division operations. *)
(* Not formalized: a remark; in the library negation and reciprocal are primitive operations. *)

(* ================================================== 4.1.4 *)
(** Definition 4.1.4 *)

(** Apartness relations: irreflexive, symmetric and cotransitive; strict partial orders: irreflexive, transitive and cotransitive. [IsApart] is stronger: a tight apartness on a set, valued in propositions; the plain notion is the combination of [Irreflexive], [Symmetric] and [CoTransitive]. *)
Definition Booij2020Thesis_4_1_4_item_i := @IsApart.
Definition Booij2020Thesis_4_1_4_item_ii := @apart_irrefl.
Definition Booij2020Thesis_4_1_4_item_iii := @StrictOrder.
Definition Booij2020Thesis_4_1_4_item_iv := @CoTransitive.

(* ================================================== 4.1.5 *)
(** Definition 4.1.5 *)

(** Constructive fields: commutative rings with a tight apartness for which addition is extensional and the elements apart from [0] are the invertible ones. *)
Definition Booij2020Thesis_4_1_5_item_i := @IsField.
Definition Booij2020Thesis_4_1_5_item_ii := @mult_apart_zero_l.

(* ================================================== 4.1.6 *)
(** Lemma 4.1.6 *)

(** In a constructive field, [1 ≶ 0], addition is compatible with the apartness, and multiplication is extensional for it. *)
Definition Booij2020Thesis_4_1_6_item_i := @field_nontrivial.
Definition Booij2020Thesis_4_1_6_item_ii := @strongrightcancellation_plus_field.
Definition Booij2020Thesis_4_1_6_item_iii := @strong_setoid_morphism_unary_2.
Definition Booij2020Thesis_4_1_6_item_iv := @field_mult_ext.

(* ================================================== 4.1.7 *)
(** Lemma 4.1.7 *)

(** A strict partial order induces an apartness [x < y ∨ y < x] and a preorder [¬(y < x)]. *)
(* Not formalized: the order classes of the library ([FullPseudoOrder]) take the apartness and [≤] as separate data related to [<]. *)

(* ================================================== 4.1.8 *)
(** Definition 4.1.8 *)

(** Lattices. *)
Definition Booij2020Thesis_4_1_8 := @LatticeOrder.

(* ================================================== 4.1.9 *)
(** Remark 4.1.9 *)

(** In a lattice, [max x y] need not be [x] or [y]; since binary meets and joins in a partial order are unique, giving [min] and [max] is equivalent to their existence. *)
(* Not formalized: a remark; the characterization of [min] and [max] in terms of [<] is Lemma 6.7.1. *)

(* ================================================== 4.1.10 *)
(** Definition 4.1.10 *)

(** Ordered fields, following HoTT book Definition 11.2.7 as the thesis does: a constructive field with a lattice order and a [FullPseudoSemiRingOrder]. *)
Definition Booij2020Thesis_4_1_10_item_i := @OrderedField.
Definition Booij2020Thesis_4_1_10_item_ii := @FullPseudoSemiRingOrder.

(* ================================================== 4.1.11 *)
(** Lemma 4.1.11 *)

(** Given the first five axioms of ordered fields, the compatibility laws of addition and multiplication with [<] are equivalent to ten familiar order laws. *)
(* Not formalized: the individual laws hold for [OrderedField], but the equivalence is not stated. *)

(* ================================================== 4.1.12 *)
(** Lemma 4.1.12 *)

(** An ordered field is a constructive field. *)
Definition Booij2020Thesis_4_1_12 := @ordered_field_field.

(* ================================================== 4.3.1 *)
(** Definition 4.3.1 *)

(** Morphisms of ordered fields: ring morphisms ([IsSemiRingPreserving], which preserve negation by [preserves_negate]) that reflect the strict order. *)
Definition Booij2020Thesis_4_3_1_item_i := @IsSemiRingPreserving.
Definition Booij2020Thesis_4_3_1_item_ii := @preserves_negate.
Definition Booij2020Thesis_4_3_1_item_iii := @StrictlyOrderReflecting.

(* ================================================== 4.3.2 *)
(** Remark 4.3.2 *)

(** A map that reflects [<] preserves [≤]. *)
Definition Booij2020Thesis_4_3_2 := @full_pseudo_order_preserving.

(* ================================================== 4.3.3 *)
(** Lemma 4.3.3 *)

(** There is a unique morphism of ordered fields from the rationals to an ordered field, and it preserves and reflects the strict order. *)
Definition Booij2020Thesis_4_3_3_item_i := @rationals_to_field.
Definition Booij2020Thesis_4_3_3_item_ii := @rationals_initial.
Definition Booij2020Thesis_4_3_3_item_iii := @strictly_order_preserving_rationals_to_field.
Definition Booij2020Thesis_4_3_3_item_iv := @strictly_order_reflecting_rationals_to_field.
Definition Booij2020Thesis_4_3_3_item_v := @issemiringstrongpreserving_rationals_to_field.
Definition Booij2020Thesis_4_3_3_item_vi := @rationals_to_field_mor.

(* ================================================== 4.3.4 *)
(** Remark 4.3.4 *)

(** The morphism from the rationals to an ordered field is an embedding. *)
Definition Booij2020Thesis_4_3_4_item_i := @isinjective_rationals_to_field.
Definition Booij2020Thesis_4_3_4_item_ii := @isembedding_rationals_to_field.

(* ================================================== 4.3.5 *)
(** Definition 4.3.5 *)

(** Archimedean ordered fields. *)
Definition Booij2020Thesis_4_3_5 := @ArchimedeanProperty.

(* ================================================== 4.3.6 *)
(** Example 4.3.6 *)

(** In an Archimedean ordered field every element merely has rational bounds [q < x < r]. *)
(* Not formalized: an example. *)

(* ================================================== 4.4.1 *)
(** Definition 4.4.1 *)

(** Modulus of Cauchy convergence. *)
Definition Booij2020Thesis_4_4_1 := @CauchyModulus.

(* ================================================== 4.4.2 *)
(** Definition 4.4.2 *)

(** Limit of a sequence. *)
Definition Booij2020Thesis_4_4_2 := @IsLimit.

(* ================================================== 4.4.3 *)
(** Remark 4.4.3 *)

(** From a modulus of Cauchy convergence [M] of a sequence with limit [l], [fun e => M (e / 2)] is a modulus of convergence to [l]. *)
(* Not formalized: a remark; [modulus_close_limit] only bounds the distance from [x (M (e / 2))] to the limit. *)

(* ================================================== 4.4.4 *)
(** Definition 4.4.4 *)

(** Cauchy complete ordered fields. *)
Definition Booij2020Thesis_4_4_4 := @IsComplete.

(* ================================================== 4.4.5 *)
(** Lemma 4.4.5 *)

(** In an Archimedean ordered field, limits of sequences are unique, so the type of limits of a sequence is a proposition. *)
Definition Booij2020Thesis_4_4_5_item_i := @limit_unique.
Definition Booij2020Thesis_4_4_5_item_ii := @ishprop_limit.

(* ================================================== 4.4.6 *)
(** Corollary 4.4.6 *)

(** A limit that merely exists can be computed. *)
Definition Booij2020Thesis_4_4_6 := @limit_merely.

(* ================================================== 4.4.7 *)
(** Corollary 4.4.7 *)

(** If a limit can be computed from a modulus of Cauchy convergence, it can be computed from the mere existence of a modulus; in particular in a Cauchy complete Archimedean ordered field. *)
Definition Booij2020Thesis_4_4_7_item_i := @limit_merely_modulus.
Definition Booij2020Thesis_4_4_7_item_ii := @limit_complete.

(* ================================================== 4.4.8 *)
(** Example 4.4.8 *)

(** The exponential function in a Cauchy complete Archimedean ordered field. *)
(* Not formalized: an example; needs finite sums, powers and factorials in an ordered field. *)

(* ================================================== 4.4.9 *)
(** Definition 4.4.9 *)

(** The Cauchy reals: rational sequences with a modulus of Cauchy convergence, quotiented by the relation identifying [x] and [y] when [|x (M (e / 4)) - y (N (e / 4))| < e] for all [e], where [M] and [N] are their moduli. *)
Definition Booij2020Thesis_4_4_9_item_i := @CauchySequence.
Definition Booij2020Thesis_4_4_9_item_ii := @cauchy_related.
Definition Booij2020Thesis_4_4_9_item_iii := @CauchyReals.

(* ================================================== 4.5.1 *)
(** Remark 4.5.1 *)

(** On the name "HoTT book reals" for the Cauchy reals of the HoTT book. *)
(* Not formalized: a remark on terminology. *)

(* ================================================== 4.5.2 *)
(** Definition 4.5.2 *)

(** Premetrics: families of relations indexed by the positive rationals, valued in propositions. *)
Definition Booij2020Thesis_4_5_2 := @IsPremetric.

(* ================================================== 4.5.3 *)
(** Definition 4.5.3 *)

(** Moduli of Cauchy convergence of sequences in a premetric space. *)
Definition Booij2020Thesis_4_5_3 := @MetricCauchyModulus.

(* ================================================== 4.5.4 *)
(** Definition 4.5.4 *)

(** Limits of sequences in a premetric space. *)
Definition Booij2020Thesis_4_5_4 := @IsMetricLimit.

(* ================================================== 4.5.5 *)
(** Definition 4.5.5 *)

(** Cauchy approximations. *)
Definition Booij2020Thesis_4_5_5_item_i := @IsCauchyApproximation.
Definition Booij2020Thesis_4_5_5_item_ii := @CauchyApproximation.

(* ================================================== 4.5.6 *)
(** Remark 4.5.6 *)

(** Cauchy approximations carry their rate of convergence in the data, whereas sequences with a modulus specify it separately. *)
(* Not formalized: a remark comparing two definitions, without formal content. *)

(* ================================================== 4.5.7 *)
(** Definition 4.5.7 *)

(** Limits of Cauchy approximations, and Cauchy complete premetric spaces. *)
Definition Booij2020Thesis_4_5_7_item_i := @IsApproximationLimit.
Definition Booij2020Thesis_4_5_7_item_ii := @CauchyComplete.

(* ================================================== 4.5.8 *)
(** Definition 4.5.8 *)

(** Cauchy structures and their morphisms. *)
Definition Booij2020Thesis_4_5_8_item_i := @CauchyStructure.
Definition Booij2020Thesis_4_5_8_item_ii := @CauchyStructureHom.

(* ================================================== 4.5.9 *)
(** Remark 4.5.9 *)

(** A morphism of Cauchy structures, indeed any map preserving closeness, acts on Cauchy approximations; identity maps are morphisms, and morphisms compose. *)
Definition Booij2020Thesis_4_5_9_item_i := @map_cauchy_approximation.
Definition Booij2020Thesis_4_5_9_item_ii := @cshom_idmap.
Definition Booij2020Thesis_4_5_9_item_iii := @cshom_compose.
(* The first part holds by construction: [CauchyStructureHom] does not contain the distance laws, which are propositions. Not formalized: the example of a Cauchy structure on a two-element type that is not Cauchy complete. *)

(* ================================================== 4.5.10 *)
(** Lemma 4.5.10 *)

(** In an Archimedean ordered field with [u] and [v] being [e]-close when [|u - v| < e], a limit [u] of a Cauchy approximation [x] satisfies [|x d - u| ≤ d]. *)
Definition Booij2020Thesis_4_5_10_item_i := @field_close.
Definition Booij2020Thesis_4_5_10_item_ii := @isapproximationlimit_le.

(* ================================================== 4.5.11 *)
(** Corollary 4.5.11 *)

(** A Cauchy complete Archimedean ordered field is Cauchy complete as a premetric space, and has a canonical Cauchy structure. *)
Definition Booij2020Thesis_4_5_11_item_i := @cauchycomplete_field.
Definition Booij2020Thesis_4_5_11_item_ii := @cauchy_structure_field.

(* ================================================== 4.5.12 *)
(** Definition 4.5.12 *)

(** The HoTT book reals: a Cauchy structure with a contractible type of morphisms to every Cauchy structure (at the same universe levels). *)
Definition Booij2020Thesis_4_5_12_item_i := @IsHoTTBookReals.
Definition Booij2020Thesis_4_5_12_item_ii := @hottbookreals_rec.
Definition Booij2020Thesis_4_5_12_item_iii := @hottbookreals_rec_unique.

(* ================================================== 4.5.13 *)
(** Theorem 4.5.13 *)

(** The HoTT book reals are Cauchy complete, with [lim x] a limit of [x]. *)
Definition Booij2020Thesis_4_5_13_item_i := @hottbookreals_to_field_reflects_close.
Definition Booij2020Thesis_4_5_13_item_ii := @isapproximationlimit_hottbookreals.
Definition Booij2020Thesis_4_5_13_item_iii := @cauchycomplete_hottbookreals.
Definition Booij2020Thesis_4_5_13_item_iv := @cauchycomplete_hottbookreals_dedekind.

(* ================================================== 4.5.14 *)
(** Definition 4.5.14 *)

(** A family [A] over a premetric space with a premetric [B] over closeness, valued in propositions, gives a premetric on the total space. *)
Definition Booij2020Thesis_4_5_14_item_i := @sig_close.
Definition Booij2020Thesis_4_5_14_item_ii := @ispremetric_sig_close.

(* ================================================== 4.5.15 *)
(** Definition 4.5.15 *)

(** Dependent Cauchy approximations. *)
Definition Booij2020Thesis_4_5_15_item_i := @IsDependentCauchyApproximation.
Definition Booij2020Thesis_4_5_15_item_ii := @DependentCauchyApproximation.

(* ================================================== 4.5.16 *)
(** Lemma 4.5.16 *)

(** Pairing a Cauchy approximation [x] with [a] gives a Cauchy approximation in the total space iff [a] is a dependent Cauchy approximation over [x]. *)
Definition Booij2020Thesis_4_5_16 := @iscauchyapproximation_sig_iff.

(* ================================================== 4.5.17 *)
(** Definition 4.5.17 *)

(** Dependent identifications. *)
Definition Booij2020Thesis_4_5_17 := @DPath.

(* ================================================== 4.5.18 *)
(** Theorem 4.5.18 *)

(** The induction principle of the HoTT book reals, derived from initiality via the Cauchy structure on the total space, with its computation rules for [rat] and [lim]; the latter uses [Funext]. *)
Definition Booij2020Thesis_4_5_18_item_i := @sig_cauchy_structure.
Definition Booij2020Thesis_4_5_18_item_ii := @hottbookreals_ind.
Definition Booij2020Thesis_4_5_18_item_iii := @hottbookreals_ind_close.
Definition Booij2020Thesis_4_5_18_item_iv := @hottbookreals_ind_beta_rat.
Definition Booij2020Thesis_4_5_18_item_v := @hottbookreals_ind_beta_lim.
Definition Booij2020Thesis_4_5_18_item_vi := @hottbookreals_ind_hprop.

(* ================================================== 4.6.1 *)
(** Definition 4.6.1 *)

(** Two-sided Dedekind cuts and the Dedekind reals. *)
Definition Booij2020Thesis_4_6_1_item_i := @IsDedekindCut.
Definition Booij2020Thesis_4_6_1_item_ii := @DedekindReals.

(* ================================================== 4.6.2 *)
(** Remark 4.6.2 *)

(** Given the other cut axioms, transitivity of a cut is equivalent to disjointness: no [q] has [x < q] and [q < x]. *)
(* Not formalized: only the direction from transitivity to disjointness is proved, as [cut_disjoint]; the converse needs roundedness and trichotomy of [Q]. *)

(* ================================================== 4.6.3 *)
(** Lemma 4.6.3 *)

(** The Dedekind reals form a set. *)
Definition Booij2020Thesis_4_6_3 := @ishset_dedekindreals.

(* ================================================== 4.6.4 *)
(** Discussion 4.6.4 *)

(** For rationals in a universe [U_i], being a Dedekind cut is a proposition in [U_i], and the Dedekind reals live in [U_(i+1)]. *)
(* Not formalized: a discussion of universe levels. [IsDedekindCut] is a proposition ([ishprop_isdedekindcut]) and [DedekindReals] is universe polymorphic. *)

(* ================================================== 4.6.5 *)
(** Definition 4.6.5 *)

(** The strict order and apartness of the Dedekind reals. *)
Definition Booij2020Thesis_4_6_5_item_i := @lt_dedekindreals.
Definition Booij2020Thesis_4_6_5_item_ii := @apart_dedekindreals.

(* ================================================== 4.6.6 *)
(** Lemma 4.6.6 *)

(** The Dedekind reals are Cauchy complete, with the limit cut given explicitly. *)
Definition Booij2020Thesis_4_6_6_item_i := @limit_dedekind.
Definition Booij2020Thesis_4_6_6_item_ii := @islimit_limit_dedekind.
Definition Booij2020Thesis_4_6_6_item_iii := @iscomplete_dedekindreals.

(* ================================================== 4.6.7 *)
(** Proposition 4.6.7 *)

(** Canonical inclusions of the Cauchy reals into the HoTT book reals and of the HoTT book reals into the Dedekind reals. *)
Definition Booij2020Thesis_4_6_7_item_i := @cauchy_reals_to_hottbookreals.
Definition Booij2020Thesis_4_6_7_item_ii := @hottbookreals_to_field_cauchy_reals.
Definition Booij2020Thesis_4_6_7_item_iii := @isinj_cauchy_reals_to_field.
Definition Booij2020Thesis_4_6_7_item_iv := @isembedding_cauchy_reals_to_hottbookreals.
Definition Booij2020Thesis_4_6_7_item_v := @hottbookreals_to_field.
Definition Booij2020Thesis_4_6_7_item_vi := @isembedding_hottbookreals_to_field.
Definition Booij2020Thesis_4_6_7_item_vii := @hottbookreals_to_dedekind.
Definition Booij2020Thesis_4_6_7_item_viii := @isembedding_hottbookreals_to_dedekind.
Definition Booij2020Thesis_4_6_7_item_ix := @isembedding_cauchy_reals_to_hottbookreals_dedekind.

(* ================================================== 5.1.1 *)
(** Proposition 5.1.1 *)

(** A Cauchy complete subset of a Cauchy complete Archimedean ordered field, such as the Dedekind reals, containing the rationals inherits a Cauchy structure. *)
Definition Booij2020Thesis_5_1_1_item_i := @ContainsRationals.
Definition Booij2020Thesis_5_1_1_item_ii := @IsCauchyCompleteSubset.
Definition Booij2020Thesis_5_1_1_item_iii := @subset_close.
Definition Booij2020Thesis_5_1_1_item_iv := @subset_cauchy_structure.

(* ================================================== 5.1.2 *)
(** Corollary 5.1.2 *)

(** The inclusion of such a subset is a morphism of Cauchy structures. *)
Definition Booij2020Thesis_5_1_2 := @cshom_subset_pr1.

(* ================================================== 5.1.3 *)
(** Proposition 5.1.3 *)

(** The HoTT book reals are contained in every such subset, compatibly with their canonical embedding. *)
Definition Booij2020Thesis_5_1_3_item_i := @hottbookreals_to_subset.
Definition Booij2020Thesis_5_1_3_item_ii := @hottbookreals_to_subset_pr1.
Definition Booij2020Thesis_5_1_3_item_iii := @hottbookreals_to_field_subset.

(* ================================================== 5.1.4 *)
(** Corollary 5.1.4 *)

(** The Cauchy reals are a Cauchy complete subset if and only if they coincide with the HoTT book reals as subsets. *)
Definition Booij2020Thesis_5_1_4_item_i := @subset_cauchy_reals.
Definition Booij2020Thesis_5_1_4_item_ii := @subset_hottbookreals.
Definition Booij2020Thesis_5_1_4_item_iii := @iscauchycompletesubset_hottbookreals.
Definition Booij2020Thesis_5_1_4_item_iv := @iscauchycompletesubset_cauchy_reals_iff.

(* ================================================== 5.1.5 *)
(** Definition 5.1.5 *)

(** Assuming propositional resizing, the Euclidean reals: the meet of the Cauchy complete subsets containing the rationals, here of any Cauchy complete Archimedean ordered field. *)
Definition Booij2020Thesis_5_1_5_item_i := @CompleteSubset.
Definition Booij2020Thesis_5_1_5_item_ii := @euclidean_reals.
Definition Booij2020Thesis_5_1_5_item_iii := @containsrationals_euclidean_reals.
Definition Booij2020Thesis_5_1_5_item_iv := @iscauchycompletesubset_euclidean_reals.
Definition Booij2020Thesis_5_1_5_item_v := @euclidean_reals_least.
Definition Booij2020Thesis_5_1_5_item_vi := @euclidean_reals_cauchy_structure.

(* ================================================== 5.1.6 *)
(** Discussion 5.1.6 *)

(** Without propositional resizing, the meet defining the Euclidean reals lands one universe higher than the subsets it is the meet of. *)
(* Not formalized: a discussion of universe levels; the formalization uses propositional resizing to define the Euclidean reals as a subset in the same universe ([euclidean_reals]). *)

(* ================================================== 5.1.7 *)
(** Theorem 5.1.7 *)

(** Assuming propositional resizing, the Euclidean reals coincide with the HoTT book reals as subsets. *)
Definition Booij2020Thesis_5_1_7 := @euclidean_reals_iff_hottbookreals.

(* ================================================== 5.1.8 *)
(** Theorem 5.1.8 *)

(** Assuming propositional resizing, the unit interval in the Euclidean reals is an interval object. *)
(* Not formalized: needs the interval in the Euclidean reals as a bipointed convex body and a translation of Escardó and Simpson's proof of its initiality. *)

(* ================================================== 5.1.9 *)
(** Corollary 5.1.9 *)

(** Assuming propositional resizing and the HoTT book reals, the unit interval in the HoTT book reals is an interval object. *)
(* Not formalized: follows from Theorem 5.1.8, which is not formalized, and [euclidean_reals_iff_hottbookreals]. *)

(* ================================================== 5.2.1 *)
(** Theorem 5.2.1 *)

(** Assuming propositional resizing, the Euclidean reals are homotopy-initial among Cauchy structures on sets. *)
Definition Booij2020Thesis_5_2_1_item_i := @SubHom.
Definition Booij2020Thesis_5_2_1_item_ii := @unique_subhom_subset.
Definition Booij2020Thesis_5_2_1_item_iii := @unique_subhom_rationals.
Definition Booij2020Thesis_5_2_1_item_iv := @limits_subset.
Definition Booij2020Thesis_5_2_1_item_v := @unique_subhom_limits.
Definition Booij2020Thesis_5_2_1_item_vi := @unique_subhom_sup.
Definition Booij2020Thesis_5_2_1_item_vii := @contr_subhom_euclidean_reals.
Definition Booij2020Thesis_5_2_1_item_viii := @contr_cshom_euclidean_reals.
Definition Booij2020Thesis_5_2_1_item_ix := @limits_subset_incl.
Definition Booij2020Thesis_5_2_1_item_x := @orderpreserving_limits_subset.
Definition Booij2020Thesis_5_2_1_item_xi := @cshom_subhom_euclidean_reals.
Definition Booij2020Thesis_5_2_1_item_xii := @subhom_cshom_euclidean_reals.

(* ================================================== 5.2.2 *)
(** Remark 5.2.2 *)

(** For a Cauchy structure [S] on a set, contractibility of the type of morphisms into [S] means existence of a morphism and pointwise uniqueness. *)
Definition Booij2020Thesis_5_2_2_item_i := @contr_cauchystructurehom_iff.
Definition Booij2020Thesis_5_2_2_item_ii := @path_cauchystructurehom.

(* ================================================== 5.2.3 *)
(** Discussion 5.2.3 *)

(** Without propositional resizing, it is open whether a given least Cauchy complete subset containing the rationals is homotopy-initial, since the subsets no longer form a dcpo. *)
(* Not formalized: a discussion of an open question. *)

(* ================================================== 5.3.1 *)
(** Definition 5.3.1 *)

(** Cancellative midpoint algebras: sets with an idempotent, commutative, medial and cancellative binary operation. *)
Definition Booij2020Thesis_5_3_1_item_i := @Midpoint.
Definition Booij2020Thesis_5_3_1_item_ii := @Medial.
Definition Booij2020Thesis_5_3_1_item_iii := @IsCancellativeMidpointAlgebra.

(* ================================================== 5.3.2 *)
(** Definition 5.3.2 *)

(** Convex bodies: cancellative midpoint algebras with an iteration operator. *)
Definition Booij2020Thesis_5_3_2_item_i := @IsIterationOperator.
Definition Booij2020Thesis_5_3_2_item_ii := @IterationOperator.
Definition Booij2020Thesis_5_3_2_item_iii := @IsConvexBody.

(* ================================================== 5.3.3 *)
(** Lemma 5.3.3 *)

(** Any two iteration operators are equal, so having one is a proposition. *)
Definition Booij2020Thesis_5_3_3_item_i := @path_iteration_operator.
Definition Booij2020Thesis_5_3_3_item_ii := @ishprop_iterationoperator.

(* ================================================== 5.3.4 *)
(** Theorem 5.3.4 *)

(** An iteration operator is equivalently the contractibility, for every sequence [x], of the type of sequences [a] with [a i = m(x i, a i.+1)] for all [i]. *)
Definition Booij2020Thesis_5_3_4 := @equiv_iteration_operator_contr_iterated_midpoints.

(* ================================================== 5.3.5 *)
(** Definition 5.3.5 *)

(** Bipointed convex bodies and their homomorphisms. *)
Definition Booij2020Thesis_5_3_5_item_i := @BipointedConvexBody.
Definition Booij2020Thesis_5_3_5_item_ii := @IsConvexBodyHom.
Definition Booij2020Thesis_5_3_5_item_iii := @ConvexBodyHom.

(* ================================================== 5.3.6 *)
(** Definition 5.3.6 *)

(** Interval objects: homotopy-initial bipointed convex bodies. *)
Definition Booij2020Thesis_5_3_6 := @IsIntervalObject.

(* ================================================== 5.3.7 *)
(** Remark 5.3.7 *)

(** Contractibility of the type of homomorphisms of bipointed convex bodies means existence of a homomorphism and pointwise uniqueness. *)
Definition Booij2020Thesis_5_3_7 := @contr_convexbodyhom_iff.

(* ================================================== 5.4.1 *)
(** Conjecture 5.4.1 *)

(** The interval [[-1, 1]] in the HoTT book reals, with the midpoint operation and the endpoints, is an interval object. *)
(* Conjecture. *)

(* ================================================== 5.4.2 *)
(** Conjecture 5.4.2 *)

(** From an interval object [I], the quotient of [Z * I] identifying overlapping unit intervals carries a Cauchy structure that is homotopy-initial among Cauchy structures on sets. *)
(* Conjecture. *)

(* ================================================== 6.1.1 *)
(** Definition 6.1.1 *)

(** Locators. *)
Definition Booij2020Thesis_6_1_1 := @locator.

(* ================================================== 6.1.3 *)
(** Lemma 6.1.3 *)

(** Assuming excluded middle, every real has a locator. *)
Definition Booij2020Thesis_6_1_3 := @all_reals_locators.

(* ================================================== 6.3.1 *)
(** Lemma 6.3.1 *)

(** A rational [' s] has a locator, in two different ways. *)
Definition Booij2020Thesis_6_3_1_item_i := @locator_left.
Definition Booij2020Thesis_6_3_1_item_ii := @locator_second.
Definition Booij2020Thesis_6_3_1_item_iii := @isembedding_rationals_to_field.

(* ================================================== 6.4.2 *)
(** Lemma 6.4.2 *)

(** A locator is equivalently a decidable [locatesRight] with its two properties. *)
Definition Booij2020Thesis_6_4_2 := @equiv_locator_locator'.

(* ================================================== 6.4.4 *)
(** Definition 6.4.4 *)

(** [locatesRight] and [locatesLeft]. *)
Definition Booij2020Thesis_6_4_4_item_i := @locates_right.
Definition Booij2020Thesis_6_4_4_item_ii := @locates_left.

(* ================================================== 6.4.6 *)
(** Lemma 6.4.6 *)

(** What a locator must locate. *)
Definition Booij2020Thesis_6_4_6_item_i := @nltqx_locates_left.
Definition Booij2020Thesis_6_4_6_item_ii := @nltxr_locates_right.

(* ================================================== 6.5.1 *)
(** Theorem 6.5.1 *)

(** Bounded search: from [exists n, P n] with [P] decidable we get [{n & P n}]. *)
Definition Booij2020Thesis_6_5_1 := @minimal_n.

(* ================================================== 6.5.4 *)
(** Corollary 6.5.4 *)

(** Bounded search over a type equivalent to [nat]. *)
Definition Booij2020Thesis_6_5_4 := @minimal_n_alt_type.

(* ================================================== 6.6.1 *)
(** Lemma 6.6.1 *)

(** A real with a locator has rational bounds. *)
Definition Booij2020Thesis_6_6_1_item_i := @lower_bound.
Definition Booij2020Thesis_6_6_1_item_ii := @upper_bound.

(* ================================================== 6.6.3 *)
(** Lemma 6.6.3 *)

(** A real with a locator has arbitrarily tight rational bounds. *)
Definition Booij2020Thesis_6_6_3 := @tight_bound.

(* ================================================== 6.7.1 *)
(** Lemma 6.7.1 *)

(** Characterizations of [-x], [x + y], [x y], reciprocals, [min] and [max] in terms of the strict order with rationals. *)
Definition Booij2020Thesis_6_7_1_item_i := @char_minus_left.
Definition Booij2020Thesis_6_7_1_item_ii := @char_minus_right.
Definition Booij2020Thesis_6_7_1_item_iii := @char_plus_left.
Definition Booij2020Thesis_6_7_1_item_iv := @char_plus_right.
Definition Booij2020Thesis_6_7_1_item_v := @char_times_left.
Definition Booij2020Thesis_6_7_1_item_vi := @char_times_right.
Definition Booij2020Thesis_6_7_1_item_vii := @char_recip_pos_left.
Definition Booij2020Thesis_6_7_1_item_viii := @char_recip_pos_right.
Definition Booij2020Thesis_6_7_1_item_ix := @char_recip_neg_left.
Definition Booij2020Thesis_6_7_1_item_x := @char_recip_neg_right.
Definition Booij2020Thesis_6_7_1_item_xi := @char_meet_left.
Definition Booij2020Thesis_6_7_1_item_xii := @char_meet_right.
Definition Booij2020Thesis_6_7_1_item_xiii := @char_join_left.
Definition Booij2020Thesis_6_7_1_item_xiv := @char_join_right.

(* ================================================== 6.7.3 *)
(** Lemma 6.7.3 *)

(** For reals with locators, [x < y] gives a rational between them. *)
Definition Booij2020Thesis_6_7_3 := @archimedean_structure.

(* ================================================== 6.7.4 *)
(** Corollary 6.7.4 *)

(** For reals [x < y] with locators and a rational [s], we can choose [x < s] or [s < y]. *)
Definition Booij2020Thesis_6_7_4 := @locator_cotransitive_rational.

(* ================================================== 6.7.5 *)
(** Remark 6.7.5 *)

(** Strong cotransitivity: for reals [x < y] with locators and a real [z] with a locator, we can choose [x < z] or [z < y]. *)
Definition Booij2020Thesis_6_7_5 := @locator_cotransitive.

(* ================================================== 6.7.6 *)
(** Theorem 6.7.6 *)

(** If [x] and [y] have locators, then so do [-x], [x + y], [x y], [x⁻¹] (for [x # 0]), [min(x, y)] and [max(x, y)]. *)
Definition Booij2020Thesis_6_7_6_item_i := @locator_minus.
Definition Booij2020Thesis_6_7_6_item_ii := @locator_plus.
Definition Booij2020Thesis_6_7_6_item_iii := @locator_times.
Definition Booij2020Thesis_6_7_6_item_iv := @locator_recip.
Definition Booij2020Thesis_6_7_6_item_v := @locator_meet.
Definition Booij2020Thesis_6_7_6_item_vi := @locator_join.

(* ================================================== 6.7.7 *)
(** Remark 6.7.7 *)

(** The absolute value [max(x, -x)] of a real with a locator has a locator. *)
Definition Booij2020Thesis_6_7_7_item_i := @locator_join.
Definition Booij2020Thesis_6_7_7_item_ii := @locator_minus.

(* ================================================== 6.8.1 *)
(** Lemma 6.8.1 *)

(** A limit of a sequence with modulus whose terms have locators has a locator. *)
Definition Booij2020Thesis_6_8_1 := @locator_limit.

(* ================================================== 6.9.2 *)
(** Definition 6.9.2 *)

(** Signed-digit representations: an integer and a sequence of signed digits whose partial sums converge to the given real. *)
Definition Booij2020Thesis_6_9_2_item_i := @digit_weight.
Definition Booij2020Thesis_6_9_2_item_ii := @digit_sum.
Definition Booij2020Thesis_6_9_2_item_iii := @SignedDigits.

(* ================================================== 6.9.4 *)
(** Lemma 6.9.4 *)

(** A real with a locator lies within distance [1] of an integer, which we can find using an integer part of rationals. *)
Definition Booij2020Thesis_6_9_4_item_i := @integer_floor.
Definition Booij2020Thesis_6_9_4_item_ii := @integer_bound.

(* ================================================== 6.9.5 *)
(** Theorem 6.9.5 *)

(** Locators and signed-digit representations are interdefinable. *)
Definition Booij2020Thesis_6_9_5_item_i := @locator_signed_digits.
Definition Booij2020Thesis_6_9_5_item_ii := @signed_digits_locator.

(* ================================================== 6.9.6 *)
(** Definition 6.9.6 *)

(** Cauchy reals in a Cauchy complete Archimedean ordered field: the elements merely in the image of the canonical map from the Cauchy reals. *)
Definition Booij2020Thesis_6_9_6_item_i := @cauchy_reals_to_field.
Definition Booij2020Thesis_6_9_6_item_ii := @rationals_to_cauchy_reals.
Definition Booij2020Thesis_6_9_6_item_iii := @cauchy_reals_to_field_rationals.
Definition Booij2020Thesis_6_9_6_item_iv := @IsCauchyReal.
Definition Booij2020Thesis_6_9_6_item_v := @iscauchyreal_iff_limit.

(* ================================================== 6.9.7 *)
(** Theorem 6.9.7 *)

(** Merely having a locator, merely having a signed-digit representation, merely being the limit of a rational sequence with a modulus, and being a Cauchy real are equivalent. *)
Definition Booij2020Thesis_6_9_7_item_i := @merely_locator_iff_signed_digits.
Definition Booij2020Thesis_6_9_7_item_ii := @merely_locator_iff_limit.
Definition Booij2020Thesis_6_9_7_item_iii := @iscauchyreal_iff_limit.
Definition Booij2020Thesis_6_9_7_item_iv := @cauchy_sequence_signed_digits.
Definition Booij2020Thesis_6_9_7_item_v := @locator_cauchy_sequence.

(* ================================================== 6.9.8 *)
(** Remark 6.9.8 *)

(** A locator can be truncated as a whole, pointwise, or in its values. *)
Definition Booij2020Thesis_6_9_8_item_i := @merely_locator_pointwise.
Definition Booij2020Thesis_6_9_8_item_ii := @pointwise_locator_iff_located.
Definition Booij2020Thesis_6_9_8_item_iii := @O_decidable_arrow.
Definition Booij2020Thesis_6_9_8_item_iv := @cotransitive.

(* ================================================== 6.9.9 *)
(** Corollary 6.9.9 *)

(** Every Dedekind real merely has a signed-digit representation if and only if the Cauchy reals and the Dedekind reals coincide. *)
Definition Booij2020Thesis_6_9_9_item_i := @signed_digits_iff_isequiv_cauchy_reals_to_dedekind.
Definition Booij2020Thesis_6_9_9_item_ii := @isequiv_cauchy_reals_to_dedekind_iff.

(* ================================================== 6.10.1 *)
(** Lemma 6.10.1 *)

(** A choice of locators for all reals gives a strongly nonconstant map to [Bool], by deciding [0 < x] or [x < 1]. *)
Definition Booij2020Thesis_6_10_1_item_i := @IsStronglyNonconstant.
Definition Booij2020Thesis_6_10_1_item_ii := @locator_choice_bool.
Definition Booij2020Thesis_6_10_1_item_iii := @isstronglynonconstant_locator_choice_bool.

(* ================================================== 6.10.2 *)
(** Lemma 6.10.2 *)

(** A strongly nonconstant map from a Cauchy complete Archimedean ordered field to [Bool] implies the weak limited principle of omniscience (Definition 2.8.4). *)
Definition Booij2020Thesis_6_10_2_item_i := @WLPO.
Definition Booij2020Thesis_6_10_2_item_ii := @iff_wlpo_ispicompact_nat.
Definition Booij2020Thesis_6_10_2_item_iii := @wlpo_bisection.
Definition Booij2020Thesis_6_10_2_item_iv := @wlpo_nonconstant.
Definition Booij2020Thesis_6_10_2_item_v := @wlpo_isstronglynonconstant.
Definition Booij2020Thesis_6_10_2_item_vi := @wlpo_locator_choice.

(* ================================================== 6.10.3 *)
(** Theorem 6.10.3 *)

(** The property [IsCut] and the structure [CutStructure] of a pair of predicates on the rationals, and how they relate via locators. *)
Definition Booij2020Thesis_6_10_3_item_i := @BoundedLower.
Definition Booij2020Thesis_6_10_3_item_ii := @BoundedUpper.
Definition Booij2020Thesis_6_10_3_item_iii := @ClosedLower.
Definition Booij2020Thesis_6_10_3_item_iv := @ClosedUpper.
Definition Booij2020Thesis_6_10_3_item_v := @OpenLower.
Definition Booij2020Thesis_6_10_3_item_vi := @OpenUpper.
Definition Booij2020Thesis_6_10_3_item_vii := @CutTransitive.
Definition Booij2020Thesis_6_10_3_item_viii := @CutLocated.
Definition Booij2020Thesis_6_10_3_item_ix := @LowerBound.
Definition Booij2020Thesis_6_10_3_item_x := @UpperBound.
Definition Booij2020Thesis_6_10_3_item_xi := @LowerRounding.
Definition Booij2020Thesis_6_10_3_item_xii := @UpperRounding.
Definition Booij2020Thesis_6_10_3_item_xiii := @CutLocator.
Definition Booij2020Thesis_6_10_3_item_xiv := @IsCut.
Definition Booij2020Thesis_6_10_3_item_xv := @CutStructure.
Definition Booij2020Thesis_6_10_3_item_xvi := @iscut_iff_isdedekindcut.
Definition Booij2020Thesis_6_10_3_item_xvii := @iscut_cutstructure.
Definition Booij2020Thesis_6_10_3_item_xviii := @iscut_merely_cutstructure.
Definition Booij2020Thesis_6_10_3_item_xix := @cut_locator_iff_locator.
Definition Booij2020Thesis_6_10_3_item_xx := @lower_bound_cut_locator.
Definition Booij2020Thesis_6_10_3_item_xxi := @upper_bound_cut_locator.
Definition Booij2020Thesis_6_10_3_item_xxii := @lower_rounding_cut_locator.
Definition Booij2020Thesis_6_10_3_item_xxiii := @upper_rounding_cut_locator.
Definition Booij2020Thesis_6_10_3_item_xxiv := @cutstructure_iscut_locator.
Definition Booij2020Thesis_6_10_3_item_xxv := @iscauchyreal_iscut_merely_locator.
Definition Booij2020Thesis_6_10_3_item_xxvi := @iscauchyreal_merely_cutstructure.

(* ================================================== 6.10.5 *)
(** Theorem 6.10.5 *)

(** It is not provable that every cut merely has the structure of a cut. *)
Definition Booij2020Thesis_6_10_5_item_i := @iscauchyreal_all_merely_cutstructure.
Definition Booij2020Thesis_6_10_5_item_ii := @isequiv_cauchy_reals_to_dedekind_iff.

(* ================================================== 7.1.1 *)
(** Definition 7.1.1 *)

(** A function lifts to locators if it is equipped with a map from locators for [x] to locators for [f x]. *)
Definition Booij2020Thesis_7_1_1 := @LiftsToLocators.

(* ================================================== 7.1.2 *)
(** Remark 7.1.2 *)

(** A lifting to locators does not determine the function, since not every real has a locator. *)
(* Not formalized: a metatheoretic remark. *)

(* ================================================== 7.1.3 *)
(** Example 7.1.3 *)

(** The exponential function lifts to locators. *)
(* Not formalized: an example; needs the exponential function. *)

(* ================================================== 7.1.4 *)
(** Definition 7.1.4 *)

(** Continuity at a point, and pointwise continuity. *)
Definition Booij2020Thesis_7_1_4_item_i := @IsContinuousAt.
Definition Booij2020Thesis_7_1_4_item_ii := @IsPointwiseContinuous.

(* ================================================== 7.1.5 *)
(** Definition 7.1.5 *)

(** A modulus of uniform continuity on an interval [[a, b]]: a modulus of uniform continuity for the restriction to the interval. *)
Definition Booij2020Thesis_7_1_5 := @UniformModulusOn.

(* ================================================== 7.1.6 *)
(** Example 7.1.6 *)

(** The exponential function has a modulus of uniform continuity on every [[a, b]], which can be computed when [a] and [b] have locators. *)
(* Not formalized: an example; needs the exponential function. *)

(* ================================================== 7.1.7 *)
(** Lemma 7.1.7 *)

(** If all constant functions lift to locators, then every element has a locator. *)
Definition Booij2020Thesis_7_1_7 := @locator_lifts_constant.

(* ================================================== 7.1.8 *)
(** Lemma 7.1.8 *)

(** Assuming excluded middle, a function which is not continuous lifts to locators. *)
Definition Booij2020Thesis_7_1_8_item_i := @step_function.
Definition Booij2020Thesis_7_1_8_item_ii := @lifts_step_function.
Definition Booij2020Thesis_7_1_8_item_iii := @not_iscontinuousat_step_function.

(* ================================================== 7.2.1 *)
(** Theorem 7.2.1 *)

(** The integral over [[a, b]] of a function with a modulus of uniform continuity on [[a, b]] that lifts to locators has a locator, if [a] and [b] do. The integral is any integration operator ([Integration]); no such operator is constructed yet. *)
Definition Booij2020Thesis_7_2_1_item_i := @Integration.
Definition Booij2020Thesis_7_2_1_item_ii := @integral_unique.
Definition Booij2020Thesis_7_2_1_item_iii := @riemann_sum.
Definition Booij2020Thesis_7_2_1_item_iv := @cauchymodulus_riemann_sum.
Definition Booij2020Thesis_7_2_1_item_v := @islimit_riemann_sum.
Definition Booij2020Thesis_7_2_1_item_vi := @locator_integral_lifts.
Definition Booij2020Thesis_7_2_1_item_vii := @locator_integral.

(* ================================================== 7.2.2 *)
(** Remark 7.2.2 *)

(** Integrals can be defined from the mere existence of a modulus of uniform continuity; the modulus itself is needed only for a locator. *)
(* Not formalized: the integral is not constructed; the integration operators of [Integration] take only mere uniform continuity ([IsUniformlyContinuous]), while [locator_integral] uses a chosen modulus. *)

(* ================================================== 7.2.3 *)
(** Example 7.2.3 *)

(** The integral of [sin (x + exp x)] from [0] to [8] has a locator. *)
(* Not formalized: an example; needs sin and exp. *)

(* ================================================== 7.3.1 *)
(** Theorem 7.3.1 *)

(** Approximate intermediate value theorem. The plain version merely gives some [x] with [|f x| < e]: the limit of the bisection need not work, contrary to the statement in the thesis. *)
Definition Booij2020Thesis_7_3_1_item_i := @approximate_ivt.
Definition Booij2020Thesis_7_3_1_item_ii := @approximate_ivt_locator.

(* ================================================== 7.3.2 *)
(** Definition 7.3.2 *)

(** Locally nonconstant functions. *)
Definition Booij2020Thesis_7_3_2 := @IsLocallyNonconstant.

(* ================================================== 7.3.3 *)
(** Example 7.3.3 *)

(** Every strictly monotone function is locally nonconstant, but not conversely. *)
(* Not formalized: an example. *)

(* ================================================== 7.3.4 *)
(** Lemma 7.3.4 *)

(** For a continuous, locally nonconstant function which lifts to locators, and [x < y] and [t] with locators, we can find a rational [r] with [x < r < y] and [f r] apart from [t]. *)
Definition Booij2020Thesis_7_3_4 := @locally_nonconstant_rational.

(* ================================================== 7.3.5 *)
(** Theorem 7.3.5 *)

(** Exact intermediate value theorem: a continuous, locally nonconstant function which lifts to locators, with [f a ≤ 0 ≤ f b] for [a < b] with locators, has a root in [[a, b]] with a locator. *)
Definition Booij2020Thesis_7_3_5 := @exact_ivt.

(* ================================================== 7.3.6 *)
(** Remark 7.3.6 *)

(** The exact intermediate value theorem only needs that the function is locally nonzero. *)
(* Not formalized: [exact_ivt] assumes [IsLocallyNonconstant]; the proof only uses it for [t = 0]. *)

(* ================================================== 7.3.7 *)
(** Example 7.3.7 *)

(** For [y > 0] with a locator, [exp x = y] has a solution with a locator. *)
(* Not formalized: an example; needs the exponential function. *)

(* ================================================== 8.0.1 *)
(** Remark 8.0.1 *)

(** Pseudometric spaces are distinct from premetric spaces. *)
(* Not formalized: a remark on terminology. *)

(* ================================================== 8.1.1 *)
(** Definition 8.1.1 *)

(** Pseudometrics and metrics, with values in the nonnegative elements of an ordered field. *)
Definition Booij2020Thesis_8_1_1_item_i := @IsPseudoMetric.
Definition Booij2020Thesis_8_1_1_item_ii := @IsMetric.

(* ================================================== 8.1.2 *)
(** Remark 8.1.2 *)

(** The condition [ρ (x, x) = 0] is equivalent to [x = y -> ρ (x, y) = 0]. *)
(* Not formalized: a trivial reformulation of [pseudometric_diag]. *)

(* ================================================== 8.1.3 *)
(** Lemma 8.1.3 *)

(** The Euclidean distance [|x - y|] is a metric. *)
Definition Booij2020Thesis_8_1_3 := @ismetric_abs_minus.

(* ================================================== 8.1.4 *)
(** Example 8.1.4 *)

(** Uniformly continuous functions [[a, b] -> [c, d]] that lift to locators form a pseudometric space. *)
(* Not formalized: an example; it points to Definition 8.2.7 and Corollary 8.2.8. *)

(* ================================================== 8.1.5 *)
(** Lemma 8.1.5 *)

(** Two limits of a sequence in a pseudometric space have distance zero; in a metric space limits are unique. *)
Definition Booij2020Thesis_8_1_5_item_i := @metric_close.
Definition Booij2020Thesis_8_1_5_item_ii := @MetricCauchyModulus.
Definition Booij2020Thesis_8_1_5_item_iii := @IsMetricLimit.
Definition Booij2020Thesis_8_1_5_item_iv := @metric_limit_distance_zero.
Definition Booij2020Thesis_8_1_5_item_v := @metric_limit_unique.

(* ================================================== 8.1.6 *)
(** Definition 8.1.6 *)

(** Cauchy completeness: a limit operator for sequences with a modulus of Cauchy convergence. *)
Definition Booij2020Thesis_8_1_6 := @MetricCauchyComplete.

(* ================================================== 8.1.7 *)
(** Definition 8.1.7 *)

(** Moduli of uniform continuity, with the identity and composition. *)
Definition Booij2020Thesis_8_1_7_item_i := @IsUniformModulus.
Definition Booij2020Thesis_8_1_7_item_ii := @isuniformmodulus_idmap.
Definition Booij2020Thesis_8_1_7_item_iii := @isuniformmodulus_compose.

(* ================================================== 8.1.8 *)
(** Lemma 8.1.8 *)

(** A uniformly continuous map with modulus [w] sends a sequence with modulus [M] to one with modulus [M o w]. *)
Definition Booij2020Thesis_8_1_8 := @metriccauchymodulus_uniform.

(* ================================================== 8.1.9 *)
(** Definition 8.1.9 *)

(** Maps preserving limits. *)
Definition Booij2020Thesis_8_1_9 := @PreservesMetricLimits.

(* ================================================== 8.1.10 *)
(** Lemma 8.1.10 *)

(** Uniformly continuous maps preserve limits. *)
Definition Booij2020Thesis_8_1_10 := @preservesmetriclimits_uniform.

(* ================================================== 8.2.1 *)
(** Definition 8.2.1 *)

(** The type [U[a,b][c,d]] of maps [[a, b] -> [c, d]] with a modulus of uniform continuity, where closed intervals carry the distance [|x - y|]. *)
Definition Booij2020Thesis_8_2_1_item_i := @ClosedInterval.
Definition Booij2020Thesis_8_2_1_item_ii := @interval_dist.
Definition Booij2020Thesis_8_2_1_item_iii := @UniformMap.

(* ================================================== 8.2.2 *)
(** Lemma 8.2.2 *)

(** The supremum of a uniformly continuous [f : [a, b] -> F] is the limit of the maxima of [f] at [n + 2] equidistant points; for a rational bound [B] on [b - a] these have the modulus of Cauchy convergence [B / w e]. *)
Definition Booij2020Thesis_8_2_2_item_i := @sample_max.
Definition Booij2020Thesis_8_2_2_item_ii := @grid_modulus.
Definition Booij2020Thesis_8_2_2_item_iii := @cauchymodulus_sample_max.
Definition Booij2020Thesis_8_2_2_item_iv := @issupremum_limit_sample_max.
Definition Booij2020Thesis_8_2_2_item_v := @supremum.
Definition Booij2020Thesis_8_2_2_item_vi := @issupremum_supremum.

(* ================================================== 8.2.3 *)
(** Lemma 8.2.3 *)

(** [U[a,b][c,d]] is a pseudometric space with the supremum distance. *)
Definition Booij2020Thesis_8_2_3_item_i := @uniform_dist.
Definition Booij2020Thesis_8_2_3_item_ii := @ispseudometric_uniform_dist.

(* ================================================== 8.2.4 *)
(** Definition 8.2.4 *)

(** Maps on a closed interval that lift to locators. *)
Definition Booij2020Thesis_8_2_4 := @IntervalLiftsToLocators.

(* ================================================== 8.2.5 *)
(** Remark 8.2.5 *)

(** Lifting to locators on a closed interval is structure, and a map of intervals with locators does not determine the function. *)
(* Not formalized: a metatheoretic remark. *)

(* ================================================== 8.2.6 *)
(** Lemma 8.2.6 *)

(** A map into a pseudometric space induces a pseudometric on its domain. *)
Definition Booij2020Thesis_8_2_6 := @ispseudometric_pullback.

(* ================================================== 8.2.7 *)
(** Definition 8.2.7 *)

(** The type [UL[a,b][c,d]] of uniformly continuous maps that lift to locators. *)
Definition Booij2020Thesis_8_2_7 := @UniformLocatorMap.

(* ================================================== 8.2.8 *)
(** Corollary 8.2.8 *)

(** [UL[a,b][c,d]] is a pseudometric space with the distance of [U[a,b][c,d]]. *)
Definition Booij2020Thesis_8_2_8_item_i := @ulmap_dist.
Definition Booij2020Thesis_8_2_8_item_ii := @ispseudometric_ulmap_dist.

(* ================================================== 8.2.9 *)
(** Lemma 8.2.9 *)

(** Elements at distance zero have equal underlying maps. *)
Definition Booij2020Thesis_8_2_9 := @path_uniform_dist_zero.

(* ================================================== 8.2.10 *)
(** Lemma 8.2.10 *)

(** [UL[a,b][c,d]] is Cauchy complete. *)
Definition Booij2020Thesis_8_2_10 := @metriccauchycomplete_ulmap_dist.

(* ================================================== 8.3.1 *)
(** Definition 8.3.1 *)

(** Lipschitz constants. *)
Definition Booij2020Thesis_8_3_1 := @IsLipschitz.

(* ================================================== 8.3.2 *)
(** Lemma 8.3.2 *)

(** A positive rational Lipschitz constant [c] gives the modulus of uniform continuity [e / c]. *)
Definition Booij2020Thesis_8_3_2 := @isuniformmodulus_lipschitz.

(* ================================================== 8.3.3 *)
(** Corollary 8.3.3 *)

(** A positive Lipschitz constant in the ordered field merely gives a modulus of uniform continuity. *)
Definition Booij2020Thesis_8_3_3 := @merely_isuniformmodulus_lipschitz.

(* ================================================== 8.3.4 *)
(** Lemma 8.3.4 *)

(** For a Lipschitz constant [c < 1], pseudo-fixed points are unique up to distance zero. *)
Definition Booij2020Thesis_8_3_4 := @pseudo_fixed_point_unique.

(* ================================================== 8.3.5 *)
(** Corollary 8.3.5 *)

(** In a metric space, for a Lipschitz constant [c < 1], the type of fixed points is a proposition. *)
Definition Booij2020Thesis_8_3_5 := @ishprop_fixed_point.

(* ================================================== 8.3.6 *)
(** Remark 8.3.6 *)

(** It suffices that such a Lipschitz constant merely exists. *)
Definition Booij2020Thesis_8_3_6 := @ishprop_fixed_point_merely.

(* ================================================== 8.3.7 *)
(** Lemma 8.3.7 *)

(** For a rational [0 < c < 1], a logarithm-like function giving for each positive rational [q] an exponent [n] with [c^n < q]. *)
Definition Booij2020Thesis_8_3_7 := @rational_log.

(* ================================================== 8.3.8 *)
(** Lemma 8.3.8 *)

(** For a rational Lipschitz constant [0 < c < 1] and [d (T x0) x0 ≤ C], the iterates of [T] at [x0] have the modulus of Cauchy convergence [log_c (e (1 - c) / C)]. *)
Definition Booij2020Thesis_8_3_8_item_i := @iterates_modulus.
Definition Booij2020Thesis_8_3_8_item_ii := @metriccauchymodulus_iterates.

(* ================================================== 8.3.9 *)
(** Remark 8.3.9 *)

(** Instead of [ρ (T x0, x0) ≤ C], one normally assumes that the space is bounded by [C]. *)
(* Not formalized: a remark; [banach_fixed_point] assumes only [d (T x0) x0 ≤ C], which follows from such a bound. *)

(* ================================================== 8.3.10 *)
(** Remark 8.3.10 *)

(** With a real Lipschitz constant [0 < c < 1] or a real bound, a modulus of Cauchy convergence of the iterates merely exists; with locators for them, one can be computed. *)
(* Not formalized: a remark; the formalization uses rational constants and bounds throughout. *)

(* ================================================== 8.3.11 *)
(** Theorem 8.3.11 *)

(** Banach's fixed point theorem: in a Cauchy complete pseudometric space, a map with a rational Lipschitz constant [0 < c < 1] has a pseudo-fixed point, unique up to distance zero. *)
Definition Booij2020Thesis_8_3_11 := @banach_fixed_point.

(* ================================================== 8.4.1 *)
(** Definition 8.4.1 *)

(** Products of pseudometric spaces, with the sum of the distances; a product of metrics is a metric. *)
Definition Booij2020Thesis_8_4_1_item_i := @prod_dist.
Definition Booij2020Thesis_8_4_1_item_ii := @ispseudometric_prod.
Definition Booij2020Thesis_8_4_1_item_iii := @ismetric_prod.

(* ================================================== 8.4.2 *)
(** Remark 8.4.2 *)

(** The product metric on [R^2] is the taxicab metric. *)
(* Not formalized: a remark on terminology. *)

(* ================================================== 8.4.3 *)
(** Lemma 8.4.3 *)

(** A product of uniformly continuous maps has the minimum of the moduli at [e / 2] as modulus. Only binary products are formalized. *)
Definition Booij2020Thesis_8_4_3_item_i := @qpos_min.
Definition Booij2020Thesis_8_4_3_item_ii := @isuniformmodulus_prod.

(* ================================================== 8.4.4 *)
(** Lemma 8.4.4 *)

(** The diagonal [X -> X * X] has modulus [e / 2]. Only the binary diagonal is formalized. *)
Definition Booij2020Thesis_8_4_4 := @isuniformmodulus_diagonal.

(* ================================================== 8.4.5 *)
(** Corollary 8.4.5 *)

(** If [f] has modulus [w] and [g] on [X * Y] has modulus [v], then [fun x => g (x, f x)] has modulus [min (v e / 2) (w (v e / 2)) / 2]. *)
Definition Booij2020Thesis_8_4_5 := @isuniformmodulus_graph.

(* ================================================== 8.4.6 *)
(** Definition 8.4.6 *)

(** Maps on a product of closed intervals that lift to locators. *)
Definition Booij2020Thesis_8_4_6 := @ProductLiftsToLocators.

(* ================================================== 8.4.7 *)
(** Theorem 8.4.7 *)

(** Picard–Lindelöf theorem, for any integration operator ([Integration]). *)
Definition Booij2020Thesis_8_4_7_item_i := @picard_lindelof.
Definition Booij2020Thesis_8_4_7_item_ii := @picard_map.
Definition Booij2020Thesis_8_4_7_item_iii := @islipschitz_picard_map.

