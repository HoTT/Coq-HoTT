(** * Index of Booij's thesis *)

(** This file lists, in thesis order, the numbered items of Chapters 3–8 of A. B. Booij, _Analysis in Univalent Type Theory_ (PhD thesis, University of Birmingham, 2020) that have been formalized, each as a [Check] of the results that formalize it. It defines nothing; it fails to build if a listed result is renamed or removed. See [BLUEPRINT.md] for the plan and for the items that are not formalized yet. *)

From HoTT Require Import Basics.Overture Basics.Classes.
From HoTT.Classes.interfaces Require Import canonical_names orders archimedean cauchy.
From HoTT.Cubical Require Import DPath.
From HoTT.Misc Require Import BoundedSearch.
From HoTT.Classes.orders Require Import archimedean.
From HoTT.Analysis Require Import Locator.

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

(** ** Chapter 4: Real numbers *)

(** Definition 4.1.8. Lattices. *)
Check LatticeOrder.

(** Lemma 4.1.12. An ordered field is a constructive field. *)
Check @ordered_field_field.

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
