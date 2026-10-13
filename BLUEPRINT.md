# Blueprint: Booij, *Analysis in Univalent Type Theory*, Chapters 3–8

This file plans the formalization of Chapters 3–8 of A. B. Booij, *Analysis in Univalent Type Theory* (PhD thesis, University of Birmingham, 2020; `Booij2020PhD.pdf`) in Coq-HoTT, next to `theories/Analysis/Locator.v`. Conventions for the work itself are in `CLAUDE.md`.

## How to read this file

- **ID** is the thesis number. Every numbered definition, lemma, theorem, proposition, corollary and conjecture in Chapters 3–8 has a row. Numbered examples are listed too and marked *optional*, since some carry constructions (e.g. the exponential) that later results mention. Remarks with formal content are collected at the end.
- **Depends on** lists the thesis items used in the statement or the proof. Items from Chapter 2 are mapped to Coq-HoTT in the first table. *U-n* refers to the unnumbered prerequisites at the end, which the thesis assumes without stating them as numbered results.
- **Target** is the file below `theories/` and the name the result gets there, following the naming rule in `CLAUDE.md` (`def_6_1_1`, `lem_6_6_1`, …). When Coq-HoTT already has the result in the right form, the target is that existing name and no new definition should be added.
- **Status** is `todo` for every entry at the time of writing. Use `stated` once the statement typechecks (in a file marked `(* STUB *)`), and `proved` once it is proved without `Admitted`.
- **Coq-HoTT has** says what existed when this blueprint was written, with file (below `theories/`) and name, and how it differs from the thesis. Check the names before relying on them (see `CLAUDE.md`).

Throughout Chapters 6–8 the thesis works with an arbitrary Cauchy complete Archimedean ordered field R. In Coq-HoTT this is the `Context` of `Analysis/Locator.v`: rationals `Q` with `Rationals Q`, a field `F` with `OrderedField F`, `ArchimedeanProperty Q F` and `IsComplete Q F`, together with assumptions still marked TODO there (`StrictlyOrderPreserving qinc`, `IsSemiRingStrongPreserving qinc`, enumerations `Q_eq : nat <~> Q` and `QQpos_eq : nat <~> Q * Qpos Q`). Removing the TODO assumptions is part of Lemma 4.3.3 below.

## Known problems in the existing code

These are not thesis items, but they affect the rows below.

- **Unproved hypotheses.** `locator_plus` takes the characterizations `char_plus_left` and `char_plus_right` as `Context` hypotheses. In `Classes/orders/archimedean.v` these and the other characterizations of Lemma 6.7.1 are stated and then `Abort`ed (only `char_minus_left` and `char_minus_right` are proved). `locator_times` is `Abort`ed.
- **Order preservation of Q → F is assumed.** `Classes/interfaces/cauchy.v` and `Analysis/Locator.v` take `IsSemiRingStrongPreserving qinc` and `StrictlyOrderPreserving qinc` as context (marked TODO); see Lemma 4.3.3.

## Chapter 2 prerequisites

These are used throughout and already exist.

| Thesis | Concept | Coq-HoTT |
|---|---|---|
| 2.4.1, 2.4.3 | propositions, propositional truncation | `IsHProp`, `HProp` (Basics/Overture.v, Basics/Trunc.v); `merely`, `Trunc_rec`, `Trunc_ind`, `tr` (Truncations/Core.v) |
| 2.4.5 | univalent logic ∃, ∨ | `hexists`, `hor` (Truncations/Core.v) |
| 2.4.9 | decidable propositions DHProp | `DHProp`, `Build_DHProp`, `dhand`, `dhor` (Universes/DProp.v); `Decidable` (Basics/Decidable.v) |
| 2.5.4, 2.5.5 | sets, contractible types | `IsHSet`, `Contr` (Basics/Overture.v) |
| 2.5.18, 2.5.1 | univalence, function extensionality | `Univalence`, `Funext`, `path_forall` (Basics/Overture.v) |
| 2.6.1–2.6.3 | subtypes, embeddings | predicates `A -> HProp`; `IsEmbedding` (Basics/Trunc.v); `path_sigma_hprop`, `equiv_path_sigma_hprop` (Types/Sigma.v) |
| 2.6.13 | propositional resizing | `PropResizing`, `issmall_hprop`, `smalltype`, `equiv_smalltype` (Basics/Overture.v) |
| 2.6.8, 2.6.12, 2.6.15 | joins and meets of subsets | none; power types `power_type` (Sets/Powers.v) only |
| 2.6.20 | a type is a proposition iff all its elements are equal | `hprop_allpath` (Basics/Trunc.v), `equiv_hprop_allpath` (Universes/HProp.v) |
| 2.7.2 | set quotients | `Quotient`, `class_of`, `qglue`, `Quotient_ind` (Colimits/Quotient.v) |
| 2.8.2 | excluded middle | `ExcludedMiddle`, `LEM` (ExcludedMiddle.v) |
| 2.8.4 | LPO, WLPO | none (see Lemma 6.10.2) |
| 2.8.6 | choice | `Choice`, `AC` (Sets/AC.v) |
| 4.2 (unnumbered) | rationals, Q+ | `Rationals` (Classes/interfaces/rationals.v); `Qpos`, `Qpos_diff`, `Q_dense`, `pos_of_Q` (Classes/theory/rationals.v) |

## Target files

All new files live in `theories/Analysis/` and get added to `theories/HoTT.v` once they contain no `(* STUB *)` marker.

| File | Contents |
|---|---|
| `Analysis/Dcpo.v` | Chapter 3 |
| `Analysis/OrderedField.v` | §4.1, §4.3 |
| `Analysis/CauchyCompleteness.v` | §4.4 except the Cauchy reals |
| `Analysis/CauchyReals.v` | Definition 4.4.9 |
| `Analysis/CauchyStructure.v` | §4.5 up to Corollary 4.5.11 |
| `Analysis/HoTTBookReals.v` | §4.5 from Definition 4.5.12 |
| `Analysis/DedekindReals.v` | §4.6 except Proposition 4.6.7 |
| `Analysis/RealsInclusions.v` | Proposition 4.6.7, §5.1.1 |
| `Analysis/EuclideanReals.v` | §5.1.2, §5.2 |
| `Analysis/IntervalObject.v` | §5.3, §5.4 |
| `Analysis/Locator.v` (existing) | §6.1–§6.8 |
| `Analysis/LocatorDigits.v` | §6.9 |
| `Analysis/LocatorCuts.v` | §6.10 |
| `Analysis/LiftsToLocators.v` | §7.1 |
| `Analysis/Integral.v` | §7.2 |
| `Analysis/IntermediateValue.v` | §7.3 |
| `Analysis/MetricSpace.v` | §8.1 |
| `Analysis/FunctionSpace.v` | §8.2 |
| `Analysis/BanachFixedPoint.v` | §8.3 |
| `Analysis/PicardLindelof.v` | §8.4 |

## Chapter 3: Fixpoints in dcpos

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 3.1.1 | A relation is reflexive, irreflexive, symmetric, antisymmetric, transitive, cotransitive. | 2.4.5 | existing names | todo | `Reflexive`, `Symmetric`, `Transitive`, `Irreflexive` (Basics/Overture.v); `AntiSymmetric` (Basics/Classes.v); `CoTransitive` (Classes/interfaces/canonical_names.v, with `hor`). Complete. |
| Def 3.1.3 | Preorder; partial order. | 3.1.1 | existing names | todo | `PreOrder` (Basics/Overture.v); `PartialOrder` (Classes/interfaces/orders.v, also asks for `IsHSet` and HProp-valued `≤`). Complete. |
| Def 3.1.4 | Inflationary endomap; semidirected, directed subset; (i-)dcpo; (i-)subdcpo. | 3.1.3, 2.6.1, 2.4.5 | `Analysis/Dcpo.v` · `def_3_1_4_inflationary`, `def_3_1_4_semidirected`, `def_3_1_4_directed`, `def_3_1_4_dcpo`, `def_3_1_4_subdcpo` | todo | None. Universe levels (items 6, 7) come from universe polymorphism: subsets `A -> HProp@{i}`. |
| Lem 3.1.5 | An i-subdcpo B of an i-dcpo A gives an i-dcpo on Σ b, b ∈ B. | 3.1.4 | `Analysis/Dcpo.v` · `lem_3_1_5` | todo | None. |
| Lem 3.1.6 | For A : U_i and an i-dcpo B, A → B with the pointwise order is an i-dcpo. | 3.1.4, 2.6.5, Funext | `Analysis/Dcpo.v` · `lem_3_1_6` | todo | None. |
| Lem 3.1.7 | With propositional resizing, P_i A is an (i+1)-dcpo under ⊆. | 3.1.4, 2.6.8, 2.6.15, 2.6.13 | `Analysis/Dcpo.v` · `lem_3_1_7` | todo | `PropResizing`, `smalltype` (Basics/Overture.v); `power_type` (Sets/Powers.v). No joins of subsets. |
| Prop 3.2.1 | The inflationary endomaps of an i-dcpo form an i-subdcpo of A → A with a top element ⊤; ⊤(x) is a common fixed point of all inflationary maps. | 3.1.4, 3.1.5, 3.1.6 | `Analysis/Dcpo.v` · `prop_3_2_1` | todo | None. |
| Cor 3.2.2 | If B is an f-closed i-subdcpo of an i-dcpo and f is inflationary, a point of B gives a fixed point of f (no resizing). | 3.1.5, 3.2.1 | `Analysis/Dcpo.v` · `cor_3_2_2` | todo | None. |
| Thm 3.2.3 | Pataraia: with propositional resizing, a monotone endomap of an i-dcpo with bottom has a least fixed point. | 3.2.2, 3.1.4, 2.6.15, 2.6.13 | `Analysis/Dcpo.v` · `thm_3_2_3` | todo | None. |

## Chapter 4: Real numbers

### 4.1 Algebraic structure of numbers

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 4.1.2 | Classical field: commutative ring where x ≠ 0 ⇒ ∃ y, xy = 1. | 2.5.4 | existing name | todo | `IsDecField` (Classes/interfaces/abstract_algebra.v): uses a total `DecRecip` with `/0 = 0`. Equivalent up to that convention; no lemma relating the two. |
| Def 4.1.4 | Apartness relation (irreflexive, symmetric, cotransitive); strict partial order (irreflexive, transitive, cotransitive). | 3.1.1 | existing names | todo | `IsApart` (Classes/interfaces/abstract_algebra.v; also asks for a set, HProp-valued, tight). `StrictOrder` (Classes/interfaces/orders.v) lacks cotransitivity; `PseudoOrder` has it, together with apartness. No exact match for either. |
| Def 4.1.5 | Constructive field: ring with tight apartness, x invertible iff x # 0, + is #-extensional. | 4.1.4 | existing name | todo | `IsField` (Classes/interfaces/abstract_algebra.v): gives `recip` on apart elements as structure plus `field_plus_ext`, `field_mult_ext`, `field_nontrivial`. Equivalent since inverses are unique; no equivalence proved. |
| Lem 4.1.6 | In a constructive field: 1 # 0; + is #-compatible; · is #-extensional. | 4.1.5 | existing names | todo | `field_nontrivial`, `field_mult_ext` are fields of `IsField`. #-compatibility of +: search Classes/theory/apartness.v and Classes/theory/fields.v. |
| Lem 4.1.7 | A strict partial order induces an apartness x # y := x < y ∨ y < x and a preorder x ≤ y := ¬(y < x). | 4.1.4 | `Analysis/OrderedField.v` · `lem_4_1_7_apart`, `lem_4_1_7_le` | todo | None as constructions. `FullPseudoOrder` (Classes/interfaces/orders.v) takes `≶` and `≤` as separate data with `apart_iff_total_lt` and `le_iff_not_lt_flip`. |
| Def 4.1.8 | Lattice: min and max compute glb and lub. | 3.1.3 | existing name | todo | `LatticeOrder` with `meet_glb`, `join_lub`, `meet_lb_l`, … (Classes/interfaces/orders.v). Complete. |
| Def 4.1.10 | Ordered field: ring, strict order, x invertible iff x # 0, ≤ antisymmetric, lattice, and the laws (†) x+y < z+w ⇒ x<z ∨ y<w and (∗) 0<z ∧ x<y ⇒ xz<yz. | 4.1.4, 4.1.7, 4.1.8 | existing name | todo | `OrderedField` (Classes/interfaces/orders.v), following HoTT book Def. 11.2.7 via `IsField`, `LatticeOrder`, `FullPseudoSemiRingOrder`. Same notion, different axioms; the equivalence is Lemma 4.1.11. |
| Lem 4.1.11 | Given axioms 1–5 of 4.1.10, (†) ∧ (∗) is equivalent to the ten listed order laws. | 4.1.10, 4.1.7 | `Analysis/OrderedField.v` · `lem_4_1_11` | todo | No equivalence. Most individual laws exist for `OrderedField`, e.g. `lt_le_trans`, `le_lt_trans` (Classes/orders/orders.v), `flip_lt_negate`, `flip_pos_minus` (Classes/orders/rings.v), `pos_mult`, `lt_1_2` (Classes/orders/semirings.v). |
| Lem 4.1.12 | An ordered field is a constructive field. | 4.1.10, 4.1.5 | existing name | todo | Holds by definition: `ordered_field_field` (Classes/interfaces/orders.v). |

### 4.3 Archimedean property

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 4.3.1 | Morphism of ordered fields: ring morphism reflecting <. | 4.1.10 | `Analysis/OrderedField.v` · `def_4_3_1` | todo | Parts only: `IsSemiRingPreserving`, `IsSemiRingStrongPreserving` (Classes/interfaces/abstract_algebra.v), `StrictlyOrderReflecting` (Classes/interfaces/orders.v). No bundled notion. |
| Lem 4.3.3 | There is a unique morphism i : Q → F of ordered fields, and it preserves <. | 4.3.1, 4.1.10 | `Analysis/OrderedField.v` · `lem_4_3_3` | todo | `rationals_to_field`, `rationals_to_field_mor`, `rationals_initial` (Classes/interfaces/rationals.v) give existence and uniqueness as a ring map, but require `FieldCharacteristic F 0`, which is not derived for ordered fields. Preservation of < is **missing**: `cauchy.v` and `Locator.v` assume it (TODO). Proving it lets those assumptions go. |
| Def 4.3.5 | Archimedean: ∀ x y, x < y ⇒ ∃ q : Q, x < q < y. | 4.3.3 | existing name | todo | `ArchimedeanProperty` (Classes/interfaces/archimedean.v). Complete. |
| Ex 4.3.6 | *optional.* In an Archimedean field every x has rational bounds ∃ q r, q < x < r. | 4.3.5 | `Analysis/OrderedField.v` · `ex_4_3_6` | todo | Inline only, inside `P_lower_inhab` and `P_upper_inhab` (Analysis/Locator.v). |

### 4.4 Cauchy completeness of real numbers

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 4.4.1 | Modulus of Cauchy convergence M : Q+ → N of a sequence in F. | 4.1.10, 4.3.3 | existing name | todo | `CauchyModulus` (Classes/interfaces/cauchy.v), with −ε < x_m − x_n < ε in place of the absolute value. |
| Def 4.4.2 | l is a limit of x: ∀ ε ∃ N ∀ n ≥ N, \|x_n − l\| < ε. | 4.1.10 | existing name | todo | `IsLimit` (Classes/interfaces/cauchy.v), using `hexists`. |
| Def 4.4.4 | Cauchy complete: from a sequence with modulus we can compute a limit. | 4.4.1, 4.4.2 | existing name | todo | `IsComplete` (Classes/interfaces/cauchy.v), Σ-valued as required. |
| Lem 4.4.5 | In an Archimedean field the type of limits of a fixed sequence is a proposition. | 4.4.2, 4.3.5, 2.6.20 | `Analysis/CauchyCompleteness.v` · `lem_4_4_5` | todo | None for `cauchy.v`. `limit_unique` (Classes/theory/premetric.v) is the analogue for separated premetric spaces. |
| Cor 4.4.6 | If a limit merely exists, we can compute it. | 4.4.5, 2.4.3 | `Analysis/CauchyCompleteness.v` · `cor_4_4_6` | todo | None. |
| Cor 4.4.7 | If a limit can be computed from a modulus, then the mere existence of a modulus suffices to compute it. | 4.4.4, 4.4.5 | `Analysis/CauchyCompleteness.v` · `cor_4_4_7` | todo | None. |
| Ex 4.4.8 | *optional.* exp(x) = Σ x^k/k! in a Cauchy complete Archimedean field, via 4.4.7 and bounds on x. | 4.4.7, 4.3.6, U-3 | `Analysis/CauchyCompleteness.v` · `ex_4_4_8` | todo | None. |
| Def 4.4.9 | Cauchy reals R_C: rational sequences with modulus, quotiented by (∀ ε) \|x_{M(ε/4)} − y_{M(ε/4)}\| < ε. | 4.4.1, 2.7.2 | `Analysis/CauchyReals.v` · `def_4_4_9` | todo | None. `Quotient` (Colimits/Quotient.v). The unnumbered claim that R_C is an Archimedean ordered field is U-1. |

### 4.5 HoTT book reals

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 4.5.2 | Premetric: an HProp-valued relation ∼ : Q+ × R × R → HProp, no axioms. | 2.4.1 | existing name | todo | `Closeness` (Classes/theory/premetric.v), Type-valued; HProp-ness must be added as a hypothesis (as in `approx_eq`). `PreMetric` there adds axioms the thesis deliberately omits. |
| Def 4.5.3 | Modulus of Cauchy convergence for a sequence in a premetric space. | 4.5.2 | `Analysis/CauchyStructure.v` · `def_4_5_3` | todo | None for premetric spaces. |
| Def 4.5.4 | Limit of a sequence in a premetric space. | 4.5.2 | `Analysis/CauchyStructure.v` · `def_4_5_4` | todo | None for sequences. |
| Def 4.5.5 | Cauchy approximation x : Q+ → R with x_δ ∼_{δ+ε} x_ε; type C_R. | 4.5.2 | existing name | todo | `Approximation` (Classes/theory/premetric.v). Complete. |
| Def 4.5.7 | u is a limit of a Cauchy approximation: ∀ ε θ, x_ε ∼_{ε+θ} u; Cauchy complete premetric space. | 4.5.5 | existing names | todo | `IsLimit`, `Lim`, `CauchyComplete` (Classes/theory/premetric.v). Complete. |
| Def 4.5.8 | Cauchy structure (rat, lim, eq and four distance laws, as a Σ-type) and morphisms CS-hom(R, S). | 4.5.2, 4.5.5 | `Analysis/CauchyStructure.v` · `def_4_5_8`, `def_4_5_8_hom` | todo | None. |
| Lem 4.5.10 | In an Archimedean field with u ∼_ε v := \|u − v\| < ε, a limit u of x satisfies \|x_δ − u\| ≤ δ. | 4.5.7, 4.3.5 | `Analysis/CauchyStructure.v` · `lem_4_5_10` | todo | None for ordered fields. |
| Cor 4.5.11 | A Cauchy complete Archimedean ordered field has a canonical Cauchy structure. | 4.3.3, 4.4.4, 4.5.8, 4.5.10 | `Analysis/CauchyStructure.v` · `cor_4_5_11` | todo | None. |
| Def 4.5.12 | R_H is a homotopy-initial Cauchy structure: CS-hom(R_H, S) is contractible for every Cauchy structure S. | 4.5.8 | `Analysis/HoTTBookReals.v` · `def_4_5_12` | todo | None. The HoTT book's Cauchy reals (§11.3) are not in Coq-HoTT; state as a predicate on a Cauchy structure. |
| Thm 4.5.13 | R_H is Cauchy complete. | 4.5.12, 4.5.18, U-2 | `Analysis/HoTTBookReals.v` · `thm_4_5_13` | todo | None. The thesis defers to HoTT book §11.3.2. |
| Def 4.5.14 | For A : R_H → U and B over ∼, the premetric (u, a) ∼_ε (v, b) := Σ ζ : u ∼_ε v, B(…, ζ) on Σ u, A(u). | 4.5.2, 4.5.12 | `Analysis/HoTTBookReals.v` · `def_4_5_14` | todo | None. |
| Def 4.5.15 | Dependent Cauchy approximation over x : C_{R_H}; type D^A_x. | 4.5.5, 4.5.14 | `Analysis/HoTTBookReals.v` · `def_4_5_15` | todo | None. |
| Lem 4.5.16 | λ ε. (x_ε, a_ε) is a Cauchy approximation in Σ u, A(u) iff a is a dependent Cauchy approximation over x. | 4.5.14, 4.5.15 | `Analysis/HoTTBookReals.v` · `lem_4_5_16` | todo | None. |
| Def 4.5.17 | Dependent identifications u =^B_p v. | — | existing name | todo | `DPath` (Cubical/DPath.v); equivalently `transport B p u = v`. Complete. |
| Thm 4.5.18 | Induction principle for R_H with computation rules for rat and lim. | 4.5.12, 4.5.14–4.5.17, Rem 4.5.9 | `Analysis/HoTTBookReals.v` · `thm_4_5_18` | todo | None. |

### 4.6 Dedekind reals

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 4.6.1 | Two-sided Dedekind cut (L, U) of predicates Q → HProp: bounded, rounded, transitive, located; R_D as a Σ-type. | 2.4.5, 4.2 | `Analysis/DedekindReals.v` · `def_4_6_1` | todo | None. |
| Lem 4.6.3 | R_D is a set. | 4.6.1, Univalence | `Analysis/DedekindReals.v` · `lem_4_6_3` | todo | Ingredients: `isset_HProp` (Universes/TruncType.v), `path_sigma_hprop` (Types/Sigma.v). |
| Def 4.6.5 | x < y := ∃ q, x < q < y; x # y := x < y ∨ y < x on R_D. | 4.6.1 | `Analysis/DedekindReals.v` · `def_4_6_5_lt`, `def_4_6_5_apart` | todo | None. |
| Lem 4.6.6 | R_D is Cauchy complete, with the limit cut given explicitly. | 4.6.1, 4.6.5, 4.4.1, 4.4.4, U-1 | `Analysis/DedekindReals.v` · `lem_4_6_6` | todo | None. Stating `IsComplete` needs the ordered-field structure on R_D (U-1). |
| Prop 4.6.7 | Canonical inclusions R_C ⊆ R_H ⊆ R_D. | 4.4.9, 4.5.11, 4.5.12, 4.5.13, 4.6.6, U-2 | `Analysis/RealsInclusions.v` · `prop_4_6_7` | todo | None. The thesis cites HoTT book Thm 11.3.50 for R_H → R_D being an embedding. |

## Chapter 5: Universal properties of real numbers

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Prop 5.1.1 | A Cauchy complete subset R ⊆ R_D containing Q inherits a Cauchy structure. | 4.5.11, 4.6.6, 4.3.3, 2.6.2 | `Analysis/RealsInclusions.v` · `prop_5_1_1` | todo | None. |
| Cor 5.1.2 | The inclusion R → R_D is a Cauchy structure morphism. | 5.1.1 | `Analysis/RealsInclusions.v` · `cor_5_1_2` | todo | None. |
| Prop 5.1.3 | R_H ⊆ R as subsets of R_D, with i_R ∘ f = i_H. | 4.5.12, 4.6.7, 5.1.2, Rem 4.5.9, 2.6.9 | `Analysis/RealsInclusions.v` · `prop_5_1_3` | todo | None. |
| Cor 5.1.4 | If R_H exists, R_C is Cauchy complete iff R_C and R_H are the same subset of R_D. | 5.1.3, 4.4.9, 4.6.7 | `Analysis/RealsInclusions.v` · `cor_5_1_4` | todo | None. |
| Def 5.1.5 | With propositional resizing, the Euclidean reals R_E: the meet of all Cauchy complete subsets of R_D containing Q. | 4.6.1, 4.6.6, 2.6.15, 2.6.13 | `Analysis/EuclideanReals.v` · `def_5_1_5` | todo | `PropResizing`, `smalltype` (Basics/Overture.v). |
| Thm 5.1.7 | With resizing and R_H, R_E and R_H coincide as subsets of R_D. | 5.1.3, 5.1.5, 4.5.13 | `Analysis/EuclideanReals.v` · `thm_5_1_7` | todo | None. |
| Thm 5.1.8 | With resizing, the unit interval in R_E is an interval object. | 5.1.5, 5.3.6 | `Analysis/EuclideanReals.v` · `thm_5_1_8` | todo | None. The thesis only says "translate Escardó–Simpson"; state it against Def 5.3.6. Large. |
| Cor 5.1.9 | With resizing and R_H, the unit interval in R_H is an interval object. | 5.1.7, 5.1.8 | `Analysis/EuclideanReals.v` · `cor_5_1_9` | todo | None. |
| Thm 5.2.1 | With resizing, CS-hom(R_E, S) is contractible for every Cauchy structure S on a set. | 3.1.7, 3.2.2, 5.1.5, 4.5.8, 4.6.6, 2.6.15 | `Analysis/EuclideanReals.v` · `thm_5_2_1` | todo | None. The proof defines sub-CS-hom(Y, S), the subset F_(S,∼) and Φ(X), and proves Claims 1–5; give each its own lemma. |
| Def 5.3.1 | Cancellative midpoint algebra (idempotent, commutative, transposition, cancellation) on a set. | 2.5.4 | `Analysis/IntervalObject.v` · `def_5_3_1` | todo | None. |
| Def 5.3.2 | Convex body: a midpoint algebra with M : A^N → A satisfying the iteration laws. | 5.3.1 | `Analysis/IntervalObject.v` · `def_5_3_2` | todo | None. |
| Lem 5.3.3 | The iteration property is a proposition: any two such M are equal. | 5.3.2, Funext, 2.6.20 | `Analysis/IntervalObject.v` · `lem_5_3_3` | todo | None. |
| Thm 5.3.4 | The iteration property holds iff ∀ x : A^N, Contr (Σ α : A^N, ∀ i, α_i = m(x_i, α_{i+1})). | 5.3.2, 5.3.3 | `Analysis/IntervalObject.v` · `thm_5_3_4` | todo | None. |
| Def 5.3.5 | Bipointed convex body and homomorphisms. | 5.3.2 | `Analysis/IntervalObject.v` · `def_5_3_5`, `def_5_3_5_hom` | todo | None. |
| Def 5.3.6 | Interval object: a homotopy-initial bipointed convex body. | 5.3.5 | `Analysis/IntervalObject.v` · `def_5_3_6` | todo | None. The thesis quantifies over "convex bodies"; it means bipointed ones. |
| Conj 5.4.1 | (I_H, m, −1, 1) with I_H = [−1, 1] ⊆ R_H and m(x, y) = (x+y)/2 is an interval object. | 5.3.6, 4.5.12 | `Analysis/IntervalObject.v` · `conj_5_4_1` | todo | None. Open problem: state as a `Definition` of the proposition, do not try to prove it. |
| Conj 5.4.2 | From an interval object, R_I := (Z × I)/∼ has a Cauchy structure that is homotopy-initial for sets. | 5.3.6, 4.5.8, 2.7.2 | `Analysis/IntervalObject.v` · `conj_5_4_2` | todo | None. Open problem: state only. |

## Chapter 6: Locators

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 6.1.1 | locator(x) := Π q r : Q, q < r → (q < x) + (x < r). | 4.3.3 | existing name | todo | `locator` (Analysis/Locator.v). Complete. |
| Lem 6.1.3 | Assuming PEM, every x has a locator. | 6.1.1, 2.8.2 | existing name | todo | `all_reals_locators` (Analysis/Locator.v). |
| Lem 6.3.1 | If ∃ s : Q, x = i(s), then x has a locator; two different constructions. | 6.1.1, 4.3.3 | `Analysis/Locator.v` · `lem_6_3_1` | todo | `locator_left`, `locator_second` (Analysis/Locator.v), for x = ' s (Σ form) only. The ∃ form needs that i is an embedding (Rem 4.3.4), so that Σ s, x = i(s) is a proposition. |
| Lem 6.4.1 | A + B ≃ Σ P : DHProp, (P → A) × (¬P → B). | 2.4.9 | `Analysis/Locator.v` · `lem_6_4_1` | todo | None. `equiv_decidable_sum` (Types/Sum.v) is a different decomposition (of a type by a decidable predicate). |
| Lem 6.4.2 | locator(x) ≃ Σ locatesRight : (Π q r, q < r → DHProp), (… → q < x) × (¬ … → x < r). | 6.4.1, 6.1.1 | existing name | todo | `locator'` (record) and `equiv_locator_locator'` (Analysis/Locator.v). Complete, though not proved via 6.4.1. |
| Def 6.4.4 | locatesRight(q <_x r) and locatesLeft(q <_x r). | 6.4.2 | existing names | todo | `locates_right`, `locates_left` (Analysis/Locator.v). Complete. |
| Lem 6.4.6 | ¬(q < x) ⇒ locatesLeft(q <_x r); ¬(x < r) ⇒ locatesRight(q <_x r). | 6.4.4 | existing names | todo | `nltqx_locates_left`, `nltxr_locates_right`, and the variants `ltxq_locates_left`, `ltrx_locates_right` (Analysis/Locator.v). Complete. |
| Ex 6.4.7 | *optional.* P(q) := locatesRight(q − 1 <_x q) is decidable and merely inhabited. | 6.4.6 | existing names | todo | `P_lower`, `P_lower_inhab` (Analysis/Locator.v, local). |
| Thm 6.5.1 | For P : N → DHProp, ∃ n, P n gives Σ n, P n. | 2.4.9, 2.4.3 | existing name | todo | `minimal_n` (Misc/BoundedSearch.v), for decidable `P : nat -> Type`. Complete. |
| Cor 6.5.4 | The same for any A with N ≃ A. | 6.5.1 | existing name | todo | `minimal_n_alt_type` (Misc/BoundedSearch.v). Complete. |
| Lem 6.6.1 | A real with a locator has bounds Σ q r : Q, q < x < r. | 6.4.7, 6.5.4, 4.3.6 | existing names | todo | `lower_bound`, `upper_bound` (Analysis/Locator.v). |
| Lem 6.6.3 | For ε : Q+, a real with a locator has u < x < v with v − u < ε. | 6.6.1, 6.4.6 | existing name | todo | `tight_bound` (Analysis/Locator.v), with v = u + ε, using `sperners_lemma_1d` (Spaces/Finite/Fin.v). |
| Lem 6.7.1 | Characterization of q < −x, −x < r, q < x+y, x+y < r, q < xy, xy < r, q < z⁻¹, z⁻¹ < r (z > 0), q < w⁻¹, w⁻¹ < r (w < 0), q < min(x, y), min(x, y) < r, q < max(x, y), max(x, y) < r. | 4.3.5, 4.1.8, 4.1.10 | existing names in `Classes/orders/archimedean.v` | proved | All parts proved in Classes/orders/archimedean.v: `char_minus_left`, `char_minus_right`, `char_plus_left`, `char_plus_right`, `char_times_left`, `char_times_right`, `char_recip_pos_left`, `char_recip_pos_right`, `char_recip_neg_left`, `char_recip_neg_right`, `char_meet_left`, `char_meet_right`, `char_join_left`, `char_join_right`. Two statements were corrected: `char_times_left`/`char_times_right` used the min/max of a, b, c, d instead of the products ac, ad, bc, bd (false as stated), and `char_recip_neg_left` had `q w < 1` instead of `1 < q w` (false for w = −1, q = −2). `char_times_*` assume `StrictlyOrderPreserving qinc` and `IsSemiRingStrongPreserving qinc` (TODO, Lemma 4.3.3). Helpers: `archimedean_mult_approx` (archimedean.v); `mult_lt_bound`, `mult_minus_mult_lt_bound`, `lt_mult_endpoints_l`, `mult_endpoints_lt_r` (Classes/orders/rings.v). |
| Lem 6.7.2 | x < y ⇒ ∃ q : Q, ε : Q+, x < q − ε < q + ε < y. | 4.3.5 | `Analysis/Locator.v` · `lem_6_7_2` | todo | Inline only, as the local `P_inhab` in section `arch_struct` (Analysis/Locator.v). |
| Lem 6.7.3 | For x, y with locators, x < y → Σ q : Q, x < q < y. | 6.7.2, 6.5.4, 6.4.6 | existing name | todo | `archimedean_structure` (Analysis/Locator.v), using `QQpos_eq`. |
| Cor 6.7.4 | For x, y with locators and s : Q, x < y → (x < s) + (s < y). | 6.7.3 | `Analysis/Locator.v` · `cor_6_7_4` | todo | None. |
| Thm 6.7.6 | Locators for −x, x + y, xy, x⁻¹ (x # 0), min(x, y), max(x, y). | 6.6.3, 6.7.1, 6.7.4, 6.3.1, Rem 6.7.7 | existing names, plus `Analysis/Locator.v` · `thm_6_7_6_times` | todo | `locator_minus`, `locator_plus` (using `char_plus_left`, `char_plus_right`), `locator_meet`, `locator_join`, `locator_recip_pos`, `locator_recip_neg`, `locator_recip` (Analysis/Locator.v). `locator_times` is `Abort`ed. |
| Lem 6.8.1 | If x has a modulus M and every x_n has a locator, then lim x has a locator. | 4.4.1, 4.4.2, 6.1.1 | existing name | todo | `locator_limit` (Analysis/Locator.v) using `modulus_close_limit` (Classes/interfaces/cauchy.v). |
| Ex 6.8.3 | *optional.* exp(x) has a locator when x has one. | 4.4.8, 6.6.1, 6.8.1 | `Analysis/Locator.v` · `ex_6_8_3` | todo | None. |
| Ex 6.8.4 | *optional.* Constants such as π and e have locators. | 6.8.1, 6.3.1 | `Analysis/Locator.v` · `ex_6_8_4` | todo | None. |
| Ex 6.9.1 | *optional.* Digit expansions give rational bounds (motivation only). | — | none | todo | Nothing to formalize. |
| Def 6.9.2 | Signed-digit representation: k : Z and digits a_i ∈ {−9, …, 9} with x = k + Σ a_i 10^(−i−1). | 4.4.4, U-3 | `Analysis/LocatorDigits.v` · `def_6_9_2` | todo | None. Integers: `Int` (Spaces/Int.v) or `Integers` (Classes/interfaces/integers.v). |
| Ex 6.9.3 | *optional.* Three signed-decimal expansions of π. | 6.9.2 | none | todo | Nothing to formalize. |
| Lem 6.9.4 | A real with a locator has k : Z with x ∈ (k − 1, k + 1). | 6.6.3, U-4 | `Analysis/LocatorDigits.v` · `lem_6_9_4` | todo | None. Floor: only `RoundUpStrict` (Classes/interfaces/round.v), giving n : nat with q < n. |
| Thm 6.9.5 | Locators and signed-digit representations are interdefinable. | 6.9.2, 6.9.4, 6.8.1, 6.3.1 | `Analysis/LocatorDigits.v` · `thm_6_9_5` (both directions) | todo | None. |
| Def 6.9.6 | isCauchyReal(x): x is in the image of R_C → R. | 4.4.9, 4.4.4 | `Analysis/LocatorDigits.v` · `def_6_9_6` | todo | None. Use `hexists`/`hfiber`. |
| Thm 6.9.7 | TFAE: ‖locator(x)‖; ∃ signed-digit representation; ∃ rational Cauchy sequence with limit x; isCauchyReal(x). | 6.9.5, 6.8.1, 6.9.6, 4.4.9 | `Analysis/LocatorDigits.v` · `thm_6_9_7` | todo | None. |
| Cor 6.9.9 | Every Dedekind real merely has a signed-digit representation iff R_C and R_D coincide. | 6.9.7, 4.6.7 | `Analysis/LocatorDigits.v` · `cor_6_9_9` | todo | None. |
| Lem 6.10.1 | A choice Π x : R, locator(x) gives a strongly non-constant f : R → 2. | 6.1.1, 6.4.4, 6.3.1 | `Analysis/LocatorCuts.v` · `lem_6_10_1` | todo | None. `Bool` (Types/Bool.v). |
| Lem 6.10.2 | A strongly non-constant R → 2 implies WLPO. | 2.8.4, 4.4.4, 4.4.7 | `Analysis/LocatorCuts.v` · `lem_6_10_2` | todo | None, and no `WLPO` in Coq-HoTT: define it next to this lemma (or in a `Misc/` file). |
| Thm 6.10.3 | For (L, U): isCut§ → isCut; isCut§ ⇒ isCut; isCut × locator → isCut§; isCut × ‖locator‖ ⇒ isCauchyReal; isCut§ ⇒ isCauchyReal. | 4.6.1, 6.6.1, 6.7.3, 6.3.1, 6.9.7 | `Analysis/LocatorCuts.v` · `thm_6_10_3_1` … `thm_6_10_3_5` | todo | None. Define the eight components of isCut and isCut§ as in §6.10. |
| Thm 6.10.5 | It is not provable that isCut(x) implies ‖isCut§(x)‖. | 6.10.3, 6.9.9 | `Analysis/LocatorCuts.v` · `thm_6_10_5` | todo | None. A non-provability claim resting on Lubarsky's model; formalize only the internal content: (Π x, isCut x → ‖isCut§ x‖) implies that R_C and R_D coincide. |

## Chapter 7: Some constructive analysis with locators

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 7.1.1 | f : R → R lifts to locators: Π x, locator(x) → locator(f x) (structure). | 6.1.1 | `Analysis/LiftsToLocators.v` · `def_7_1_1` | todo | None. |
| Ex 7.1.3 | *optional.* exp lifts to locators. | 4.4.8, 6.8.3, 7.1.1 | `Analysis/LiftsToLocators.v` · `ex_7_1_3` | todo | None. |
| Def 7.1.4 | f is continuous at x (∀ ε ∃ δ …) and pointwise continuous. | 4.1.10 | `Analysis/LiftsToLocators.v` · `def_7_1_4` | todo | `Continuous` (Classes/theory/premetric.v) is the same shape for premetric spaces, but F has no `Closeness` instance yet. |
| Def 7.1.5 | Modulus of uniform continuity ω : Q+ → Q+ for f on [a, b]. | 4.1.10 | `Analysis/LiftsToLocators.v` · `def_7_1_5` | todo | `Uniform` and `Interval` (Classes/theory/premetric.v), for premetric spaces. |
| Ex 7.1.6 | *optional.* exp has a modulus of uniform continuity on [a, b], computable when a, b have locators. | 4.4.8, 7.1.5, 6.7.3 | `Analysis/LiftsToLocators.v` · `ex_7_1_6` | todo | None. |
| Lem 7.1.7 | If all constant functions lift to locators, every x has a locator. | 7.1.1, 6.3.1 | `Analysis/LiftsToLocators.v` · `lem_7_1_7` | todo | None. |
| Lem 7.1.8 | Assuming PEM, some discontinuous f : R → R lifts to locators. | 6.1.3, 7.1.1, 7.1.4, 2.8.2 | `Analysis/LiftsToLocators.v` · `lem_7_1_8` | todo | `ExcludedMiddle`, `LEM` (ExcludedMiddle.v). |
| Thm 7.2.1 | If f has a modulus of uniform continuity on [a, b], a and b have locators and f lifts to locators, then ∫_a^b f has a locator. | 7.1.1, 7.1.5, 6.3.1, 6.7.6, 6.6.1, 6.8.1, 4.4.4, U-5 | `Analysis/Integral.v` · `thm_7_2_1` | todo | None. |
| Ex 7.2.3 | *optional.* ∫_0^8 sin(x + exp x) dx has a locator. | 7.2.1, 7.1.3 | `Analysis/Integral.v` · `ex_7_2_3` | todo | None; needs sin. |
| Thm 7.3.1 | Approximate IVT: f pointwise continuous on [a, b], f(a) < 0 < f(b) ⇒ for each ε we can find x with \|f(x)\| < ε; with a locator if f lifts and a, b have locators. | 7.1.1, 7.1.4, 6.7.6, 6.6.1, 6.8.1, 4.4.4 | `Analysis/IntermediateValue.v` · `thm_7_3_1` | todo | None. |
| Def 7.3.2 | Locally nonconstant: ∀ x < y, t, ∃ z, x < z < y ∧ f(z) # t. | 4.1.7 | `Analysis/IntermediateValue.v` · `def_7_3_2` | todo | None. |
| Ex 7.3.3 | *optional.* Strictly monotone functions are locally nonconstant, not conversely. | 7.3.2 | `Analysis/IntermediateValue.v` · `ex_7_3_3` | todo | None. |
| Lem 7.3.4 | For f continuous, locally nonconstant and lifting to locators, and x < y, t with locators, find r : Q with x < r < y and f(r) # t. | 7.3.2, 7.1.4, 7.1.1, 6.5.4, 6.7.3, 6.4.6 | `Analysis/IntermediateValue.v` · `lem_7_3_4` | todo | None. Search over Q × Q+ as in `archimedean_structure`. |
| Thm 7.3.5 | Exact IVT: f continuous, locally nonconstant, lifts to locators, a < b with locators, f(a) ≤ 0 ≤ f(b) ⇒ a root of f with a locator. | 7.3.4, 6.7.6, 6.6.1, 6.8.1, 4.4.4 | `Analysis/IntermediateValue.v` · `thm_7_3_5` | todo | None. |
| Ex 7.3.7 | *optional.* exp(x) = y has a solution with a locator when y > 0 has one. | 7.3.5, 7.1.3, 7.3.3 | `Analysis/IntermediateValue.v` · `ex_7_3_7` | todo | None. |

## Chapter 8: Metric spaces

| ID | Statement | Depends on | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Def 8.1.1 | Metric and pseudometric ρ : X × X → R≥0 on a set. | 4.1.10 | `Analysis/MetricSpace.v` · `def_8_1_1_pseudometric`, `def_8_1_1_metric` | todo | None. `PreMetric` (Classes/theory/premetric.v) is closeness-based, not distance-based. |
| Lem 8.1.3 | ρ(x, y) = \|x − y\| is a metric on R. | 8.1.1 | `Analysis/MetricSpace.v` · `lem_8_1_3` | todo | `Abs`, `abs` (Classes/interfaces/canonical_names.v); \|·\| lemmas for Q only (`Q_triangle_le`, …, Classes/theory/rationals.v). |
| Ex 8.1.4 | *optional.* Pointer to the space of Def 8.2.7. | 8.2.7 | none | todo | Nothing to formalize. |
| Lem 8.1.5 | Two limits of a sequence in a pseudometric space have distance 0; limits are unique in metric spaces. | 8.1.1, 4.5.4 | `Analysis/MetricSpace.v` · `lem_8_1_5` | todo | `limit_unique` (Classes/theory/premetric.v) is the separated-premetric analogue. |
| Def 8.1.6 | Cauchy complete pseudometric space: a lim function on sequences with modulus. | 8.1.1, 4.5.3, 4.5.4 | `Analysis/MetricSpace.v` · `def_8_1_6` | todo | None for sequences; `CauchyComplete` (Classes/theory/premetric.v) is for approximations. |
| Def 8.1.7 | Modulus of uniform continuity between premetric spaces. | 4.5.2 | existing name | todo | `Uniform` (Classes/theory/premetric.v); composition `uniform_compose`. Complete. |
| Lem 8.1.8 | A uniformly continuous map sends a sequence with modulus M to one with modulus M ∘ ω. | 8.1.7, 4.5.3 | `Analysis/MetricSpace.v` · `lem_8_1_8` | todo | None. |
| Def 8.1.9 | f preserves limits. | 4.5.4 | `Analysis/MetricSpace.v` · `def_8_1_9` | todo | None. |
| Lem 8.1.10 | Uniformly continuous maps preserve limits. | 8.1.7, 8.1.9 | `Analysis/MetricSpace.v` · `lem_8_1_10` | todo | None. |
| Def 8.2.1 | U[a,b][c,d]: maps [a, b] → [c, d] with a modulus of uniform continuity. | 7.1.5 | `Analysis/FunctionSpace.v` · `def_8_2_1` | todo | `Interval` (Classes/theory/premetric.v). |
| Lem 8.2.2 | The supremum of a uniformly continuous f : [a, b] → R is the limit of maxima over equidistant samples, with modulus (b − a)/ω(ε). | 7.1.5, 4.4.4, 4.4.7, 4.1.8 | `Analysis/FunctionSpace.v` · `lem_8_2_2` | todo | None. (b − a)/ω(ε) is real; turning it into a natural needs a rational bound, via 4.4.7 or locators for a and b. |
| Lem 8.2.3 | U[a,b][c,d] is a pseudometric space with the sup distance. | 8.2.1, 8.2.2, 8.1.1 | `Analysis/FunctionSpace.v` · `lem_8_2_3` | todo | None. |
| Def 8.2.4 | f : [a, b] → [c, d] lifts to locators. | 7.1.1, 6.1.1 | `Analysis/FunctionSpace.v` · `def_8_2_4` | todo | None. |
| Lem 8.2.6 | A map π : Y → X pulls back a pseudometric on X to one on Y. | 8.1.1 | `Analysis/MetricSpace.v` · `lem_8_2_6` | todo | None. |
| Def 8.2.7 | UL[a,b][c,d]: uniformly continuous maps that lift to locators. | 8.2.1, 8.2.4 | `Analysis/FunctionSpace.v` · `def_8_2_7` | todo | None. |
| Cor 8.2.8 | UL[a,b][c,d] is a pseudometric space with distance computed as on U. | 8.2.3, 8.2.6, 8.2.7 | `Analysis/FunctionSpace.v` · `cor_8_2_8` | todo | None. |
| Lem 8.2.9 | Elements of UL at distance 0 have equal underlying maps. | 8.2.8, 8.2.2, Funext | `Analysis/FunctionSpace.v` · `lem_8_2_9` | todo | None. |
| Lem 8.2.10 | UL[a,b][c,d] is Cauchy complete. | 8.2.7, 8.1.6, 6.8.1, 4.4.4 | `Analysis/FunctionSpace.v` · `lem_8_2_10` | todo | None. |
| Def 8.3.1 | Lipschitz constant c : R for a map of pseudometric spaces. | 8.1.1 | `Analysis/BanachFixedPoint.v` · `def_8_3_1` | todo | `Lipschitz` (Classes/theory/premetric.v): closeness-based with c : Q+. |
| Lem 8.3.2 | A rational Lipschitz constant c gives the modulus ε/c. | 8.3.1, 8.1.7 | `Analysis/BanachFixedPoint.v` · `lem_8_3_2` | todo | Premetric analogue only: `lipschitz_continuous` (Classes/theory/premetric.v) gives `Continuous`. |
| Cor 8.3.3 | A real Lipschitz constant gives the mere existence of a modulus. | 8.3.2, 4.3.5 | `Analysis/BanachFixedPoint.v` · `cor_8_3_3` | todo | None. |
| Lem 8.3.4 | For c < 1, pseudo-fixed points are pseudo-unique. | 8.3.1, 8.1.1 | `Analysis/BanachFixedPoint.v` · `lem_8_3_4` | todo | None. |
| Cor 8.3.5 | In a metric space with c < 1, the type of fixed points is a proposition. | 8.3.4, 2.6.20 | `Analysis/BanachFixedPoint.v` · `cor_8_3_5` | todo | None. |
| Lem 8.3.7 | For 0 < c < 1 rational, log_c : Q+ → N with c^(log_c q) < q. | U-4 | `Analysis/BanachFixedPoint.v` · `lem_8_3_7` | todo | None. |
| Lem 8.3.8 | With rational Lipschitz constant 0 < c < 1 and ρ(T x₀, x₀) ≤ C, the iterates T^n(x₀) have modulus log_c(ε(1 − c)/C). | 8.3.7, 8.3.1, 8.1.1, 4.5.3 | `Analysis/BanachFixedPoint.v` · `lem_8_3_8` | todo | None. |
| Thm 8.3.11 | Banach: a Cauchy complete pseudometric space with a point, bounded by C : Q, and T with rational Lipschitz constant 0 < c < 1 has a pseudo-unique pseudo-fixed point. | 8.3.8, 8.3.2, 8.3.4, 8.1.6, 8.1.10, 8.1.5 | `Analysis/BanachFixedPoint.v` · `thm_8_3_11` | todo | None. The proof uses ρ(T x₀, x₀) ≤ C from Lemma 8.3.8 rather than the boundedness of X (Rem 8.3.9). |
| Def 8.4.1 | Product of pseudometric spaces with the sum metric; a product of metrics is a metric. | 8.1.1 | `Analysis/PicardLindelof.v` · `def_8_4_1` | todo | None. Do binary products first; n-ary via `Fin` if needed. |
| Lem 8.4.3 | f₁ × ⋯ × f_n is uniformly continuous with modulus min_i ω_i(ε/n). | 8.4.1, 8.1.7 | `Analysis/PicardLindelof.v` · `lem_8_4_3` | todo | None. |
| Lem 8.4.4 | The diagonal X → Xⁿ has modulus ε/n. | 8.4.1, 8.1.7 | `Analysis/PicardLindelof.v` · `lem_8_4_4` | todo | None. |
| Cor 8.4.5 | h(x) := g(x, f x) is uniformly continuous with an explicit modulus. | 8.4.3, 8.4.4, 8.1.7 | `Analysis/PicardLindelof.v` · `cor_8_4_5` | todo | None. |
| Def 8.4.6 | g : [a, b] × [c, d] → R lifts to locators. | 8.2.4 | `Analysis/PicardLindelof.v` · `def_8_4_6` | todo | None. |
| Thm 8.4.7 | Picard–Lindelöf: for x₀, y₀, a, b, L with locators and g uniformly continuous, lifting to locators and L-Lipschitz in y, we compute l with a locator and f ∈ UL[x₀ − l, x₀ + l] with f(x) = y₀ + ∫_{x₀}^x g(t, f t) dt. | 8.2.2, 8.2.7–8.2.10, 8.3.11, 8.4.5, 8.4.6, 7.2.1, 6.6.1, 6.7.3, 6.7.6, U-5 | `Analysis/PicardLindelof.v` · `thm_8_4_7` | todo | None. |

## Remarks with formal content

Remarks are not numbered results, but these contain claims that later proofs use, or that are cheap to state.

| ID | Statement | Used by | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| Rem 4.3.4 | i : Q → F is an embedding. | 6.3.1, 5.1.1 | `Analysis/OrderedField.v` · `rem_4_3_4` | todo | None. |
| Rem 4.5.9 | Morphisms of Cauchy structures automatically preserve the distance laws, act on Cauchy approximations, and contain identities and compositions. | 4.5.18, 5.1.3 | `Analysis/CauchyStructure.v` · `rem_4_5_9` | todo | None. |
| Rem 4.6.2 | Given the other cut axioms, transitivity is equivalent to disjointness. | 4.6.1 | `Analysis/DedekindReals.v` · `rem_4_6_2` | todo | None. |
| Rem 5.2.2 | For S a set, contractibility of CS-hom(R_E, S) means existence plus pointwise uniqueness. | 5.2.1 | `Analysis/EuclideanReals.v` · `rem_5_2_2` | todo | None. |
| Rem 6.7.5 | Strong cotransitivity: for x < y with locators and z with a locator, (x < z) + (z < y). | 6.7.4 | `Analysis/Locator.v` · `rem_6_7_5` | todo | None. |
| Rem 6.7.7 | \|x\| = max(x, −x) has a locator when x has one. | 6.7.6 | `Analysis/Locator.v` · `rem_6_7_7` | todo | None (from `locator_join` and `locator_minus`). |
| Rem 6.9.8 | ‖locator(x)‖ ⇒ (Π q r, ‖q < r → …‖) ⇔ locatedness. | 6.9.7 | `Analysis/LocatorDigits.v` · `rem_6_9_8` | todo | None. |
| Rem 8.3.6 | Cor 8.3.5 only needs the mere existence of a Lipschitz constant. | 8.3.5 | `Analysis/BanachFixedPoint.v` · `rem_8_3_6` | todo | None. |

## Unnumbered prerequisites

The thesis uses these without stating them as numbered results. Each needs its own lemmas before the dependent rows can be done.

| ID | What | Needed by | Target | Status | Coq-HoTT has |
|---|---|---|---|---|---|
| U-1 | The ordered-field structure on R_C and on R_D (operations, Archimedean property): "we will not show this in detail". | 4.4.9, 4.6.6, 4.6.7, 6.9.6 | `Analysis/CauchyReals.v`, `Analysis/DedekindReals.v` | todo | None. |
| U-2 | The HoTT book development of R_H (§11.3): Cauchy completeness (11.3.2) and the embedding into R_D (Thm 11.3.50). | 4.5.13, 4.6.7 | `Analysis/HoTTBookReals.v` | todo | None. |
| U-3 | Finite sums, natural powers, factorials and geometric-series bounds in an ordered field. | 4.4.8, 6.9.2, 8.3.7, 8.3.8 | `Analysis/OrderedField.v` | todo | Partial: ring-level tools in `Classes/`; `nat_iter`. Search before adding. |
| U-4 | Integer floor on Q and the binomial bound used for log_c. | 6.9.4, 8.3.7 | `Analysis/OrderedField.v` | todo | `RoundUpStrict` (Classes/interfaces/round.v) only. |
| U-5 | The Riemann integral of a uniformly continuous function on [a, b] (as a limit of Riemann sums), with linearity, monotonicity, \|∫ f\| ≤ ∫ \|f\| and ∫ c = c(b − a). | 7.2.1, 8.4.7 | `Analysis/Integral.v` | todo | None. |
