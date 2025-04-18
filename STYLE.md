<!-- VSCode is able to do the TOC and section numbering using the "Markdown All
     in One" extension. It can also be manually updated. -->

## Table of Contents

- [Conventions And Style Guide](#conventions-and-style-guide)
  - [1. Organization](#1-organization)
    - [1.1. The Core library](#11-the-core-library)
    - [1.2. Non-core files](#12-non-core-files)
    - [1.3. Tests](#13-tests)
    - [1.4. Dependencies](#14-dependencies)
  - [2. Naming Conventions](#2-naming-conventions)
    - [2.1. General principles](#21-general-principles)
    - [2.2. Capitalization and spacing](#22-capitalization-and-spacing)
    - [2.3. Suffixes](#23-suffixes)
    - [2.4. Induction and recursion principles](#24-induction-and-recursion-principles)
    - [2.5. Path algebra functions](#25-path-algebra-functions)
    - [2.6. Equivalences](#26-equivalences)
  - [3. Records, Structures, Typeclasses](#3-records-structures-typeclasses)
    - [3.1. Two-component records](#31-two-component-records)
    - [3.2. Typeclasses](#32-typeclasses)
    - [3.3. When to declare instances](#33-when-to-declare-instances)
    - [3.4. Local and Global Instances](#34-local-and-global-instances)
    - [3.5. Using Typeclasses](#35-using-typeclasses)
    - [3.6. Truncation](#36-truncation)
    - [3.7. Coercions and Existing Instances](#37-coercions-and-existing-instances)
  - [4. Axioms](#4-axioms)
    - [4.1. Univalence, function extensionality and propositional resizing](#41-univalence-function-extensionality-and-propositional-resizing)
    - [4.2. Higher inductive types](#42-higher-inductive-types)
    - [4.3. Relationships between axioms](#43-relationships-between-axioms)
    - [4.4. Assuming axioms](#44-assuming-axioms)
    - [4.5. Technical note: Universe-polymorphic axioms](#45-technical-note-universe-polymorphic-axioms)
  - [5. Higher Inductive Types](#5-higher-inductive-types)
    - [5.1. Case analysis on private inductive](#51-case-analysis-on-private-inductive)
  - [6. Universe Polymorphism](#6-universe-polymorphism)
    - [6.1. Displaying universes](#61-displaying-universes)
    - [6.2. Universe annotations](#62-universe-annotations)
    - [6.3. Unexpected universes](#63-unexpected-universes)
    - [6.4. Lifting and lowering](#64-lifting-and-lowering)
    - [6.5. Universes and HITs](#65-universes-and-hits)
  - [7. Transparency and Opacity](#7-transparency-and-opacity)
  - [8. Imports/exports](#8-importsexports)
  - [9. Formatting](#9-formatting)
    - [9.1. Location of commands](#91-location-of-commands)
    - [9.2. Indentation](#92-indentation)
    - [9.3. Line lengths and comments](#93-line-lengths-and-comments)
    - [9.4. Tactic scripts](#94-tactic-scripts)
    - [9.5. Placement of Arguments and types](#95-placement-of-arguments-and-types)
  - [10. Implicit Arguments](#10-implicit-arguments)
  - [11. Coding Hints](#11-coding-hints)
    - [11.1. Notations](#111-notations)
    - [11.2. Unfolding definitions](#112-unfolding-definitions)
    - [11.3. Finding theorems](#113-finding-theorems)
    - [11.4. Simpl nomatch](#114-simpl-nomatch)
    - [11.5. Available tactics](#115-available-tactics)
  - [12. Contributing to the library](#12-contributing-to-the-library)
    - [12.1. Fork \& Pull](#121-fork--pull)
    - [12.2. Approval of pull requests](#122-approval-of-pull-requests)
    - [12.3. Commit messages](#123-commit-messages)
    - [12.4. Creating new files](#124-creating-new-files)
    - [12.5. Continuous Integration](#125-continuous-integration)
    - [12.6. Git rebase](#126-git-rebase)
    - [12.7. Timing scripts](#127-timing-scripts)
  - [13. Bugs in Coq](#13-bugs-in-coq)
    - [13.1. Reporting bugs](#131-reporting-bugs)
    - [13.2. Minimizing bugs](#132-minimizing-bugs)

# Conventions And Style Guide

## 1. Organization

### 1.1. The Core library

We do not use the Coq standard library, instead working from scratch.
We do not use the Coq universes `Prop` and `SProp`.

The Coq files of the HoTT library live in the `theories/` directory.
Many are in subdirectories, and a subdirectory `Foo/` often has a
corresponding file `Foo.v` that imports everything in the subdirectory.

- `Basics/*`: These files contain basic definitions that underlie
  everything else. Nothing in the Basics directory should depend on
  anything outside the Basics directory. The file `Basics` in the
  root imports everything from the directory `Basics/`, so most other
  files in the library start with `Require Import HoTT.Basics.` (See
  remarks below on qualified imports.)

- `Types/*`: This subdirectory contains a file corresponding to each
  basic type former (e.g. sigma-types, pi-types, etc.), which proves
  the "computational" rules for the path-types, transport, functorial
  action, etc. of that type former. It also `Types/Equiv`,
  which proves that being an
  equivalence is an hprop. The univalence axiom is introduced, as a
  typeclass (see below) in `Types/Universe`. Function extensionality
  is introduced in `Basics/Overture` for dependency reasons, but
  developed further in `Types/Forall` and `Types/Arrow`. Some type
  formers are defined in their corresponding `Types/` file, while
  others are defined in `Basics/Overture` for dependency reasons but
  studied further in their `Types/` file. Files in `Types/` should
  not depend on anything except `Basics` and other `Types/` files.

- `Universes/*`: Files related to universe levels, classifying maps, or
  to particular subuniverses, including `UniverseLevel`, `Smallness`,
  `ObjectClassifier`, `BAut`, `HProp`, `HSet`, `DProp`, and `TruncType`.
  The files here depend on files in `Types/`, and occasionally on some
  files mentioned below.

- There are files in the root `theories/` directory, including
  `EquivGroupoids`, `ExcludedMiddle`, `Factorization`, `HFiber`,
  `Extensions`, `Projective`, `Idempotents`, etc. These contain more
  advanced results which may depend on files in the whole library. We
  try to limit the number of files in the top-level folder, and would
  like to reduce the number.

- `Misc/*`: Some files don't have a logical home, so they instead live here. We
  try to limit the number of files living here.

- `WildCat/*`: Files related to wild categories. They are used
  extensively in the library, so we try to minimize the files they
  depend on.

- `Modalities/*`: Files involving modalities. The most important files
  here are `Modalities/ReflectiveSubuniverse` and `Modalities/Modality`.

- `Basics/Trunc`, `TruncType`, `Truncations/*`: Files involving truncations.
  There are interdependencies between the files in `Truncations/` and some
  of the `Modalities/*` files.

- `Equiv/*`: Files showing that various definitions of equivalence agree.

- `Pointed/*`: Files related to pointed types.

- `HIT/*`: Files involving higher inductive types. Each higher
  inductive type is defined in a corresponding file (see conventions
  on defining HITs, below). These are only lightly used in the rest
  of the library. See `Colimits/*` for the HIT that is most commonly used.

- `Diagrams/*`: Files involving graphs and diagrams, used for colimits and
  limits.

- `Colimits/*`: Files involving colimits. `Colimits/GraphQuotient`
  defines graph quotients as a HIT, and other constructions are
  built from this.

- `Limits/*`: Files involving limits.

- `Cubical/*`: Files involving cubical methods in HoTT.

- `Algebra/*`: Files related to algebra.

- `Analysis/*`: Files related to analysis.

- `Sets/*`: Files related to set theory.

- `Spaces/*`: Files involving various spaces, including `Spaces/Nat/*`,
  `Spaces/Pos/*`, `Spaces/Int/*`, `Spaces/Finite/*`, `Spaces/List/*`,
  `Spaces/Circle`, `Spaces/Torus/*`, `Spaces/Universe`, `Spaces/BAut/*`
  and `Spaces/No/*` (the surreal numbers),

- `Homotopy/*`: Files related to synthetic homotopy theory.
  Also contains `Homotopy/IdentitySystems` and `Homotopy/EncodeDecode`,
  which give results for computing path types.

- `Spectra/*`: Files related to spectra in the sense of stable
  homotopy theory.

- `Tactics, Tactics/*`: some more advanced tactics.

- `HoTT`: This file imports and exports everything in the core (that
  is, everything mentioned above). Thus, in a development based on
  the HoTT library, you can say simply `Require Import HoTT` to pull
  in everything (but don't do this for files in the core itself).

- `theories/Classes/*`: The math classes library. While we don't
  regard this as part of the core library, and don't explicitly
  export the contents in `HoTT`, some files in the classes library
  are used by files in the core library.

### 1.2. Non-core files

- `theories/Axioms/`: Contains `FunextAxiom` and `UnivalenceAxiom`:
  You can import these files to assume the axioms globally (in the
  core, we track them with typeclasses).

- `theories/Metatheory/*`: Contains `UnivalenceImpliesFunext`,
  `IntervalImpliesFunext`, `ImpredicativeTruncation`, `PropTrunc`,
  `Nat` (a definition of the natural numbers using univalence and
  propositional resizing), and other meta-theoretic results.

- `theories/Utf8` and `theories/Utf8Minimal`: optional Unicode
  notations for the basic definitions (we avoid Unicode in the core
  library).

- `theories/Categories/*`: The categories library, which is not
  considered part of the core (e.g. it uses unicode), but nevertheless
  lives in `theories/`.

- `contrib/HoTTBook`: This file lists all the definitions and theorems
  from the HoTT Book and gives pointers to where the corresponding
  fact is defined in the library. It is not intended to be a
  formalization of the book, but rather a guide to the library for a
  reader familiar with the book.

- `contrib/HoTTBookExercises`: This file contains both formalizations
  of the exercises from the HoTT Book, and pointers to the
  corresponding facts in the library. The latter pointers serve the
  same purpose as `contrib/HoTTBook`, but the former may contain
  alternative solutions, such as ones that depend only on the concepts
  that are introduced prior to the exercise in the book.

- `contrib/*`: Other work in progress, or files not judged appropriate
  for the core.

### 1.3. Tests

- `test/*`: Tests of the library. See the file `test/README.md` for more
  information.

### 1.4. Dependencies

A dependency graph of all the files in the library can be found on the
[wiki][wiki]; this may be helpful in avoiding circular dependencies.
It is updated automatically by Travis (see below) on every push to the
master branch.

[wiki]: https://github.com/HoTT/HoTT/wiki

## 2. Naming Conventions

### 2.1. General principles

In general, the name of a theorem (or definition, or instance, etc.)
should begin with the property (or structure, or class, or record,
etc.) being proven, and then state the object or construction it is
being proven about. For instance, `isequiv_idmap` proves `IsEquiv
idmap`, and `equiv_compose` constructs an "Equiv" record by composing
two given equivalences.

In particular, a prefix of `path_` means a theorem that constructs a
path in some type. For instance, `path_sigma` is a theorem
constructing paths in a sigma-type.

More generally, where applicable the order of parts in a lemma name
should roughly respect their placement in (the syntax tree of) the
goal, from outermost to deepest. For instance, `path_equiv`
constructs a path in the type `Equiv f g`, while `isequiv_path_equiv`
shows that `path_equiv` is an equivalence.

### 2.2. Capitalization and spacing

Names of types, such as `Unit` and `Equiv` and `IsHProp`, should
generally be capitalized. Names of functions and definitions should
be lowercase, including the names of types when they appear therein.
Thus, for instance, the theorem that `Unit` is contractible is
`contr_unit : Contr Unit`.

Multiple-word names, especially in lowercase, should generally be
separated with underscores. We make an exception for names of types
beginning with `is`, such as `IsEquiv` and `IsTrunc`.

### 2.3. Suffixes

A suffix of `D` indicates a dependent version of something ordinarily
non-dependent. For instance, `ap` applies to non-dependent functions
while `apD` applies to dependent ones. When possible, the
non-dependent version should be an instantiation of the dependent one
using constant type families, but sometimes they are more different
than this, usually due to the fact that `transport_const` is not the
identity (e.g. `ap` and `apD`).

When there is more than one theorem that seems to merit the same name,
and no obvious concise way to distinguish them, one of them can be
given a prime suffix, e.g. we have `path_sigma` and `path_sigma'`.
Do this with caution.

### 2.4. Induction and recursion principles

In conformity with the HoTT Book, the induction principle of a
(perhaps higher) inductive type `thing` (that is, its dependent
eliminator) should be named `thing_ind`, while its recursion principle
(non-dependent eliminator) should be named `thing_rec`.

However, by default, when you declare a (non-higher) inductive type,
Coq automatically defines induction principles named `thing_rect`,
`thing_rec`, and `thing_ind` that vary only in the sort of their
target (`Type`, `Set`, or `Prop`). In order to turn this off, you
must say `Local Unset Elimination Schemes` before defining an
inductive type. You can then have Coq automatically generate the
correctly named induction principles with

```coq
Scheme thing_ind := Induction for thing Sort Type.
Scheme thing_rec := Minimality for thing Sort Type.
```

Unfortunately, Coq's built-in tactics `induction` and `elim` assume
that the induction principles are named in Coq's default manner. We
are hoping that this will be [fixed eventually][inductionbug], but in
the meantime, to make those tactics work, you need to also say

```coq
Definition thing_rect := thing_ind.
```

(We have not turned on `Global Unset Elimination Schemes` because this
would cause `induction` and `elim` to fail for all newly defined
inductive types unless these `Scheme` commands are also given, which
might be an unpleasant and confusing surprise to people who haven't
read (or don't remember) these instructions.)

Note that elimination schemes are always off for `Private Inductive`
types such as are used to hack HITs. For HITs, you must always define
both the induction and recursion principles by hand, as described
in the appropriate section below.

Some types have a "coinduction" or "corecursion" principle; these
should have instead the suffix `_coind` or `_corec`.

Finally, a type will often have a universal property expressed by
saying that its induction or recursion (or coinduction or corecursion)
principle is an equivalence. These should be named according to the
naming conventions for equivalences below, e.g. `isequiv_thing_rec`
and `equiv_thing_rec`.

[inductionbug]: https://github.com/coq/coq/issues/3745

### 2.5. Path algebra functions

The path algebra functions defined mainly in `Basics/PathGroupoids`
follow a particular set of naming conventions. Generally they are
named according to the head constant of their primary input and the
pattern of paths appearing therein. For more details, see the
comments in `Basics/PathGroupoids`.

### 2.6. Equivalences

When defining an equivalence, the standard naming procedure is to

- Define the function in one direction with a name, say `foo`.
- Define an `IsEquiv` instance for this function, called `isequiv_foo`.
- Define an `Equiv` record putting them together, called `equiv_foo`.

The inverse function can then be referred to as `foo ^-1`. Avoid
using `equiv_foo` unless you really do need an `Equiv` object, rather
than a function which happens to be an equivalence.

On the other hand, sometimes it is easier to define an equivalence
by composing together existing equivalences, in which case one goes
immediately to the last step, defining `equiv_foo`. If the equivalence
is used frequently as an ordinary function, one might also define `foo`
as the underlying function of `equiv_foo`; see `path_equiv`, as an example.

## 3. Records, Structures, Typeclasses

We use Coq Records when appropriate for important definitions. For
instance, being an equivalence (`IsEquiv`) and equivalences (`Equiv`) are
both Record types (in fact, the former is a typeclass). The file
`Basics/Tactics` contains a tactic `issig` for proving semiautomatically
that record types are equivalent to the corresponding sigma-types, so
that the relevant general theorems can be applied to them.

### 3.1. Two-component records

Sometimes a two-component record is better defined as a sigma-type,
especially if it is a "subset type" whose second component is an
hprop. For instance, this has the advantage that we do not need new
names for its constructor and its fields, and we can apply theorems in
`Types/Sigma` to it directly rather than via `issig`.

TODO: Decide about `hProp` and `hSet` and `TruncType` (issue [#514](https://github.com/HoTT/HoTT/issues/514)).

### 3.2. Typeclasses

We are using typeclasses in preference to canonical structures.
Typeclasses are particularly convenient for h-properties of objects.
Here are some of the typeclasses we are using:

- equivalences: `IsEquiv`
- truncation levels: `IsTrunc` (a notation for `IsTrunc_internal`)
- axioms (see below): `Funext`, `Univalence`
- subuniverses: `In`, `Replete`, `MapIn`, `IsConnected`, `IsConnMap`

`IsHSet`, `IsHProp`, and `Contr` are notations for `IsTrunc 0`,
`IsTrunc -1`, and `IsTrunc -2` respectively. See the comments in
`Overture.v` for more details.

### 3.3. When to declare instances

When constructing terms in a typeclass record such as `IsEquiv`, `Contr`,
or `IsTrunc`, one has the choice to declare it as an `Instance`, in which
case it is added to the hint database that is searched when Coq tries
to do typeclass instance resolution. Care must be taken with this, as
indiscriminately adding theorems to this database can easily result in
infinite loops (or at least very long loops).

In general, it seems to be better not to add instances which suggest
an open-ended search. E.g. the theorem that truncation levels are
closed under equivalence is a bad candidate for an `Instance`, because
when Coq is searching for a proof of `Contr B` this theorem could
cause it to look through all possible types A for an equivalence `A
<~> B` and a proof of `Contr A`. Results of this sort should be
proven as `Definition`s or `Theorem`s, not as `Instance`s. If you
need to use a result of this sort in the middle of a proof, use a
tactic like `pose` or `assert` to add a particular instance of its
conclusion to the context; then it will be found by subsequent
typeclass resolution.

If you have determined through trial and error that a particular
result should not be an `Instance` (e.g. when making it an `Instance`,
a tactic in some other proof loops, but changing it to a `Definition`
prevents this), please add a comment to that effect where it is
defined. This way no one else will come along and helpfully change it
back to an `Instance`.

If a particular fact should not be made an ordinary instance, it can
still be made an "immediate instance", meaning that Coq will use it
automatically to solve a goal _if_ its hypotheses are already present
in the context, but will not initiate an instance search for those
hypotheses otherwise. This avoids infinite instance-search loops. To
declare a fact as an immediate instance, make it a `Definition` rather
than an `Instance` and then say

```coq
Hint Immediate foo : typeclass_instances.
```

### 3.4. Local and Global Instances

Each `Instance` declaration has an associated "locality attribute".
The `Local` attribute makes the instance local to the current section,
module, or file (although its _definition_ will still be visible
globally, it won't be in the instance database for typeclass
resolution outside its containing section, module or file). The
`Global` attribute makes the instance available in any file that
"loads" this file via the `Require` command, which is a transitive
relation including all direct and indirect dependencies of the current
file. The `#[export]` locality uses the module system to manage the
scope of the typeclass hint, so that the hint is available wherever
the module is opened using the `Import` keyword, but not transitively
(analogous to "open" in ML languages).

When declaring an `Instance` you should prefer the `export` locality attribute
to the `Global` locality attribute. Inside a section, you should
explicitly annotate instance declarations as `Local` or `#[export]`
to avoid ambiguity. Outside a section, you may omit the annotation,
and in this case Coq defaults to the `export` attribute since 8.18.

### 3.5. Using Typeclasses

Try to avoid ever giving a name to variables inhabiting typeclasses.
When introducing such a variable, you can write `intros ?` to put it
in the hypotheses without specifying a name for it. When using such a
variable, typeclass resolution means you shouldn't even need to refer
to it by name: you can write `_` in tactics such as `refine` and Coq
will find typeclass instances from the context. Even `exact _` works.
(You can usually also use `typeclasses eauto` or `eauto with
typeclass_instances`, but `exact _` is preferable when it works, as it
is shorter and uses a tactic name the reader is presumably already
familiar with.)

Unfortunately, it is not currently possible to write `_` in a
`refine`d term for an inhabitant of a typeclass and have Coq generate
a subgoal if it can't find an instance; Coq will fail if it can't
resolve a typeclass variable from the context. You have to `assert`
or `pose` such an inhabitant first, or give an explicit term for it.

Note that when you don't give a name to a variable, Coq often names it
`H` or some modification thereof. For that reason, it's often better
avoid using `H` for your own explicitly named variables, since if you
do and later on someone introduces a new unnamed hypothesis that Coq
names `H`, your name will result in a conflict. Conversely, we
sometimes give a hypothesis a name that won't be used, to preempt
such conflicts, such as `{ua : Univalence}` or `{fs : Funext}`.

One gotcha about typeclass arguments is that they cannot be inferred
automatically when preceded by non-implicit arguments. So for instance
if we write

```coq
Definition foo (A : Type) `{Funext}
```

then the `Funext` argument will not generally be inferable. Thus,
typeclass arguments should generally come first if possible. In
addition, note that when section variables are generalized at the
close of a section, they appear first. Thus, if anything in a section
requires `Funext` or `Univalence`, those hypotheses should go in the
`Context` at the top of the section in order that they'll come first
in the eventual argument lists.

### 3.6. Truncation

The conventions for the typeclass `IsTrunc` are:

- We prefer to do inference with `IsTrunc n A` rather than `IsTrunc n (a = b)`.
- We prefer to expand `IsTrunc n (forall a, P a)` into `forall a,
IsTrunc n (P a)`, and similarly for other data types. For instance,
  `IsTrunc n (A * B)` gets transformed to `IsTrunc n A` and `IsTrunc n B`,
  as a goal.
- Due to the desire to use `IsTrunc` rather than `Contr`, we have
`Contr` as a notation for `IsTrunc minus_two`.
<!-- I don't think this applies anymore:
   Due to a
  [bug in coq](https://coq.inria.fr/bugs/show_bug.cgi?id=3100), we
  need to iota-expand some explicit instances of `Contr`, such as
  `Instance foo : Contr bar := let x := {| center := ... |} in x.`
  rather than `Instance foo : Contr bar := { center := ... }.`
-->

### 3.7. Coercions and Existing Instances

A ["coercion" from `A` to
`B`](https://rocq-prover.org/refman/addendum/implicit-coercions.html)
is a function that Coq will insert silently if given an `A` when it
expects a `B`, and which it doesn't display. For example, we have
declared `equiv_fun` as a coercion from `A <~> B` to `A -> B`, so that
we can use an equivalence as a function without needing to manually
apply the projection `equiv_fun`. Coercions can make code easier to
read and write, but when used carelessly they can have the opposite
effect.

When making a record field `proj1` into a coercion, we prefer that the
coercion should not be reversible, because of the additional
complexity that reversible coercions add to unification problems, and
we prefer that coercions be conspicuous when reading the source code.
Therefore, define the coercion on its own line after the record
declaration as `Coercion proj1 : MyRec >-> FieldType` rather than
using the reversible coercion syntax `proj1 :> FieldType`.

(This library also uses the `:>` notation when needed for path types
to indicate the type in which the paths are taken: `x = y :> A` for
`x, y : A`.)

If `proj1` is a record field whose type is a typeclass and we'd
like to add this field as a typeclass instance, then we prefer
the concise ["substructure"
notation](https://rocq-prover.org/refman/addendum/type-classes.html#substructures)
`proj1 :: ClassType` over the separate vernacular command
`Existing Instance proj1.` after the record declaration.

## 4. Axioms

### 4.1. Univalence, function extensionality and propositional resizing

The "axioms" of `Univalence`, `Funext` (function extensionality) and
`PropResizing` (propositional resizing) are typeclasses rather than
Coq `Axiom`s. (But see the technical note below on universe
polymorphism.) In the core, we use these typeclasses to keep track
of which theorems depend on the axioms and which don't.

This means that any theorem which depends on one or the other must
take an argument of the appropriate type. It is simple to write
this using typeclass magic as follows:

```coq
Theorem uses_univalence `{Univalence} (A : Type) ...
```

The axiom-term witnessing univalence does not have to be named, nor
does it have to be passed explicitly to any other lemma which uses
univalence; once it is in the typeclass context, it should be found
automatically.

For longer developments using `Univalence` or `Funext`, it is probably
preferable to assume it as part of the context.

```coq
Section UsesUnivalence.
  Context `{Univalence}.
```

Now everything defined and proven in this section can use univalence
without saying so explicitly, and at the end of the section it will be
implicitly generalized if necessary. (Results that don't use univalence
won't get an univalence argument.) The backquote syntax
``{Univalence}` allows us to avoid giving a name to the hypothesis.
(Backquote syntax is also used for implicit generalization of
variables, but that is not needed for univalence and funext.)

### 4.2. Higher inductive types

Every higher inductive type technically assumes some `Axioms`. These
axioms are asserted globally by the corresponding `HIT/` file or
`Colimits/GraphQuotient`, since there's not much point to assuming a
HIT without the axioms that make it work.

### 4.3. Relationships between axioms

The file `UnivalenceImpliesFunext` shows, as its name implies, that
univalence implies funext. However, this file is not needed in
practice, since in `Types/Universe` we assert axiomatically that
univalence implies funext.

Similarly, the file `HIT/IntervalImpliesFunext` proves funext from the
interval type assumed in `HIT/Interval`, so if you import this file
then funext is always true automatically (just as if you'd imported
`FunextAxiom`). Of course, once you've imported `HIT/Interval` it is
always possible to prove funext by hand, but by importing
`HIT/Interval` without `HIT/IntervalImpliesFunext` you can still use
the interval in some places and track moral uses of funext elsewhere.

### 4.4. Assuming axioms

When working in a derived development using the HoTT library, you may
import the files `FunextAxiom` and/or `UnivalenceAxiom` to assume
these axioms globally. You should _not_ assume these axioms yourself
by writing something such as `Axiom fs : Funext`. The problem with
this is that if two different files do this, and then a third file
imports them both, it ends up with two different witnesses for
`Funext`, not definitionally equal. Thus, derived objects that should
be judgmentally equal might fail to be so because they use different
witnesses.

### 4.5. Technical note: Universe-polymorphic axioms

In order for the "axioms" univalence and funext to be usable at
different universe levels, the types `Univalence` and `Funext` do not
technically assert the axioms themselves. Rather they assert
inhabitants of dummy types, while the axioms are actually declared
globally but depending on elements of those dummy types. This is not
something you generally need to worry about; see the comments in
`Basics/Overture` for more information.

However, one situation in which this matters is when proving an
implication between axioms. Because `Univalence` and `Funext` are
dummy types, we cannot actually prove that `Univalence -> Funext`.
Instead we define placeholders with names like `Funext_type` and
`Univalence_type` that have the actual type that the axiom would have
except for the polymorphism trick, and prove that `Univalence_type ->
Funext_type`. Then we feel justified in asserting as a further
`Axiom` that `Univalence -> Funext`.

When introducing further axioms, please use this same naming
convention. For another example, see `ExcludedMiddle.v`.

## 5. Higher Inductive Types

Most higher inductive types are defined in the `HIT/`
directory, but `Colimits/GraphQuotient` also uses a HIT.
All are defined using [Dan Licata's "private inductive
types" hack][hit-hack] which was
[implemented in Coq](https://coq.inria.fr/files/coq5_submission_3.pdf)
by Yves Bertot. This means the procedure for defining a HIT is:

1. Wrap the entire definition in a module, which you will usually want
   to export to the rest of the file containing the definition.

2. Define a `Private Inductive` type whose constructors are the
   desired point-constructors of your HIT.

3. Assert the desired path-constructors as `Axiom`s.

4. Define the induction principle, with all the correct hypotheses, by
   matching against the point-constructors. There is an important
   additional hack here. If the path-hypotheses are not "used"
   anywhere in the `match`, then Coq will notice and will consider two
   invocations of the induction principle to be judgmentally equal if
   they have the same point-hypotheses, even if their path-hypotheses
   differ. Thus, it is important to "use" the path-hypotheses
   trivially by making the `match` return a function which is then
   applied to all the path-hypotheses. For example, with the circle
   we write `fun x => match x with base => fun _ => b end l` instead
   of `fun x => match x with base => b end`.

5. Assert the "computation rules" for the path-constructors, in the
   form of propositional equalities, as `Axiom`s.

6. Close the module. It is important to do this immediately after
   defining the induction principle, so that the private inductive
   type can't be matched against anywhere else; any other uses of it
   have to call the correct induction principle.

7. Usually, you will want to also define a non-dependent recursor and
   its computation rules as well.

Look at some of the existing files in `HIT/*` for examples.

Going forward, we try to use `Colimits/GraphQuotient` to define further
higher inductive types.

[hit-hack]: http://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/

### 5.1. Case analysis on private inductive

You may get this error at `Qed`/`Defined` if unification unfolded
the induction principle and used its value to produce the proof term.

To fix this, you need to identify which tactic produced the problematic term,
then either avoid unification by annotating more (e.g. `apply (@foo bla)`
instead of `apply foo`), or guide unification by manipulating the goal
(e.g. using `rewrite` with the lemma witnessing the computation rule of
the inductive principle) or making related definitions opaque.

## 6. Universe Polymorphism

We have Coq's "universe polymorphism" feature turned on throughout
the library. Thus, all definitions are universe polymorphic by
default, i.e. they can be applied to types that live in any universe
level.

Usually, this is not something you have to worry about, as Coq tries
to automatically make everything maximally polymorphic, but sometimes
a bit of attention is required. If Coq is claiming that an instance
is not found which is "obviously" present, or a term doesn't have a
type that it "clearly" does (or, of course, if it complains about a
universe inconsistency), then a universe problem may be the culprit.

### 6.1. Displaying universes

If you suspect a universe problem, usually the first thing to do is to
turn on the display of universes with the command `Set Printing
Universes`. This causes Coq to print the universe parameters of every
occurrence of a definition when displaying the current proof state or
when giving an error message, and also to print the universe
parameters and the constraints imposed on them when displaying a
definition with `Print` or `About` or a typechecking a term with
`Check`. (Nowadays Coq is sometimes smart enough to display universes
automatically when giving an error message that would otherwise look
like "unable to unify `A` with `A`".) To display the current universe
_constraints_ during a proof, use `Show Universes` (this is not to be
confused with `Print Universes`, which displays the current list of
_global_ universes; the latter is usually quite small with universe
polymorphism enabled).

The universe parameters of an occurrence of a definition are displayed
as `foo@{Top.1 Top.2}`. Here `foo` is a definition which takes two
universe parameters, and this occurrence of `foo` has those two
parameters instantiated to the universes `Top.1` and `Top.2`. When
displaying a definition with `Print` or `About`, its universe
parameters are shown in a comment below the definition, followed by
`|-` and a list of the constraints on those parameters.

In general, the universe parameters of a definition are automatically
computed from the parameters of its constituents, and the order of the
parameters is likewise induced by the order in which they occur in the
definition. This means you must generally pay close attention to the
output of `Print` or `About` to learn which universe parameter is
which, and insignificant-seeming changes in a definition can sometimes
cause changes in the number or order of its universe parameters.

Note that `Check foo` will often give a different list of universes
than `Print foo` and `About foo`. This is because the latter two
display information about `foo` as a _definition_, while `Check`
treats its argument as a _term_ to be typechecked, and Coq is willing
to collapse some universes during typechecking.

### 6.2. Universe annotations

You can exert a certain degree of control over universe polymorphism
by using explicit universe annotations, which use the same syntax as
the display of universes: if you write `foo@{i j}`, that means `foo`
with its two universe parameters instantiated to the universes `i` and
`j`. You are required to supply exactly the right number of
universes, and be careful about the order in which they occur.

It is very important to note that universe names such as `i` and `j`
are _definition local_ and _implicitly declared_. This means that
whenever you write `i` inside a universe annotation, Coq implicitly
declares a universe named `i`, and all occurrences of the universe `i`
_in the same definition_ refer to the same universe. When the
definition is complete, this universe will become one of its universe
parameters. An annotation named `i` in a different definition will
instead become one of _that_ definition's parameters. Thus, if you
define `foo` using a universe `i`, and then define `bar` which uses
`foo`, in order to force a particular universe parameter of `bar` to
coincide with `i` in `foo`, you must annotate the occurrences of `foo`
in `bar` appropriately.

It is also possible to explicitly declare and name universes globally
with the `Universe` command, usually within a section. Universes
declared with `Universe` will be discharged on each section definition
independently.

The universe variables of a definition can be declared and their
constraints can be chosen by hand. This is good practice for
delicate situations, as it serves to both document the expected
constraints and to cause an error if a future change causes the
universe variables or constraints to change. We also use `Check`
commands, mostly in `test/*`, to verify that universe variables
before as expected.

There are several uses for universe annotations. One is to force a
definition to have fewer universe parameters than it would otherwise.
This can sometimes improve performance: if you know that in practice,
several of the universes occurring in a definition will always be the
same, then saving Coq the burden of carrying them all around
separately can sometimes make it run faster. Additionally, reducing
the number of universe parameters in a definition can make it
significantly easier to universe-annotate uses of that definition
later on.

Another reason for universe annotations is to make a definition _more_
universe polymorphic. In some situations, in the absence of
annotations Coq will automatically collapse one or more universe
parameters which could be kept separate if annotated. It is not clear
under exactly what situations this occurs, but one culprit appears to
be section variables: if you declare a section variable which you need
to be universe polymorphic, you may need to annotate it.

(Another occasional culprit of less-polymorphic-than-expected
definitions seems to be giving type parameters without a type. At
least in some situations, writing `Definition foo {A B} ...` rather
than `Definition foo {A B : Type} ...` can cause `A` and `B` to live
in the same universe.)

Finally, universe annotations can also be necessary to instruct Coq
how to instantiate the universes when using a definition. In some
situations, Coq seems to make a default guess that doesn't work
(perhaps collapsing some universes that need to remain distinct) and
then complains without trying anything else; an annotation can point
it in the right direction.

In Coq, the bottom universe is denoted `Set`, but this does not
mean that its elements 0-truncated. In `Basics/Overture`, we
define a notation `Type0` for this universe.

Coq also has universes `Prop` and `SProp` which we do not use in
the library.

### 6.3. Unexpected universes

If you ever need to pay close attention to universes, it is useful to
know that there are several ways in which extra universe parameters
can creep into a definition unexpectedly. Here are a few.

The `induction` tactic invokes the appropriate induction principle,
which is a function generally named `*_ind` or `*_rect` (see notes on
naming conventions above). This function, in turn, requires a
universe parameter describing the size of its output. Therefore, if
you prove something by `induction` that is generalized over a "large"
argument (e.g. a type or a type family), the resulting definition will
pick up an extra universe parameter that's strictly larger than the
argument in question. One way to avoid this is to instead use a
`Fixpoint` definition, or the tactic `fix`, along with `destruct`.
There is a tactic `simple_induction` defined in `Basics/Tactics` whose
interface is almost the same as `induction` but does this internally,
although it only works for induction over `nat` and `trunc_index`.

If you apply the `symmetry` tactic when constructing an equivalence to
reverse the direction of the goal, then rather than applying
`equiv_inverse` directly it goes through the `Symmetric` typeclass.
This involves a universe for the size of the type _on which_ the
symmetric relation lives, which in the case of `Equiv` is the
universe. Thus, applying `symmetry` to an `Equiv` introduces a
strictly larger universe. A solution is to `apply equiv_inverse`
instead. Similarly, use `equiv_compose'` instead of `transitivity`.

Typeclass inference doesn't always find the simplest solution, and may
insert unnecessary calls to instances that introduce additional
universes. One solution is to alter the proofs of those instances as
described above; another is to call the instance(s) you need
explicitly, rather than relying on typeclass inference to find them.

Sometimes binders without type annotations, like `forall n, foo n`
where `foo : nat -> Type0`, will produce a fresh universe for
the variable's type, eg `forall n : (? : Type@{fresh}), foo n`,
which will remain in the definition as a phantom type:
`fresh |= forall n : nat, foo n`. Annotating the binder will get rid of it.
See also [bug #4868](https://coq.inria.fr/bugs/show_bug.cgi?id=4868).

### 6.4. Lifting and lowering

The file `Universes/UniverseLevel` contains an operation `Lift` which
lifts a type from one universe to a larger one, with maps `lift` and
`lower` relating the two types and forming an equivalence. There are
primed versions `Lift'`, `lift'`, and `lower'` which allow the two
universe levels to possibly be the same.

In the past, `Lift` was used to force universe levels to be distinct,
but now that Coq supports constraints between universe variables,
this is no longer needed in practice.

The file `Universes/Smallness` contains results allowing us to show
that a type lives in a certain universe.

### 6.5. Universes and HITs

Another use for universe annotations is to force HITs to live in the
correct universe. Coq assigns a universe level to an inductive type
based on the levels of its indices and constructors, which is correct
for ordinary inductive types. However, the universe level of a HIT
should depend also on the levels of its path-constructors, but since
these are not actually constructors of the `Private Inductive`, Coq
doesn't take them into account.

We have not yet formulated a general method for resolving this. In
the few cases when it arises, it should be solvable with universe
annotations, but we have not yet implemented such a fix; see bug #565.

## 7. Transparency and Opacity

If the value of something being defined matters, then you must either
give an explicit term defining it, or construct it with tactics and
end the proof with `Defined.` But if all that matters is that you
have defined something with a given type, you can construct it with
tactics and end the proof with `Qed.` The latter makes the term
"opaque" so that it doesn't "compute".

If something _can_ be made opaque, it is generally preferable to do
so, for performance reasons. However, many things which a traditional
type theorist would make opaque cannot be opaque in homotopy type
theory. For instance, none of the higher-groupoid structure in
PathGroupoids can be made opaque, not even the "coherence laws". If
you doubt this, try making some of it opaque and you will find that
the "higher coherences" such as `pentagon` and `eckmann_hilton` will
fail to typecheck.

In general, it is okay to construct something transparent using
tactics; it's often a matter of aesthetics whether an explicit proof
term or a tactic proof is more readable or elegant, and personal
aesthetics may differ. Consider, for example, the explicit proof term
given for `eckmann_hilton`: some may consider it optimally elegant,
while others would prefer to be able to step through a tactic proof to
understand what is happening step-by-step.

One thing to beware of is explicit `match` terms that require `in` or
`return` annotations, as these are particularly difficult for
newcomers to understand. Avoiding them is not a hard and fast rule,
but when there is a short proof using tactics that produces an
acceptable proof term, it should probably be preferred.

The important thing is that when defining a transparent term with
tactics, you should restrict yourself to tactics which maintain a high
degree of control over the resulting term; "blast" tactics like
`autorewrite` should be eschewed. Even plain `rewrite` is usually to
be avoided in this context: although the terms it produces are at
least predictable, they are one big `transport` (under a different
name) whereas a term we would want to reason about ought to be
constructed using smaller pieces like `ap` and `concat` which we can
understand.

Here are some acceptable tactics to use in transparent definitions
(this is not an exhaustive list):

- `intros`, `revert`, `generalize`, `generalize dependent`
- `pose`, `assert`, `set`, `cut`
- `transparent assert` (see below)
- `fold`, `unfold`, `simpl`, `cbn`, `hnf`, `change`
- `case`, `elim`, `destruct`, `induction`
- `apply`, `eapply`, `assumption`, `eassumption`, `exact`
- `refine`, `nrefine`, `srefine`, `snrefine` (see below for the last three)
- `rapply`, `napply`, `tapply`, `srapply`, `snapply`, `stapply` (see below)
- `lhs`, `lhs_V`, `rhs`, `rhs_V`
- `reflexivity`, `symmetry`, `transitivity`, `etransitivity`
- `by`, `done`

Conversely, if you want to use `rewrite`, that is fine, but you might
then make the thing you are defining opaque. If it turns out later
that you need it to be transparent, then you should go back and prove
it without using `rewrite`.

Currently, there are some basic facts in the library, such as the
"adjointify" lemma, which are proven using `rewrite` and hence are at
least partially opaque. It might be desirable one day to prove these
more explicitly and make them transparent, but so far it has not been
necessary.

Note that it _is_ acceptable for the definition of a transparent
theorem to invoke other theorems which are opaque. For instance,
the `isequiv_adjointify` lemma itself is actually transparent, but it
invokes an opaque sublemma that computes the triangle identity (using
`rewrite`). Making the main lemma transparent is necessary so that
the other parts of an equivalence -- the inverse function and
homotopies -- will compute. Thus, a transparent definition will not
generally be "completely transparent".

It is possible to make subterms of a term opaque by using the
`abstract` tactic, although that requires grouping the entire proof
script to be abstracted into a single command with semicolons,
e.g. `abstract (apply lem1; apply lem2; reflexivity)`. Note that the
`assert` tactic produces subterms that cannot be inspected by the rest
of the proof script, but they remain transparent in the resulting
proof term (at least if the proof is ended with `Defined.`).

For a transparent subterm, use `refine` or `transparent assert` (the
latter defined in `Basics/Overture`; see "Available tactics", below).

## 8. Imports/exports

Most `Require` commands should be just `Require Import` rather than
`Require Export`: imports should not be re-exported, by default.

However, if you can't imagine making practical use of file `Foo`
without file `Bar`, then `Bar` may export `Foo` via `Require Export
Foo`. For instance, `Modality` exports `ReflectiveSubuniverse` because
so many of the theorems about modalities are actually theorems about
reflective subuniverses.

## 9. Formatting

### 9.1. Location of commands

All `Require` commands should be placed at the top of a file.
Ideally, they should be grouped onto lines according to the rough
grouping of files listed under "Organization". Requires should
generally be followed by all `[Local] Open Scope` commands, and then
by `Generalizable Variables` commands.

The latter two might also occur in Sections later on in the file, but
in that case they should usually come at the beginning of the Section.
The assumptions of a section, such as `Variable` and `Context`, should
also generally come at the beginning of that section.

### 9.2. Indentation

In general, the bodies of sections and modules should be indented, two
spaces per nested section or module. This is the default behavior of
ProofGeneral.

However, when enclosing existing code in a new section or module, it
is acceptable to avoid re-indenting it at the same time, to avoid
excessive churn in the diff. If you wish, you can submit a separate
pull request or commit for the re-indentation, labeled as "only
whitespace changes" so that no one bothers reading the diff carefully.

### 9.3. Line lengths and comments

Lines of code should be of limited width; try to restrict yourself to
not much more than 70 characters. Remember that when Coq code is
often edited in split-screen so that the screen width is cut in half,
and that not everyone's screen is as wide as yours.

[coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html) is used
to produce a browsable
[view of the library](https://hott.github.io/Coq-HoTT/coqdoc-html/toc.html).
coqdoc treats comments specially, so comments should follow the
conventions described on the coqdoc page. The most important ones are
that Coq expressions within comments are surrounded by square brackets,
and that headings are indicated with comments of the form

```coq
(** * This is a top-level section *)
(** ** This is a subsection *)
(** *** This is a sub-subsection *)
```

Section titles should be less than 80 characters, on one line, and not
end in a period. Other comments are generally written using the style
`(** This is a comment. *)` or `(* This is a comment. *)`, with the
latter generally used for inline comments during a proof.

Text in comments should not contain hard newlines.
Putting hard newlines in text makes it extremely ugly when viewed in a
window that is narrower than the width to which you filled it. If
editing in Emacs, turn off `auto-fill-mode` and turn on
`visual-line-mode`; then you'll be able to read comment paragraphs
without scrolling horizontally, no matter how narrow your window is.
The repository contains a file .dir-locals.el in the top-level directory
which turns on `visual-line-mode` when emacs visits any file in the
repository.

Documentation can be built locally using `make doc` or `dune build @theories/doc`. The HTML files generated by Dune are placed in `_build/default/HoTT.html/`.

Unfortunately, when viewing source code on Github, these long comment
lines are not wrapped, making them hard to read. If you use the
Stylish plugin, you can make them wrap by adding the following style:

    @-moz-document domain(github.com) {
        div.line {
            white-space: pre-wrap;
        }
    }

This messes up the line-numbering, though, you'll have to turn it
off in order to link to or comment on a particular line.

### 9.4. Tactic scripts

When writing tactic scripts, `Proof.` and `Defined.` should be given
as individual lines, and the tactic code should be indented. Within
the tactic script, use newlines as a "logical grouping" construct.
Important tactic invocations, such as a top-level `induction` which
create a branch point in the proof, should generally be on lines by
themselves. Other lines can contain several short tactic commands
(separated by either periods or semicolons), if they together
implement a single idea or finish off a subgoal.

For long proofs with multiple significant subgoals, use branching
constructs such as bullets and braces to clarify the structure. See
the section of the Coq Reference Manual entitled "Navigation in the
proof tree".

### 9.5. Placement of Arguments and types

If the entire type of a theorem or definition does not fit on one
line, then it is better to put the result type (the part after the
colon) on an indented line by itself, together with the colon to make
it clear that this is the result type.

```coq
Definition triangulator {A : Type} {x y z : A} (p : x = y) (q : y = z)
  : concat_p_pp p 1 q @ whiskerR (concat_p1 p) q.
```

Of course, if the list of input types does not fit on a line by
itself, it should be broken across lines as well, with later lines
indented, and similarly for the result type.

```coq
Definition pentagon {A : Type} {v w x y z : A}
  (p : v = w) (q : w = x) (r : x = y) (s : y = z)
  : whiskerL p (concat_p_pp q r s)
      @ concat_p_pp p (q@r) s
      @ whiskerR (concat_p_pp p q r) s.
```

For definitions given with an explicit term, that term should usually
also be on an indented line by itself, together with the := to make it
clear that this is the definition.

```coq
Definition concat_p1 {A : Type} {x y : A} (p : x = y) : p @ 1 = p
  := match p with idpath => 1 end.
```

Of course, if the term is longer than one line, it should be broken
across lines, with later lines indented further.

## 10. Implicit Arguments

Do not use `Set Implicit Arguments` in the core. It makes it
difficult for a newcomer to read the code; use braces `{...}` to
explicitly mark which arguments are implicit. If necessary, you can
use the `Arguments` command to adjust implicitness of arguments after
a function is defined, but braces are preferable when possible.

If you want to use `Arguments` to make _all_ the arguments of
a function explicit, the obvious-looking syntax `Arguments foo a b`
does not work: you have to write `Arguments foo : clear implicits`
instead.

## 11. Coding Hints

### 11.1. Notations

The operation `compose`, notation `g o f`, is simply a notation for
`fun x => g (f x)` rather than a defined constant. We define `compose
:= (fun g f x => g (f x))` so that typeclass inference can pick up
`isequiv_compose` instances. This has the unfortunate side-effect
that `simpl`/`cbn` is enough to "unfold" `compose`, and there's no way
to prevent this. We could additionally define `g o f := (fun x => g
(f x))` to change this, but this would result in identically looking
goals which are really different. We consider it poor style to use
`compose` as a partially applied constant, such as `compose g`; we
take the point of view that `fun f => g o f` is more readable anyway.

### 11.2. Unfolding definitions

When a definition has to be unfolded repeatedly in the middle of
proofs, you can say `Local Arguments name / .`, which tells `simpl`
and related tactics to automatically unfold `name`. In particular,
this allows the tactic `simpl rewrite` (defined in `Tactics`) to apply
theorems containing `name` to goals in which it has been unfolded. It
seems better not to make these declarations globally, however.

It may not always be obvious which definition this needs to be applied
to; sometimes the unification failure happens in an implicit argument
that is not directly visible in the output. One way to discover where
the problem lies is to turn on printing of all implicit arguments with
`Set Printing All`; another is to use `Set Debug Tactic Unification`
and inspect the output to see where `rewrite` is failing to unify.

### 11.3. Finding theorems

The naming conventions mentioned above often help to guess the name of
a theorem. However, it still may happen that you expect that a
theorem should exist but don't know what it is called. One approach
to finding it is to guess what file it should live in and look there;
for instance, theorems about sigma-types are often in `Types/Sigma.v`,
and so on.

Another approach is to use Coq's command `Search` to display all the
theorems that relate to a particular definition. For example, `Search
(IsHProp ?A)` will show all results in which the expression `IsHProp
A` appears for some `A`, and `Search "ishprop"` will show all results
having "ishprop" in the name. However, some results about `HProp` are
true for any truncation level, so you may want to expand your search
to include `IsTrunc`. In general, if you can't find something at
first using `Search`, think about ways that your desired theorem might
be generalized and search for those instead.

Generalizing from a particular truncation level (like `IsHProp`) to
all truncation levels is a good example. Another one that it's
important to be aware of is a generalization from truncation
(`IsTrunc` and `Trunc`) to all reflective subuniverses or modalities;
many many theorems about truncation are actually proven more generally
in the latter situations.

### 11.4. Simpl nomatch

If a theorem or definition is defined by `destruct` or `match` (as
many operations on paths are), and if its value needs to be reasoned
about in tactic proofs, then it is helpful to declare its arguments as
`Arguments foo ... : simpl nomatch`. This instructs `simpl` and
related tactics never to simplify it if doing so would result in a
`match` that doesn't reduce, which is usually what you want.

### 11.5. Available tactics

Here are some tactics defined in the core that you may find useful.
They are described more fully, usually with examples, in the files
where they are defined.

- `nrefine`, `srefine`, `snrefine`:
  Defined in `Basics/Tactics`, these are shorthands for
  `notypeclasses refine`, `simple refine`, and `simple notypeclasses refine`.
  It's good to avoid typeclass search if it isn't needed.

- `napply`, `rapply`, `tapply`:
  Defined in `Basics/Tactics`, each of these is similar to `apply`,
  except that they use the unification engine of `refine`, which
  is different and often stronger than that of `apply`.
  `napply t` computes the type of `t`
  (possibly with holes, if `t` has holes) and tries to unify the type
  of `t` with the goal; if this succeeds, it generates goals for each
  hole in `t` not solved by unification; otherwise, it repeats this
  process with `t _`, `t _ _ `, and so on until it has the correct
  number of arguments to unify with the goal.
  `rapply` is like `napply`, (`rapply` succeeds iff
  `napply` does) except that after it succeeds in unifying with the
  goal, it solves all typeclass goals it can. `tapply` is stronger
  than `rapply`: if Coq cannot compute a type for `t` or successfully
  unify the type of `t` with the goal, it will elaborate all typeclass
  holes in `t` that it can, and then try again to compute the type of
  `t` and unify it with the goal. (Like `rapply`, `tapply` also
  instantiates typeclass goals after successful unification with the
  goal as well: if `rapply` succeeds, so does `tapply` and their
  outcomes are equivalent.)
- `snapply`, `srapply`, `stapply`: Sibling tactics to `napply`,
  `rapply` and `tapply`, except that they use `simple refine` instead
  of `refine` (beta reduction is not attempted when unifying with the
  goal, and no new goals are shelved)

  Here are some tips:

  - If `apply` fails with a unification error you think it shouldn't
    have, try `napply`, and then `rapply` if `napply` generates
    typeclass goals.
  - If you want to use type class resolution as well, try `tapply`.
    But it's better to use `napply` if it works.
  - You could add a prime to the tactic, to try with many arguments
    first, decreasing the number on each try.
  - If you are trying to construct an element of a sum type `sig (A :
Type) (P: A->Type)` (or something equivalent, such as a `NatTrans`
    record consisting of a `Transformation` and a proof that it
    `Is1Natural`) and you want to manually construct `t : A` first and
    then prove that `P t` holds for the given `t`, then use the
    `simple` version of the tactic, like `srapply exist` or `srapply
Build_Record`, so that the first goal generated is `A`. If it's
    more convenient to instantiate `a : A` while proving `P`, then use
    `rapply exist` - for example, `Goal { x & x = 0 }. rapply exist;
reflexivity. Qed.`

- `lhs`, `lhs_V`, `rhs`, `rhs_V`: Defined in `Basics/Tactics`.
  These are tacticals that apply a specified tactic to one side
  of an equality. E.g. `lhs napply concat_1p.`

- `transparent assert`: Defined in `Basics/Overture`, this tactic is
  like `assert` but produces a transparent subterm rather than an
  opaque one. Due to restrictions of tactic notations, you have to
  write `transparent assert (foo : (bar baz))` rather than
  `transparent assert (foo : bar baz)`.

- `issig`: Defined in `Basics/Tactics`, this tactic proves automatically
  that a record type is equivalent to a nested sigma-type.

- `make_equiv`: Defined in `Basics/Equivalences`, this tactic can prove
  two types are equivalent if the proof involves juggling components.
  See also `make_equiv_contr_basedpaths`.

- `pointed_reduce`: Defined in `Pointed/Core`, this tactic lets you
  assume that functions are strictly pointed. See related tactics there.

- `strip_truncations`, `strip_modalities` and `strip_reflections`: These
  let you lift an element from `O X` to `X` when the goal is `O`-local,
  for various `O`.

- `simpl rewrite`: Defined in `Tactics`, this tactic applies `simpl`
  to the type of a lemma, and to the goal, before rewriting the goal
  with the lemma. In particular, this is useful for rewriting with
  lemmas containing definitions like `compose` that appear unfolded in
  the goal: if the operation has `Arguments ... / .` as above then
  `simpl` will unfold it.

- `binder apply`: Defined in `Tactics/BinderApply`, this tactic
  applies a lemma inside of a lambda abstraction, in the goal or in a
  hypothesis.

## 12. Contributing to the library

### 12.1. Fork & Pull

We mainly work by the "Fork & Pull" model. Briefly: to contribute,
[create your own fork][fork] of the repository, do your main work
there, and [issue pull requests][pull] when work is ready to be
brought into the main library. Direct pushes to the library should
never be made.

There are various reasons for preferring the fork/pull workflow.
Firstly, it helps maintain code consistency. Secondly, it makes it
easier for all to keep track of what is being added --- it’s easier to
survey changes grouped into pull requests than in individual commits.
Thirdly, it means we can make our work in progress as messy and
uncertain as we want, while keeping the main library clean and tidy.

Submit your pull request not from the master
branch of your fork, but from another branch created specially for
that purpose. Among other things, this allows you to continue
developing on your fork without changing the pull request, since a
pull request is automatically updated to contain all commits pushed to
the branch that it was made from. It also allows you to submit
multiple unrelated pull requests at the same time that do not depend
on each other.

[fork]: https://help.github.com/articles/fork-a-repo
[pull]: https://help.github.com/articles/using-pull-requests
[minor]: http://en.wikipedia.org/wiki/Help:Minor_edit

### 12.2. Approval of pull requests

Before being merged, pull requests must be approved by one of
the core developers, not counting whoever submitted it. An approval
can be an official "Approving review" through the GitHub UI, or just a
comment such as LGTM ("Looks Good To Me"). Currently the rules are:

- Any objections or requested changes must be addressed somehow before
  merging (which doesn't always mean making the changes, but a
  discussion must be had and resolved).

- In general, a pull request should not be merged unless the CI tests
  confirm that it builds successfully. Exceptions to this rule
  sometimes have to be made if the CI configuration is broken for
  some unrelated reason, but in that case it is better if the
  person(s) approving the pull request confirms locally that it builds
  successfully.

  Note also that the CI doesn't automatically restart itself on a pull
  request when the master branch changes. Thus, if other pull
  requests have been merged in the interval since a given pull request
  was first submitted, it may be necessary to rebase that pull request
  against the new master, to make
  sure before merging it that it won't break the master branch.

- In the absence of objections, one approval suffices for a pull
  request to be merged.

- In the absence of objections, a minor pull request may be merged
  if at least 48 hours have passed after its submission. In some
  cases, this can be done immediately.

If a pull request is lacking approval and hasn't received any
discussion, feel free to bump it back to attention with a comment.

### 12.3. Commit messages

Please try to keep commit messages clear and informative. We don’t
currently have a specific preferred convention, but the answers
[here][commits1] and [here][commits2] (not just the top answers!) give
excellent, if varied, advice. That said, this is a minor point. Good
code with bad commit messages is much better than the reverse!

Some good examples, showing what kind of change was made (additions,
updates, fixes), and what material it was on:

- "adapt to the new version of coqtop by disabling the native compiler"
- "resolved universe inconsistency in Freudenthal"
- "epis are surjective"

Some bad examples:

- "further progress" Progress in what files?
- "Bug in [Equivalences.v]." Was the bug fixed, or just noticed and
  flagged in comments, or what?
- "asdfjkl"

[commits1]: http://stackoverflow.com/questions/43598/suggestions-for-a-good-commit-message-format-guideline
[commits2]: http://stackoverflow.com/questions/3580013/should-i-use-past-or-present-tense-in-git-commit-messages

### 12.4. Creating new files

If you create a new file, `make` will only compile it if it is being
tracked by `git`, so you will need to `git add` it.

You will probably also want to add your new file to `HoTT.v`, unless
it is outside the core (e.g. in `contrib/`) or should not be exported
for some other reason.

### 12.5. Continuous Integration

We use [GitHub Actions][github-actions] to check the compilation of
pull requests, do documentation building, and run the testing suite.

Documentation shown on the [project wiki][wiki] is built and deployed
after a pull request is merged.

Normally you shouldn't need to know anything about this; GitHub
actions will automatically check every pull request made.

The file `.github/workflows/ci.yml` contains the configuration for
GitHub Actions. This has to be updated very rarely.

[github-actions]: https://github.com/features/actions
[wiki]: https://github.com/HoTT/Coq-HoTT/wiki

### 12.6. Git rebase

If the master branch has diverged in some significant way since a pull
request was made, then merging it may result in non-compiling code.
Or the changes may conflict so that github becomes unable to merge it
automatically. In either case, the situation should be resolved
manually before the pull request can be merged, and the resolution
should generally be done by the submitter of the pull request.

One way to do the resolution is to merge the current master branch
into the branch from which the pull request was made, resolving
conflicts manually, and then make and commit whatever other changes
may be necessary. This has the disadvantage of creating new merge
commits, so another option is to `git rebase` against the master
branch. We encourage the use of `rebase` if you are comfortable with
it; but for newcomers to git, rebasing can be intimidating, so merges
are also perfectly acceptable.

### 12.7. Timing scripts

There are scripts in `etc/timing` to track (compile-time) performance
changes in the library. When you make large changes, you may want to
include performance information in your commit message (recommended,
but certainly not required!).

**Note:** Make sure you have gnu time installed. Many terminals have
their own `time` command but this will not work. To install time
run `sudo apt install time`. You will also need to rerun the
`./configure` script so that it detects the newly installed time.

To run the timing scripts, use the following work-flow
from the root of the repository after you have made your edits. To
make use of these scripts, you must first run `git submodule update
--init --recursive`.

    $ git status
    $ git add <all files mentioned above which you care to have in the repo>
    $ git status

It's good practice at this point to ensure that there are no `.v`
files mentioned.

    $ ./etc/coq-scripts/timing/make-pretty-timed-diff.sh
    $ make

Ensure that `make` succeeds, since `make-pretty-timed-diff.sh` will
succeed even if some files fail to build.

    $ git commit -at ./time-of-build-both.log

This pops open an editor. You should add lines at the beginning of
the commit message, leaving at least one blank line before the
performance table.

See the comments at the top of `make-pretty-timed-diff.sh` for more
detailed instructions and caveats.

## 13. Bugs in Coq

More often than we would like, we run across bugs in Coq. A sure sign
of a bug in Coq is when you get a message about an "Anomaly", but a
bug can also be unjustifiable behavior. If you aren't sure whether
something is a bug in Coq, feel free to [open an issue][new issue]
about it on the Coq-HoTT GitHub project.

[new issue]: https://github.com/HoTT/HoTT/issues/new

### 13.1. Reporting bugs

Bugs in Coq should be reported on the [Coq bug tracker][bugs]. You
should search the tracker first to see whether your bug has
already been reported.

After reporting a bug, you may need to add a temporary workaround to
the HoTT library until the bug is fixed. In this case, please add a
comment labeling this as a workaround and citing the bug report. That
way when the bug is fixed, we can remove the workaround.

[bugs]: https://coq.inria.fr/bugs

### 13.2. Minimizing bugs

When submitting a bug report, it is appreciated to submit a minimal
test example. Since the HoTT library is quite large, it can be quite
some work to track down the actual trigger of a bug. Fortunately,
Jason Gross has written a convenient "bug minimizing" script, which is
available in his [coq-tools][coq-tools] repository. To use it:

1. Clone the coq-tools repository somewhere (usually somewhere outside
   the HoTT library directory).

2. Attempt to compile the file where the bug occurs, e.g. by running
   `make theories/Path/To/Buggy.vo` from the root of the HoTT library
   directory. This creates a `.glob` file which the bug-finder needs.

3. `cd theories` and then run the bug-finder script `find-bug.py`. It
   will combine the file with all the rest of the library that it
   needs, ask you to confirm the error, and then proceed to minimize
   it as much as possible.

You will need to pass the bug-finder several arguments to tell it to
pass the right flags and where to find the rest of the library;
a common invocation would be something like

    $ /path/to/find-bug.py --arg -noinit --arg -indices-matter -R . HoTT Path/To/Buggy.v bug_minimized.v

When it exits, the minimized code producing the bug will be in
`bug_minimized.v`.

Note that sometimes `coqc` and
`coqtop` can exhibit different behavior, and one may produce a bug
while the other doesn't. The bug-finder normally uses
both `coqc` and `coqtop`, but you can tell it to "fake" `coqc` using
`coqtop` by passing the argument `--coqc-as-coqtop` instead of
`--coqc`.

[coq-tools]: https://github.com/JasonGross/coq-tools
