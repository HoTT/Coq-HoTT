# Conventions And Style Guide #

## Organization ##

### The Core library ###

The Coq files of the HoTT library live in the theories/ directory.
They are currently in several groups:

- `Basics/*`: These files contain basic definitions that underlie
  everything else.  Nothing in the Basics directory should depend on
  anything outside the Basics directory.  The file `Basics` in the
  root imports everything from the directory `Basics/`, so most other
  files in the library start with `Require Import HoTT.Basics.` (see
  remarks below on qualified imports).

- `Types/*`: This subdirectory contains a file corresponding to each
  basic type former (e.g. sigma-types, pi-types, etc.), which proves
  the "computational" rules for the path-types, transport, functorial
  action, etc. of that type former.  It also contains `Types/Record`,
  which provides tactics for proving records equivalent to iterated
  sigma-types, and `Types/Equiv`, which proves that being an
  equivalence is an hprop.  The univalence axiom is introduced, as a
  typeclass (see below) in `Types/Universe`.  Function extensionality
  is introduced in `Basics/Overture` for dependency reasons, but
  developed further in `Types/Forall` and `Types/Arrow`.  Some type
  formers are defined in their corresponding `Types/` file, while
  others are defined in `Basics/Overture` for dependency reasons but
  studied further in their `Types/` file.  Files in `Types/` should
  not depend on anything except `Basics` and other `Types/` files.

- Other files in the root `theories/` directory, such as `Trunc`,
  `TruncType`, `HProp`, `HSet`, `EquivalenceVarieties`,
  `FunextVarieties`, `ObjectClassifier`, `ReflectiveSubuniverse`,
  `Modality`: These contain more advanced facts and theories which may
  depend on files in `Types/`.  The file `Misc` can be used to help resolve
  potentially circular dependencies, although it should be avoided
  whenever possible.  Note that `make clean; make` will produce an
  error if there is a dependency loop (ordinary `make` may not).

- `hit/*`: Files involving higher inductive types.  Each higher
  inductive type is defined in a corresponding file (see conventions
  on defining HITs, below).  Since the definition of a HIT involves
  axioms added to the core theory, we isolate them in this directory.
  In particular, nothing in the root directory should depend on
  anything in `hit/` (except, of course, for `HoTT` and `Tests`, below).

- `Tactics, Tactics/*`: some more advanced tactics.

- `HoTT`: This file imports and exports everything in the core (that
  is, everything mentioned above).  Thus, in a development based on
  the HoTT library, you can say simply `Require Import HoTT` to pull
  in everything (but don't do this for files in the core itself).

- `Tests`: Test suites for the rest of the library.  Currently nearly
  empty.

- `Utf8`: optional Unicode notations for the basic definitions
  (we avoid Unicode in the core libary).  Not exported by `HoTT`.

- `FunextAxiom, UnivalenceAxiom`: You can import these files to assume
  the axioms globally (in the core, we track them with typeclasses).
  Two additional related files are `UnivalenceImpliesFunext` and
  `hit/IntervalImpliesFunext`; see below.  None of these are exported
  by `HoTT`.

A dependency graph of all the files in the library can be found on the
[wiki][wiki]; this may be helpful in avoiding circular dependencies.
It is updated automatically by Travis (see below) on every push to the
master branch.

[wiki]: https://github.com/HoTT/HoTT/wiki

### Non-core files ###

- `theories/categories/*`: The categories library, which is not
  considered part of the core (e.g. it uses unicode), but nevertheless
  lives in `theories/`.

- `contrib/HoTTBook`: This file lists all the definitions and theorems
  from the HoTT Book and gives pointers to where the corresponding
  fact is defined in the library.  It is not intended to be a
  formalization of the book, but rather a guide to the library for a
  reader familiar with the book.

- `contrib/HoTTBookExercises`: This file contains both formalizations
  of the exercises from the HoTT Book, and pointers to the
  corresponding facts in the library.  The latter pointers serve the
  same purpose as `contrib/HoTTBook`, but the former may contain
  alternative solutions, such as ones that depend only on the concepts
  that are introduced prior to the exercise in the book.

- `contrib/*`: Other work in progress, or files not judged appropriate
  for the core.


## Naming Conventions ##

### General principles ###

In general, the name of a theorem (or definition, or instance, etc.)
should begin with the property (or structure, or class, or record,
etc.) being proven, and then state the object or construction it is
being proven about.  For instance, `isequiv_idmap` proves `IsEquiv
idmap`, and `equiv_compose` constructs an "Equiv" record by composing
two given equivalences.

In particular, a prefix of `path_` means a theorem that constructs a
path in some type.  For instance, `path_sigma` is a theorem
constructing paths in a sigma-type.

More generally, where applicable the order of parts in a lemma name
should roughly respect their placement in (the syntax tree of) the
goal, from outermost to deepest.  For instance, `path_equiv`
constructs a path in the type `Equiv f g`, while `isequiv_path_equiv`
shows that `path_equiv` is an equivalence.

### Capitalization and spacing ###

Names of types, such as `Unit` and `Equiv` and `IsHProp`, should
generally be capitalized.  Names of functions and definitions should
be lowercase, including the names of types when they appear therein.
Thus, for instance, the theorem that `Unit` is contractible is
`contr_unit : Contr Unit`.

Multiple-word names, especially in lowercase, should generally be
separated with underscores.  We make an exception for names of types
beginning with `is`, such as `IsEquiv` and `IsTrunc`.

### Suffixes ###

A suffix of `D` indicates a dependent version of something ordinarily
non-dependent.  For instance, `ap` applies to non-dependent functions
while `apD` applies to dependent ones.  When possible, the
non-dependent version should be an instantiation of the dependent one
using constant type families, but sometimes they are more different
than this, usually due to the fact that `transport_const` is not the
identity (e.g. `ap` and `apD`).

When there is more than one theorem that seems to merit the same name,
and no obvious concise way to distinguish them, one of them can be
given a prime suffix, e.g. we have `path_sigma` and `path_sigma'`.
Do this with caution.

### Induction and recursion principles ###

In conformity with the HoTT Book, the induction principle of a
(perhaps higher) inductive type `thing` (that is, its dependent
eliminator) should be named `thing_ind`, while its recursion principle
(non-dependent eliminator) should be named `thing_rec`.

However, by default, when you declare a (non-higher) inductive type,
Coq automatically defines induction principles named `thing_rect`,
`thing_rec`, and `thing_ind` that vary only in the sort of their
target (`Type`, `Set`, or `Prop`).  In order to turn this off, you
must say `Local Unset Elimination Schemes` before defining an
inductive type.  You can then have Coq automatically generate the
correctly named induction principles with

```coq
Scheme thing_ind := Induction for thing Sort Type.
Scheme thing_rec := Minimality for thing Sort Type.
```

Unfortunately, Coq's built-in tactics `induction` and `elim` assume
that the induction principles are named in Coq's default manner.  We
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
types such as are used to hack HITs.  For HITs, you must always define
both the induction and recursion principles by hand, as described
in the appropriate section below.

Some types have a "coinduction" or "corecursion" principle; these
should have instead the suffix `_coind` or `_corec`.

Finally, a type will often have a universal property expressed by
saying that its induction or recursion (or coinduction or corecursion)
principle is an equivalence.  These should be named according to the
naming conventions for equivalences below, e.g. `isequiv_thing_rec`
and `equiv_thing_rec`.

[inductionbug]: https://coq.inria.fr/bugs/show_bug.cgi?id=3745

### Path algebra functions ###

The path algebra functions defined mainly in `Basics/PathGroupoids`
follow a particular set of naming conventions.  Generally they are
named according to the head constant of their primary input and the
pattern of paths appearing therein.  For more details, see the
comments in `Basics/PathGroupoids`.

### Equivalences ###

When defining an equivalence, the standard naming procedure is to

- Define the function in one direction with a name, say `foo`.
- Define an `IsEquiv` instance for this function, called `isequiv_foo`.
- Define an `Equiv` record putting them together, called `equiv_foo`.

The inverse function can then be referred to as `foo ^-1`.  Avoid
using `equiv_foo` unless you really do need an `Equiv` object, rather
than a function which happens to be an equivalence.


## Records, Structures, Typeclasses ##

We use Coq Records when appropriate for important definitions.  For
instance, contractibility (`Contr`) and equivalences (`Equiv`) are
both Record types (in fact, the former is a typeclass).  The file
`Types/Record` contains some tactics for proving semiautomatically
that record types are equivalent to the corresponding sigma-types, so
that the relevant general theorems can be applied to them.

### Two-component records ###

Sometimes a two-component record is better defined as a sigma-type,
especially if it is a "subset type" whose second component is an
hprop.  For instance, this has the advantage that we do not need new
names for its constructor and its fields, and we can apply theorems in
`Types/Sigma` to it directly rather than via `issig`.

TODO: Decide about `hProp` and `hSet` and `TruncType` (issue #514).

### Typeclasses ###

We are using typeclasses in preference to canonical structures.
Typeclasses are particularly convenient for h-properties of objects.
Here are some of the typeclasses we are using:

- equivalences: `IsEquiv`
- truncation levels: `Contr`, `IsTrunc`
- axioms (see below): `Funext`, `Univalence`
- subuniverses: `In`, `Replete`

`IsHSet`, `IsHProp`, and `Contr` are notations for `IsTrunc 0`,
`IsTrunc -1`, and `IsTrunc -2` respectively.  Since `IsTrunc` is
defined recursively with contractibility as the base case, there is a
bit of magic involving a definition called `Contr_internal`; see the
comments in `Overture.v`.

### When to declare instances ###

When constructing terms in a typeclass record such as `IsEquiv`, `Contr`,
or `IsTrunc`, one has the choice to declare it as an `Instance`, in which
case it is added to the hint database that is searched when Coq tries
to do typeclass instance resolution.  Care must be taken with this, as
indiscriminately adding theorems to this database can easily result in
infinite loops (or at least very long loops).

In general, it seems to be better not to add instances which suggest
an open-ended search.  E.g. the theorem that truncation levels are
closed under equivalence is a bad candidate for an `Instance`, because
when Coq is searching for a proof of `Contr B` this theorem could
cause it to look through all possible types A for an equivalence `A
<~> B` and a proof of `Contr A`.  Results of this sort should be
proven as `Definition`s or `Theorem`s, not as `Instance`s.  If you
need to use a result of this sort in the middle of a proof, use a
tactic like `pose` or `assert` to add a particular instance of its
conclusion to the context; then it will be found by subsequent
typeclass resolution.

If you have determined through trial and error that a particular
result should not be an `Instance` (e.g. when making it an `Instance`,
a tactic in some other proof loops, but changing it to a `Definition`
prevents this), please add a comment to that effect where it is
defined.  This way no one else will come along and helpfully change it
back to an `Instance`.

If a particular fact should not be made an ordinary instance, it can
still be made an "immediate instance", meaning that Coq will use it
automatically to solve a goal *if* its hypotheses are already present
in the context, but will not initiate an instance search for those
hypotheses otherwise.  This avoids infinite instance-search loops.  To
declare a fact as an immediate instance, make it a `Definition` rather
than an `Instance` and then say

```coq
Hint Immediate foo : typeclass_instances.
```

### Local and Global Instances ###

When declaring an `Instance` you should *always* use either the
`Local` or the `Global` keyword.  The former makes the instance local
to the current section, module, or file (although its *definition*
will still be visible globally, it won't be in the instance database
for typeclass resolution outside its containing section, module or
file), while the latter puts it in the instance database globally.
If you write `Instance` without `Local` or `Global`, Coq will
sometimes make it local and sometimes global, so to avoid confusion it
is better to always specify explicitly which you intend.

### Using Typeclasses ###

Try to avoid ever giving a name to variables inhabiting typeclasses.
When introducing such a variable, you can write `intros ?` to put it
in the hypotheses without specifying a name for it.  When using such a
variable, typeclass resolution means you shouldn't even need to refer
to it by name: you can write `_` in tactics such as `refine` and Coq
will find typeclass instances from the context.  Even `exact _` works.
(You can usually also use `typeclasses eauto` or `eauto with
typeclass_instances`, but `exact _` is preferable when it works, as it
is shorter and uses a tactic name the reader is presumably already
familiar with.)

Unfortunately, it is not currently possible to write `_` in a
`refine`d term for an inhabitant of a typeclass and have Coq generate
a subgoal if it can't find an instance; Coq will die if it can't
resolve a typeclass variable from the context.  You have to `assert`
or `pose` such an inhabitant first, or give an explicit term for it.

Note that when you don't give a name to a variable, Coq often names it
`H` or some modification thereof.  For that reason, it's often better
avoid using `H` for your own explicitly named variables, since if you
do and later on someone introduces a new unnamed hypothesis that Coq
names `H`, your name will result in a conflict.  Conversely, we
sometimes give a hypothesis a name that won't be used, to pre-empt
such conflicts, such as `{ua : Univalence}` or `{fs : Funext}`.

### Truncation ###

The conventions for the typeclass `IsTrunc` are:

* We prefer to do inference with `IsTrunc n A` rather than `IsTrunc n (a = b)`.
* We prefer to expand `IsTrunc n (forall a, P a)` into `forall a,
  IsTrunc n (P a)`, and similarly for other data types.  For instance,
  `IsTrunc n (A * B)` gets transformed to `IsTrunc n A` and `IsTrunc n B`,
  as a goal.
* Due to the desire to use `IsTrunc` rather than `Contr`, we have
  `Contr` as a notation for `IsTrunc minus_two`, which bottoms out at
  `Contr_internal`, which is its own typeclass.  Due to a
  [bug in coq](https://coq.inria.fr/bugs/show_bug.cgi?id=3100), we
  need to iota-expand some explicit instances of `Contr`, such as
  `Instance foo : Contr bar := let x := {| center := ... |} in x.`
  rather than `Instance foo : Contr bar := { center := ... }.`

### Coercions and Existing Instances ###

A "coercion" from `A` to `B` is a function that Coq will insert
silently if given an `A` when it expects a `B`, and which it doesn't
display.  For example, we have declared `equiv_fun` as a coercion from
`A <~> B` to `A -> B`, so that we can use an equivalence as a function
without needing to manually apply the projection `equiv_fun`.
Coercions can make code easier to read and write, but when used
carelessly they can have the opposite effect.

When defining a record, Coq allows you to declare a field as a
coercion by writing its type with `:>` instead of `:`.  Please do
_not_ do this in the core: instead, give an explicit `Coercion`
declaration after defining the record.  There are two reasons for
this.  Firstly, the syntax `:>` is very short and easy to miss when
reading the code, while coercions are important to be aware of.
Secondly, it is potentially confusing because the same syntax `:>`
when defining a typeclass (i.e. a `Class` instead of a `Record`) has a
different meaning: it declares a field as an `Existing Instance`.
Please do not use it in that case either; declare your `Existing
Instance`s explicitly as well.


## Axioms ##

### Univalence and function extensionality ###

The "axioms" of `Univalence` and `Funext` (function extensionality)
are typeclasses rather than Coq `Axiom`s.  (But see the technical note
below on universe polymorphism.)  In the core, we use these
typeclasses to keep track of which theorems depend on the axioms and
which don't.  This means that any theorem which depends on one or the
other must take an argument of the appropriate type.  It is simple to
write this using typeclass magic as follows:

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
implicitly generalized if necessary.  The backquote syntax
``{Univalence}` allows us to avoid giving a name to the hypothesis.
(Backquote syntax is also used for implicit generalization of
variables, but that is not needed for univalence and funext.)

### Higher inductive types ###

Every higher inductive type technically assumes some `Axioms`.  These
axioms are asserted globally by the corresponding `hit/` file, since
there's not much point to assuming a HIT without the axioms that make
it work.

### Relationships between axioms ###

The file `UnivalenceImpliesFunext` shows, as its name implies, that
univalence implies funext.  Thus, if you import this file, then
whenever you have assumed univalence, then funext is also true
automatically and doesn't need to be assumed separately.  (This is
usually good, to simplify your hypotheses, unless you are working in
part of the core that `UnivalenceImpliesFunext` depends on.)

Similarly, the file `hit/IntervalImpliesFunext` proves funext from the
interval type assumed in `hit/Interval`, so if you import this file
then funext is always true automatically (just as if you'd imported
`FunextAxiom`).  Of course, once you've imported `hit/Interval` it is
always possible to prove funext by hand, but by importing
`hit/Interval` without `hit/IntervalImpliesFunext` you can still use
the interval in some places and track moral uses of funext elsewhere.

### Assuming axioms ###

When working in a derived development using the HoTT library, you may
import the files `FunextAxiom` and/or `UnivalenceAxiom` to assume
these axioms globally.  You should _not_ assume these axioms yourself
by writing something such as `Axiom fs : Funext`.  The problem with
this is that if two different files do this, and then a third file
imports them both, it ends up with two different witnesses for
`Funext`, not definitionally equal.  Thus, derived objects that should
be judgmentally equal might fail to be so because they use different
witnesses.

### Technical note: Universe-polymorphic axioms ###

In order for the "axioms" univalence and funext to be usable at
different universe levels, the types `Univalence` and `Funext` do not
technically assert the axioms themselves.  Rather they assert
inhabitants of dummy types, while the axioms are actually declared
globally but depending on elements of those dummy types.  This is not
something you generally need to worry about; see the comments in
`Basics/Overture` for more information.


## Higher Inductive Types ##

At present, higher inductive types are restricted to the `hit/`
directory, and are all defined using Dan Licata's "private inductive
types" hack.  This means the procedure for defining a HIT is:

1. Wrap the entire definition in a module, which you will usually want
   to export to the rest of the file containing the definition.

2. Define a `Private Inductive` type whose constructors are the
   desired point-constructors of your HIT.

3. Assert the desired path-constructors as `Axiom`s.

4. Define the induction principle, with all the correct hypotheses, by
   matching against the point-constructors.  There is an important
   additional hack here.  If the path-hypotheses are not "used"
   anywhere in the `match`, then Coq will notice and will consider two
   invocations of the induction principle to be judgmentally equal if
   they have the same point-hypotheses, even if their path-hypotheses
   differ.  Thus, it is important to "use" the path-hypotheses
   trivially by making the `match` return a function which is then
   applied to all the path-hypotheses.  For example, with the circle
   we write `fun x => match x with base => fun _ => b end l` instead
   of `fun x => match x with base => b end`.

5. Assert the "computation rules" for the path-constructors, in the
   form of propositional equalities, as `Axiom`s.

6. Close the module.  It is important to do this immediately after
   defining the induction principle, so that the private inductive
   type can't be matched against anywhere else; any other uses of it
   have to call the correct induction principle.

7. Usually, you will want to also define a non-dependent recursor and
   its computation rules as well.

Look at some of the existing files in `hit/*` for examples.


## Transparency and Opacity ##

If the value of something being defined matters, then you must either
give an explicit term defining it, or construct it with tactics and
end the proof with `Defined.`  But if all that matters is that you
have defined something with a given type, you can construct it with
tactics and end the proof with `Qed.`  The latter makes the term
"opaque" so that it doesn't "compute".

If something *can* be made opaque, it is generally preferable to do
so, for performance reasons.  However, many things which a traditional
type theorist would make opaque cannot be opaque in homotopy type
theory.  For instance, none of the higher-groupoid structure in
PathGroupoids can be made opaque, not even the "coherence laws".  If
you doubt this, try making some of it opaque and you will find that
the "higher coherences" such as `pentagon` and `eckmann_hilton` will
fail to typecheck.

In general, it is okay to contruct something transparent using
tactics; it's often a matter of aesthetics whether an explicit proof
term or a tactic proof is more readable or elegant, and personal
aesthetics may differ.  Consider, for example, the explicit proof term
given for `eckmann_hilton`: some may consider it optimally elegant,
while others would prefer to be able to step through a tactic proof to
understand what is happening step-by-step.

One thing to beware of is explicit `match` terms that require `in` or
`return` annotations, as these are particularly difficult for
newcomers to understand.  Avoiding them is not a hard and fast rule,
but when there is a short proof using tactics that produces an
acceptable proof term, it should probably be preferred.

The important thing is that when defining a transparent term with
tactics, you should restrict yourself to tactics which maintain a high
degree of control over the resulting term; "blast" tactics like
`autorewrite` should be eschewed.  Even plain `rewrite` is usually to
be avoided in this context: although the terms it produces are at
least predictable, they are one big `transport` (under a different
name) whereas a term we would want to reason about ought to be
constructed using smaller pieces like `ap` and `concat` which we can
understand.

Here are some acceptable tactics to use in transparent definitions
(this is probably not an exhaustive list):

- `intros`, `revert`, `generalize`, `generalize dependent`
- `pose`, `assert`, `set`, `cut`
- `transparent assert` (see below)
- `fold`, `unfold`, `simpl`, `cbn`, `hnf`
- `case`, `elim`, `destruct`, `induction`
- `apply`, `eapply`, `assumption`, `eassumption`, `refine`, `exact`
- `reflexivity`, `symmetry`, `transitivity`, `etransitivity`
- `by`, `done`

Conversely, if you want to use `rewrite`, that is fine, but you should
then make the thing you are defining opaque.  If it turns out later
that you need it to be transparent, then you should go back and prove
it without using `rewrite`.

Currently, there are some basic facts in the library, such as the
"adjointify" lemma, which are proven using `rewrite` and hence are at
least partially opaque.  It might be desirable one day to prove these
more explicitly and make them transparent, but so far it has not been
necessary.

Note that it *is* acceptable for the definition of a transparent
theorem to invoke other theorems which are opaque.  For instance,
the "adjointify" lemma itself is actually transparent, but it invokes
an opaque sublemma that computes the triangle identity (using
`rewrite`).  Making the main lemma transparent is necessary so that
the other parts of an equivalence -- the inverse function and
homotopies -- will compute.  Thus, a transparent definition will not
generally be "completely transparent".

It is possible to make subterms of a term opaque by using the
`abstract` tactic, although that requires grouping the entire proof
script to be abstracted into a single command with semicolons,
e.g. `abstract (apply lem1; apply lem2; reflexivity)`.  Note that the
`assert` tactic produces subterms that cannot be inspected by the rest
of the proof script, but they remain transparent in the resulting
proof term (at least if the proof is ended with `Defined.`).

For a transparent subterm, use `refine` or `transparent assert` (the
latter defined in `Basics/Overture`; see "Available tactics", below).


## Formatting ##

### Location of commands

All `Require` commands should be placed at the top of a file.
Ideally, they should be grouped onto lines according to the rough
grouping of files listed under "Organization".  Requires should
generally be followed by all `[Local] Open Scope` commands, and then
by `Generalizable Variables` commands.

The latter two might also occur in Sections later on in the file, but
in that case they should usually come at the beginning of the Section.
The assumptions of a section, such as `Variable` and `Context`, should
also generally come at the beginning of that section.

### Indentation

In general, the bodies of sections and modules should be indented, two
spaces per nested section or module.  This is the default behavior of
ProofGeneral.

However, when enclosing existing code in a new section or module, it
is acceptable to avoid re-indenting it at the same time, to avoid
excessive churn in the diff.  If you wish, you can submit a separate
pull request or commit for the re-indentation, labeled as "only
whitespace changes" so that no one bothers reading the diff carefully.

### Line lengths

Lines of code should be of limited width; try to restrict yourself to
not much more than 70 characters.  Remember that when Coq code is
often edited in split-screen so that the screen width is cut in half,
and that not everyone's screen is as wide as yours.

Text in comments, on the other hand, should not contain hard newlines.
Putting hard newlines in text makes it extremely ugly when viewed in a
window that is narrower than the width to which you filled it.  If
editing in Emacs, turn off `auto-fill-mode` and turn on
`visual-line-mode`; then you'll be able to read comment paragraphs
without scrolling horizontally, no matter how narrow your window is.
Some files contain `(* -*- mode: coq; mode: visual-line -*- *)` at the
top, which does this automatically; feel free to add it to files that
are missing it.

Unfortunately, when viewing source code on Github, these long comment
lines are not wrapped, making them hard to read.  If you use the
Stylish plugin, you can make them wrap by adding the following style:

    @-moz-document domain(github.com) {
        div.line {
            white-space: pre-wrap;
        }
    }

This messes up the line-numbering, though, you'll have to turn it
off in order to link to or comment on a particular line.

### Tactic scripts ###

When writing tactic scripts, `Proof.` and `Defined.` should be given
as individual lines, and the tactic code should be indented.  Within
the tactic script, use newlines as a "logical grouping" construct.
Important tactic invocations, such as a top-level `induction` which
create a branch point in the proof, should generally be on lines by
themselves.  Other lines can contain several short tactic commands
(separated by either periods or semicolons), if they together
implement a single idea or finish off a subgoal.

For long proofs with multiple significant subgoals, use branching
constructs such as bullets and braces to clarify the structure.  See
the section of the Coq Reference Manual entitled "Navigation in the
proof tree".

### Placement of Arguments and types ###

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


## Implicit Arguments ##

Do not use `Set Implicit Arguments` in the core.  It makes it
difficult for a newcomer to read the code; use braces `{...}` to
explicitly mark which arguments are implicit.  If necessary, you can
use the `Arguments` command to adjust implicitness of arguments after
a function is defined, but braces are preferable when possible.

Warning: if you want to use `Arguments` to make *all* the arguments of
a function explicit, the obvious-looking syntax `Arguments foo a b`
does not work: you have to write `Arguments foo : clear implicits`
instead.


## Coding Hints ##

### Unfolding compose and other definitions ###

The operation `compose`, notation `g o f`, is a defined constant
rather than simply a notation for `fun x => g (f x)` so that it can be
used as a head for typeclass resolution, e.g. in `isequiv_compose`.
However, this means that frequently it has to be folded and unfolded
in the middle of proofs.

One trick that is sometimes helpful is `Local Arguments compose / .`,
which tells `simpl` and related tactics to automatically unfold
`compose`.  In particular, this allows the tactic `simpl rewrite`
(defined in `Tactics`) to apply theorems containing `compose` to goals
in which it has been unfolded.  It seems better not to make this
declaration globally, however.

Occasionally it may also be necessary to give a similar command for
definitions other than `compose` as well, and it may not be obvious
where the issue lies; sometimes the unification failure happens in an
implicit argument that is not directly visible in the output.  One way
to discover where the problem lies is to turn on printing of all
implicit arguments with `Set Printing All`; another is to use `Set
Debug Tactic Unification` and inspect the output to see where
`rewrite` is failing to unify.  (As of Oct 2014, however, the latter
requires a more up-to-date version of Coq than our submodule currently
points to.)

### Simpl nomatch ###

If a theorem or definition is defined by `destruct` or `match` (as
many operations on paths are), and if its value needs to be reasoned
about in tactic proofs, then it is helpful to declare its arguments as
`Arguments foo ... : simpl nomatch`.  This instructs `simpl` and
related tactics never to simplify it if doing so would result in a
`match` that doesn't reduce, which is usually what you want.

### Available tactics ###

Here are some tactics defined in the core that you may find useful.
They are described more fully, usually with examples, in the files
where they are defined.

- `transparent assert`: Defined in `Basics/Overture`, this tactic is
  like `assert` but produces a transparent subterm rather than an
  opaque one.  Due to restrictions of tactic notations, you have to
  write `transparent assert (foo : (bar baz))` rather than
  `transparent assert (foo : bar baz)`.

- `simpl rewrite`: Defined in `Tactics`, this tactic applies `simpl`
  to the type of a lemma, and to the goal, before rewriting the goal
  with the lemma.  In particular, this is useful for rewriting with
  lemmas containing definitions like `compose` that appear unfolded in
  the goal: if the operation has `Arguments ... / .` as above then
  `simpl` will unfold it.

- `binder apply`: Defined in `Tactics/BinderApply`, this tactic
  applies a lemma inside of a lambda abstraction, in the goal or in a
  hypothesis.

- `issig`: Defined in `Types/Record`, this tactic proves automatically
  that a record type is equivalent to a nested sigma-type.  (Actually,
  there are separate tactics `issig2`, `issig3`, etc. depending on how
  many fields the record has, but their code is virtually identical,
  and a tactic notation `issig` invokes the appropriate one
  automatically.  If you need a version with more fields than yet
  exists, feel free to add it.)


## Contributing to the library ##

### Fork & Pull ###

We mainly work by the "Fork & Pull" model.  Briefly: to contribute,
[create your own fork][fork] of the repository, do your main work
there, and [issue pull requests][pull] when work is ready to be
brought into the main library.  Direct pushes to the library should be
restricted to minor edits, in roughly [the sense of Wikipedia][minor]:
improvements to documentation, typo corrections, etc.

There are various reasons for preferring the fork/pull workflow.
Firstly, it helps maintain code consistency.  Secondly, it makes it
easier for all to keep track of what is being added --- it’s easier to
survey changes grouped into pull requests than in individual commits.
Thirdly, it means we can make our work in progress as messy and
uncertain as we want, while keeping the main library clean and tidy.

It is suggested that you submit your pull request not from the master
branch of your fork, but from another branch created specially for
that purpose.  Among other things, this allows you to continue
developing on your fork without changing the pull request, since a
pull request is automatically updated to contain all commits pushed to
the branch that it was made from.  It also allows you to submit
multiple unrelated pull requests at the same time that do not depend
on each other.

[fork]: https://help.github.com/articles/fork-a-repo

[pull]: https://help.github.com/articles/using-pull-requests

[minor]: http://en.wikipedia.org/wiki/Help:Minor_edit

### Two pairs of eyes ###

In general, pull requests require "two pairs of eyes" from among the
core developers, i.e. two people to approve them before they are
merged.  This usually works fine, but can sometimes stall if most of
the core developers are busy.  If a pull request seems to have
stalled, feel free to bump it back to attention with a comment.

### Commit messages ###

Please try to keep commit messages clear and informative.  We don’t
currently have a specific preferred convention, but the answers
[here][commits1] and [here][commits2] (not just the top answers!) give
excellent, if varied, advice.  That said, this is a minor point.  Good
code with bad commit messages is much better than the reverse!

Some good examples, showing what kind of change was made (additions,
updates, fixes), and what material it was on:

- "adapt to the new version of coqtop by disabling the native compiler"
- "Resolved universe inconsistency in Freudenthal."
- "epis are surjective"

Some bad examples:

- "further progess"  Progress in what files?
- "Bug in [Equivalences.v]."  Was the bug fixed, or just noticed and
  flagged in comments, or what?
- "asdfjkl"

[commits1]: http://stackoverflow.com/questions/43598/suggestions-for-a-good-commit-message-format-guideline

[commits2]: http://stackoverflow.com/questions/3580013/should-i-use-past-or-present-tense-in-git-commit-messages

### Creating new files ###

If you create a new file, you must add it to `Makefile_targets.mk` so
that it will get compiled by `make`.  We suggest running `make strict`
rather than just `make`, so that you will get an error if you forget.
Of course, you'll also need to `git add` it.

You will probably also want to add your new file to `HoTT.v`, unless
it is outside the core (e.g. in `contrib/`) or should not be exported
for some other reason.

### Travis ###

We use the [Travis Continuous Integration Platform][travis] to check
that pull requests do not break anything, and also to automatically
update various things (such as the documentation, proviola, and
dependency graph liked on the [project wiki][wiki]).  Normally you
shouldn't need to know anything about this; Travis automatically
checks every pull request made to the central repository.

[travis]: https://travis-ci.org/

[wiki]: https://github.com/HoTT/HoTT/wiki

### Git rebase ###

If the master branch has diverged in some significant way since a pull
request was made, then merging it may result in non-compiling code.
Or the changes may conflict so that github becomes unable to merge it
automatically.  In either case, the situation should be resolved
manually before the pull request can be merged, and the resolution
should generally be done by the submitter of the pull request.

One way to do the resolution is to merge the current master branch
into the branch from which the pull request was made, resolving
conflicts manually, and then make and commit whatever other changes
may be necessary.  This has the disadvantage of creating new merge
commits, so another option is to `git rebase` against the master
branch.  We encourage the use of `rebase` if you are comfortable with
it; but for newcomers to git, rebasing can be intimidating, so merges
are also perfectly acceptable.

### Timing scripts ###

There are scripts in `etc/timing` to track (compile-time) performance
changes in the library.  When you make large changes, you may want to
include performance information in your commit message (recommended,
but certainly not required!).  To do this, use the following work-flow
from the root of the repository after you have made your edits.  To
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

This pops open an editor.  You should add lines at the beginning of
the commit message, leaving at least one blank line before the
performance table.

See the comments at the top of `make-pretty-timed-diff.sh` for more
detailed instructions and caveats.
