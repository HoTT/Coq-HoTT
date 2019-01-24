(** * Profunctors *)
Require Import Category.Core Functor.Core Category.Prod Category.Dual Functor.Prod.Core SetCategory.Core.
Local Set Warnings Append "-notation-overridden".
Require Import Basics.Notations.
Local Set Warnings Append "notation-overridden".

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Declare Scope profunctor_scope.
Delimit Scope profunctor_scope with profunctor.

Section profunctor.
  (** Quoting nCatLab:

      If [C] and [D] are categories, a profunctor from [C] to [D] is a functor [Dᵒᵖ * C -> Set]. Such a profunctor is usually written as [F : C ⇸ D].

      Every functor [f : C -> D] induces two profunctors [D(1, f) : C ⇸ D] and [D(f, 1) : D ⇸ C], defined by [D(1,f)(d,c) = D(d, f(c))] and [D(f, 1)(c,d) = D(f(c), d)]. These profunctors are called representable (or sometimes one of them is corepresentable).

      In particular the identity profunctor [Id : C ⇸ C] is represented by the identity functor and hence is given by the hom-functor [C(−, −) : Cᵒᵖ * C -> Set].

      The notion generalizes to many other kinds of categories. For instance, if [C] and [D] are enriched over some symmetric closed monoidal category [V], then a profunctor from [C] to [D] is a [V]-functor [Dᵒᵖ ⊗ C -> V]. If they are internal categories, then a profunctor [C ⇸ D] is an internal diagram on [Dᵒᵖ * C], and so on. There are also other equivalent definitions in each case; see below.

      A profunctor is also sometimes called a (bi)module or a distributor or a correspondence, though the latter word is also used for a span. The term “module” tends to be common in Australia, especially in the enriched case; here the intuition is that for one-object [V]-categories, i.e. monoids in [V], profunctors really are the same as bimodules between such monoids in the usual sense. “Profunctor” is perhaps more common in the Set-based and internal cases (but is also used in the enriched case); here the intuition is that a profunctor is a generalization of a functor, via the construction of “representable” profunctors. Jean Bénabou, who invented the term and originally used “profunctor,” now prefers “distributor,” which is supposed to carry the intuition that a distributor generalizes a functor in a similar way to how a distribution generalizes a function.

      Note that the convention that a profunctor is a functor [Dᵒᵖ * C -> Set] is not universal; some authors reverse C and D and/or put the “op” on the other one. See the discussion below. *)

  Context `{Funext}.
  Variables C D : PreCategory.

  (** We capitalize [Profunctor] just like we capitalize [Functor]. *)
  Definition Profunctor := Functor (D^op * C) set_cat.
End profunctor.

Bind Scope profunctor_scope with Profunctor.

Module Export ProfunctorCoreNotations.
  Notation "x -|-> y" := (Profunctor x y) : type_scope.
End ProfunctorCoreNotations.
