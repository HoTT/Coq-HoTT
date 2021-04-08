(** * Representable profunctors *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.Category.Prod HoTT.Categories.Category.Dual HoTT.Categories.Functor.Prod.Core HoTT.Categories.SetCategory.Core HoTT.Categories.Profunctor.Core HoTT.Categories.Functor.Dual HoTT.Categories.Profunctor.Identity HoTT.Categories.Functor.Composition.Core HoTT.Categories.Functor.Identity.
Require Import HoTT.HSet.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope profunctor_scope.

Section representable.
  (** Quoting nCatLab on profunctors:

      Every functor [f : C → D] induces two profunctors [D(1, f) : C ⇸ D] and [D(f, 1) : D ⇸ C], defined by [D(1, f)(d, c) = D(d, f(c))] and [D(f, 1)(c, d) = D(f(c), d)]. These profunctors are called representable (or sometimes one of them is corepresentable). *)

  Context `{Funext}.

  Definition representable C D (F : Functor C D) : C -|-> D
    := 1%profunctor o (1, F).

  (** TODO: Is there a define this so that we get proofs by duality about representable functors?  If we had judgemental eta expansion, maybe we could do it as [swap o (representable F^op)^op]? *)
  Definition corepresentable C D (F : Functor C D) : D -|-> C
    := 1%profunctor o (F^op, 1).
End representable.
