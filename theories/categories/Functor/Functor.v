(** * Functors *)
(** Since there are only notations in [Functor.Notations], we can just export those. *)
Require Export Functor.Notations.

(** ** Definition *)
Require Functor.Core.
(** ** Composition *)
Require Functor.Composition.Core.
(** ** Duals *)
Require Functor.Dual.
(** ** Identity *)
Require Functor.Identity.
(** ** Classification of path space *)
Require Functor.Paths.
(** ** Product functors *)
Require Functor.Prod.
(** ** Coproduct functors *)
Require Functor.Sum.
(** ** Full, Faithful, Fully Faithful *)
Require Functor.Attributes.
(** ** Pointwise functors (functoriality of functor category construction) *)
Require Functor.Pointwise.

Include Functor.Composition.Core.
Include Functor.Core.
Include Functor.Dual.
Include Functor.Identity.
Include Functor.Paths.
Include Functor.Prod.
Include Functor.Sum.
Include Functor.Attributes.
Include Functor.Pointwise.
(** We don't want to make utf-8 notations the default, so we don't export them. *)

(** Since [Prod] is a separate sub-directory, we need to re-create the module structure *)
Module Prod.
  Require Functor.Prod.Prod.
  Include Functor.Prod.Prod.
End Prod.

Module Pointwise.
  Require Functor.Pointwise.Pointwise.
  Include Functor.Pointwise.Pointwise.
End Pointwise.

Module Composition.
  Require Functor.Composition.Composition.
  Include Functor.Composition.Composition.
End Composition.
