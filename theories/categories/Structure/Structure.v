(** Since there are only notations in [Structure.Notations], we can just export those. *)
Require Export Structure.Notations.

Require Structure.Core.

Include Structure.Core.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
