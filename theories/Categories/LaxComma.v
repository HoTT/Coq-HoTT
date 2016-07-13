(** * Lax Comma Categories *)
(** Since there are only notations in [LaxComma.Notations], we can just export those. *)
Require Export LaxComma.Notations.

(** ** Definitions *)
Require LaxComma.Core.

Include LaxComma.Core.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
