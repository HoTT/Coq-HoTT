(** * Lax Comma Categories *)
(** Since there are only notations in [LaxComma.Notations], we can just export those. *)
Local Set Warnings Append "-notation-overridden".
Require Export HoTT.Categories.LaxComma.Notations.

(** ** Definitions *)
Require HoTT.Categories.LaxComma.Core.

Include LaxComma.Core.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
