(** Since there are only notations in [Structure.Notations], we can just export those. *)
Require Export HoTT.Categories.Structure.Notations.

Require HoTT.Categories.Structure.Core.
Require HoTT.Categories.Structure.IdentityPrinciple.

Include Structure.Core.
Include Structure.IdentityPrinciple.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
