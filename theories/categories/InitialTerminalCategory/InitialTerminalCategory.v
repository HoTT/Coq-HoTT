(** * Initial and terminal categories *)
(** ** Definitions *)
Require InitialTerminalCategory.Core.
Include InitialTerminalCategory.Core.
(** ** Functors to and from initial and terminal categories *)
Module Functors.
  Require InitialTerminalCategory.Functors.
  Include InitialTerminalCategory.Functors.
End Functors.
(** ** Natural transformations between functors from initial categories and to terminal categories *)
Module NaturalTransformations.
  Require InitialTerminalCategory.NaturalTransformations.
  Include InitialTerminalCategory.NaturalTransformations.
End NaturalTransformations.

Require Export InitialTerminalCategory.Notations.
