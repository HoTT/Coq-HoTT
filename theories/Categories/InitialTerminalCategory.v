(** * Initial and terminal categories *)
(** ** Definitions *)
Require InitialTerminalCategory.Core.
Include InitialTerminalCategory.Core.

(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
(** ** Functors to and from initial and terminal categories *)
Require InitialTerminalCategory.Functors.
(** ** Natural transformations between functors from initial categories and to terminal categories *)
Require InitialTerminalCategory.NaturalTransformations.
(** ** Pseudounctors from initial and terminal categories *)
Require InitialTerminalCategory.Pseudofunctors.


Require Export InitialTerminalCategory.Notations.
