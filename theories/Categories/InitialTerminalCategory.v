(** * Initial and terminal categories *)
(** ** Definitions *)
Require HoTT.Categories.InitialTerminalCategory.Core.
Include InitialTerminalCategory.Core.

(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
(** ** Functors to and from initial and terminal categories *)
Require HoTT.Categories.InitialTerminalCategory.Functors.
(** ** Natural transformations between functors from initial categories and to terminal categories *)
Require HoTT.Categories.InitialTerminalCategory.NaturalTransformations.
(** ** Pseudounctors from initial and terminal categories *)
Require HoTT.Categories.InitialTerminalCategory.Pseudofunctors.


Require Export HoTT.Categories.InitialTerminalCategory.Notations.
