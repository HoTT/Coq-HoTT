(** To assume the Univalence axiom outright, import this file.
    (Doing this instead of simply positing Univalence directly
    avoids creating multiple witnesses for the axiom in
    different developments.) *)

Require Import types.Universe.

Instance univalence_axiom : Univalence.
  admit.
Defined.
