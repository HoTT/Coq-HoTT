(** To assume the Univalence axiom outright, import this file.
    (Doing this instead of simply positing Univalence directly
    avoids creating multiple witnesses for the axiom in
    different developments.) *)

Require Import Types.Universe.

Axiom univalence_axiom : Univalence.
Global Existing Instance univalence_axiom.
