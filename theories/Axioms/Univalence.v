Require Import Types.Universe.

(** To assume the Univalence axiom outright, import this file. (Doing this instead of simply positing Univalence directly avoids creating multiple witnesses for the axiom in different developments.) *)

Axiom univalence_axiom : Univalence.
Existing Instance univalence_axiom.
