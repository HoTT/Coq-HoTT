(** To assume the Funext axiom outright, import this file.
    (Doing this instead of simply positing Funext directly
    avoids creating multiple witnesses for the axiom in
    different developments.) *)

Require Import Overture.

Context `{funext_axiom : Funext}.
