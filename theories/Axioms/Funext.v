(** To assume the Funext axiom outright, import this file.
    (Doing this instead of simply positing Funext directly
    avoids creating multiple witnesses for the axiom in
    different developments.) *)

Require Import Basics.Overture.

Axiom funext_axiom : Funext.
Global Existing Instance funext_axiom.
