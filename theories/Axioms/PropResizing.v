Require Import Basics.Overture.

(** To assume the PropResizing axiom outright, import this file. (Doing this instead of simply positing PropResizing directly avoids creating multiple witnesses for the axiom in different developments.) *)

Axiom propresizing_axiom : PropResizing.
Global Existing Instance propresizing_axiom.
