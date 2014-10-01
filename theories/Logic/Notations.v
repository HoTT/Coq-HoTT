(* -*- mode: coq; mode: visual-line -*- *)
Require Import Logic.Generic.

(** We define some notations for the generic logical operations.  These are in a separate file so that people can use Logic.Generic without them.  (It would not suffice to put them in their own scope, because for satisfactory behavior they all need to be in [type_scope].)

Moreover, we put them each in a separate module so that people who wish can import some of them but not others.  Thus, you can say 

Require Import Logic.Notations.

to get them all, or

Require Logic.Notations.
Import Logic.Notations.Exists.
...

to get only some of them. *)

Module Export Not.

  Global Notation "~ P" := (hnot P) (at level 75, right associativity) : type_scope.

End Not.

Module Export Or.

  Global Notation "P \/ Q" := (hor P Q) (at level 85, right associativity) : type_scope.

End Or.

Module Export Exists.

  (** The following notation allows us to write [hexists (x:A), P x] rather than [hex (fun (x:A) => P x)]. *)
  Global Notation "'hexists' x .. y , p" := (hex (fun x => .. (hex (fun y => p)) ..))
    (at level 200, x binder, y binder, right associativity)
  : type_scope.

End Exists.
