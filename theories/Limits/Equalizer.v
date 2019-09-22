Require Import Basics.

(** Equalizers *)

Definition Equalizer {A B} (f g : A -> B)
  := {x : A & f x = g x}.
