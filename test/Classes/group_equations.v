From HoTT Require Import
  Classes.interfaces.abstract_algebra
  Classes.theory.groups
  Classes.theory.rings.

Generalizable Variables R.

(** The equations in [Classes.theory.groups] that take the operation as an explicit argument can be used to rewrite with [plus] and [mult]. *)

Local Example swap_middle_plus_mult `{IsCRing R} (a b c d : R)
  : (a + b) + (c + d) = (a + c) + (b + d)
    /\ (a * b) * (c * d) = (a * c) * (b * d).
Proof.
  split.
  - rewrite (swap_middle (+)).
    reflexivity.
  - rewrite (swap_middle (.*.)).
    reflexivity.
Defined.

Local Example inverse_cancel_plus `{IsCRing R} (x y z : R)
  : (x - y + y) + (x + y - y) + ((x - y) + (y - z)) + ((z + x) - (z + y))
    = x + x + (x - z) + (x - y).
Proof.
  rewrite (left_inverse_cancel (+)).
  rewrite (right_inverse_cancel (+)).
  rewrite (inverse_telescope (+)).
  rewrite (common_left_cancel (+)).
  reflexivity.
Defined.
