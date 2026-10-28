From HoTT Require Import Basics.
From HoTT Require Import Homotopy.Join.Core.

Local Open Scope path_scope.

Section ZigzagNaturality.
  Universe u v w.
  Constraint u <= w.
  Constraint v <= w.
  Context {A : Type@{u}} {B : Type@{v}}.

  Example zigzag_natsq_universes
    {a a' c c' : A} {b b' : B}
    (p : a = a') (q : c = c') (r : b = b')
    : ap joinl p @ zigzag@{u v w} a' c' b'
      = zigzag@{u v w} a c b @ ap joinl q
    := zigzag_natsq@{u v w} p q r.

  Example zigzag_natsq_idpath (a c : A) (b : B)
    : zigzag_natsq (idpath a) (idpath c) (idpath b)
      = concat_1p_p1 (zigzag a c b) := idpath.
End ZigzagNaturality.

(** The diamond twist is a dependent path between equalities of zigzags, without a PathSquare. *)
Example diamond_twist_path {A : Type} {a a' : A} (p : a = a')
  : transport (fun x => zigzag a' x a = zigzag a' x x) p
      (diamond_v a' a 1) = diamond_h a a' 1
  := diamond_twist p.

Example diamond_twist_idpath {A : Type} (a : A)
  : diamond_twist (idpath a) = diamond_symm a a := idpath.
