From HoTT Require Import Basics.Overture Basics.PathGroupoids.

Local Open Scope path_scope.

Section Diagonal.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}} (f : A -> A -> B).

  (** The diagonal rule works with independent source and target universes. *)
  Example ap011_diag_universes {x y : A} (p : x = y)
    : ap011 f p p = ap (fun a => f a a) p
    := ap011_diag@{u v} f p.

  Example ap011_diag_idpath (a : A)
    : ap011_diag f (idpath a) = idpath := idpath.

  (** It combines with the existing rule to compute one argument at a time. *)
  Example ap_diagonal_is_ap {x y : A} (p : x = y)
    : ap (fun a => f a a) p
      = ap (fun a => f a x) p @ ap (fun a => f y a) p
    := (ap011_diag f p)^ @ ap011_is_ap f p p.
End Diagonal.
