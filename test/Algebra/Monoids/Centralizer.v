From HoTT.Basics Require Import Overture.
From HoTT.Algebra.Monoids Require Import Monoid Centralizer.

Section AssociativeOperation.
  Universe u.
  Context {A : Type@{u}} {Aop : SgOp A} `{!Associative Aop}.

  (** Multiplicative closure does not require the carrier to be a set. *)
  Succeed Definition test@{|} (g h k : A)
    (p : centralizer g h) (q : centralizer g k)
    : centralizer g (Aop h k) := centralizer_sgop g h k p q.
End AssociativeOperation.

Section UnitalOperation.
  Universe u.
  Context {A : Type@{u}} {Aop : SgOp A} {Aunit : MonUnit A}
    `{!LeftIdentity Aop mon_unit, !RightIdentity Aop mon_unit}.

  (** Unit membership requires neither associativity nor setness. *)
  Succeed Definition test@{|} (g : A)
    : centralizer g mon_unit := centralizer_unit g.
End UnitalOperation.
