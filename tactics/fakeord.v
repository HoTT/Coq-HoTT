Require Import HoTT.Basics.Overture HoTT.Types.Bool.
Require Export HoTTClasses.misc.settings.

(* Fake orders are orders used for computing at the meta level,
   so we don't need to prove anything about them. *)

Inductive CMP := LT | EQ | GT.

Class FakeOrdered A := fake_lt : A -> A -> CMP.

Instance: FakeOrdered Empty.
Proof.
intros [].
Defined.

Instance: FakeOrdered Unit.
Proof.
intros _ _;exact EQ.
Defined.

Instance fakeord_sum `{FakeOrdered A} `{FakeOrdered B} : FakeOrdered (A+B)
  := fun s1 s2 =>
  match s1, s2 with
  | inl a1, inl a2 => fake_lt a1 a2
  | inr b1, inr b2 => fake_lt b1 b2
  | inl _, inr _ => LT
  | inr _, inl _ => GT
  end.
