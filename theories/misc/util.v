Require Import
  HoTTClasses.misc.stdlib_hints.

Definition ap2 `(f : A -> B -> C) {x1 x2 y1 y2}:
  x1 = x2 -> y1 = y2 -> f x1 y1 = f x2 y2.
Proof.
intros H1 H2;destruct H1,H2;reflexivity.
Defined.

Definition uncurry {A B C} (f: A -> B -> C) (p: A * B): C := f (fst p) (snd p).

Definition DN (T: Type): Type := (T -> Empty) -> Empty.
Class Stable P := stable: DN P -> P.

Lemma not_symmetry `{Symmetric A R} (x y: A): ~R x y -> ~R y x.
Proof.
auto.
Qed.
(* Also see Coq bug #2358.
   A totally different approach would be to define negated relations
   such as inequality as separate relations rather than notations,
   so that the existing [symmetry] will work for them.
   However, this most likely breaks other things. *)

Fixpoint repeat {A:Type} (n:nat) (f : A -> A) (x : A) : A :=
  match n with
  | 0%nat => x
  | S k => f (repeat k f x)
  end.
