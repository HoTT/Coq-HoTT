(** Test that Ltac2 is available and compatible with the library. *)

From HoTT Require Import HoTT.

From Ltac2 Require Import Ltac2.

Ltac2 Type rec PNat :=
  [ Z | S (PNat) ].

Ltac2 rec padd (m : PNat) (n : PNat) :=
  match m with
  | Z => n
  | S m => S (padd m n)
  end.

Ltac2 Eval padd (S (S Z)) (S Z).

Ltac2 Type rec 'a Tree :=
  [ Empty | Node ('a, 'a Tree, 'a Tree)].

Ltac2 rec tree_size (t : 'a Tree) :=
  match t with
  | Empty => 0
  | Node _ l r => Int.add 1 (Int.add (tree_size l) (tree_size r))
  end.

Ltac2 Eval tree_size (Node 1 (Node 2 Empty Empty) Empty).
