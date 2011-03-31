(** Coq is very good at inductive definitions. We look at a
    simple example. *)

(** This is how you import a package. The package [Arith] contains
    basic facts about natural numbers. *)
Require Import Arith.

(** A binary tree is either empty or it is composed of the left
   and the right subtree. *)
Inductive tree :=
  | empty : tree
  | node : tree -> tree -> tree.

(** Exercise: draw the following tree. *)
Definition bush :=
  node (node empty empty)
  (node empty (node (node empty empty)
    (node empty (node empty (node empty empty))))).

(** The size of the tree is the number of its nodes, and is a
   recursively defined function. In Coq such functions are defined
   with [Fixpoint]. Only total functions can be defined, so Coq will
   reject a [Fixpoint] definition for which it cannot demonstrate
   well-foundedness.

   Remark: the successor operation is called [S].
*)
Fixpoint size t :=
  match t with
    | empty => 0
    | node t1 t2 => S (size t1 + size t2)
  end.

(** Here is anoter simple function on trees which swaps around
   the left and the right subtrees recursively. *)
Fixpoint swap t :=
  match t with
    | empty => empty
    | node t1 t2 => node (swap t2) (swap t1)
  end.

(** We can compute the value of a function on a particular argument. *)

Eval compute in size bush.

Eval compute in swap bush.

(** Coq automatically generates inductive reasoning principles
   from inductive definitions. *)
Print tree_ind.

(** The [induction] tactic applied the generated inductive principles,
   as shown by this simple theorem. *)
Theorem swap_preserves_size t : size t = size (swap t).
Proof.
  induction t.
  auto.
  simpl.
  f_equal.
  transitivity (size t2 + size t1).
  (* At this point we suspect that the standard Coq library contains
     the fact that plus is commutative. There are various search
     commands that let you inspect the known theorems. *)
  SearchAbout plus.
  (* After some scrolling of up and down we find [plus_comm]. *)
  apply plus_comm.
  f_equal; auto.
Qed.
Print swap_preserves_size.

(** Exercise: prove that [swap] is an involution. *)

(** The full tree of depth [n]. *)
Fixpoint full_tree n :=
  match n with
    | 0 => empty
    | S m => node (full_tree m) (full_tree m)
  end.

(** Exercise: prove that [full_tree] is a fixed point of [swap]. *)

(** Exercise: define a function which counts how many times the empty
   tree appears in a tree. For example, [empty] appears 9 times in
   [bush]. Prove a theorem which relates the number of nodes and the
   number of empty trees in a tree. *)
