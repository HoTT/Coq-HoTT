(** * Enumerations by the natural numbers *)

(** We enumerate pairs of natural numbers, and deduce that a product of two images of the natural numbers is again an image of the natural numbers.  Such surjections from the natural numbers are what bounded search needs, see [minimal_n_alt_type]. *)

From HoTT Require Import Basics Types.Prod Truncations.Core Spaces.Nat.Core.
From HoTT Require Import Modalities.ReflectiveSubuniverse.

Local Open Scope nat_scope.

(** ** Enumerating pairs *)

(** We enumerate pairs of natural numbers diagonal by diagonal.  Here the [m]th diagonal consists of the pairs [(a, b)] with [a + b = m]. *)
Fixpoint nat_unpair (n : nat) : nat * nat
  := match n with
     | 0 => (0, 0)
     | S n => match nat_unpair n with
             | (0, b) => (S b, 0)
             | (S a, b) => (a, S b)
             end
     end.

(** If we hit the end of a diagonal, we hit everything else on the diagonal. *)
Local Definition nat_unpair_hit_diagonal (a b : nat) (p : {n : nat & nat_unpair n = (a + b, 0)})
  : {m : nat & nat_unpair m = (a, b)}.
Proof.
  revert a p; induction b as [|b IH]; intros a p.
  - rewrite nat_add_zero_r in p.  exact p.
  - rewrite nat_add_succ_r in p.
    destruct (IH (S a) p) as [m q].
    exists (S m). cbn; rewrite q. reflexivity.
Defined.

(** We hit everything on the x-axis. *)
Local Definition nat_unpair_hit_axis (d : nat) : {n : nat & nat_unpair n = (d, 0)}.
Proof.
  induction d as [|d IH].
  - exact (0; idpath).
  - destruct (nat_unpair_hit_diagonal 0 d IH) as [n p].
    exists (S n). cbn; rewrite p. reflexivity.
Defined.

(** [nat_unpair] is a split surjective map. *)
Definition nat_unpair_hit (a b : nat) : {n : nat & nat_unpair n = (a, b)}
  := nat_unpair_hit_diagonal a b (nat_unpair_hit_axis (a + b)).

(** Therefore, [nat_unpair] is surjective. *)
Instance issurj_nat_unpair : IsSurjection nat_unpair.
Proof.
  apply BuildIsSurjection; intros [a b].
  exact (tr (nat_unpair_hit a b)).
Defined.

(** We can use [nat_unpair] to enumerate the product of two types that can be enumerated. *)
Definition nat_prod_enumerator {X Y : Type} (s : nat -> X) (t : nat -> Y) : nat -> X * Y
  := functor_prod s t o nat_unpair.

(** The map is surjective because connected maps are closed under composition and products via [conn_map_compose] and [conn_map_functor_prod]. *)
Instance issurj_nat_prod_enumerator {X Y : Type} {s : nat -> X} {t : nat -> Y}
  `{IsSurjection s} `{IsSurjection t}
  : IsSurjection (nat_prod_enumerator s t)
  := _.
