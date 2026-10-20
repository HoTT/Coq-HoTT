(** * Enumerations by the natural numbers *)

(** We enumerate pairs of natural numbers, and deduce that a product of two images of the natural numbers is again an image of the natural numbers.  Such surjections from the natural numbers are what bounded search needs, see [minimal_n_alt_type]. *)

From HoTT Require Import Basics Types.Prod Truncations.Core Spaces.Nat.Core.

Local Open Scope nat_scope.

(** ** Enumerating pairs *)

(** We enumerate pairs of natural numbers diagonal by diagonal. *)
Fixpoint nat_unpair (n : nat) : nat * nat
  := match n with
     | 0 => (0, 0)
     | S n => match nat_unpair n with
             | (0, b) => (S b, 0)
             | (S a, b) => (a, S b)
             end
     end.

Local Definition nat_unpair_hit_diagonal (a b n : nat) (p : nat_unpair n = (a + b, 0))
  : {m : nat & nat_unpair m = (a, b)}.
Proof.
  revert a p; induction b as [|b IH]; intros a p.
  - exists n; rewrite p, nat_add_zero_r; reflexivity.
  - destruct (IH (S a) (p @ ap (fun k => (k, 0)) (nat_add_succ_r a b))) as [m q].
    exists (S m); cbn; rewrite q; reflexivity.
Defined.

Local Definition nat_unpair_hit_axis (d : nat) : {n : nat & nat_unpair n = (d, 0)}.
Proof.
  induction d as [|d IH].
  - exact (0; idpath).
  - destruct (nat_unpair_hit_diagonal 0 d _ IH.2) as [n p].
    exists (S n); cbn; rewrite p; reflexivity.
Defined.

Definition nat_unpair_hit (a b : nat) : {n : nat & nat_unpair n = (a, b)}
  := nat_unpair_hit_diagonal a b (nat_unpair_hit_axis (a + b)).1 (nat_unpair_hit_axis (a + b)).2.

Definition nat_prod_enumerator {X Y : Type} (s : nat -> X) (t : nat -> Y) (n : nat) : X * Y
  := (s (fst (nat_unpair n)), t (snd (nat_unpair n))).

Definition issurj_nat_prod_enumerator {X Y : Type} (s : nat -> X) (t : nat -> Y)
  {s_surj : IsSurjection s} {t_surj : IsSurjection t}
  : IsSurjection (nat_prod_enumerator s t).
Proof.
  apply BuildIsSurjection; intros [x y].
  pose proof (@center (merely (hfiber s x)) (s_surj x)) as a.
  pose proof (@center (merely (hfiber t y)) (t_surj y)) as b.
  strip_truncations; destruct a as [a p], b as [b q].
  destruct (nat_unpair_hit a b) as [n r].
  apply tr; exists n; unfold nat_prod_enumerator; rewrite r; exact (path_prod' p q).
Defined.
