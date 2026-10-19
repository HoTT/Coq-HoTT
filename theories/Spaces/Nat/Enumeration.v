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

Lemma nat_unpair_hit (a b : nat) : {n : nat & nat_unpair n = (a, b)}.
Proof.
  (** By induction on the diagonal [a + b], and then on [b]. *)
  pose (d := a + b); assert (e : a + b = d) by reflexivity; clearbody d.
  revert a b e; induction d as [|d IH]; intros a b; revert a.
  - intros a e; exists 0.
    destruct a; [|discriminate e]; destruct b; [|discriminate e]; reflexivity.
  - induction b as [|b IHb]; intros a e.
    + destruct (IH 0 d idpath) as [n p]; exists (S n); cbn; rewrite p.
      rewrite <- e, nat_add_zero_r; reflexivity.
    + destruct (IHb (S a) (nat_add_succ_l a b @ (nat_add_succ_r a b)^ @ e)) as [n p].
      exists (S n); cbn; rewrite p; reflexivity.
Defined.

(** Surjections from the natural numbers onto [X] and onto [Y] give a surjection onto [X * Y]. *)
Definition nat_prod_enumerator {X Y : Type} (s : nat -> X) (t : nat -> Y) (n : nat) : X * Y
  := (s (fst (nat_unpair n)), t (snd (nat_unpair n))).

Definition issurj_nat_prod_enumerator {X Y : Type} (s : nat -> X) (t : nat -> Y)
  {s_surj : IsSurjection s} {t_surj : IsSurjection t}
  : IsSurjection (nat_prod_enumerator s t).
Proof.
  apply BuildIsSurjection; intros [x y].
  pose proof (@center _ (s_surj x)) as a; pose proof (@center _ (t_surj y)) as b.
  strip_truncations; destruct a as [a p], b as [b q].
  destruct (nat_unpair_hit a b) as [n r].
  apply tr; exists n; unfold nat_prod_enumerator; rewrite r; exact (path_prod' p q).
Defined.
