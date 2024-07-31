Require Import Basics.Overture Basics.Decidable Spaces.Nat.
Require Import Algebra.Rings.Ring.
Require Import Classes.interfaces.abstract_algebra.

Local Set Universe Minimization ToSet.
Local Set Polymorphic Inductive Cumulativity.

(** ** Kronecker Delta *)

Section AssumeDecidable.
  (** Throughout this section, we assume that we have a type [A] with decidable equality. This will be our indexing type and can be thought of as [nat] for reading purposes. *)

  Universes u v.
  Context {A : Type@{u}} `{DecidablePaths@{u} A} {R : Ring@{v}}.

  (** The Kronecker delta function is a function of elements of [A] that is 1 when the two numbers are equal and 0 otherwise. It is useful for working with finite sums of ring elements. *)
  Definition kronecker_delta@{} (i j : A) : R
    := if dec (i = j) then 1 else 0.

  (** Kronecker delta with the same index is 1. *)
  Definition kronecker_delta_refl@{} (i : A)
    : kronecker_delta i i = 1.
  Proof.
    unfold kronecker_delta.
    generalize (dec (i = i)).
    by rapply decidable_paths_refl.
  Defined.

  (** Kronecker delta with differing indices is 0. *)
  Definition kronecker_delta_neq@{} {i j : A} (p : i <> j)
    : kronecker_delta i j = 0.
  Proof.
    unfold kronecker_delta.
    by decidable_false (dec (i = j)) p.
  Defined.

  (** Kronecker delta is symmetric in its arguments. *)
  Definition kronecker_delta_symm@{} (i j : A)
    : kronecker_delta i j = kronecker_delta j i.
  Proof.
    unfold kronecker_delta.
    destruct (dec (i = j)) as [p|q].
    - by decidable_true (dec (j = i)) p^.
    - by decidable_false (dec (j = i)) (symmetric_neq q).
  Defined.

  (** An injective endofunction on [A] preserves the Kronecker delta. *)
  Definition kronecker_delta_map_inj@{} (i j : A) (f : A -> A)
    `{!IsInjective f}
    : kronecker_delta (f i) (f j) = kronecker_delta i j.
  Proof.
    unfold kronecker_delta.
    destruct (dec (i = j)) as [p|p].
    - by decidable_true (dec (f i = f j)) (ap f p).
    - destruct (dec (f i = f j)) as [q|q].
      + apply (injective f) in q.
        contradiction.
      + reflexivity.
  Defined.

  (** Kronecker delta commutes with any ring element. *)
  Definition kronecker_delta_comm@{} (i j : A) (r : R)
    : r * kronecker_delta i j = kronecker_delta i j * r.
  Proof.
    unfold kronecker_delta.
    destruct (dec (i = j)).
    - exact (rng_mult_one_r _ @ (rng_mult_one_l _)^).
    - exact (rng_mult_zero_r _ @ (rng_mult_zero_l _)^).
  Defined.
    
End AssumeDecidable.

(** The following lemmas are specialised to when the indexing type is [nat]. *)

(** Kronecker delta where the first index is strictly less than the second is 0. *)
Definition kronecker_delta_lt {R : Ring} {i j : nat} (p : (i < j)%nat)
  : kronecker_delta (R:=R) i j = 0.
Proof.
  apply kronecker_delta_neq.
  intros q; destruct q.
  by apply lt_irrefl in p.
Defined.

(** Kronecker delta where the first index is strictly greater than the second is 0. *)
Definition kronecker_delta_gt {R : Ring} {i j : nat} (p : (j < i)%nat)
  : kronecker_delta (R:=R) i j = 0.
Proof.
  apply kronecker_delta_neq.
  intros q; destruct q.
  by apply lt_irrefl in p.
Defined.

(** Kronecker delta can be used to extract a single term from a finite sum. *)
Definition rng_sum_kronecker_delta_l {R : Ring} (n i : nat) (Hi : (i < n)%nat)
  (f : forall k, (k < n)%nat -> R)
  : ab_sum n (fun j Hj => kronecker_delta i j * f j Hj) = f i Hi.
Proof.
  revert i Hi f; simple_induction n n IHn; intros i Hi f.
  1: destruct (not_leq_Sn_0 _ Hi).
  destruct (dec (i = n)) as [p|p].
  - destruct p; simpl.
    rewrite kronecker_delta_refl.
    rewrite rng_mult_one_l.
    rewrite <- rng_plus_zero_r.
    apply ap11.
    { apply (ap (fun h => plus (f i h))), path_ishprop. }
    nrapply ab_sum_zero.
    intros k Hk.
    rewrite (kronecker_delta_gt Hk).
    apply rng_mult_zero_l.
  - simpl; lhs nrapply ap.
    + nrapply IHn.
      apply neq_iff_lt_or_gt in p.
      destruct p; [assumption|].
      apply gt_iff_not_leq in Hi.
      contradiction Hi.
    + rewrite (kronecker_delta_neq p).
      rewrite rng_mult_zero_l.
      rewrite grp_unit_l.
      apply ap, path_ishprop.
Defined.

(** Variant of [rng_sum_kronecker_delta_l] where the indexing is swapped. *)
Definition rng_sum_kronecker_delta_l' {R : Ring} (n i : nat) (Hi : (i < n)%nat)
  (f : forall k, (k < n)%nat -> R)
  : ab_sum n (fun j Hj => kronecker_delta j i * f j Hj) = f i Hi.
Proof.
  lhs nrapply path_ab_sum.
  2: nrapply rng_sum_kronecker_delta_l.
  intros k Hk.
  cbn; f_ap; apply kronecker_delta_symm.
Defined.

(** Variant of [rng_sum_kronecker_delta_l] where the Kronecker delta appears on the right. *)
Definition rng_sum_kronecker_delta_r {R : Ring} (n i : nat) (Hi : (i < n)%nat)
  (f : forall k, (k < n)%nat -> R)
  : ab_sum n (fun j Hj => f j Hj * kronecker_delta i j) = f i Hi.
Proof.
  lhs nrapply path_ab_sum.
  2: nrapply rng_sum_kronecker_delta_l.
  intros k Hk.
  apply kronecker_delta_comm.
Defined.

(** Variant of [rng_sum_kronecker_delta_r] where the indexing is swapped. *)
Definition rng_sum_kronecker_delta_r' {R : Ring} (n i : nat) (Hi : (i < n)%nat)
  (f : forall k, (k < n)%nat -> R)
  : ab_sum n (fun j Hj => f j Hj * kronecker_delta j i) = f i Hi.
Proof.
  lhs nrapply path_ab_sum.
  2: nrapply rng_sum_kronecker_delta_l'.
  intros k Hk.
  apply kronecker_delta_comm.
Defined.
