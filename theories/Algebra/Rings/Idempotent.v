Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
Require Import Basics.Equivalences Basics.Trunc Types.Sigma WildCat.Core.
Require Import Nat.Core Rings.Ring.

Local Open Scope mc_scope.

(** * Idempotent elements of rings *)

(** ** Definition *)

Class IsIdempotent (R : Ring) (e : R)
  := rng_idem : e * e = e.

Global Instance ishprop_isidempotent R e : IsHProp (IsIdempotent R e).
Proof.
  unfold IsIdempotent; exact _.
Defined.

(** *** Examples *)

(** Zero is idempotent. *)
Global Instance isidempotent_zero (R : Ring) : IsIdempotent R 0
  := rng_mult_zero_r 0.

(** One is idempotent. *)
Global Instance isidempotent_one (R : Ring) : IsIdempotent R 1
  := rng_mult_one_r 1.

(** If [e] is idempotent, then [1 - e] is idempotent. *)
Global Instance isidempotent_complement (R : Ring) (e : R) `{IsIdempotent R e}
  : IsIdempotent R (1 - e).
Proof.
  unfold IsIdempotent.
  rewrite rng_dist_l_negate.
  rewrite 2 rng_dist_r_negate.
  rewrite 2 rng_mult_one_l.
  rewrite rng_mult_one_r.
  rewrite rng_idem.
  rewrite rng_plus_negate_r.
  rewrite rng_negate_zero.
  nrapply rng_plus_zero_r.
Defined.

(** If [e] is idempotent, then it is also an idempotent element of the opposite ring. *)
Global Instance isidempotent_op (R : Ring) (e : R) `{i : IsIdempotent R e}
  : IsIdempotent (rng_op R) e
  := i.

(** Any positive power of an idempotent element [e] is [e]. *)
Definition rng_power_idem {R : Ring} (e : R) `{IsIdempotent R e} (n : nat)
  : (1 <= n)%nat -> rng_power e n = e.
Proof.
  intros L; induction L.
  - snrapply rng_mult_one_r.
  - rhs_V rapply rng_idem.
    exact (ap (e *.) IHL).
Defined.

(** Ring homomorphisms preserve idempotent elements. *)
Global Instance isidempotent_rng_homo {R S : Ring} (f : R $-> S) (e : R)
  : IsIdempotent R e -> IsIdempotent S (f e).
Proof.
  intros p.
  lhs_V nrapply rng_homo_mult.
  exact (ap f p).
Defined.

(** ** Orthogonal idempotent elements *)

(** Two idempotent elements [e] and [f] are orthogonal if both [e * f = 0] and [f * e = 0]. *)
Class IsOrthogonal (R : Ring) (e f : R)
  `{!IsIdempotent R e, !IsIdempotent R f} := {
  rng_idem_orth : e * f = 0 ;
  rng_idem_orth' : f * e = 0 ;
}.

Definition issig_IsOrthogonal {R : Ring} {e f : R}
  `{IsIdempotent R e, IsIdempotent R f}
  : _ <~> IsOrthogonal R e f
  := ltac:(issig).

Global Instance ishprop_isorthogonal R e f
  `{IsIdempotent R e, IsIdempotent R f}
  : IsHProp (IsOrthogonal R e f).
Proof.
  exact (istrunc_equiv_istrunc _ issig_IsOrthogonal). 
Defined.

(** *** Properties *)

(** Two idempotents being orthogonal is a symmetric relation. *)
Definition isorthogonal_swap (R : Ring) (e f : R) `{IsOrthogonal R e f}
  : IsOrthogonal R f e
  := {| rng_idem_orth := rng_idem_orth' ; rng_idem_orth' := rng_idem_orth |}.
Hint Immediate isorthogonal_swap : typeclass_instances.

(** If [e] and [f] are orthogonal idempotents, then they are also orthogonal idempotents in the opposite ring. *)
Global Instance isorthogonal_op {R : Ring} (e f : R) `{r : IsOrthogonal R e f}
  : IsOrthogonal (rng_op R) e f.
Proof.
  snrapply Build_IsOrthogonal.
  - exact (rng_idem_orth' (R:=R)).
  - exact (rng_idem_orth (R:=R)).
Defined.

(** If [e] and [f] are orthogonal idempotents, then [e + f] is idempotent. *)
Global Instance isidempotent_plus_orthogonal {R : Ring} (e f : R)
  `{IsOrthogonal R e f}
  : IsIdempotent R (e + f).
Proof.
  unfold IsIdempotent.
  rewrite rng_dist_l.
  rewrite 2 rng_dist_r.
  rewrite 2 rng_idem.
  rewrite 2 rng_idem_orth.
  by rewrite rng_plus_zero_r, rng_plus_zero_l.
Defined.

(** An idempotent element [e] is orthogonal to its complement [1 - e]. *)
Global Instance isorthogonal_complement {R : Ring} (e : R) `{IsIdempotent R e}
  : IsOrthogonal R e (1 - e).
Proof.
  snrapply Build_IsOrthogonal.
  1: rewrite rng_dist_l_negate,rng_mult_one_r.
  2: rewrite rng_dist_r_negate, rng_mult_one_l.
  1,2: rewrite rng_idem.
  1,2: apply rng_plus_negate_r.
Defined.
