From HoTT Require Import Basics Types.
Require Import Join.Core Join.JoinAssoc Suspension Spaces.Spheres.
Require Import WildCat.
Require Import Spaces.Nat.Core.

(** * [Join Bool A] is equivalent to [Susp A]

  We give a direct proof of this fact. It is also possible to give a proof using [opyon_equiv_0gpd]; see PR#1769. *)

Definition join_to_susp (A : Type) : Join Bool A -> Susp A.
Proof.
  srapply Join_rec.
  - exact (fun b => if b then North else South).
  - exact (fun a => South).
  - intros [|] a.
    + exact (merid a).
    + reflexivity.
Defined.

Definition susp_to_join (A : Type) : Susp A -> Join Bool A.
Proof.
  srapply (Susp_rec (joinl true) (joinl false)).
  exact (zigzag true false).
Defined.

Instance isequiv_join_to_susp (A : Type) : IsEquiv (join_to_susp A).
Proof.
  snapply (isequiv_adjointify _ (susp_to_join A)).
  - snapply Susp_ind.
    1,2: reflexivity.
    intros a; cbn beta.
    transport_paths FFlr.
    apply equiv_p1_1q.
    lhs napply (ap _ _); [napply Susp_rec_beta_merid | ].
    lhs napply (Join_rec_beta_zigzag _ _ _ true false a).
    apply concat_p1.
  - srapply (Join_ind_FFlr (join_to_susp A)); cbn beta.
    1: intros [|]; reflexivity.
    1: intros a; apply jglue.
    intros b a; cbn beta.
    lhs nrefine (ap _ _ @@ 1).
    1: napply Join_rec_beta_jglue.
    destruct b.
    + rhs napply concat_1p.
      lhs nrefine (_ @@ 1); [napply Susp_rec_beta_merid | ].
      apply concat_pV_p.
    + reflexivity.
Defined.

Definition equiv_join_susp (A : Type) : Join Bool A <~> Susp A
  := Build_Equiv _ _ (join_to_susp A) _.

(** It follows that the join powers of [Bool] are spheres.  These are sometimes a convenient alternative to working with spheres, so we give them a name. *)
Definition bool_pow (n : nat) := join_power Bool n.

Definition equiv_bool_pow_sphere (n : nat): bool_pow n <~> Sphere (n.-1).
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - simpl.  refine (_ oE equiv_join_susp _).
    exact (emap Susp IHn).
Defined.

(** It follows that joins of spheres are spheres, starting in dimension -1. *)
Definition equiv_join_sphere (n m : nat)
  : Join (Sphere n.-1) (Sphere m.-1) <~> Sphere (n + m)%nat.-1.
Proof.
  refine (_ oE equiv_functor_join _ _).
  2,3: symmetry; exact (equiv_bool_pow_sphere _).
  refine (equiv_bool_pow_sphere _ oE _).
  apply join_join_power.
Defined.
