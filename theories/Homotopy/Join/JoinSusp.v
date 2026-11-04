From HoTT Require Import Basics Types.
Require Import Join.Core Join.JoinAssoc Suspension Spaces.Spheres.
From HoTT.WildCat Require Import Core Universe Equiv.
Require Import Spaces.Nat.Core.
Require Import Pointed.Core Pointed.pEquiv Pointed.pSusp.

Local Open Scope pointed_scope.

(** * Diamonds in the self-join of a suspension *)

Definition diamond_susp {A : Type} (t : Susp A)
  : diamond South t North t.
Proof.
  revert t.
  snapply Susp_ind.
  - exact (diamond_v South North 1).
  - exact (diamond_h North South 1).
  - intro a.
    apply diamond_twist.
Defined.

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

(** A pointed version of [equiv_join_sphere], starting in dimension 0. *)
Definition pequiv_pjoin_sphere (n m : nat)
  : pjoin (psphere n) (Sphere m) <~>* psphere (n + m.+1)%nat
  := Build_pEquiv' (equiv_join_sphere n.+1 m.+1) 1.

(** The suspension of a join is the join with one factor suspended. *)
Definition equiv_susp_join (A B : Type)
  : Susp (Join A B) <~> Join (Susp A) B
  := equiv_functor_join (equiv_join_susp A) equiv_idmap
       oE join_assoc Bool A B
       oE (equiv_join_susp (Join A B))^-1%equiv.

Definition pequiv_psusp_join (A B : Type)
  : psusp (Join A B) <~>* pjoin (psusp A) B
  := Build_pEquiv' (equiv_susp_join A B) 1.
