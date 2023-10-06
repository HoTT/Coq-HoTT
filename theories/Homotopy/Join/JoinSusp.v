Require Import Basics Types.
Require Import Join.Core Join.JoinAssoc Suspension Spaces.Spheres.
Require Import WildCat.
Require Import Spaces.Nat.Core.

(** We give a direct proof that the join of [bool] with a type is equivalent to a suspension. It is also possible to give a proof using [opyon_equiv_0gpd]; see PR#1769. *)

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
  intros a.
  exact (jglue _ a @ (jglue _ a)^).
Defined.

Global Instance isequiv_join_to_susp (A : Type) : IsEquiv (join_to_susp A).
Proof.
  snrapply (isequiv_adjointify _ (susp_to_join A)).
  - snrapply Susp_ind.
    1,2: reflexivity.
    intros a.
    apply (transport_paths_FFlr' (f:=susp_to_join A)).
    apply equiv_p1_1q.
    lhs nrapply (ap _ _); [nrapply Susp_rec_beta_merid | ].
    lhs nrapply (ap_pp _ _ (jglue false a)^).
    lhs nrefine (_ @@ _).
    1: lhs nrapply ap_V; nrapply (ap inverse).
    1,2: nrapply Join_rec_beta_jglue.
    apply concat_p1.
  - srapply (Join_ind_FFlr (join_to_susp A)); cbn beta.
    1: intros [|]; reflexivity.
    1: intros a; apply jglue.
    intros b a; cbn beta.
    lhs nrefine (ap _ _ @@ 1).
    1: nrapply Join_rec_beta_jglue.
    destruct b.
    all: rhs nrapply concat_1p.
    + lhs nrefine (_ @@ 1); [nrapply Susp_rec_beta_merid | ].
      apply concat_pV_p.
    + apply concat_1p.
Defined.

Definition equiv_join_susp (A : Type) : Join Bool A <~> Susp A
  := Build_Equiv _ _ (join_to_susp A) _.

(** It follows that the iterated join of [Bool] gives a sphere. *)
Definition equiv_join_power_bool_sphere (n : nat): Join_power' Bool n <~> Sphere (n.-1).
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
  2,3: symmetry; exact (equiv_join_power_bool_sphere _).
  refine (equiv_join_power_bool_sphere _ oE _).
  apply join_join_power.
Defined.
