Require Import Basics.
Require Import Types.
Require Import Truncations UnivalenceImpliesFunext.
Require Export Classes.interfaces.abstract_algebra.
Import TrM.

Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.

Class IsHSpace (X : pType) := {
  hspace_op :> SgOp X;
  hspace_left_identity :> LeftIdentity hspace_op (point _);
  hspace_right_identity :> RightIdentity hspace_op (point _);
}.

Global Instance hspace_mon_unit {X : pType} `{IsHSpace X} : MonUnit X := point _.

Definition hspace_id {X : pType} := point X.

Section HSpaceProperties.

  Context 
   `{Univalence}
    {A : pType}
   `{IsHSpace A}
   `{IsConnected 0 A}.

  Global Instance isequiv_hspace_left_op
    : forall (a : A), IsEquiv (fun x => a * x).
  Proof.
    refine (conn_map_elim (-1) (unit_name hspace_id) _ _).
    + exact (conn_point_incl hspace_id).
    + apply Unit_ind.
      serapply (isequiv_homotopic idmap).
      intro a; symmetry.
      apply left_identity.
  Defined.

  Global Instance isequiv_hspace_right_op
    : forall (a : A), IsEquiv (fun x => x * a).
  Proof.
    refine (conn_map_elim (-1) (unit_name hspace_id) _ _).
    + exact (conn_point_incl hspace_id).
    + apply Unit_ind.
      serapply (isequiv_homotopic idmap).
      intro a; symmetry.
      apply right_identity.
  Defined.

  Definition equiv_hspace_left_op (a : A) : A <~> A
    := Build_Equiv _ _ _ (isequiv_hspace_left_op a).

  Definition equiv_hspace_right_op (a : A) : A <~> A
    := Build_Equiv _ _ _ (isequiv_hspace_right_op a).

End HSpaceProperties.
