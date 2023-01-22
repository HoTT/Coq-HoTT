Require Export Classes.interfaces.abstract_algebra.
Require Import HSpace.Core.

Local Open Scope mc_mult_scope.

(** ** Coherent H-space structures *)

(** An H-space is coherent when the left and right identities agree at the base point. *)

Class IsCoherent (X : pType) `{IsHSpace X} :=
  iscoherent : left_identity _ = right_identity _.

Record IsCohHSpace (A : pType) := {
    ishspace_cohhspace : IsHSpace A;
    iscoherent_cohhspace : IsCoherent A;
  }.
#[export] Existing Instances ishspace_cohhspace iscoherent_cohhspace.

Definition issig_iscohhspace (A : pType)
  : { hspace_op : SgOp A
    & { hspace_left_identity : LeftIdentity hspace_op _
    & { hspace_right_identity : RightIdentity hspace_op _
    & hspace_left_identity (point _) = hspace_right_identity _ } } }
      <~> IsCohHSpace A.
Proof.
  transitivity { H : IsHSpace A & IsCoherent A }.
  2: issig.
  unfold IsCoherent.
  make_equiv.
Defined.
