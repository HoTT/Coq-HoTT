Require Import Basics HSpace.Core Pointed.Core.

Local Open Scope mc_mult_scope.
Local Open Scope pointed_scope.

(** ** Coherent H-space structures *)

(** An H-space is coherent when the left and right identities agree at the base point. *)

Class IsCoherent (X : pType) `{IsHSpace X} :=
  iscoherent : left_identity pt = right_identity pt.

Record IsCohHSpace (A : pType) := {
    ishspace_cohhspace : IsHSpace A;
    iscoherent_cohhspace : IsCoherent A;
  }.
#[export] Existing Instances ishspace_cohhspace iscoherent_cohhspace.

Definition issig_iscohhspace (A : pType)
  : { hspace_op : SgOp A
    & { hspace_left_identity : LeftIdentity hspace_op pt
    & { hspace_right_identity : RightIdentity hspace_op pt
    & hspace_left_identity pt = hspace_right_identity pt } } }
      <~> IsCohHSpace A.
Proof.
  transitivity { H : IsHSpace A & IsCoherent A }.
  2: issig.
  unfold IsCoherent.
  make_equiv.
Defined.
