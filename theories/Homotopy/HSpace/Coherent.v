Require Import Basics HSpace.Core Pointed.Core Pointed.Loops.

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

(** A type equivalent to a coherent H-space is a coherent H-space. *)
Definition iscohhspace_equiv_cohhspace {X Y : pType} `{IsCohHSpace Y} (f : X <~>* Y)
  : IsCohHSpace X.
Proof.
  snrapply Build_IsCohHSpace.
  - rapply (ishspace_equiv_hspace f).
    apply ishspace_cohhspace; assumption.
  - unfold IsCoherent; cbn.
    refine (_ @@ 1).
    refine (ap (ap f^-1) _).
    pointed_reduce_pmap f.
    refine (1 @@ _).
    exact (@iscoherent [Y, f pt] _ _).
Defined.

(** Every loop space is a coherent H-space. *)
Definition iscohhspace_loops {X : pType} : IsCohHSpace (loops X).
Proof.
  snrapply Build_IsCohHSpace.
  - apply ishspace_loops.
  - reflexivity.
Defined.
