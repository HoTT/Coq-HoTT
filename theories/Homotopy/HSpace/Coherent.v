From HoTT Require Import Basics HSpace.Core Pointed.Core Pointed.Loops.

Local Open Scope mc_mult_scope.
Local Open Scope pointed_scope.

(** ** Coherent H-space structures *)

(** An H-space is coherent when the left and right identities agree at the base point. *)

Class IsCoherent (X : pType) `{IsHSpace X} :=
  iscoherent : left_identity pt = right_identity pt.

Record IsCohHSpace (A : pType) := {
    ishspace_cohhspace :: IsHSpace A;
    iscoherent_cohhspace :: IsCoherent A;
  }.

Definition issig_iscohhspace (A : pType)
  : { hspace_op : SgOp A
    & { hspace_left_identity : LeftIdentity hspace_op pt
    & { hspace_right_identity : RightIdentity hspace_op pt
    & hspace_left_identity pt = hspace_right_identity pt } } }
      <~> IsCohHSpace A
  := ltac:(make_equiv).

(** A type equivalent to a coherent H-space is a coherent H-space. *)
Definition iscohhspace_equiv_cohhspace {X Y : pType} `{IsCohHSpace Y} (f : X <~>* Y)
  : IsCohHSpace X.
Proof.
  snapply Build_IsCohHSpace.
  - rapply (ishspace_equiv_hspace f).
    apply ishspace_cohhspace; assumption.
  - unfold IsCoherent; cbn.
    refine (_ @@ 1).
    refine (ap (ap f^-1) _).
    pelim f.
    refine (1 @@ _).
    exact iscoherent.
Defined.

(** Every loop space is a coherent H-space. *)
Definition iscohhspace_loops {X : pType} : IsCohHSpace (loops X).
Proof.
  srapply Build_IsCohHSpace.
  - exact ishspace_loops.
  - reflexivity.
Defined.
