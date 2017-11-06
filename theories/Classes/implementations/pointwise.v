Require Import
  HoTT.Classes.interfaces.abstract_algebra.

(** If [B] is a (bounded) lattice, then so is [A -> B], pointwise.
    This relies on functional extensionality. *)
Section contents.
  Context `{Funext}.

  Context {A B : Type}.
  Context `{BJoin : Join B}.
  Context `{BMeet : Meet B}.
  Context `{BBottom : Bottom B}.
  Context `{BTop : Top B}.

  Global Instance bot_fun : Bottom (A -> B)
    := fun _ => ⊥.

  Global Instance top_fun : Top (A -> B)
    := fun _ => ⊤.

  Global Instance join_fun : Join (A -> B) :=
    fun (f g : A -> B) (a : A) => (f a) ⊔ (g a).

  Global Instance meet_fun : Meet (A -> B) :=
    fun (f g : A -> B) (a : A) => (f a) ⊓ (g a).

  (** Try to solve some of the lattice obligations automatically *)
  Create HintDb lattice_hints.
  Hint Resolve
       associativity
       absorption
       commutativity | 1 : lattice_hints.
  Local Ltac reduce_fun := compute; intros; apply path_forall; intro.
  Local Ltac try_solve_fun :=
    reduce_fun;
    eauto 10 with lattice_hints typeclass_instances.

  Global Instance lattice_fun `{!Lattice B} : Lattice (A -> B).
  Proof.
    repeat split; try apply _; try_solve_fun.
    * apply binary_idempotent.
    * apply binary_idempotent.
  Defined.

  Instance boundedjoinsemilattice_fun
   `{!BoundedJoinSemiLattice B} :
    BoundedJoinSemiLattice (A -> B).
  Proof.
    repeat split; try apply _; try_solve_fun.
    * apply left_identity.
    * apply right_identity.
    * apply commutativity.
    * apply binary_idempotent.
  Defined.

  Instance boundedmeetsemilattice_fun
   `{!BoundedMeetSemiLattice B} :
    BoundedMeetSemiLattice (A -> B).
  Proof.
    repeat split; try apply _; reduce_fun.
    * apply associativity.
    * apply left_identity.
    * apply right_identity.
    * apply commutativity.
    * apply binary_idempotent.
  Defined.

  Global Instance boundedlattice_fun
   `{!BoundedLattice B} : BoundedLattice (A -> B).
  Proof.
    repeat split; try apply _; reduce_fun; apply absorption.
  Defined.
End contents.
