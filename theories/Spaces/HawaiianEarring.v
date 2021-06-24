Require Import Basics Types.
Require Import WildCat Pointed.
Require Import Algebra.Groups.
Require Import Homotopy.Bouquet.
Require Import Limits.Limit Colimits.Colimit.
Require Import Diagrams.Sequence Diagrams.Diagram Diagrams.Graph.
Require Import Spaces.Finite.

(** * Earring space *)

(** The Earring space (a.k.a the Hawaiian Earring) is a topological space defined by the union of countably many circles of radius 1/n. Here we give a direct description of it's homotopy type. *)

(** Given a Bouquet of n circles, there is an inclusion map into a Bouquet of n.+1 circles. *)
Definition bouquet_fin_incl (n : nat)
  : Bouquet (Fin n) $-> Bouquet (Fin n.+1)
  := fmap Bouquet fin_incl.

(** The colimit of these maps should be a bouquet on nat. That should follow formally from Bouquet consisting of composed left adjoints, therefore preserving colimits. Hence it will follow from the colimit of Fin being nat. *)

(** The Earring space will follow from the retracts of these inclusion maps in fin, not behaving so well with the Bouquet functor. *)

Definition bouquet_fin_proj (n : nat)
  : Bouquet (Fin n.+2) $-> Bouquet (Fin n.+1)
  := fmap Bouquet (fin_proj n).

(** Functoriality makes showing this is a retract easy. *)
Definition bouquet_fin_proj_succ (n : nat)
  : bouquet_fin_proj n $o bouquet_fin_incl n.+1 $== Id _.
Proof.
  refine ((fmap_comp Bouquet _ _)^$ $@ fmap2 _ _
    $@ fmap_id Bouquet _).
  apply path_fin_proj_succ.
Defined.

(** Now taking the limit of this sequence will yield the Earring space. *)

(** The sequence for the Earring space *)

(** This is the same as a [Sequence] but with the arrows reversed. *)
Definition sequenceop_graph : Graph :=
  Build_Graph nat (fun n m : nat => m.+1%nat = n).

Definition SequenceOp := Diagram sequenceop_graph.

Definition Build_SequenceOp
  (X : nat -> Type) (f : forall n : nat, X (S n) -> X n)
  : SequenceOp.
Proof.
  srapply (Build_Diagram sequenceop_graph X).
  intros n m [].
  rapply f.
Defined.

Definition seqop_earring : SequenceOp :=
  Build_SequenceOp
    (fun n => Bouquet (Fin n.+1))
    bouquet_fin_proj.

Definition Earring : Type := Limit seqop_earring.

(** TODO: Characterise the fundamental group of the Earring space. This has been done in the literature. See for example this blog post: https://wildtopology.com/2013/11/23/the-hawaiian-earring/ *)


