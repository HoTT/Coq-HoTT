From HoTT Require Import Basics Types.
Require Import Diagrams.Sequence.
Require Import Homotopy.Join.Core.
Require Import Colimits.Colimit Colimits.Sequential.

Local Open Scope nat_scope.

(** * Propositional truncation as a colimit. *)

(** In this file we give an alternative construction of the propositional truncation using colimits. This can serve as a metatheoretic justification that propositional truncations exist. *)

(** The sequence of increasing joins. *)
Definition Join_seq (A : Type) : Sequence.
Proof.
  srapply Build_Sequence.
  1: exact (iterated_join A).
  intros n.
  exact joinr.
Defined.

(** Propositional truncation can be defined as the colimit of this sequence. *)
Definition PropTrunc A : Type := Colimit (Join_seq A).

(** The constructor is given by the colimit constructor. *)
Definition ptr_in {A} : A -> PropTrunc A := colim (D:=Join_seq A) 0.

(** The sequential colimit of this sequence is the propositional truncation. *)

(** Universal property of propositional truncation. *)
Lemma equiv_PropTrunc_rec `{Funext} (A P : Type) `{IsHProp P}
  : (PropTrunc A -> P) <~> (A -> P).
Proof.
  refine (_ oE equiv_colim_seq_rec _ P).
  srapply equiv_iff_hprop.
  { intros h.
    exact (h 0). }
  intros f.
  induction n.
  - exact f.
  - cbn.
    srapply Join_rec.
    1,2: assumption.
    intros a b.
    rapply path_ishprop.
Defined.

(** The propositional truncation is a hprop. *)
Instance ishprop_proptrunc `{Funext} (A : Type)
  : IsHProp (PropTrunc A).
Proof.
  rapply hprop_inhabited_contr.
  rapply (equiv_PropTrunc_rec _ _)^-1.
  intros x.
  srapply contr_colim_seq_into_prop.
  - intros n.
    destruct n.
    1: exact x.
    exact (joinl x).
  - intros n.
    rapply jglue.
Defined.
