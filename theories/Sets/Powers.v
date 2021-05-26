From HoTT Require Import Basics TruncType abstract_algebra.
From HoTT Require Import PropResizing.PropResizing.

From HoTT.Sets Require Import Cardinality.


(** * Definition of Power types *)

(* The definition is only used in Hartogs.v to allow defining a coercion,
   everywhere else we prefer to write out the definition for clarity. *)

Definition power_type (A : Type) : Type :=
  A -> HProp.


(** * Iterated powers *)

Lemma inject_power {PR : PropResizing} X :
  IsHSet X -> inject X (X -> HProp).
Proof.
  intros HX.
  set (f (x : X) := fun y => Build_HProp (resize_hprop (x = y))).
  exists f. intros x x' H.
  eapply (equiv_resize_hprop _)^-1. change (f x x').
  rewrite H. cbn. apply equiv_resize_hprop. reflexivity.
Qed.

Fixpoint powit X n :=
  match n with
  | O => X 
  | S n => powit X n -> HProp
  end.

Lemma powit_shift X n :
  powit (X -> HProp) n = (powit X n -> HProp).
Proof.
  induction n in X |- *; cbn.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Instance hset_power {UA : Univalence} (X : HSet) :
  IsHSet (X -> HProp).
Proof.
  intros p q. apply hprop_allpath. intros H H'.
  destruct (equiv_path_arrow p q) as [f [g Hfg Hgf _]].
  rewrite <- (Hfg H), <- (Hfg H'). apply ap. apply path_forall.
  intros x. apply isset_HProp.
Qed.

Instance hset_powit {UA : Univalence} (X : HSet) n :
  IsHSet (powit X n).
Proof.
  induction n; cbn.
  - apply X.
  - apply (@hset_power UA (Build_HSet (powit X n))).
Qed.

Lemma inject_powit {UA : Univalence} {PR : PropResizing} (X : HSet) n :
  inject X (powit X n).
Proof.
  induction n.
  - apply inject_refl.
  - eapply inject_trans; try apply IHn.
    apply inject_power. exact _.
Qed.

Lemma infinite_inject X Y :
  infinite X -> inject X Y -> infinite Y.
Proof.
  apply inject_trans.
Qed.

Lemma infinite_powit {UA : Univalence} {PR : PropResizing} (X : HSet) n :
  infinite X -> infinite (powit X n).
Proof.
  intros H. eapply infinite_inject; try apply H. apply inject_powit.
Qed.

