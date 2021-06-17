From HoTT Require Import Basics TruncType abstract_algebra.
From HoTT Require Import PropResizing.PropResizing.
From HoTT Require Import Spaces.Card.


(** * Definition of Power types *)

(* The definition is only used in Hartogs.v to allow defining a coercion,
   everywhere else we prefer to write out the definition for clarity. *)

Definition power_type (A : Type) : Type :=
  A -> HProp.


(** * Iterated powers *)

Lemma Injection_power {PR : PropResizing} X :
  IsHSet X -> Injection X (X -> HProp).
Proof.
  intros HX.
  set (f (x : X) := fun y => Build_HProp (resize_hprop (x = y))).
  exists f. intros x x' H.
  eapply (equiv_resize_hprop _)^-1. change (f x x').
  rewrite H. cbn. apply equiv_resize_hprop. reflexivity.
Qed.

Fixpoint power_iterated X n :=
  match n with
  | O => X 
  | S n => power_iterated X n -> HProp
  end.

Lemma power_iterated_shift X n :
  power_iterated (X -> HProp) n = (power_iterated X n -> HProp).
Proof.
  induction n in X |- *; cbn.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Global Instance hset_power {UA : Univalence} (X : HSet) :
  IsHSet (X -> HProp).
Proof.
  intros p q. apply hprop_allpath. intros H H'.
  destruct (equiv_path_arrow p q) as [f [g Hfg Hgf _]].
  rewrite <- (Hfg H), <- (Hfg H'). apply ap. apply path_forall.
  intros x. apply isset_HProp.
Qed.

Global Instance hset_power_iterated {UA : Univalence} (X : HSet) n :
  IsHSet (power_iterated X n).
Proof.
  induction n; cbn.
  - apply X.
  - apply (@hset_power UA (Build_HSet (power_iterated X n))).
Qed.

Lemma Injection_power_iterated {UA : Univalence} {PR : PropResizing} (X : HSet) n :
  Injection X (power_iterated X n).
Proof.
  induction n.
  - reflexivity.
  - Fail rewrite IHn. eapply Injection_trans; try apply IHn.
    apply Injection_power. exact _.
Qed.

Lemma infinite_inject X Y :
  infinite X -> Injection X Y -> infinite Y.
Proof.
  apply Injection_trans.
Qed.

Lemma infinite_power_iterated {UA : Univalence} {PR : PropResizing} (X : HSet) n :
  infinite X -> infinite (power_iterated X n).
Proof.
  intros H. eapply infinite_inject; try apply H. apply Injection_power_iterated.
Qed.

