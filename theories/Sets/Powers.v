From HoTT Require Import Basics Types TruncType.
From HoTT Require Import Universes.Smallness.
From HoTT Require Import Spaces.Card Spaces.Nat.Core.

(** * Definition of Power types *)

(* The definition is only used in Hartogs.v to allow defining a coercion, and one place below.  Everywhere else we prefer to write out the definition for clarity. *)

Definition power_type (A : Type) : Type
  := A -> HProp.

(** * Iterated powers *)

Lemma Injection_power {PR : PropResizing} X
  : IsHSet X -> Injection X (X -> HProp).
Proof.
  intros HX.
  set (f (x : X) := fun y => Build_HProp (smalltype (x = y))).
  exists f. intros x x' H.
  eapply equiv_smalltype. change (f x x').
  rewrite H. cbn. apply equiv_smalltype. reflexivity.
Qed.

Definition power_iterated X n := nat_iter n power_type X.

Definition power_iterated_shift X n
  : power_iterated (X -> HProp) n = (power_iterated X n -> HProp)
  := (nat_iter_succ_r _ _ _)^.

Global Instance hset_power {UA : Univalence} (X : HSet)
  : IsHSet (X -> HProp).
Proof.
  apply istrunc_S.
  intros p q. apply hprop_allpath. intros H H'.
  destruct (equiv_path_arrow p q) as [f [g Hfg Hgf _]].
  rewrite <- (Hfg H), <- (Hfg H'). apply ap. apply path_forall.
  intros x. apply path_ishprop.
Qed.

Global Instance hset_power_iterated {UA : Univalence} (X : HSet) n
  : IsHSet (power_iterated X n).
Proof.
  nrapply (nat_iter_invariant n power_type (fun A => IsHSet A)).
  - intros Y HS. rapply hset_power.
  - exact _.
Defined.

Lemma Injection_power_iterated {UA : Univalence} {PR : PropResizing} (X : HSet) n
  : Injection X (power_iterated X n).
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - eapply Injection_trans; try apply IHn.
    apply Injection_power. exact _.
Qed.

Lemma infinite_inject X Y
  : infinite X -> Injection X Y -> infinite Y.
Proof.
  apply Injection_trans.
Qed.

Lemma infinite_power_iterated {UA : Univalence} {PR : PropResizing} (X : HSet) n
  : infinite X -> infinite (power_iterated X n).
Proof.
  intros H. eapply infinite_inject; try apply H. apply Injection_power_iterated.
Qed.
