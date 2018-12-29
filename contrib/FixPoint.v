Require Import Basics.Overture.
Require Import Types.Bool.
Require Import HProp.

Require Import Basics.Trunc. (* IsEmbedding *)
Require Import HIT.Truncations. (* IsSurjection *)

Import TrM.

Lemma isSur2 {A B} {f : A -> B} {sur : IsSurjection f} :
  forall y, exists x, f x = y.
Proof.
  intro.
  destruct (sur y) as [c d].
  set (c' := c).
  apply (untrunc_istrunc) in c'.
  + apply c'.
Admitted.

Section Lawvere.

  Context {A B : Type}.


(** 
    Lawveres theorem
    If there is an onto map e : A -> B^A then every f : B -> B has 
    a fixed point.
**)

  Theorem Lawvere (e : A -> (A -> B)) {sur : IsSurjection e} 
    : forall (f : B -> B), exists x, f x = x.
  Proof.
    intro f.
    set (sur2 := isSur2 e).
    destruct (isSur2 (fun x => f (e x x))) as [y p].
    refine (e y y; _).
    set (foo := f (e y y)).
    rewrite p. unfold foo. reflexivity.
  Admitted.

End Lawvere.

Section Cantor.
  Context {A : Type}.

  Lemma negb_not_fixed : not (exists x, negb x = x).
  Proof.
    intro.
    destruct X as [x p].
    revert p. 
    apply (not_fixed_negb x).
  Qed.

  Corollary cantor (f : A -> (A -> Bool)) :  not (IsSurjection f).
  Proof.
    intro X.
    pose ((@Lawvere _ _ f X negb)) as bar.
    apply (negb_not_fixed bar).
  Qed.

End Cantor.