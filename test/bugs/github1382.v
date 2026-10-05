From HoTT Require Import Basics Types.

(* Tests for discriminate tactic *)

Goal O = S O -> Empty.
Proof.
  discriminate 1.
Qed.

Goal forall H : O = S O, H = H.
Proof.
  discriminate H.
Qed.

Goal O = S O -> Unit.
Proof.
  intros H. discriminate H.
Qed.
Goal O = S O -> Unit.
Proof.
  intros H. Ltac g x := discriminate x. g H.
Qed.

Goal (forall x y : nat, x = y -> x = S y) -> Unit.
Proof.
  intros.
  try discriminate (H O) || exact tt.
Qed.

Goal (forall x y : nat, x = y -> x = S y) -> Unit.
Proof.
  intros H. ediscriminate (H O). instantiate (1:=O).
Abort.

(* Check discriminate on types with local definitions *)

Inductive A : Type0 := B (T := Unit) (x y : Bool) (z := x).
Goal forall x y, B x true = B y false -> Empty.
Proof.
  discriminate.
Qed.

