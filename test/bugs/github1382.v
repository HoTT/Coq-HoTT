From HoTT Require Import Basics Types.

(* Tests for discriminate tactic *)

Goal O = S O -> Empty.
 discriminate 1.
Qed.

Goal forall H : O = S O, H = H.
 discriminate H.
Qed.

Goal O = S O -> Unit.
intros H. discriminate H. Qed.
Goal O = S O -> Unit.
intros H. Ltac g x := discriminate x. g H. Qed.

Goal (forall x y : nat, x = y -> x = S y) -> Unit.
intros.
try discriminate (H O) || exact tt.
Qed.

Goal (forall x y : nat, x = y -> x = S y) -> Unit.
intros H. ediscriminate (H O). instantiate (1:=O). Abort.

(* Check discriminate on types with local definitions *)

Inductive A : Type0 := B (T := Unit) (x y : Bool) (z := x).
Goal forall x y, B x true = B y false -> Empty.
discriminate.
Qed.

