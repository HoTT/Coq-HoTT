
Require Import HoTT.Basics Fin.

(** ** Tactics *)

Ltac FinIndOn X := repeat
  match type of X with
  | Fin 0 => destruct X
  | Empty => destruct X
  | Unit => destruct X
  | Fin ?n => destruct X as [X|X]
  | ?L + Unit => destruct X as [X|X]
  end.

(** This tactic can be used to generate n cases from a goal like forall (x : Fin n), _ *)
Ltac FinInd := let X := fresh "X" in intro X; FinIndOn X.
