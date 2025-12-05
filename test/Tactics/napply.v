From HoTT Require Import Basics.Overture Basics.Tactics.
From HoTT Require Import Spaces.Nat.Core.

Local Open Scope nat_scope.

(** Testing the different [apply] tactics in the library. *)

Definition test1_type := {n : nat & n < 3}.
Fail Definition test1 : test1_type := ltac:(apply exist).
Fail Definition test1 : test1_type := ltac:(rapply exist).
Fail Definition test1 : test1_type := ltac:(napply exist).
Fail Definition test1 : test1_type := ltac:(tapply exist).
Succeed Definition test1 : test1_type := ltac:(napply exist; exact _).

(** Testing deprecated tactics *)
Fail #[warnings="+deprecated-tactic-notation-since-2025-03-11"]
Definition test1 : test1_type := ltac:(nrapply exist).
Fail #[warnings="+deprecated-tactic-notation-since-2025-03-11"]
Definition test1 : test1_type := ltac:(snrapply exist).
