Require Import Overture.

(** * Universe Levels *)

(** We provide casting definitions for raising universe levels. *)

(** Because we have cumulativity (that [T : U@{i}] gives us [T : U@{j}] when [i < j]), we may define [Lift : U@{i} → U@{j}] to be the identity function with a fancy type; the type says that [i < j]. *)
Definition Lift (A : Type@{i}) : Type@{j}
  := Eval hnf in let enforce_lt := Type@{i} : Type@{j} in A.

Definition lift {A} : A -> Lift A := fun x => x.

Definition lower {A} : Lift A -> A := fun x => x.

Global Instance isequiv_lift T : IsEquiv (@lift T)
  := @BuildIsEquiv
       _ _
       (@lift T)
       (@lower T)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).

(** This version doesn't force strict containment, i.e. it allows the two universes to possibly be the same. *)

Definition Lift' (A : Type@{i}) : Type@{j}
  := Eval hnf in let enforce_le := (fun x => x) : Type@{i} -> Type@{j} in A.

Definition lift' {A : Type@{i}} : A -> Lift'@{i j} A := fun x => x.

Definition lower' {A : Type@{i}} : Lift'@{i j} A -> A := fun x => x.

Global Instance isequiv_lift' T : IsEquiv (@lift'@{i j} T)
  := @BuildIsEquiv
       _ _
       (@lift' T)
       (@lower' T)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).

(** We make [lift] and [lower] opaque so that typeclass resolution doesn't pick up [isequiv_lift] as an instance of [IsEquiv idmap] and wreck havok. *)
Typeclasses Opaque lift lower lift' lower'.

(*Fail Check Lift nat : Type0.
Check 1 : Lift nat.*)
