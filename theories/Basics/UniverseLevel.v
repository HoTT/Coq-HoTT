Require Import Basics.Overture Basics.PathGroupoids.

(** * Universe Levels *)

(** We provide casting definitions for raising universe levels. *)

(** Because we have cumulativity (that [T : U@{i}] gives us [T : U@{j}] when [i < j]), we may define [Lift : U@{i} → U@{j}] to be the identity function with a fancy type; the type says that [i < j]. *)
Definition Lift@{i j} (A : Type@{i}) : Type@{j}
  := Eval hnf in let enforce_lt := Type@{i} : Type@{j} in A.

Definition lift {A} : A -> Lift A := fun x => x.

Definition lower {A} : Lift A -> A := fun x => x.

Definition lift2 {A B} (f : forall x : A, B x) : forall x : Lift A, Lift (B (lower x))
  := f.

Definition lower2 {A B} (f : forall x : Lift A, Lift (B (lower x))) : forall x : A, B x
  := f.

(** We make [lift] and [lower] opaque so that typeclass resolution doesn't pick up [isequiv_lift] as an instance of [IsEquiv idmap] and wreck havok. *)
Typeclasses Opaque lift lower lift2 lower2.

Global Instance isequiv_lift T : IsEquiv (@lift T)
  := @BuildIsEquiv
       _ _
       (@lift T)
       (@lower T)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).

Global Instance isequiv_lift2 A B : IsEquiv (@lift2 A B)
  := @BuildIsEquiv
       _ _
       (@lift2 A B)
       (@lower2 A B)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).

Global Instance lift_isequiv {A B} (f : A -> B) {H : IsEquiv f} : @IsEquiv (Lift A) (Lift B) (lift2 f)
  := @BuildIsEquiv
       (Lift A) (Lift B)
       (lift2 f)
       (lift2 (f^-1))
       (fun x => ap lift (eisretr f (lower x)))
       (fun x => ap lift (eissect f (lower x)))
       (fun x => ((ap (ap lift) (eisadj f (lower x)))
                    @ (ap_compose f lift _)^)
                   @ (@ap_compose A (Lift A) (Lift B) lift (lift2 f) _ _ _)).

Global Instance lower_isequiv {A B} (f : Lift A -> Lift B) {H : IsEquiv f} : @IsEquiv A B (lower2 f)
  := @BuildIsEquiv
       _ _
       (lower2 f)
       (lower2 (f^-1))
       (fun x => ap lower (eisretr f (lift x)))
       (fun x => ap lower (eissect f (lift x)))
       (fun x => ((ap (ap lower) (eisadj f (lift x)))
                    @ (ap_compose f lower _)^)
                   @ (@ap_compose (Lift A) A B lower (lower2 f) _ _ _)).

Definition lower_equiv {A B} (e : Equiv (Lift A) (Lift B)) : Equiv A B
  := @BuildEquiv A B (lower2 e) _.

(** This version doesn't force strict containment, i.e. it allows the two universes to possibly be the same.  No fancy type is necessary here other than the universe annotations, because of cumulativity. *)

Definition Lift'@{i j} (A : Type@{i}) : Type@{j} := A.

(** However, if we don't give the universes as explicit arguments here, then Coq collapses them. *)
Definition lift'@{i j} {A : Type@{i}} : A -> Lift'@{i j} A := fun x => x.

Definition lower'@{i j} {A : Type@{i}} : Lift'@{i j} A -> A := fun x => x.

Definition lift'2@{i i' j j'} {A : Type@{i}} {B : A -> Type@{i'}} (f : forall x : A, B x)
: forall x : Lift'@{i j} A, Lift'@{i' j'} (B (lower' x))
  := f.

Definition lower'2@{i i' j j'} {A : Type@{i}} {B : A -> Type@{i'}}
           (f : forall x : Lift'@{i j} A, Lift'@{i' j'} (B (lower' x)))
: forall x : A, B x
  := f.

(** We make [lift] and [lower] opaque so that typeclass resolution doesn't pick up [isequiv_lift] as an instance of [IsEquiv idmap] and wreck havok. *)
Typeclasses Opaque lift' lower' lift'2 lower'2.

Definition isequiv_lift'@{i j} (T : Type@{i}) : IsEquiv (@lift'@{i j} T)
  := @BuildIsEquiv
       _ _
       (@lift' T)
       (@lower' T)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).
Global Existing Instance isequiv_lift'. (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4411 *)

Definition isequiv_lift'2@{e0 e1 i i' j j'} (A : Type@{i}) (B : A -> Type@{j}) : IsEquiv@{e0 e1} (@lift'2@{i i' j j'} A B)
  := @BuildIsEquiv
       _ _
       (@lift'2 A B)
       (@lower'2 A B)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).
Global Existing Instance isequiv_lift'2. (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4411 *)

Definition lift'_isequiv@{a b i j i' j'}  {A : Type@{a}} {B : Type@{b}} (f : A -> B) {H : IsEquiv f} : @IsEquiv (Lift'@{i j} A) (Lift'@{i' j'} B) (lift'2 f)
  := @BuildIsEquiv
       (Lift' A) (Lift' B)
       (lift'2 f)
       (lift'2 (f^-1))
       (fun x => ap lift' (eisretr f (lower' x)))
       (fun x => ap lift' (eissect f (lower' x)))
       (fun x => ((ap (ap lift') (eisadj f (lower' x)))
                    @ (ap_compose f lift' _)^)
                   @ (@ap_compose A (Lift' A) (Lift' B) lift' (lift'2 f) _ _ _)).
Global Existing Instance lift'_isequiv. (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4411 *)

Definition lower'_isequiv@{i j i' j'} {A : Type@{i}} {B : Type@{j}} (f : Lift'@{i j} A -> Lift'@{i' j'} B) {H : IsEquiv f} : @IsEquiv A B (lower'2 f)
  := @BuildIsEquiv
       _ _
       (lower'2 f)
       (lower'2 (f^-1))
       (fun x => ap lower' (eisretr f (lift' x)))
       (fun x => ap lower' (eissect f (lift' x)))
       (fun x => ((ap (ap lower') (eisadj f (lift' x)))
                    @ (ap_compose f lower' _)^)
                   @ (@ap_compose (Lift' A) A B lower' (lower'2 f) _ _ _)).
Global Existing Instance lower'_isequiv. (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4411 *)

Definition lower'_equiv@{i j i' j'} {A : Type@{i}} {B : Type@{j}} (e : Equiv (Lift'@{i j} A) (Lift'@{i' j'} B)) : Equiv A B
  := @BuildEquiv A B (lower'2 e) _.

(*Fail Check Lift nat : Type0.
Check 1 : Lift nat.*)
