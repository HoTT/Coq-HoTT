Require Import Overture.

Set Implicit Arguments.

(** * Universe Levels *)

(** We provide casting definitions for raising universe levels. *)

(** [type_eq] is a variant of [=] which does not unify universes. *)
Inductive type_eq (A : Type) : Type -> Type :=
| type_eq_refl : type_eq A A
| type_eq_impossible : False -> forall B : Type, type_eq A B.

Section local.
  Let type_cast_up_type : Type.
  Proof.
    let U0 := constr:(Type) in
    let U1 := constr:(Type) in
    let unif := constr:(U0 : U1) in
    exact (forall T : U0, { T' : U1 & type_eq T T' }).
  Defined.

  Definition type_cast_up : type_cast_up_type
    := fun T => existT (fun T' => type_eq T T') T (type_eq_refl _).
End local.

Definition Lift (T : Type) := projT1 (type_cast_up T).
Definition paths_Lift (T : Type) : (T : Type) = Lift T
  := match projT2 (type_cast_up T) in (type_eq _ T') return (T : Type) = T' with
       | type_eq_refl => idpath
       | type_eq_impossible bad _ => match bad with end
     end.
Definition lift {T} : T -> Lift T := fun x => x.
Global Instance isequiv_lift T : IsEquiv (@lift T)
  := @BuildIsEquiv
       _ _
       (fun x => x)
       (fun x => x)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).
Definition lower {A} := (@equiv_inv _ _ (@lift A) _).

(** We make [lift] and [lower] opaque so that typeclass resolution doesn't pick up [isequiv_lift] as an instance of [IsEquiv idmap] and wreck havok. *)
Typeclasses Opaque lift lower.
Global Opaque lift lower.


(*Fail Check Lift nat : Set.
Check 1 : Lift nat.*)
