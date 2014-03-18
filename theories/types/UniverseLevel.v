Require Import Overture.

Set Implicit Arguments.

(** * Universe Levels *)

(** We provide casting definitions for raising universe levels. *)

Section local.
  Let type_cast_up_type : Type.
  Proof.
    let U0 := constr:(Type) in
    let U1 := constr:(Type) in
    let unif := constr:(U0 : U1) in
    exact (U0 -> U1).
  Defined.

  (** Because we have cumulativity (that [T : Uᵢ] gives us [T : Uᵢ₊₁]), we may define [Lift : U₀ → U₁] as the identity function with a fancy type; the type says that [U₀ ⊊ U₁]. *)
  Definition Lift : type_cast_up_type
    := fun T => T.
End local.

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
