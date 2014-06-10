Require Import Overture.

Set Implicit Arguments.

(** * Universe Levels *)

(** We provide casting definitions for raising universe levels. *)

Section local.
  Let type_cast_up_type : Type.
  Proof.
    let U1 := constr:(Type) in
    let U0 := constr:(Type : U1) in
    match U0 with 
        | ?T : _ => exact (T -> U1)
    end.
  Defined.

  (** Because we have cumulativity (that [T : Uᵢ] gives us [T : Uᵢ₊₁]), we may define [Lift : U₀ → U₁] as the identity function with a fancy type; the type says that [U₀ ⊊ U₁]. *)
  Definition Lift := 
    fun T : Type => T : $(let ty := type of T in 
                          let ty' := type of ty in
                           refine ty')$.
End local.

Definition lift {T} : T -> Lift T := fun x => x.
Definition isequiv_lift T : IsEquiv (@lift T)
  := @BuildIsEquiv
       _ _
       (fun x => x)
       (fun x => x)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).

Hint Extern 4 (IsEquiv (@lift _)) => apply isequiv_lift : typeclass_instances.

Definition lower {A} := (@equiv_inv _ _ (@lift A) _).

(** We make [lift] and [lower] opaque so that typeclass resolution doesn't pick up [isequiv_lift] as an instance of [IsEquiv idmap] and wreck havok. *)
Typeclasses Opaque lift lower.


(* Check Lift nat : Type0. *)
(* Check 1 : Lift nat. *)
