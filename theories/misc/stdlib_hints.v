Require Export HoTT.Basics.Overture HoTT.Basics.Trunc HoTT.HIT.Truncations.
Require Import HoTT.Basics.Decidable.
Require Export HoTTClasses.misc.settings.

Hint Resolve tt : core.

Lemma merely_destruct {A} {P : Type} {sP : IsHProp P}
  (x : merely A) : (A -> P) -> P.
Proof.
intros E;revert x.
apply Trunc_ind.
- apply _.
- exact E.
Qed.

Monomorphic Universe Ubool.
Definition bool := (HoTT.Types.Bool.Bool@{Ubool}).

(* Unicode *)

Reserved Notation "x ≤ y" (at level 70, no associativity).

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := compose g f.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).
Notation "(∘)" := compose (only parsing) : mc_scope.

(*
   For a lemma like [compose_bijective] we don't declare it has an instance otherwise we end up looping
   [Bijective f] == [Bijective (id o f)] <- [Bijective id] * [Bijective f] <- [Bijective f]
   Instead we do [Hint Extern (Bijective (_ o _)) => class_apply @compose_bijective : typeclasses_instances.]
*)
Ltac class_apply c := autoapply c using typeclass_instances.
