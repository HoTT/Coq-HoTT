Require Export HoTTClasses.misc.settings.
Require Export HoTT.Basics.Overture HoTT.Basics.Trunc HoTT.HIT.Truncations.

(* HoTT compat *)
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
Reserved Notation "x ≥ y" (at level 70, no associativity).

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Definition compose {A B C : Type} (g : B → C) (f : A → B) : A -> C := compose g f.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).
Notation "(∘)" := compose (only parsing) : mc_scope.

Ltac class_apply c := autoapply c using typeclass_instances.
