Require Import HoTT.Basics.Overture.
Require Import Coq.Unicode.Utf8.

Hint Unfold Reflexive Symmetric Transitive.
Hint Constructors PreOrder.

(*
   These tactics automatically solve symmetry and transitivity problems,
   when the hypothesis are in the context. They should be added as hints
   like

     Hint Extern 4 (?x = ?x) => reflexivity.
     Hint Extern 4 (?x = ?y) => auto_symm.
     Hint Extern 4 (?x = ?y) => auto_trans.

   once the appropriate head constants are defined.
*)
Ltac auto_symm := match goal with
                    [ H: ?R ?x ?y |- ?R ?y ?x] => apply (symmetry H)
                  end.
Ltac auto_trans := match goal with
                    [ H: ?R ?x ?y, I: ?R ?y ?z |- ?R ?x ?z] => apply (transitivity H I)
                  end.

(*
   These tactics make handling sig types slightly easier.
*)
Ltac exist_hyp := match goal with [ H : sig ?P |- ?P _  ] => exact (proj2_sig H) end.
Hint Extern 0 => exist_hyp: core typeclass_instances.

Ltac exist_proj1 :=
  match goal with
    | [ |- context [proj1_sig ?x] ] => apply (proj2_sig x)
  end.
Hint Extern 0 => exist_proj1: core typeclass_instances.

(* HoTT compat *)
Notation False := Empty (only parsing).
Notation True := Unit (only parsing).
Hint Resolve tt : core.

Notation False_rect := Empty_rect (only parsing).

Notation left := inl (only parsing).
Notation right := inr (only parsing).

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

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).
