From HoTT Require Import Basics Types Universes.DProp Tactics.EquivalenceInduction.

Local Open Scope nat_scope.

(** Test 1 from issue #754 *)
Inductive nat@{i | Set < i} : Type@{i} :=
| O : nat
| S : nat -> nat.
Fixpoint code_nat (m n : nat) {struct m} : DProp.DHProp :=
  match m with
    | O => match n with
             | O => DProp.True
             | S _ => DProp.False
           end
    | S m' => match n with
                | O => DProp.False
                | S n' => code_nat m' n'
              end
  end.

Local Set Warnings Append "-notation-overridden".
Notation "x =n y" := (code_nat x y) : nat_scope.
Local Set Warnings Append "notation-overridden".
Bind Scope nat_scope with nat.
Axiom equiv_path_nat :
  forall n m : nat,
    Trunc.trunctype_type (DProp.dhprop_hprop (n =n m)) <~> n = m.

Definition nat_discr `{Funext} {n: nat}: O <> S n.
Proof.
  intro H'.
  equiv_induction (@equiv_path_nat O (S n)).
  assumption.
Qed.
