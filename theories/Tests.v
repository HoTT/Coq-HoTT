Require Import HoTT.

Fail Check Type0 : Type0.
Check Susp nat : Type0.
Fail Check Susp Type0 : Type0.

Fail Check (fun (P : interval -> Type) (a : P Interval.zero) (b : P Interval.one)
                (p p' : seg # a = b)
            => idpath : interval_ind P a b p = interval_rect P a b p').

Local Open Scope nat_scope.
Fail Check Lift nat : Type0.
Check 1 : Lift nat.

Check lift'@{i j}.
Check lower'@{i j}.
Check isequiv_lift'@{i j}.

(** Check that [ispointed_susp] doesn't require just a [Set] *)
Check (fun A : Type => _ : IsPointed (Susp A)).
Check (@ispointed_susp Type).
Check (@ispointed_susp Set).

(** Check that nested sigma-type notation didn't get clobbered by surreal cuts *)
Check ({ l : Unit & { n : Unit & Unit }}).

(** Regression check issue #744 *)
Module Foo (Os : ReflectiveSubuniverses).
  Module Import Os_Theory := ReflectiveSubuniverses_Theory Os.
  Goal Unit.
    let lem' := preconcat_any @to_O_natural_compose in
    pose proof lem' as H.
    let test := left_associate_concat_in H in
    pose test.
  Admitted.
End Foo.

(** Test 1 from issue #754 *)
Module Issue754_1.
  Inductive nat : Type1 :=
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
End Issue754_1.
