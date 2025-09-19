From HoTT Require Import Basics.
Require Export Basics.Nat.
Require Export HoTT.Universes.DProp.

(** * Characterization of the path types of [nat] *)

(** We characterize the path types of [nat].  We put this in its own file because it uses [DProp], which has a lot of dependencies. *)

Local Set Universe Minimization ToSet.

Local Close Scope trunc_scope.
Local Open Scope nat_scope.

Fixpoint code_nat (m n : nat) {struct m} : DHProp@{Set} :=
  match m, n with
  | 0, 0 => True
  | m'.+1, n'.+1 => code_nat m' n'
  | _, _ => False
  end.

Infix "=n" := code_nat : nat_scope.

Fixpoint idcode_nat {n} : (n =n n) :=
  match n as n return (n =n n) with
  | 0 => tt
  | S n' => @idcode_nat n'
  end.

Fixpoint path_nat {n m} : (n =n m) -> (n = m) :=
  match m as m, n as n return (n =n m) -> (n = m) with
  | 0, 0 => fun _ => idpath
  | m'.+1, n'.+1 => fun H : (n' =n m') => ap S (path_nat H)
  | _, _ => fun H => match H with end
  end.

Instance isequiv_path_nat {n m} : IsEquiv (@path_nat n m).
Proof.
  refine (isequiv_adjointify
            (@path_nat n m)
            (fun H => transport (fun m' => (n =n m')) H idcode_nat)
            _ _).
  { intros []; simpl.
    induction n; simpl; trivial.
    by destruct (IHn^)%path. }
  { intro. apply path_ishprop. }
Defined.

Definition equiv_path_nat {n m} : (n =n m) <~> (n = m)
  := Build_Equiv _ _ (@path_nat n m) _.
