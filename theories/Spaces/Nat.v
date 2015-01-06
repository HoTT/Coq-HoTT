(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers, depending on TruncType *)

Require Import HoTT.Basics.
Require Import HoTT.Types.Bool HoTT.Types.Nat HoTT.TruncType.
Import BoolSortCoercion.

Local Open Scope equiv_scope.

(** ** Equality *)
(** *** Boolean equality and its properties *)

Local Notation cast p := (transport is_true p^ tt)%path.
Local Notation cast' := (inverse o @path_b_true__of__is_true _).

Definition idcode_nat {n} : n =n n := cast idcode_nat'.
Definition path_nat {n m} : n =n m -> n = m := path_nat' o cast'.
Global Instance isequiv_path_nat {n m} : IsEquiv (@path_nat n m).
Proof.
  exact _.
Defined.
Definition equiv_path_nat {n m} : (n =n m) <~> (n = m)
  := BuildEquiv _ _ (@path_nat n m) _.

(** ** Theorems about natural number ordering *)

Fixpoint leq0n {n} : 0 <= n :=
  match n as n return 0 <= n with
    | 0 => tt
    | n'.+1 => @leq0n n'
  end.

Fixpoint subnn {n} : n - n =n 0 :=
  match n as n return n - n =n 0 with
    | 0 => tt
    | n'.+1 => @subnn n'
  end.

Global Instance leq_refl : Reflexive leq
  := @subnn.

Fixpoint leq_transb {x y z} : (x <= y -> y <= z -> x <= z)%Bool :=
  match x as x, y as y, z as z return (x <= y -> y <= z -> x <= z)%Bool with
    | 0, 0, 0 => tt
    | x'.+1, 0, 0 => tt
    | 0, y'.+1, 0 => tt
    | 0, 0, z'.+1 => tt
    | x'.+1, y'.+1, 0 => cast implb_true
    | x'.+1, 0, z'.+1 => tt
    | 0, y'.+1, z'.+1 => @leq_transb 0 y' z'
    | x'.+1, y'.+1, z'.+1 => @leq_transb x' y' z'
  end.

(** TODO: Move this *)
Definition implb_impl' {a b : Bool} : (a -> b)%Bool <-> (a -> b).
Proof.
  destruct a, b; simpl; split; try constructor; try (intros; assumption).
  intro p; apply p; constructor.
Defined.

Global Instance leq_trans : Transitive (fun n m => leq n m).
Proof.
  intros x y z p.
  apply implb_impl'; revert p.
  apply implb_impl'.
  apply leq_transb.
Defined.

Fixpoint leq_antisymb {x y} : (x <= y -> y <= x -> x =n y)%Bool :=
  match x as x, y as y return (x <= y -> y <= x -> x =n y)%Bool with
    | 0, 0 => tt
    | x'.+1, y'.+1 => @leq_antisymb x' y'
    | _, _ => tt
  end.

Lemma leq_antisym : forall {x y}, x <= y -> y <= x -> x = y.
Proof.
  intros x y p q.
  apply path_nat.
  revert q; apply implb_impl'.
  revert p; apply implb_impl'.
  apply leq_antisymb.
Defined.
