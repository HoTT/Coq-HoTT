(* From Mike S. *)

Add Rec LoadPath "../".

Require Import Homotopy.

Definition path_to_eq {A} {a b : A} : a == b -> a = b.
Proof.
  path_induction.
Defined.

Definition path_to_eq_transport A (P : A -> Type) (a b : A) (p : a == b)
  (z : P a) : transport p z == eq_rect a P z b (path_to_eq p).
Proof.
  path_induction.
Defined.

Definition flip (x : bool) : bool :=
  match x with
    | true => false
    | false => true
  end.

Definition flip_path : (bool:Type) == bool.
Proof.
  apply equiv_to_path.
  exists flip.
  apply hequiv_is_equiv with flip;
  intros x; destruct x; auto.
Defined.

Definition equiv_trans {U V} (w : U <~> V) (x : U) :
  transport (P := fun A => A) (equiv_to_path w) x == w x.
Proof.
  refine (@equiv_induction
    (fun U V (w : U <~> V) =>
      forall (x : U), transport (P := fun A => A) (equiv_to_path w) x == w x)
    _ U V w x).
  intros T y.
  path_via (transport (P := fun A => A)
    (equiv_to_path (path_to_equiv (idpath T))) y).
  path_via (transport (P := fun A => A) (idpath T) y).
  apply happly, map, equiv_to_path_retraction.
Defined.

Definition should_be_false : bool :=
  @eq_rect Type bool (fun A => A) true bool (path_to_eq flip_path).

Definition is_false : should_be_false == false.
Proof.
  path_via (transport (P := fun A => A) flip_path true).
  refine (!path_to_eq_transport _ _ _ _ _ _).
  apply equiv_trans.
Defined.

Recursive Extraction should_be_false.

Inductive Empty : Type := .

Definition Is_false (b : bool) : Type
  := match b with
      | true => Empty
      | false => unit
     end.

Definition should_be_false_Is_false : Is_false should_be_false
  := (@eq_rect bool false Is_false tt should_be_false (path_to_eq (! is_false))).

Recursive Extraction should_be_false_Is_false.


(* For comparison: a legitimate extraction involving the empty type. *)
Definition ex_falso_nat : Empty -> nat
  := fun a => match a with end.

Recursive Extraction ex_falso_nat.

(* For comparison, some extractions dealing with a direct inconsistency *)

Axiom inconsistency : false = true.

Definition true_Is_false : Is_false true
  := @eq_rect bool false Is_false tt true inconsistency.

Recursive Extraction true_Is_false.
(* I don’t follow this code at all!  The results are clearer if we use bool and nat: *)

Definition bool_or_nat (b : bool) : Type
  := match b with
       | true => bool
       | false => nat
     end.

Definition true_over_true : bool_or_nat true.
Proof.
  simpl.  exact true.
Defined.

Recursive Extraction true_over_true.

Definition true_over_false : bool_or_nat false.
Proof.
  rewrite inconsistency.  apply true_over_true.
Defined.

Recursive Extraction true_over_false.
