(** Do setoids whose equality is hProp give a model of type theory? *)

Require Import ExtensionalityAxiom.
Require Import HoTT.Homotopy.

Structure HProp := {
  hprop_carrier :> Type ;
  hprop_is_prop : is_prop hprop_carrier
}.

(* Facts about hProps missing from HoTT. *)
Definition hconj : HProp -> HProp -> HProp.
Proof.
  intros [A propA] [B propB].
  exists (A * B).
  apply allpath_prop.
  intros [x x'] [y y'].
  apply prod_path.
  apply propA.
  apply propB.
Defined.

Definition hthen : HProp -> HProp -> HProp.
Proof.
  intros [A propA] [B propB].
  exists (A -> B).
  apply allpath_prop.
  intros p q.
  by_extensionality. (* CRASH HERE ON HOQTOP! *)

Hint Resolve hprop_is_prop.

Structure Setoid := {
  setoid_carrier :> Type ;
  setoid_eq : setoid_carrier -> setoid_carrier -> HProp ;
  setoid_refl : (forall x : setoid_carrier, setoid_eq x x) ;
  setoid_symm : (forall x y : setoid_carrier, setoid_eq x y -> setoid_eq y x) ;
  setoid_trans : (forall x y z : setoid_carrier, setoid_eq x y -> setoid_eq y z-> setoid_eq y z)
}.

Notation "x ~ y" := (setoid_eq _ x y) (at level 50).

(** We must show how to interpret dependent sums and products on setoids, and that
   they satisfy the desired rules.

   Before we can do that, we should define what a family of setoids is. We require
   it to respect equality in the sense that equal elements of the index type give
   equivalent setoids. *)

Structure Family (A : Setoid) := {
  family_map :> A -> Setoid ;
  family_trans : (forall x y : A, x ~ y -> family_map x <~> family_map y)
}.

(** Now it should be possible to define sums and products. *)

Section DependentSum.

  Parameter A : Setoid.
  Parameter F : Family A.

  Let sum_carrier := { x : A & setoid_carrier (F x) }.

  Let sum_eq : sum_carrier -> sum_carrier -> HProp.
  Proof.
    intros [x u] [y v].
    apply 


Definition Sum {A : Setoid} (F : Family A) : Setoid.
Proof.
  refine {| setoid_carrier := { x : A & setoid_carrier (F x) } ;
            setoid_eq := (fun u v => 
 |}.
