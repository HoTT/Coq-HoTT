(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Non-dependent function types *)

Require Import Common Paths Contractible Equivalences Funext.
Open Scope path_scope.
Open Scope equiv_scope.

(** *** Transport *)

(* Note: conclusion should be [==] if that is defined in an earlier file. *) 
Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (p^ # y)).
Proof.
  destruct p; simpl; auto.
Defined.

(* Where do these go?

Lemma trans_map {A} {P Q : fibration A} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = p # f x z.
Proof.
  path_induction.
Defined.

Lemma trans_map2 {A} {P Q R : fibration A} {x y : A} (p : x = y)
  (f : forall x, P x -> Q x -> R x) (z : P x) (w: Q x) :
  f y (p # z) (p # w) = p # f x z w.
Proof.
  path_induction.
Defined.
*)
