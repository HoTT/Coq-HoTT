Require Import ssreflect ssrfun ssrbool ssrnat.
Require Import Paths Fibrations Contractible Equivalences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PathNotations.

Open Scope path_scope.
Open Scope equiv_scope.

(* Lemma is_contr_is_contr X : is_contr X -> is_contr (is_contr X). *)

Fixpoint has_hlevel (n : nat) : Type -> Type :=
  if n is m.+1 then (fun X => forall (x y : X), has_hlevel m (x = y)) 
  else is_contr.
