Require Import ssreflect ssrfun.
Require Import Paths (* Fibrations*).
(* assia : in fact we do not rely on the file aubout fibrations. *)

Import PathNotations.

Open Scope path_scope.

(** A space [A] is contractible if there is a point [x : A] and a
   (pointwise) homotopy connecting the identity on [A] to the constant
   map at [x].  Thus an element of [is_contr A] is a pair whose
   first component is a point [x] and the second component is a
   pointwise retraction of [A] to [x]. *)

Definition is_contr A := {x : A & forall y : A, y = x}.

(** If a space is contractible, then any two points in it are
   connected by a path in a canonical way. *)

Lemma contr_path {A} (x y : A) : is_contr A -> x = y.
Proof. case=> z p; rewrite (p x) (p y); exact: 1. Qed.

(** Similarly, any two parallel paths in a contractible space are homotopic.  *)
Lemma contr_path2 {A} {x y : A} (p q : x = y) : is_contr A -> p = q.
Proof.
case => b hb.
suff {p q} cst t : t = (hb x) * (hb y)^-1  by rewrite (cst p) (cst q).
by case t; rewrite mulpV.
Qed.

(** It follows that any space of paths in a contractible space is contractible. *)

Lemma contr_pathcontr {A} (x y : A) : is_contr A -> is_contr (x = y).
Proof.
  move=> ctr; exists (contr_path x y ctr) => p; exact: contr_path2.
Qed.

(** The total space of any based path space is contractible. *)
(* assia : or, the homotopy class of a point is contractile *)
Lemma pathspace_contr {X} (x : X) : is_contr (sigT (identity x)).
Proof. exists (existT _ x 1); case=> [y p]; case p; exact 1. Qed.

(* Lemma pathspace_contr' {X} (x:X) : is_contr { y:X  &  x = y }. *)
(* Proof. *)
(*   exists (existT (fun y => x = y) x 1). *)
(*   intros [y p]. *)
(*   case p. *)
(*   exact 1. *)
(* Qed. *)

Lemma pathspace_contr_opp {X} (x:X) : is_contr {y : X & y = x }.
Proof.
  exists (existT (fun y => y = x) _ 1). 
  case=> [y p]; case p; exact 1.
Qed.

(** The unit type is contractible. *)
Lemma unit_contr : is_contr unit.
Proof. by exists tt => [[]]. Qed.
