(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the empty type *)

Require Import HoTT.Basics.
Local Open Scope path_scope.

(** ** Unpacking *)
(** ** Eta conversion *)
(** ** Paths *)
(** ** Transport *)
(** ** Functorial action *)
(** ** Equivalences *)
(** ** Universal mapping properties *)

Global Instance contr_from_Empty {_ : Funext} (A : Type) :
  Contr (Empty -> A).
Proof.
  refine (BuildContr (Empty -> A) (Empty_rec A) _).
  intros f; apply path_forall; intros x; elim x.
Defined.  

(** ** Behavior with respect to truncation *)

Global Instance hprop_Empty : IsHProp Empty.
Proof. intro x. destruct x. Defined.

Lemma Empty_rec {T : Type} (falso: Empty) : T.
Proof. case falso. Defined.

Global Instance all_to_empty_isequiv (T : Type) (f : T -> Empty) : IsEquiv f.
Proof.
  refine (BuildIsEquiv _ _ _ 
    (Empty_ind (fun _ => T))                (* := equiv_inf *)
    (fun fals:Empty => match fals with end) (* : Sect equiv_inf f *)
    (fun t:T => match (f t) with end)       (* : Sect f equiv_inf *)
    (_)                                     (* adjointify part *)  ).
  intro t. 
  exact (Empty_rec (f t)).
Defined.

(** ** Paths *)

(** We could probably prove some theorems about non-existing paths in
   [Empty], but this is really quite useless. As soon as an element
   of [Empty] is hypothesized, we can prove whatever we like with
   a simple elimination. *)
