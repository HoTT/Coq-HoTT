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

(** We eta-expand [_] to [fun _ => _] to work around a bug in HoTT/coq: https://github.com/HoTT/coq/issues/117 *)
Global Instance contr_from_Empty {_ : Funext} (A : Type) :
  Contr (Empty -> A) :=
  BuildContr _
             (Empty_rect (fun _ => A))
             (fun f => path_forall _ f (fun x => Empty_rect (fun _ => _) x)).

(** ** Behavior with respect to truncation *)

Global Instance hprop_Empty : IsHProp Empty.
Proof. intro x. destruct x. Defined.

Lemma all_to_empty_isequiv (T : Type) (f : T -> Empty) : IsEquiv f.
Proof.
  refine (BuildIsEquiv _ _ _ 
    (Empty_rect (fun _ => T))               (* := equiv_inf *)
    (fun fals:Empty => match fals with end) (* : Sect equiv_inf f *)
    (fun t:T => match (f t) with end)       (* : Sect f equiv_inf *)
    (_)                                     (* adjointify part *)  ).
  intro t. 
  pose (f t) as my_false. elim my_false.
Defined.

(** ** Paths *)

(** We could probably prove some theorems about non-existing paths in
   [Empty], but this is really quite useless. As soon as an element
   of [Empty] is hypothesized, we can prove whatever we like with
   a simple elimination. *)
