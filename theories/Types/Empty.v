(** * Theorems about the empty type *)

Require Import Basics.Overture Basics.Equivalences Basics.Trunc.

Local Set Universe Minimization ToSet.

Local Open Scope path_scope.

(** ** Unpacking *)
(** ** Eta conversion *)
(** ** Paths *)
(** ** Transport *)
(** ** Functorial action *)
(** ** Equivalences *)
(** ** Universal mapping properties *)

Global Instance contr_from_Empty@{u} {_ : Funext} (A : Empty -> Type@{u})
  : Contr@{u} (forall x:Empty, A x).
Proof.
  refine (Build_Contr@{u} _ (Empty_ind A) _).
  intros f; apply path_forall@{Set u u}; intros x; elim x.
Defined.

Lemma Empty_rec {T : Type} (falso: Empty) : T.
Proof. case falso. Defined.

Global Instance isequiv_empty_rec@{u} `{Funext} (A : Type@{u})
  : IsEquiv@{Set u} (fun (_ : Unit) => @Empty_rec A) | 0
  := isequiv_adjointify@{Set u} _
  (fun _ => tt)
  (fun f => path_forall@{Set u u} _ _ (fun x => Empty_rec x))
  (fun x => match x with tt => idpath end).

Definition equiv_empty_rec@{u} `{Funext} (A : Type@{u})
  : Unit <~> ((Empty -> A) : Type@{u})
  := (Build_Equiv@{Set u} _ _ (fun (_ : Unit) => @Empty_rec A) _).

(** ** Behavior with respect to truncation *)

Global Instance istrunc_Empty@{} (n : trunc_index) : IsTrunc n.+1 Empty.
Proof.
  refine (@istrunc_leq (-1) n.+1 tt _ _).
  apply istrunc_S.
  intros [].
Defined.

Global Instance isequiv_all_to_empty (T : Type) (f : T -> Empty) : IsEquiv f.
Proof.
  refine (Build_IsEquiv _ _ _ 
    (Empty_ind (fun _ => T))                (* := equiv_inv *)
    (fun fals:Empty => match fals with end) (* : f o equiv_inv == idmap *)
    (fun t:T => match (f t) with end)       (* : equiv_inv o f == idmap *)
    (_)                                     (* adjointify part *)  ).
  intro t. 
  exact (Empty_rec (f t)).
Defined.

Definition equiv_to_empty {T : Type} (f : T -> Empty) : T <~> Empty
  := Build_Equiv T Empty f _.

(** ** Paths *)

(** We could probably prove some theorems about non-existing paths in [Empty], but this is really quite useless. As soon as an element of [Empty] is hypothesized, we can prove whatever we like with a simple elimination. *)
