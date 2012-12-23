(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the unit type *)

Require Import Common Paths Contractible Equivalences Funext.
Open Scope path_scope.
Open Scope equiv_scope.

(** *** Eta conversion *)

Definition eta_unit (z : unit) : tt = z
  := match z with tt => 1 end.

(** *** Universal mapping property *)

Instance isequiv_unit_rect `{FunextAxiom} (A : Type)
  : IsEquiv (@unit_rect A)
  := isequiv_adjointify _
  (fun f : unit -> A => f tt)
  (fun f : unit -> A => path_forall (unit_rect (f tt)) f
                                    (fun x => match x with tt => 1 end))
  (fun _ => 1).

(** *** Paths *)

(* This is all kind of ridiculous, but it fits the pattern. *)

Definition path_unit_uncurried (z z' : unit) : unit -> z = z'
  := fun _ => match z, z' with tt, tt => 1 end.

Definition path_unit (z z' : unit) : z = z'
  := path_unit_uncurried z z' tt.

Definition eta_path_unit {z z' : unit} (p : z = z') :
  path_unit z z' = p.
Proof.
  destruct p. destruct z. reflexivity.
Defined.

Instance isequiv_path_unit (z z' : unit) : IsEquiv (path_unit_uncurried z z').
  refine (BuildIsEquiv _ _ (path_unit_uncurried z z') (fun _ => tt)
    (fun p:z=z' =>
      match p in (_ = z') return (path_unit_uncurried z z' tt = p) with
        | idpath => match z as z return (path_unit_uncurried z z tt = 1) with
                    | tt => 1
                  end
      end)
    (fun x => match x with tt => 1 end) _).
  intros []; destruct z, z'; reflexivity.
Defined.

(** *** HLevel *)

Instance contr_unit : Contr unit := {
  center := tt;
  contr := fun t : unit => match t with tt => 1 end
}.

(** *** Equivalences *)

Generalizable Variables A.

(** A contractible type is equivalent to [unit]. *)
Definition equiv_contr_unit `{Contr A} : A <~> unit.
Proof.
  refine (BuildEquiv _ _
    (fun (_ : A) => tt)
    (BuildIsEquiv _ _ _ 
      (fun (_ : unit) => center A)
      (fun t : unit => match t with tt => 1 end)
      (fun x : A => contr x) _)).
  intro x. apply inverse, ap_const.
Defined.

(* Conversely, a type equivalent to [unit] is contractible. *)
Instance contr_equiv_unit (A : Type) (f : A <~> unit) : Contr A
  := BuildContr A (f^-1 tt)
  (fun a => ap f^-1 (contr (f a)) @ eissect f a).
