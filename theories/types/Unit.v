(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the unit type *)

Require Import Overture PathGroupoids Equivalences.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A.

(** *** Eta conversion *)

Definition eta_unit (z : unit) : tt = z
  := match z with tt => 1 end.

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

Definition equiv_path_unit (z z' : unit) : unit <~> (z = z')
  := BuildEquiv _ _ (path_unit_uncurried z z') _.

(** *** Transport *)

(** Is a special case of transporting in a constant fibration. *)

(** *** Universal mapping properties *)

(* The positive universal property *)
Instance isequiv_unit_rect `{Funext} (A : Type) : IsEquiv (@unit_rect A)
  := isequiv_adjointify _
  (fun f : unit -> A => f tt)
  (fun f : unit -> A => path_forall (unit_rect (f tt)) f
                                    (fun x => match x with tt => 1 end))
  (fun _ => 1).

(* The negative universal property *)
Definition unit_corect {A : Type} : unit -> (A -> unit)
  := fun _ _ => tt.

Instance isequiv_unit_corect `{Funext} (A : Type) : IsEquiv (@unit_corect A)
  := isequiv_adjointify _
  (fun f => tt)
  _ _.
Proof.
  - intro f. apply path_forall; intros x; apply path_unit.
  - intro x; destruct x; reflexivity.
Defined.

Definition equiv_unit_corect `{Funext} (A : Type)
  : unit <~> (A -> unit)
  := BuildEquiv _ _ (@unit_corect A) _.

(** *** Truncation *)

(* The unit type is contractible *)
Instance contr_unit : Contr unit := {
  center := tt;
  contr := fun t : unit => match t with tt => 1 end
}.

(** *** Equivalences *)

(** A contractible type is equivalent to [unit]. *)
Definition equiv_contr_unit `{Contr A} : A <~> unit.
Proof.
  refine (BuildEquiv _ _
    (fun (_ : A) => tt)
    (BuildIsEquiv _ _ _ 
      (fun (_ : unit) => center A)
      (fun t : unit => match t with tt => 1 end)
      (fun x : A => contr x) _)).
  intro x. apply symmetry, ap_const.
Defined.

(* Conversely, a type equivalent to [unit] is contractible. *)
Instance contr_equiv_unit (A : Type) (f : A <~> unit) : Contr A
  := BuildContr A (f^-1 tt)
  (fun a => ap f^-1 (contr (f a)) @ eissect f a).
