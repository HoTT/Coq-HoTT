(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the unit type *)

(* coq calls it "unit", we call it "Unit" *)
Inductive Unit : Set :=
    tt : Unit.

Require Import Overture PathGroupoids Equivalences.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A.

(** ** Eta conversion *)

Definition eta_unit (z : Unit) : tt = z
  := match z with tt => 1 end.

(** ** Paths *)

(* This is all kind of ridiculous, but it fits the pattern. *)

Definition path_unit_uncurried (z z' : Unit) : Unit -> z = z'
  := fun _ => match z, z' with tt, tt => 1 end.

Definition path_unit (z z' : Unit) : z = z'
  := path_unit_uncurried z z' tt.

Definition eta_path_unit {z z' : Unit} (p : z = z') :
  path_unit z z' = p.
Proof.
  destruct p. destruct z. reflexivity.
Defined.

Instance isequiv_path_unit (z z' : Unit) : IsEquiv (path_unit_uncurried z z') | 0.
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

Definition equiv_path_unit (z z' : Unit) : Unit <~> (z = z')
  := BuildEquiv _ _ (path_unit_uncurried z z') _.

(** ** Transport *)

(** Is a special case of transporting in a constant fibration. *)

(** ** Universal mapping properties *)

(* The positive universal property *)
Arguments Unit_rect [A] a u : rename.

Instance isequiv_unit_rect `{Funext} (A : Type) : IsEquiv (@Unit_rect (fun _ => A)) | 0
  := isequiv_adjointify _
  (fun f : Unit -> A => f tt)
  (fun f : Unit -> A => path_forall (@Unit_rect (fun _ => A) (f tt)) f
                                    (fun x => match x with tt => 1 end))
  (fun _ => 1).

(* For various reasons, it is typically more convenient to define functions out of the unit as constant maps, rather than [Unit_rect]. *)
Notation unit_name x := (fun (_ : Unit) => x).

(* The negative universal property *)
Definition unit_corect {A : Type} : Unit -> (A -> Unit)
  := fun _ _ => tt.

Instance isequiv_unit_corect `{Funext} (A : Type) : IsEquiv (@unit_corect A) | 0
  := isequiv_adjointify _
  (fun f => tt)
  _ _.
Proof.
  - intro f. apply path_forall; intros x; apply path_unit.
  - intro x; destruct x; reflexivity.
Defined.

Definition equiv_unit_corect `{Funext} (A : Type)
  : Unit <~> (A -> Unit)
  := BuildEquiv _ _ (@unit_corect A) _.

(** ** Truncation *)

(* The Unit type is contractible *)
(** Because [Contr] is a notation, and [Contr_internal] is the record, we need to iota expand to fool Coq's typeclass machinery into accepting supposedly "mismatched" contexts. *)
Instance contr_unit : Contr Unit | 0 := let x := {|
  center := tt;
  contr := fun t : Unit => match t with tt => 1 end
|} in x.

(** ** Equivalences *)

(** A contractible type is equivalent to [Unit]. *)
Definition equiv_contr_unit `{Contr A} : A <~> Unit.
Proof.
  refine (BuildEquiv _ _
    (fun (_ : A) => tt)
    (BuildIsEquiv _ _ _
      (fun (_ : Unit) => center A)
      (fun t : Unit => match t with tt => 1 end)
      (fun x : A => contr x) _)).
  intro x. apply symmetry, ap_const.
Defined.

(* Conversely, a type equivalent to [Unit] is contractible. *)
Instance contr_equiv_unit (A : Type) (f : A <~> Unit) : Contr A | 10000
  := BuildContr A (f^-1 tt)
  (fun a => ap f^-1 (contr (f a)) @ eissect f a).
