(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the unit type *)

Require Import Basics.Overture Basics.Equivalences.
Local Open Scope path_scope.

Local Set Universe Minimization ToSet.

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

Global Instance isequiv_path_unit (z z' : Unit) : IsEquiv (path_unit_uncurried z z') | 0.
Proof.
  refine (Build_IsEquiv _ _ (path_unit_uncurried z z') (fun _ => tt)
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
  := Build_Equiv _ _ (path_unit_uncurried z z') _.

(** ** Transport *)

(** Is a special case of transporting in a constant fibration. *)

(** ** Universal mapping properties *)

(* The positive universal property *)
Arguments Unit_ind [A] a u : rename.

Global Instance isequiv_unit_ind `{Funext} (A : Unit -> Type)
: IsEquiv (@Unit_ind A) | 0
  := isequiv_adjointify _
  (fun f : forall u:Unit, A u => f tt)
  (fun f : forall u:Unit, A u => path_forall (@Unit_ind A (f tt)) f
                                             (fun x => match x with tt => 1 end))
  (fun _ => 1).

Global Instance isequiv_unit_rec `{Funext} (A : Type)
: IsEquiv (@Unit_ind (fun _ => A)) | 0
  := isequiv_unit_ind (fun _ => A).

#[local]
Hint Extern 4 => progress (cbv beta iota) : typeclass_instances.

Definition equiv_unit_rec `{Funext} (A : Type)
  : A <~> (Unit -> A)
  := (Build_Equiv _ _ (@Unit_ind (fun _ => A)) _).

(* For various reasons, it is typically more convenient to define functions out of the unit as constant maps, rather than [Unit_ind]. *)
Notation unit_name x := (fun (_ : Unit) => x).

Global Instance isequiv_unit_name@{i j} `{Funext} (A : Type@{i})
: @IsEquiv@{i j} _ (Unit -> _) (fun (a:A) => unit_name a).
Proof.
  refine (isequiv_adjointify _ (fun f : Unit -> _ => f tt) _ _).
  - intros f; apply path_forall@{i i j}; intros x.
    apply ap@{i i}, path_unit.
  - intros a; reflexivity.
Defined.

(* The negative universal property *)
Definition unit_coind {A : Type} : Unit -> (A -> Unit)
  := fun _ _ => tt.

Global Instance isequiv_unit_coind `{Funext} (A : Type) : IsEquiv (@unit_coind A) | 0.
Proof.
  refine (isequiv_adjointify _ (fun f => tt) _ _).
  - intro f. apply path_forall; intros x; apply path_unit.
  - intro x; destruct x; reflexivity.
Defined.

Definition equiv_unit_coind `{Funext} (A : Type)
  : Unit <~> (A -> Unit)
  := Build_Equiv _ _ (@unit_coind A) _.

(** ** Truncation *)

(* The Unit type is contractible *)
Global Instance contr_unit : Contr Unit | 0 := Build_Contr _ tt (fun t : Unit => match t with tt => 1 end).

(** ** Equivalences *)

(** A contractible type is equivalent to [Unit]. *)
Definition equiv_contr_unit `{Contr A} : A <~> Unit
  := equiv_contr_contr.

(* Conversely, a type equivalent to [Unit] is contractible. We don't make this an instance because Coq would have to guess the equivalence.  And when it has a map in mind, it would try to use [isequiv_contr_contr], which would cause a cycle. *)
Definition contr_equiv_unit (A : Type) (f : A <~> Unit) : Contr A
  := contr_equiv' Unit f^-1%equiv.

(** The constant map to [Unit].  We define this so we can get rid of an unneeded universe variable that Coq generates when [const tt] is used in a context that doesn't have [Universe Minimization ToSet] as this file does. If we ever set that globally, then we could get rid of this and remove some imports of this file. *)
Definition const_tt (A : Type) := @const A Unit tt.
