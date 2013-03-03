(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the booleans *)

Require Import Overture Contractible Equivalences types.Prod.
Local Open Scope equiv_scope.

(* coq calls it "bool", we call it "Bool" *)
Inductive Bool : Type :=
  | true : Bool
  | false : Bool.

Add Printing If Bool.

Delimit Scope bool_scope with Bool.

Bind Scope bool_scope with Bool.

Definition andb (b1 b2 : Bool) : Bool := if b1 then b2 else false.

Definition orb (b1 b2 : Bool) : Bool := if b1 then true else b2.

Definition negb (b : Bool) := if b then false else true.

Definition implb (b1 b2 : Bool) : Bool := if b1 then b2 else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.

Section BoolForall.
  Variable P : Bool -> Type.
  
  Let f (s : forall b, P b) := (s false, s true).

  Let g (u : P false * P true) (b : Bool) : P b :=
    match b with
      | false => fst u
      | true => snd u
    end.

  Let eissect' `{Funext} : Sect f g.
  Proof.
    intro s; apply path_forall; intro b; destruct b; reflexivity.
  Defined.

  Let eisretr' : Sect g f := fun _ => eta_prod _.

  Definition equiv_bool_forall_prod `{Funext} :
    (forall b, P b) <~> P false * P true.
  Proof.
    exists f.
    refine {| equiv_inv := g ; eisretr := eisretr' ; eissect := eissect' |}.
    admit.
    (* must first show that decidable types are in IsHSet. *)
  Defined.

End BoolForall.