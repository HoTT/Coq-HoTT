(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the booleans *)

Require Import Overture Contractible Equivalences Funext types.Prod.
Local Open Scope equiv_scope.

Section BoolForall.
  Variable P : bool -> Type.
  
  Let f (s : forall b, P b) := (s false, s true).

  Let g (u : P false * P true) (b : bool) : P b :=
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
    (* must first show that decidable types are in HSet. *)
  Defined.

End BoolForall.