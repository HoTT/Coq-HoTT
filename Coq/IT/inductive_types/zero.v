(** Rules for the inductive type Zero with no constructors. **)
    
Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom Zero : U.

(* No introduction rule. *)

(* Elimination rule. *)
Axiom zero_rec : forall (E : Zero -> U) (x : Zero), E x.

(* No beta rule. *)

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition zero_eta_1 (E : Zero -> U) (h : forall x, E x) :
  forall (x : Zero), Id (h x) (zero_rec E x)
  := zero_rec (fun x => Id (h x) (zero_rec E x)).