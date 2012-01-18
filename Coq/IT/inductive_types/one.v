(** Rules for the weak inductive type One with one constructor and propositional
    beta rule. **)
    
Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom One : U.

(* Introduction rule. *)
Axiom unit : One.

(* Elimination rule. *)
Axiom one_rec : forall (E : One -> U) (e_u : E unit) (x : One), E x.

(* Beta rule. *)
Axiom one_beta : forall (E : One -> U) (e_u : E unit),
  Id (one_rec E e_u unit) e_u.

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition one_eta_1 (E : One -> U) (e_u : E unit) (h : forall x, E x) (p : Id (h unit) e_u) :
  forall (x : One), Id (h x) (one_rec E e_u x)
  := one_rec (fun x => Id (h x) (one_rec E e_u x)) (p @ (one_beta E e_u)!).

(* Second-order eta rule. *)
Definition one_eta_2 (E : One -> U) (e_u : E unit) (h : forall x, E x) (p : Id (h unit) e_u) :
  Id (one_eta_1 E e_u h p unit @ one_beta E e_u) p.
Proof.
apply cancel_right_inv.
apply one_beta with (E := fun x => Id (h x) (one_rec E e_u x)).
Defined.
