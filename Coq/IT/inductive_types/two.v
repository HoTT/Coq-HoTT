(** Rules for the weak inductive type Two with two constructors and propositional
    beta rules. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom Two : U.

(* Introduction rules. *)
Axiom false : Two.
Axiom true : Two.

(* Elimination rule. *)
Axiom two_rec : forall (E : Two -> U) (e_f : E false) (e_t : E true) (x : Two), E x.

(* Beta rules. *)
Axiom two_beta_f : forall (E : Two -> U) (e_f : E false) (e_t : E true),
  Id (two_rec E e_f e_t false) e_f.

Axiom two_beta_t : forall (E : Two -> U) (e_f : E false) (e_t : E true),
  Id (two_rec E e_f e_t true) e_t.

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition two_eta_1 (E : Two -> U) (e_f : E false) (e_t : E true) (h : forall x, E x) (p_f : Id (h false) e_f) (p_t : Id (h true) e_t) :
  forall (x : Two), Id (h x) (two_rec E e_f e_t x)
  := two_rec (fun x => Id (h x) (two_rec E e_f e_t x))
             (p_f @ (two_beta_f E e_f e_t)!)
             (p_t @ (two_beta_t E e_f e_t)!).

(* Second-order eta rules. *)
Definition two_eta_2_l (E : Two -> U) (e_f : E false) (e_t : E true) (h : forall x, E x) (p_f : Id (h false) e_f) (p_t : Id (h true) e_t) :
  Id (two_eta_1 E e_f e_t h p_f p_t false @ two_beta_f E e_f e_t) p_f.
Proof.
apply cancel_right_inv.
apply two_beta_f with (E := fun x => Id (h x) (two_rec E e_f e_t x)).
Defined.

Definition two_eta_2_r (E : Two -> U) (e_f : E false) (e_t : E true) (h : forall x, E x) (p_f : Id (h false) e_f) (p_t : Id (h true) e_t) :
  Id (two_eta_1 E e_f e_t h p_f p_t true @ two_beta_t E e_f e_t) p_t.
Proof.
apply cancel_right_inv.
apply two_beta_t with (E := fun x => Id (h x) (two_rec E e_f e_t x)).
Defined.
