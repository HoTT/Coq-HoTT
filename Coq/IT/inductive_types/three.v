(** Rules for the weak inductive type Three with three constructors and
    propositional beta rules. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom Three : U.

(* Introduction rules. *)
Axiom left : Three.
Axiom center : Three.
Axiom right : Three.

(* Elimination rule. *)
Axiom three_rec : forall (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right) (x : Three), E x.

(* Beta rules. *)
Axiom three_beta_l : forall (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right),
  Id (three_rec E e_l e_c e_r left) e_l.

Axiom three_beta_c : forall (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right),
  Id (three_rec E e_l e_c e_r center) e_c.

Axiom three_beta_r : forall (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right),
  Id (three_rec E e_l e_c e_r right) e_r.

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition three_eta_1 (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right) (h : forall x, E x) (p_l : Id (h left) e_l) (p_c : Id (h center) e_c) (p_r : Id (h right) e_r) :
  forall (x : Three), Id (h x) (three_rec E e_l e_c e_r x)
  := three_rec (fun x => Id (h x) (three_rec E e_l e_c e_r x))
               (p_l @ (three_beta_l E e_l e_c e_r)!)
               (p_c @ (three_beta_c E e_l e_c e_r)!)
               (p_r @ (three_beta_r E e_l e_c e_r)!).

(* Second-order eta rules. *)
Definition three_eta_2_l (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right) (h : forall x, E x) (p_l : Id (h left) e_l) (p_c : Id (h center) e_c) (p_r : Id (h right) e_r) :
  Id (three_eta_1 E e_l e_c e_r h p_l p_c p_r left @ three_beta_l E e_l e_c e_r)
     p_l.
Proof.
apply cancel_right_inv.
apply three_beta_l with (E := fun x => Id (h x) (three_rec E e_l e_c e_r x)).
Defined.

Definition three_eta_2_c (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right) (h : forall x, E x) (p_l : Id (h left) e_l) (p_c : Id (h center) e_c) (p_r : Id (h right) e_r) :
  Id (three_eta_1 E e_l e_c e_r h p_l p_c p_r center @ three_beta_c E e_l e_c e_r)
     p_c.
Proof.
apply cancel_right_inv.
apply three_beta_c with (E := fun x => Id (h x) (three_rec E e_l e_c e_r x)).
Defined.

Definition three_eta_2_r (E : Three -> U) (e_l : E left) (e_c : E center) (e_r : E right) (h : forall x, E x) (p_l : Id (h left) e_l) (p_c : Id (h center) e_c) (p_r : Id (h right) e_r) :
  Id (three_eta_1 E e_l e_c e_r h p_l p_c p_r right @ three_beta_r E e_l e_c e_r)
     p_r.
Proof.
apply cancel_right_inv.
apply three_beta_r with (E := fun x => Id (h x) (three_rec E e_l e_c e_r x)).
Defined.
