(** Rules for the inductive type Sum A B, the weak version of A + B. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom Sum : U -> U -> U.

(* Introduction rules. *)
Axiom inl : forall (A B : U), A -> Sum A B.
Axiom inr : forall (A B : U), B -> Sum A B.

(* Elimination rule. *)
Axiom sum_rec : forall (A B : U) (E : Sum A B -> U) (e_l : forall a, E (inl A B a)) (e_r : forall b, E (inr A B b))
  (x : Sum A B), E x.

(* Beta rules. *)
Axiom sum_beta_l : forall (A B : U) (E : Sum A B -> U) (e_l : forall a, E (inl A B a)) (e_r : forall b, E (inr A B b))
  (a : A), Id (sum_rec A B E e_l e_r (inl A B a)) (e_l a).

Axiom sum_beta_r : forall (A B : U) (E : Sum A B -> U) (e_l : forall a, E (inl A B a)) (e_r : forall b, E (inr A B b))
  (b : B), Id (sum_rec A B E e_l e_r (inr A B b)) (e_r b).

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition sum_eta_1 (A B : U) (E : Sum A B -> U) (e_l : forall a, E (inl A B a)) (e_r : forall b, E (inr A B b)) (h : forall x, E x) (p_l : forall a, Id (h (inl A B a)) (e_l a)) (p_r : forall b, Id (h (inr A B b)) (e_r b)) :
  forall (x : Sum A B), Id (h x) (sum_rec A B E e_l e_r x)
  := sum_rec A B (fun x => Id (h x) (sum_rec A B E e_l e_r x))
                 (fun a => p_l a @ (sum_beta_l A B E e_l e_r a)!)
                 (fun b => p_r b @ (sum_beta_r A B E e_l e_r b)!).

(* Second-order eta rules. *)
Definition sum_eta_2_l (A B : U) (E : Sum A B -> U) (e_l : forall a, E (inl A B a)) (e_r : forall b, E (inr A B b)) (h : forall x, E x) (p_l : forall a, Id (h (inl A B a)) (e_l a)) (p_r : forall b, Id (h (inr A B b)) (e_r b)) :
  forall (a : A),
  Id (sum_eta_1 A B E e_l e_r h p_l p_r (inl A B a) @ sum_beta_l A B E e_l e_r a)
     (p_l a).
Proof.
intros.
apply cancel_right_inv.
apply sum_beta_l with (E := fun x => Id (h x) (sum_rec A B E e_l e_r x)) (a := a).
Defined.

Definition sum_eta_2_r (A B : U) (E : Sum A B -> U) (e_l : forall a, E (inl A B a)) (e_r : forall b, E (inr A B b)) (h : forall x, E x) (p_l : forall a, Id (h (inl A B a)) (e_l a)) (p_r : forall b, Id (h (inr A B b)) (e_r b)) :
  forall (b : B),
  Id (sum_eta_1 A B E e_l e_r h p_l p_r (inr A B b) @ sum_beta_r A B E e_l e_r b)
     (p_r b).
Proof.
intros.
apply cancel_right_inv.
apply sum_beta_r with (E := fun x => Id (h x) (sum_rec A B E e_l e_r x)) (b := b).
Defined.
