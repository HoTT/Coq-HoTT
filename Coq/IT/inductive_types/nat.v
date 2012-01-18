(** Rules for the inductive type Nat, the weak version of natural numbers. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom Nat : U.

(* Introduction rules. *)
Axiom zero : Nat.
Axiom suc : Nat -> Nat.

(* Elimination rule. *)
Axiom nat_rec : forall (E : Nat -> U) (e_z : E zero) (e_s : forall n, E n -> E (suc n))
  (x : Nat), E x.

(* Beta rules. *)
Axiom nat_beta_z : forall (E : Nat -> U) (e_z : E zero) (e_s : forall n, E n -> E (suc n)),
  Id (nat_rec E e_z e_s zero) e_z.

Axiom nat_beta_s : forall (E : Nat -> U) (e_z : E zero) (e_s : forall n, E n -> E (suc n))
  (n : Nat), Id (nat_rec E e_z e_s (suc n)) (e_s n (nat_rec E e_z e_s n)).

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition nat_eta_1 (E : Nat -> U) (e_z : E zero) (e_s : forall n, E n -> E (suc n)) (h : forall x, E x) (p_z : Id (h zero) e_z) (p_s : forall n, Id (h (suc n)) (e_s n (h n))) :
  forall (x : Nat), Id (h x) (nat_rec E e_z e_s x)
  := nat_rec (fun x => Id (h x) (nat_rec E e_z e_s x))
             (p_z @ (nat_beta_z E e_z e_s)!)
             (fun n hyp => p_s n @ mapid (e_s n) hyp @ (nat_beta_s E e_z e_s n)!).

(* Second-order eta rules. *)
Definition nat_eta_2_z (E : Nat -> U) (e_z : E zero) (e_s : forall n, E n -> E (suc n)) (h : forall x, E x) (p_z : Id (h zero) e_z) (p_s : forall n, Id (h (suc n)) (e_s n (h n))) :
  Id (nat_eta_1 E e_z e_s h p_z p_s zero @ nat_beta_z E e_z e_s) p_z.
Proof.
intros.
apply cancel_right_inv.
apply nat_beta_z with (E := fun x => Id (h x) (nat_rec E e_z e_s x)).
Defined.

Definition nat_eta_2_s (E : Nat -> U) (e_z : E zero) (e_s : forall n, E n -> E (suc n)) (h : forall x, E x) (p_z : Id (h zero) e_z) (p_s : forall n, Id (h (suc n)) (e_s n (h n))) :
  forall (n : Nat),
  Id (nat_eta_1 E e_z e_s h p_z p_s (suc n) @ nat_beta_s E e_z e_s n)
     (p_s n @ mapid (e_s n) (nat_eta_1 E e_z e_s h p_z p_s n)).
Proof.
intros.
apply cancel_right_inv.
apply nat_beta_s with (E := fun x => Id (h x) (nat_rec E e_z e_s x)).
Defined.
