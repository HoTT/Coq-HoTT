(** Rules for the inductive type W A B, the weak version of W-types over A and B. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom W : forall (A : U) (B : A -> U), U.

(* Introduction rule. *)
Axiom sup : forall (A : U) (B : A -> U) (x : A) (f : B x -> W A B), W A B.

(* Elimination rule. *)
Axiom w_rec : forall (A : U) (B : A -> U) (E : W A B -> U) (e_s : forall x f, (forall b, E (f b)) -> E (sup A B x f))
  (w : W A B), E w.

(* Beta rule. *)
Axiom w_beta : forall (A : U) (B : A -> U) (E : W A B -> U) (e_s : forall x f, (forall b, E (f b)) -> E (sup A B x f))
  (x : A) (f : B x -> W A B),
  Id (w_rec A B E e_s (sup A B x f)) (e_s x f (fun b => w_rec A B E e_s (f b))).

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition w_eta_1 (A : U) (B : A -> U) (E : W A B -> U) (e_s : forall x f, (forall b, E (f b)) -> E (sup A B x f)) (h : forall x, E x) (p_s : forall x f, Id (h (sup A B x f)) (e_s x f (fun b => h (f b)))) :
  forall (w : W A B), Id (h w) (w_rec A B E e_s w)
  := w_rec A B (fun w => Id (h w) (w_rec A B E e_s w))
               (fun x f hyp => p_s x f @ mapid (e_s x f) (dfunext _ _ _ hyp) @ (w_beta A B E e_s x f)!).

(* Second-order eta rule. *)
Definition w_eta_2 (A : U) (B : A -> U) (E : W A B -> U) (e_s : forall x f, (forall b, E (f b)) -> E (sup A B x f)) (h : forall x, E x) (p_s : forall x f, Id (h (sup A B x f)) (e_s x f (fun b => h (f b)))) :
  forall (x : A) (f : B x -> W A B),
  Id (w_eta_1 A B E e_s h p_s (sup A B x f) @ w_beta A B E e_s x f)
     (p_s x f @ mapid (e_s x f) (dfunext _ _ _ (fun b => w_eta_1 A B E e_s h p_s (f b)))).
Proof.
intros.
apply cancel_right_inv.
apply w_beta with (E := fun w => Id (h w) (w_rec A B E e_s w)).
Defined.
