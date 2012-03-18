(** Rules for the inductive type List A, the weak version of lists of type A. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom List : U -> U.

(* Introduction rules. *)
Axiom nil : forall (A : U), List A.
Axiom cons : forall (A : U), A -> List A -> List A.

(* Elimination rule. *)
Axiom list_rec : forall (A : U) (E : List A -> U) (e_n : E (nil A)) (e_c : forall a l, E l -> E (cons A a l))
  (x : List A), E x.

(* Beta rules. *)
Axiom list_beta_n : forall (A : U) (E : List A -> U) (e_n : E (nil A)) (e_c : forall a l, E l -> E (cons A a l)),
  Id (list_rec A E e_n e_c (nil A)) e_n.

Axiom list_beta_c : forall (A : U) (E : List A -> U) (e_n : E (nil A)) (e_c : forall a l, E l -> E (cons A a l))
  (a : A) (l : List A),
  Id (list_rec A E e_n e_c (cons A a l)) (e_c a l (list_rec A E e_n e_c l)).

(***********************************************************************)
(***********************************************************************)

(* Derived rules. *)

(* First-order eta rule. *)
Definition list_eta_1 (A : U) (E : List A -> U) (e_n : E (nil A)) (e_c : forall a l, E l -> E (cons A a l)) (h : forall x, E x) (p_n : Id (h (nil A)) e_n) (p_c : forall a l, Id (h (cons A a l)) (e_c a l (h l))) :
  forall (x : List A), Id (h x) (list_rec A E e_n e_c x)
  := list_rec A (fun x => Id (h x) (list_rec A E e_n e_c x))
                (p_n @ (list_beta_n A E e_n e_c)!)
                (fun a l hyp => p_c a l @ mapid (e_c a l) hyp @ (list_beta_c A E e_n e_c a l)!).

(* Second-order eta rules. *)
Definition list_eta_2_n (A : U) (E : List A -> U) (e_n : E (nil A)) (e_c : forall a l, E l -> E (cons A a l)) (h : forall x, E x) (p_n : Id (h (nil A)) e_n) (p_c : forall a l, Id (h (cons A a l)) (e_c a l (h l))) :
  Id (list_eta_1 A E e_n e_c h p_n p_c (nil A) @ list_beta_n A E e_n e_c) p_n.
Proof.
intros.
apply cancel_right_inv.
apply list_beta_n with (E := fun x => Id (h x) (list_rec A E e_n e_c x)).
Defined.

Definition list_eta_2_c (A : U) (E : List A -> U) (e_n : E (nil A)) (e_c : forall a l, E l -> E (cons A a l)) (h : forall x, E x) (p_n : Id (h (nil A)) e_n) (p_c : forall a l, Id (h (cons A a l)) (e_c a l (h l))) :
  forall (a : A) (l : List A),
  Id (list_eta_1 A E e_n e_c h p_n p_c (cons A a l) @ list_beta_c A E e_n e_c a l)
     (p_c a l @ mapid (e_c a l) (list_eta_1 A E e_n e_c h p_n p_c l)).
Proof.
intros.
apply cancel_right_inv.
apply list_beta_c with (E := fun x => Id (h x) (list_rec A E e_n e_c x)).
Defined.
