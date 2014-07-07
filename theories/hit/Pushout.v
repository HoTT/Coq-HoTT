(* -*- mode: coq; mode: visual-line -*- *)

(** * The flattening lemma. *)

Require Import Overture PathGroupoids Equivalences.
Require Import types.Paths types.Forall types.Sigma types.Arrow types.Universe.
Require Import types.Unit HSet types.Sum.
Require Import Trunc Contractible.
Require Import hit.Truncations.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(* Record Span :=  *)
(*   { A : Type; B : Type; C : Type; *)
(*     f : C -> A; *)
(*     g : C -> B }. *)

(* Record Cocone (S : Span) (D : Type) :=  *)
(*   { i : A S -> D; *)
(*     j : B S -> D; *)
(*     h : forall c, i (f S c) = j (g S c) }. *)


(** First we define the general non-recursive HIT. *)

Module Export BaseHIT.

Private Inductive pushout {A B C : Type} (f : A -> B) (g : A -> C) : Type :=
| push : B + C -> pushout f g.

Arguments push {A B C f g} a.

Definition pushl {A B C} {f : A -> B} {g : A -> C} (a : A) : pushout f g := push (inl (f a)).
Definition pushr {A B C} {f : A -> B} {g : A -> C} (a : A) : pushout f g := push (inr (g a)).

Axiom pp : forall {A B C f g} (a:A), @pushl A B C f g a = pushr a.

Definition pushout_rect {A B C} (f : A -> B) (g : A -> C) (P : pushout f g -> Type)
  (push' : forall a : B + C, P (push a))
  (pp' : forall a : A, (@pp A B C f g a) # (push' (inl (f a))) = push' (inr (g a)))
  : forall w, P w
  := fun w => match w with push a => fun _ => push' a end pp'.

Axiom pushout_rect_beta_pp
  : forall {A B C f g} (P : @pushout A B C f g -> Type)
  (push' : forall a : B + C, P (push a))
  (pp' : forall a : A, (@pp A B C f g a) # (push' (inl (f a))) = push' (inr (g a)))
  (a : A),
  apD (pushout_rect f g P push' pp') (pp a) = pp' a.

End BaseHIT.


Definition pushout_rectnd {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (push' : B + C -> P)
  (pp' : forall a : A, push' (inl (f a)) = push' (inr (g a)))
  : @pushout A B C f g -> P
  := pushout_rect f g (fun _ => P) push' (fun a => transport_const _ _ @ pp' a).

Definition pushout_rectnd_beta_pp {A B C f g} (P : Type)
  (push' : B + C -> P)
  (pp' : forall a : A, push' (inl (f a)) = push' (inr (g a)))
  (a : A)
  : ap (pushout_rectnd P push' pp') (pp a) = pp' a.
Proof.
  unfold pushout_rectnd.
  eapply (cancelL (transport_const (pp a) _)).
  refine ((apD_const (@pushout_rect A B C f g (fun _ => P) push' _) (pp a))^ @ _).
  refine (pushout_rect_beta_pp (fun _ => P) _ _ _).
Defined.

Section Cone.
  Context {A B : hSet} (f : A -> B).
  Definition one {A : Type} : A -> Unit := fun x => tt.

  Definition cone := Truncation 0 (pushout f one).

  Global Instance istrunc_cone : IsHSet cone := _.

  Definition cone_point : cone := truncation_incl (push (inr tt)).
End Cone.
