(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import Types.Paths Types.Forall Types.Sigma Types.Arrow Types.Universe Types.Unit Types.Sum.
Require Import HSet TruncType.
Require Export HIT.Coeq.
Require Import HIT.Truncations.
Local Open Scope path_scope.


(** * Homotopy Pushouts *)

(*
Record Span :=
  { A : Type; B : Type; C : Type;
    f : C -> A;
    g : C -> B }.

Record Cocone (S : Span) (D : Type) :=
  { i : A S -> D;
    j : B S -> D;
    h : forall c, i (f S c) = j (g S c) }.
*)

(** We define pushouts in terms of coproducts and coequalizers. *)

Definition pushout {A B C : Type} (f : A -> B) (g : A -> C) : Type
  := Coeq (inl o f) (inr o g).

Definition push {A B C : Type} {f : A -> B} {g : A -> C}
  := @coeq _ _ (inl o f) (inr o g).

Definition pushl {A B C} {f : A -> B} {g : A -> C} (a : A) : pushout f g := push (inl (f a)).
Definition pushr {A B C} {f : A -> B} {g : A -> C} (a : A) : pushout f g := push (inr (g a)).

Definition pp {A B C : Type} {f : A -> B} {g : A -> C} (a : A) : pushl a = pushr a
  := @cp A (B+C) (inl o f) (inr o g) a.

Definition pushout_ind {A B C} (f : A -> B) (g : A -> C) (P : pushout f g -> Type)
  (push' : forall a : B + C, P (push a))
  (pp' : forall a : A, (pp a) # (push' (inl (f a))) = push' (inr (g a)))
  : forall w, P w
  := Coeq_ind P push' pp'.

Definition pushout_ind_beta_pp {A B C f g}
           (P : @pushout A B C f g -> Type)
           (push' : forall a : B + C, P (push a))
           (pp' : forall a : A, (pp a) # (push' (inl (f a))) = push' (inr (g a))) (a : A)
: apD (pushout_ind f g P push' pp') (pp a) = pp' a
  := Coeq_ind_beta_cp P push' pp' a.

(** But we want to allow the user to forget that we've defined pushouts in terms of coequalizers. *)
Arguments pushout : simpl never.
Arguments push : simpl never.
Arguments pp : simpl never.
Arguments pushout_ind : simpl never.
Arguments pushout_ind_beta_pp : simpl never.

Definition pushout_rec {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (push' : B + C -> P)
  (pp' : forall a : A, push' (inl (f a)) = push' (inr (g a)))
  : @pushout A B C f g -> P
  := pushout_ind f g (fun _ => P) push' (fun a => transport_const _ _ @ pp' a).

Definition pushout_rec_beta_pp {A B C f g} (P : Type)
  (push' : B + C -> P)
  (pp' : forall a : A, push' (inl (f a)) = push' (inr (g a)))
  (a : A)
  : ap (pushout_rec P push' pp') (pp a) = pp' a.
Proof.
  unfold pushout_rec.
  eapply (cancelL (transport_const (pp a) _)).
  refine ((apD_const (@pushout_ind A B C f g (fun _ => P) push' _) (pp a))^ @ _).
  refine (pushout_ind_beta_pp (fun _ => P) _ _ _).
Defined.

(** ** Cones of hsets *)

Section SetCone.
  Context {A B : hSet} (f : A -> B).

  Definition setcone := Trunc 0 (pushout f (const tt)).

  Global Instance istrunc_setcone : IsHSet setcone := _.

  Definition setcone_point : setcone := tr (push (inr tt)).
End SetCone.
