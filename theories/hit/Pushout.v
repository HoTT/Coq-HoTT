(* -*- mode: coq; mode: visual-line -*- *)

(** * The flattening lemma. *)

Require Import Overture PathGroupoids Equivalences.
Require Import types.Paths types.Forall types.Sigma types.Arrow types.Universe.
Local Open Scope path_scope.
Local Open Scope equiv_scope.


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
  := fun w => match w with push a => push' a end.

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
  refine (cancelL (transport_const (pp a) _) _ _ _). shelve. shelve. 
  exact f. exact g.
  refine ((apD_const (@pushout_rect A B C f g (fun _ => P) push' _) (pp a))^ @ _).
  refine (pushout_rect_beta_pp (fun _ => P) _ _ _).
Defined.

Require Import types.Unit HSet. 

Definition isepi {X Y} (f:X->Y) := forall Z: hSet,
                                    forall g h: Y -> Z, g o f = h o f -> g = h.

Definition hEpi {X Y} (f : X -> Y) := forall Z : hSet,
                                        forall g : Y -> Z, 
                                          Contr  { h : Y -> Z & g o f = h o f }.

Definition const {A B} (b : B) := fun x : A => b.
Require Import Trunc Contractible.
Definition trunc_pushout n A B C f g `{IsTrunc n A, IsTrunc n B, IsTrunc n C} : 
  IsTrunc n (@pushout A B C f g).
Proof.
  induction n; simpl; intros.
  exists (pushl (f:=f) (g:=g) (center _)).
  intros y.
  refine (pushout_rect _ _ (fun y => pushl (center A) = y) _ _ y).
  intros a. destruct a. unfold pushl. apply ap. apply ap. apply path_contr.
  assert (c = g (center A)). apply path_contr. 
  eapply concat. apply pp. unfold pushr. apply ap. apply ap.
  symmetry. apply X.
  simpl. unfold transitivity. unfold transitive_paths.
  intros. admit.

  simpl in *.
  revert x y. intros x. refine (pushout_rect _ _ (fun x => forall y, IsTrunc n (x = y))  _ _ x). 
  intros []. simpl. intros b.
  refine (pushout_rect _ _ (fun x => IsTrunc n (push (inl b) = x))  _ _).  intros []. intros. 
  
  

  typeclasses eauto.
Defined.

Section Cone.
  Context {A B : hSet} (f : A -> B).
  Definition one {A : Type} : A -> Unit := fun x => tt.

  Definition Cf := pushout f one.

  Lemma Cf_hSet : IsHSet Cf.
  Proof.
    intro y.
    refine (pushout_rect _ _ (fun y => forall y', IsHProp (y = y')) _ _ y).
    intro.
    refine (pushout_rect _ _ (fun y => IsHProp (push a = y)) _ _).
    intros.
    

  Definition t : Cf := push_right tt.

  Lemma isepi_isContr `{Funext} : hEpi f -> Contr Cf.
  Proof.
    intros hepi.
    red. simpl. exists t.
    intros. refine (pushout_rect _ _ _ _ _ _ y); clear y. 
    intros. pose (α1 := @pp A B Unit f one).
    pose (tot:= { h : B -> Cf & push_left o f = h o f }).
    pose (l := (push_left; idpath) : tot).
    pose (r := (@const B Cf t; path_forall _ _ α1) : tot). 
    pose (hepi Cf push_left).

Definition mapping
