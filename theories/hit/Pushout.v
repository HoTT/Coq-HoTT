(* -*- mode: coq; mode: visual-line -*- *)

(** * The flattening lemma. *)

Require Import Overture PathGroupoids Equivalences.
Require Import types.Paths types.Forall types.Sigma types.Arrow types.Universe.
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

Require Import types.Unit HSet types.Sum.

Definition isepi {X Y} (f:X->Y) := forall Z: hSet,
                                    forall g h: Y -> Z, g o f = h o f -> g = h.

Definition hEpi {X Y} (f : X -> Y) := forall Z : hSet,
                                        forall g : Y -> Z, 
                                          Contr  { h : Y -> Z & g o f = h o f }.

Definition const {A B} (b : B) := fun x : A => b.
Require Import Trunc Contractible Tactics.

Lemma transport_precomp {A B C} (f : A -> B) (g g' : B -> C) (p : g = g') :
      transport (fun h : B -> C => g o f = h o f) p 1 =
      ap (fun h => h o f) p.
Proof.
  destruct p.
  simpl. reflexivity.
Defined.    

Lemma apD10_ap_precomp {A B C} (f : A -> B) (g g' : B -> C) (p : g = g') a :
   apD10 (ap (fun h : B -> C => h o f) p) a = apD10 p (f a).
Proof.
  destruct p. simpl. reflexivity.
Defined.

Section Cone.
  Context {A B : hSet} (f : A -> B).
  Definition one {A : Type} : A -> Unit := fun x => tt.

  Definition Cf := pushout f one.

  Instance Cf_hSet : IsHSet Cf.
  Proof.
    admit.
  Defined.    

  Definition t : Cf := push (inr tt).


  Lemma isepi_isContr `{Funext} : hEpi f -> Contr Cf.
  Proof.
    intros hepi.
    red. simpl. exists t.

    pose (α1 := @pp A B Unit f one).
    pose (tot:= { h : B -> Cf & push o inl o f = h o f }).
    pose (l := (push o inl; idpath) : tot).
    pose (r := (@const B Cf t; path_forall _ _ α1) : tot). 
    subst tot.

    + assert (l = r).
      pose (hepi {| setT := Cf |} (push o inl)). 
      apply path_contr.
    subst l r.

    pose (I0 b := apD10 (X ..1) b).
    refine (pushout_rect _ _ _ _ _).
    intros [b|[]]; [|reflexivity]. 
    apply inverse. apply I0.
    
    simpl. subst α1. intros.
    change (paths t) with (fun x => t = x).
    rewrite transport_paths_r. subst I0. simpl.
    pose (X..2). simpl in p. rewrite transport_precomp in p.
    assert (H':=concat (ap (fun x => apD10 x a) p) (apD10_path_forall _ _ _ a)).
    clear p.
    pose (concat (apD10_ap_precomp f _ _ (X ..1) a)^ H').
    simpl in p.
    rewrite p. apply concat_Vp.
  Defined.

End Cone.