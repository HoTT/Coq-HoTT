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



Definition pushout_rectnd {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (push' : B + C -> P)
  (pp' : forall a : A, push' (inl (f a)) = push' (inr (g a)))
  : @pushout A B C f g -> P
  := pushout_rect f g (fun _ => P) push' (fun a => transport_const _ _ @ pp' a).

Section Paths.
  Context {A B C} {f : A -> B} {g : A -> C}.

  (* Definition pushout_eq (z z' : pushout f g) := *)
  (*   match z, z' with *)
  (*     | push (inl z0), push (inl z'0) => z0 = z'0 *)
  (*     | push (inr z0), push (inr z'0) => z0 = z'0 *)
  (*     | push (inl a), push (inr b) =>  *)
  (*       { x : A & f x = a /\ g x = b } *)
  (*     | push (inr a), push (inl b) =>  *)
  (*       { x : A & f x = b /\ g x = a } *)
  (*   end. *)
  
  (* Definition equiv_left (a : A) (w : B) := *)
  (*   (fun x : f a = w => (a; (x, 1)) : {x : A & (f x = w) * (g x = g a)}). *)

  (* Definition equiv_right (a : A) (w : B) : {x : A & (f x = w) * (g x = g a)} -> f a = w. *)
  (* Proof. *)
  (*   intros [x [p q]]. destruct p. *)
  (*   admit. *)
  (* Defined. *)

  (* Definition isequiv a b : IsEquiv (equiv a b). *)
  (* Proof. *)
  (*   esplit. *)

(*   Definition pushout_eq `{Funext} `{Univalence} : forall (z z' : pushout f g), Type. *)
(*     refine (pushout_rectnd (pushout f g -> Type)  *)
(*                            (fun z =>  *)
(*                               match z with *)
(*                                 | inl z0 => *)
(*                                   pushout_rectnd Type  *)
(*                                      (fun z' => *)
(*                                         match z' with *)
(*                                           | inl z'0 => z0 = z'0 *)
(*                                           | inr z'0 => { x : A & f x = z0 /\ g x = z'0 } *)
(*                                         end) _ *)
(*                                 | inr z0 => *)
(*                                   pushout_rectnd Type  *)
(*                                      (fun z' => *)
(*                                         match z' with *)
(*                                           | inl z'0 => { x : A & f x = z'0 /\ g x = z0 } *)
(*                                           | inr z'0 => z0 = z'0 *)
(*                                         end) _ *)
(*                               end) *)
(*                    _); intros. *)
(*     admit.  *)
(*     admit.  *)
(*     unfold pushout_rectnd. *)
(*     unfold pushout_rect. apply path_forall. *)
(*     intros w. destruct w as [[w|w]].  *)
(*     pose (path_universe equiv). *)
(*   Defined. *)

(*   Definition pushout_eq_pushoutrect z z' : pushout_eq_pushoutrect_type z z'. *)
(*   Proof. red. simpl. unfold pushout_rectnd. unfold pushout_rect. simpl.  *)
(*          unfold pushout_eq. *)
(*          destruct z as [[z|z]], z' as [[z'|z']]; exact 1. *)
(*   Defined. *)

(*   Definition path_pushout (z z' : pushout f g) *)
(*              (pq : pushout_eq z z') : z = z'. *)
(*   Proof. *)
(*     destruct z as [[z|z]], z' as [[z'|z']], pq; try exact idpath. *)
(*     destruct p. destruct p, p0. apply pp. *)
(*     destruct p. destruct p, p0. symmetry. apply pp. *)
(*   Defined. *)

(*   Definition path_pushout_inv (z z' : pushout f g) *)
(*              (pq : z = z') *)
(*   : pushout_eq z z'. *)
(*   Proof. *)
(*     destruct pq, z as [[z|z]]; exact 1. *)
(*   Defined. *)

(*   Definition eisretr_path_pushout {z z' : pushout f g} *)
(*   : Sect (path_pushout_inv z z') (path_pushout z z'). *)
(*   Proof. *)
(*     intros p. destruct p. destruct z as [[z|z]]; exact 1.  *)
(*   Defined. *)

(*   Definition eissect_path_pushout {z z' : pushout f g} *)
(*   : Sect (path_pushout z z')  (path_pushout_inv z z'). *)
(*   Proof. *)
(*     intros p. pose (pushout_eq_pushoutrect z z'). red in p0. rewrite p0 in p. *)
(* destruct z as [[z|z]], z' as [[z'|z']], p; simpl; try exact 1.  *)
(*     destruct p. unfold path_pushout_inv. destruct p. destruct p0. simpl. *)
(*     set (e := pp x).  *)
(*     pose (apD (pushout_rect f g  *)


(*   Defined. *)

End Paths.

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
Require Import Trunc Truncations Contractible Tactics.

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

Lemma apD10_ap_postcomp {A B C} (f : B -> C) (g g' : A -> B) (p : g = g') a :
   apD10 (ap (fun h : A -> B => f o h) p) a = ap f (apD10 p a).
Proof.
  destruct p. simpl. reflexivity.
Defined.

Section Cone.
  Universe i.
  
  Context {A B : hSet@{i}} (f : A -> B).
  Definition one {A : Type@{i}} : A -> Unit := fun x => tt.

  Definition Cf := Truncation@{i} 0 (pushout f one).

  Instance Cf_hSet : IsHSet Cf.
  Proof. apply istrunc_truncation. Defined.

  Definition t : Cf := truncation_incl@{i} (push (inr tt)).

  Lemma isepi_isContr `{Funext} : hEpi@{i i i i i i} f -> Contr Cf.
  Proof.
    intros hepi.
    red. simpl. exists t.

    pose (α1 := @pp A B Unit f one).
    pose (tot:= { h : B -> Cf & truncation_incl o push o inl o f = h o f }).
    pose (l := (truncation_incl o push o inl; idpath) : tot).
    pose (r:= (@const B Cf t; (ap (fun f => @truncation_incl 0 _ o f) (path_forall _ _ α1))) : tot).
    subst tot.

    + assert (l = r).
      red in hepi.
      pose (hepi {| setT := Cf |} (truncation_incl o push o inl)).
      apply path_contr.
    subst l r.

    pose (I0 b := apD10 (X ..1) b).
    refine (Truncation_rect _ _).
    refine (pushout_rect _ _ _ _ _).
    intros [b|[]]; [|reflexivity]. 
    apply inverse. apply I0.
    
    simpl. subst α1. intros.
    unfold t. 
    subst I0. simpl.
    pose (X..2). simpl in p. rewrite transport_precomp in p.
    assert (H':=concat (ap (fun x => apD10 x a) p) (apD10_ap_postcomp truncation_incl _ _ (path_forall pushl pushr pp) _)).
    rewrite (apD10_path_forall _ _ _ a) in H'.
    clear p.
    pose (concat (apD10_ap_precomp f _ _ (X ..1) a)^ H').
    simpl in p.
    rewrite p. 
    rewrite transport_paths_Fr.
    apply concat_Vp.
  Defined.

End Cone.