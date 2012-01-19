(* Goal: trying to see how necessary the assumtion of UIP is in the derivation of dependent W-types from W-types (as per various authors: Dybjer 1997, Abbot/Altenkirch/Ghani 2007, Voevodsky 2009(?), possibly also Gimenez 1996, etc). *)

(* STATUS: BROKEN — REWORKING IN PROGRESS. *) 

(* This document derives dependent W-types, using :
(a) pi-types, sigma types, path types;
(b) W-types;
(c) a universe, or alternatively a large elim rule for W-types (in the definition of [is_good]);
(d) functional extensionality, [funext]/[funext_comp] (‘Π-ext’, ‘Π-ext-comp’ in Richard Garner’s “On the strength of dependent products…”).

Most of the work does not require [fext], but just the weaker principle

(e) the axiom [eta_exp], a propositional eta-rule for functions (RG’s [Π-prop-η]), and its associated computation rule [eta_comp].

I’m pretty certain that [eta_exp] is necessary.  I’m not quite so sure about [funext] — I can’t see how to do without it, but it doesn’t seem implausible that a cleverer implementation of the intro and elim rules could obviate the need for it.

Currently, Coq’s [Prop]-valued equality is used throughout for the convenience of rewrite; however, the code is of course all homotopy-valid.
*)

Add Rec LoadPath "../".

Require Import Paths.
Require Import Fibrations.
Require Import Funext.

Axiom funext : funext_dep_statement.

Axiom funext_comp : funext_comp1_statement funext.


(* In fact [funext_comp] is sort of a consequence of [funext]; but that’s a story for another day! *)

Definition eta : eta_dep_statement
  := naive_funext_dep_implies_eta funext.

Implicit Arguments eta [[A] [P]].

Definition eta_comp {A:Type} {P : A -> Type} (f : forall x, P x)
  : eta (fun x => f x) == idpath (fun x => f x).
Proof.
  apply funext_comp.  
Defined.

Inductive W (A : Type) (B : A -> Type) : Type :=
  | w_intro (a : A) (f : B a -> W A B) : W A B.

(*
W_rect
     : forall (A : Type) (B : A -> Type) (P : W A B -> Type),
       (forall (a : A) (f : B a -> W A B),
        (forall b : B a, P (f b)) -> P (w_intro A B a f)) ->
       forall w : W A B, P w
*)

Section dep_W_from_W.

Variable I : Type.
Variable A : I -> Type.
Variable B : forall i:I, A i -> Type.
Variable s : forall {i} {a}, B i a -> I.
Implicit Arguments s [i a].


Inductive dep_W : I -> Type
:=
  dep_w_intro (i:I) (a : A i) (f : forall (b : B i a), dep_W(s b))
            : dep_W i.

(*
dep_W_rect
     : forall P : (forall i : I, dep_W i -> Type),
              (forall (i : I) (a : A i)
                      (f : forall b : B i a, dep_W (s b)),
                      (forall b : B i a, P (s b) (f b))
               -> P i (dep_w_intro i a f))
       -> forall (i : I) (d : dep_W i),
       P i d

Goal now: using just [W] above, construct a type with this recursor and the corresponding comp rule. 
*)

Definition IA := {i:I & A i}.

Definition B' (ia : IA) : Type := 
  match ia with (existT i a) => B i a end.

Definition crude_terms : Type := W IA B'.

Definition fst (ia : IA) := 
  match ia with (existT i _) => i end.

Definition snd (ia : IA) : A (fst ia) := 
  match ia with (existT i a) => a end.

Definition s' {ia : IA} : B' ia -> I :=
  match ia with (existT i a) => @s i a end.

Definition type_of (t : crude_terms) : I :=
  match t with (w_intro ia _) => fst ia end.
 
Open Scope type_scope.

Fixpoint is_good (t : crude_terms) : I -> Type :=
  fun i =>
  match t with (w_intro ia f) => 
    (match ia with (existT j a) => j == i end)
     *
    (forall (b:B' ia), is_good (f b) (s' b))
  end.

Definition new_dep_W (i:I) : Type :=
  {t : crude_terms & is_good t i }.

(* I hate doing this, but it’s handy in places: *)
Definition ndW_pair {i:I} (t:crude_terms) (t_good : is_good t i) : new_dep_W i.
Proof.  apply (existT _ t); auto.
Defined.

Definition undlg_term {i:I} (t:new_dep_W i) : crude_terms := 
  match t with (existT t' _) => t' end.

Definition new_dep_w_intro (i : I) (a : A i)
                     (f : forall b : B i a, new_dep_W (s b))
                   : new_dep_W i.
Proof.
  unfold new_dep_W.
  unfold crude_terms.
  exists (w_intro IA B' (existT (fun i => A i) i a) (fun b => (undlg_term (f b)))).  simpl.  split.
  (* show this term has appropriate type *)
    apply idpath.
  (* show the subterms are good *)
  intro b.  destruct (f b) as [t t_good].
  simpl.  auto.
Defined.

Definition new_dep_w_intro' (i : I) (a : A i)
                     (f : forall b : B i a, new_dep_W (s b))
                   : new_dep_W i
:=
  existT
    (fun t : W IA B' =>  is_good t i)
    (w_intro IA B' (existT (fun i0 : I => A i0) i a)
             (fun b : B' (existT (fun i0 : I => A i0) i a)
                      => undlg_term (f b)))
    ( (idpath _)
    , (fun b : B' (existT (fun i0 : I => A i0) i a) =>
        match (f b) 
          as fb return ((fun t : crude_terms => is_good t (s' b)) (undlg_term fb))
        with
          (existT t t_good) => t_good
        end)).
(* A by-hand alternative definition to give a slightly cleaner term. *)

Theorem new_dep_W_rect
  (P : forall i : I, new_dep_W i -> Type)
  (H_rect : forall (i : I) (a : A i)
                   (f : forall b : B i a, new_dep_W (s b)),
                   (forall b : B i a, P (s b) (f b))
                 -> P i (new_dep_w_intro i a f))
  (i : I) (d : new_dep_W i)
  : P i d.
Proof.
  destruct d as [t t_good].
  generalize dependent i.
  induction t as [[i a] f' H'].  simpl in *.
  intros i' [i_eq_i' f'_good].
  destruct i_eq_i' as [i].
  (* The following step is the main subtlety: we need, sooner or later, to eta-expand [f'] and [f'_good] in the conclusion, since [H_rect] only proves [P] for terms of the form [new_dep_w_intro i a f], i.e. of the form [ndW_pair (w_intro a f) f_good] where f, f_good are both eta-expanded. *)
  eta_expand f'.  intro H'.  eta_intro f'_good.
  set (f := fun (b :B i a) => ndW_pair (f' b) (f'_good b)).
  apply (H_rect i a f).  clear H_rect.
  subst f. simpl.  intro b.
  apply H'.
  (* Finally, need to justify eta-expansion. *)
  apply @eta.
Defined.

Theorem new_dep_W_comp
    (P : forall i : I, new_dep_W i -> Type)
    (H_rect : forall (i : I) (a : A i)
                     (g : forall b : B i a, new_dep_W (s b)),
                     (forall b : B i a, P (s b) (g b))
                   -> P i (new_dep_w_intro i a g))
    (i : I) (a : A i) (g : forall b : B i a, new_dep_W (s b))
  : new_dep_W_rect P H_rect i (new_dep_w_intro i a g) 
  == H_rect i a g (fun b => (new_dep_W_rect P H_rect (s b) (g b))).
Proof.
  (* First we show it just in the case where [g] is a lambda-term whose values are pairs.  (If [eta_comp] held on the nose, then so would this case of [new_dep_W_comp].) *)
  set (g' := (fun b : B i a =>
     @ndW_pair (s b) (undlg_term (g b))
       (let (t, t_good) as s0 return (is_good (undlg_term s0) (s b)) :=
            g b in
        t_good))).
  assert (new_dep_W_rect P H_rect i (new_dep_w_intro i a g') ==
   H_rect i a g' (fun b : B i a => new_dep_W_rect P H_rect (s b) (g' b))).
  simpl.
  unfold transport.  simpl paths_rect.  unfold paths_rect.  simpl.
  unfold eq_rect_r.  simpl.  (* Large term rewriting… *)
  path_simplify' eta_comp.
  rewrite eta_comp.  simpl.  (*        …goes…         *)
  rewrite eta_comp.  simpl.  (*       …slowly!        *)
  apply idpath.

  replace g with (fun b : B i a =>
     @ndW_pair (s b) (undlg_term (g b))
       (let (t, t_good) as s0 return (is_good (undlg_term s0) (s b)) :=
            g b in
        t_good)).
  simpl.
  unfold eq_rect_r.  simpl.  (* Large term rewriting… *)
  rewrite eta_comp.  simpl.  (*        …goes…         *)
  rewrite eta_comp.  simpl.  (*       …slowly!        *)
  apply idpath.
  (* Now, by functional extensionality, arbitrary [g] is propositionally equal to one of the canonical form assumed above.  Note that this is our *only* direct use of [funext]; up to here, we only used [eta_exp] and [eta_comp]. *)
  apply funext.  intro b.
  destruct (g b); apply idpath.
Defined.

End dep_W_from_W.
