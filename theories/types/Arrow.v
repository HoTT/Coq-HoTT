(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Non-dependent function types *)

Require Import Overture PathGroupoids Contractible Equivalences Trunc.
Require Import Paths Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B C D f g n.

Section AssumeFunext.
Context `{Funext}.

(** *** Paths *)

(** As for dependent functions, paths [p : f = g] in a function type [A -> B] are equivalent to functions taking values in path types, [H : forall x:A, f x = g x], or concisely [H : f == g].  These are all given in the [Overture], but we can give them separate names for clarity in the non-dependent case. *)

Definition path_arrow {A B : Type} (f g : A -> B)
  : (f == g) -> (f = g)
  := path_forall f g.

Definition ap10_path_arrow {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_arrow f g h) = h
  := apD10_path_forall f g h.

Definition eta_path_arrow {A B : Type} (f g : A -> B) (p : f = g)
  : path_arrow f g (ap10 p) = p
  := eta_path_forall f g p.

Definition path_arrow_1 {A B : Type} (f : A -> B)
  : (path_arrow f f (fun x => 1)) = 1
  := eta_path_arrow f f 1.

Instance isequiv_path_arrow {A B : Type} (f g : A -> B)
  : IsEquiv (path_arrow f g)
  := isequiv_path_forall f g.

Definition equiv_path_arrow {A B : Type} (f g : A -> B)
  : (f == g) <~> (f = g)
  := equiv_path_forall f g.

(** *** Transport *)

(** Transporting in non-dependent function types is somewhat simpler than in dependent ones. *)

Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (p^ # y)).
Proof.
  destruct p; simpl; auto.
Defined.


(** *** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". *)

Definition dpath_arrow `{Funext}
  {A:Type} (B C : A -> Type) (x1 x2:A) (p:x1=x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  : (forall (y1:B x1), transport C p (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => B x -> C x) p f = g).
Proof.
  destruct p.
  apply equiv_path_arrow.
Defined.


(** *** Functorial action *)

Definition functor_arrow `(f : B -> A) `(g : C -> D)
  : (A -> C) -> (B -> D)
  := @functor_forall A (fun _ => C) B (fun _ => D) f (fun _ => g).

Definition ap_functor_arrow `(f : B -> A) `(g : C -> D)
  (h h' : A -> C) (p : h == h')
  : ap (functor_arrow f g) (path_arrow _ _ p)
  = path_arrow _ _ (fun b => ap g (p (f b)))
  := @ap_functor_forall _ A (fun _ => C) B (fun _ => D)
  f (fun _ => g) h h' p.

(** *** Equivalences *)

Instance isequiv_functor_arrow `{IsEquiv B A f} `{IsEquiv C D g}
  : IsEquiv (functor_arrow f g)
  := @isequiv_functor_forall _ A (fun _ => C) B (fun _ => D)
     _ _ _ _.

Definition equiv_functor_arrow `{IsEquiv B A f} `{IsEquiv C D g}
  : (A -> C) <~> (B -> D)
  := @equiv_functor_forall _ A (fun _ => C) B (fun _ => D)
  f _ (fun _ => g) _.

Definition equiv_functor_arrow' `(f : B <~> A) `(g : C <~> D)
  : (A -> C) <~> (B -> D)
  := @equiv_functor_forall' _ A (fun _ => C) B (fun _ => D)
  f (fun _ => g).
  
(** What remains is really identical to that in [Forall].  *)

End AssumeFunext.
