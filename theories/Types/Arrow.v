(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Non-dependent function types *)

Require Import HoTT.Basics.
Require Import Types.Paths Types.Forall.
Local Open Scope path_scope.


Generalizable Variables A B C D f g n.

Section AssumeFunext.
Context `{Funext}.

(** ** Paths *)

(** As for dependent functions, paths [p : f = g] in a function type [A -> B] are equivalent to functions taking values in path types, [H : forall x:A, f x = g x], or concisely [H : f == g].  These are all given in the [Overture], but we can give them separate names for clarity in the non-dependent case. *)

Definition path_arrow {A B : Type} (f g : A -> B)
  : (f == g) -> (f = g)
  := path_forall f g.

(** There are a number of combinations of dependent and non-dependent for [apD10_path_forall]; we list all of the combinations as helpful lemmas for rewriting. *)
Definition ap10_path_arrow {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_arrow f g h) == h
  := apD10_path_forall f g h.

Definition apD10_path_arrow {A B : Type} (f g : A -> B) (h : f == g)
  : apD10 (path_arrow f g h) == h
  := apD10_path_forall f g h.

Definition ap10_path_forall {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_forall f g h) == h
  := apD10_path_forall f g h.

Definition eta_path_arrow {A B : Type} (f g : A -> B) (p : f = g)
  : path_arrow f g (ap10 p) = p
  := eta_path_forall f g p.

Definition path_arrow_1 {A B : Type} (f : A -> B)
  : (path_arrow f f (fun x => 1)) = 1
  := eta_path_arrow f f 1.

Definition equiv_ap10 `{Funext} {A B : Type} f g
: (f = g) <~> (f == g)
  := Build_Equiv _ _ (@ap10 A B f g) _.

Global Instance isequiv_path_arrow {A B : Type} (f g : A -> B)
  : IsEquiv (path_arrow f g) | 0
  := isequiv_path_forall f g.

Definition equiv_path_arrow {A B : Type} (f g : A -> B)
  : (f == g) <~> (f = g)
  := equiv_path_forall f g.

(** ** Path algebra *)

Definition path_arrow_pp {A B : Type} (f g h : A -> B)
           (p : f == g) (q : g == h)
: path_arrow f h (fun x => p x @ q x) = path_arrow f g p @ path_arrow g h q
:= path_forall_pp f g h p q.

(** ** Transport *)

(** Transporting in non-dependent function types is somewhat simpler than in dependent ones. *)

Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (p^ # y)).
Proof.
  destruct p; simpl; auto.
Defined.

Definition transport_arrow_toconst {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C) (y : B x2)
  : (transport (fun x => B x -> C) p f) y  =  f (p^ # y).
Proof.
  destruct p; simpl; auto.
Defined.

Definition transport_arrow_fromconst {A B : Type} {C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B -> C x1) (y : B)
  : (transport (fun x => B -> C x) p f) y  =  p # (f y).
Proof.
  destruct p; simpl; auto.
Defined.

(** And some naturality and coherence for these laws. *)

Definition ap_transport_arrow_toconst {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C) {y1 y2 : B x2} (q : y1 = y2)
  : ap (transport (fun x => B x -> C) p f) q
    @ transport_arrow_toconst p f y2
    = transport_arrow_toconst p f y1
    @ ap (fun y => f (p^ # y)) q.
Proof.
  destruct p, q; reflexivity.
Defined.


(** ** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". *)

Definition dpath_arrow
  {A:Type} (B C : A -> Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  : (forall (y1:B x1), transport C p (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => B x -> C x) p f = g).
Proof.
  destruct p.
  apply equiv_path_arrow.
Defined.

Definition ap10_dpath_arrow
  {A:Type} (B C : A -> Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  (h : forall (y1:B x1), transport C p (f y1) = g (transport B p y1))
  (u : B x1)
  : ap10 (dpath_arrow B C p f g h) (p # u)
  = transport_arrow p f (p # u)
  @ ap (fun x => p # (f x)) (transport_Vp B p u)
  @ h u.
Proof.
  destruct p; simpl; unfold ap10.
  exact (apD10_path_forall f g h u @ (concat_1p _)^).
Defined.

(** ** Maps on paths *)

(** The action of maps given by application. *)
Definition ap_apply_l {A B : Type} {x y : A -> B} (p : x = y) (z : A) :
  ap (fun f => f z) p = ap10 p z
:= 1.

Definition ap_apply_Fl {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) (z : B) :
  ap (fun a => (M a) z) p = ap10 (ap M p) z
:= match p with 1 => 1 end.

Definition ap_apply_Fr {A B C : Type} {x y : A} (p : x = y) (z : B -> C) (N : A -> B) :
  ap (fun a => z (N a)) p = ap01 z (ap N p)
:= (ap_compose N _ _).

Definition ap_apply_FlFr {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) (N : A -> B) :
  ap (fun a => (M a) (N a)) p = ap11 (ap M p) (ap N p)
:= match p with 1 => 1 end.

(** The action of maps given by lambda. *)
Definition ap_lambda {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) :
  ap (fun a b => M a b) p =
  path_arrow _ _ (fun b => ap (fun a => M a b) p).
Proof.
  destruct p;
  symmetry;
  simpl; apply path_arrow_1.
Defined.

(** ** Functorial action *)

Definition functor_arrow `(f : B -> A) `(g : C -> D)
  : (A -> C) -> (B -> D)
  := @functor_forall A (fun _ => C) B (fun _ => D) f (fun _ => g).

Definition not_contrapositive `(f : B -> A)
  : not A -> not B
  := functor_arrow f idmap.

Definition ap_functor_arrow `(f : B -> A) `(g : C -> D)
  (h h' : A -> C) (p : h == h')
  : ap (functor_arrow f g) (path_arrow _ _ p)
  = path_arrow _ _ (fun b => ap g (p (f b)))
  := @ap_functor_forall _ A (fun _ => C) B (fun _ => D)
  f (fun _ => g) h h' p.

(** ** Truncatedness: functions into an n-type is an n-type *)

Global Instance contr_arrow {A B : Type} `{Contr B}
  : Contr (A -> B) | 100
:= contr_forall.

Global Instance trunc_arrow {A B : Type} `{IsTrunc n B}
  : IsTrunc n (A -> B) | 100
:= trunc_forall.

(** ** Equivalences *)

Global Instance isequiv_functor_arrow `{IsEquiv B A f} `{IsEquiv C D g}
  : IsEquiv (functor_arrow f g) | 1000
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

(* We could do something like this notation, but it's not clear that it would be that useful, and might be confusing. *)
(* Notation "f -> g" := (equiv_functor_arrow' f g) : equiv_scope. *)

(** What remains is really identical to that in [Forall].  *)

End AssumeFunext.

(** ** Decidability *)

(** This doesn't require funext *)
Global Instance decidable_arrow {A B : Type}
       `{Decidable A} `{Decidable B}
: Decidable (A -> B).
Proof.
  destruct (dec B) as [x2|y2].
  - exact (inl (fun _ => x2)).
  - destruct (dec A) as [x1|y1].
    + apply inr; intros f.
      exact (y2 (f x1)).
    + apply inl; intros x1.
      elim (y1 x1).
Defined.
