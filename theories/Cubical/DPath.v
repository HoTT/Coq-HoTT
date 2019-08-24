Require Import Basics.
Require Import Types.

Declare Scope dpath_scope.
Delimit Scope dpath_scope with dpath.

Local Open Scope dpath_scope.

Definition DPath {A} (P : A -> Type) {a0 a1} (p : a0 = a1)
  (b0 : P a0) (b1 : P a1) : Type.
Proof.
  destruct p.
  exact (b0 = b1).
Defined.

(* This allows DPaths to collapse to paths under cbn *)
Arguments DPath _ / _ _ _ : simpl nomatch.

(* Here is an alternative definition of DPath, for now the original suffices *)
(* Definition DPath {A} (P : A -> Type) {a0 a1} (p : a0 = a1)
  (b0 : P a0) (b1 : P a1) := transport P p b0 = b1.  *)

(* We can prove they are equivalent anyway *)
Definition dp_path_transport {A P} {a0 a1 : A} {p : a0 = a1} {b0 b1}
  : transport P p b0 = b1 -> DPath P p b0 b1.
Proof.
  by destruct p.
Defined.

Global Instance isequiv_dp_path_transport {A} (P : A -> Type) {a0 a1}
  (p : a0 = a1) (b0 : P a0) (b1 : P a1)
  : IsEquiv (@dp_path_transport A P a0 a1 p b0 b1).
Proof.
  serapply isequiv_adjointify; by destruct p.
Defined.

(* Here is a notation for DPaths that can make it easier to use *)
Notation "x =[ q ] y" := (DPath (fun t => DPath _ t _ _) q x y) (at level 10)
  : dpath_scope.

(* We have reflexivity for DPaths, this helps coq guess later *)
Definition dp_id {A} {P : A -> Type} {a : A} {x : P a} : DPath P 1 x x := 1%path.

(* Althought 1%dpath is definitionally 1%path, coq cannot guess this so it helps
   to have 1 be a dpath before hand. *)
Notation "1" := dp_id : dpath_scope.

(* DPath induction *)
Definition DPath_ind (A : Type) (P : A -> Type) (P0 : forall (a0 a1 : A)
  (p : a0 = a1) (b0 : P a0) (b1 : P a1), DPath P p b0 b1 -> Type)
  : (forall (x : A) (y : P x), P0 x x 1%path y y 1) ->
    forall (a0 a1 : A) (p : a0 = a1) (b0 : P a0) (b1 : P a1)
    (d : DPath P p b0 b1), P0 a0 a1 p b0 b1 d.
Proof.
  intros X a0 a1 [] b0 b1 []; apply X.
Defined.

(* DPath version of apD *)
Definition dp_apD {A P} (f : forall a, P a) {a0 a1 : A}
  (p : a0 = a1) : DPath P p (f a0) (f a1).
Proof.
  by destruct p.
Defined.

(* A DPath over a constant family is just a path *)
Definition dp_const {A C} {a0 a1 : A} {p : a0 = a1} {x y}
  : (x = y) -> DPath (fun _ => C) p x y.
Proof.
  by destruct p.
Defined.

Global Instance isequiv_dp_const {A C} {a0 a1 : A} {p : a0 = a1} {x y}
  : IsEquiv (@dp_const _ C _ _ p x y).
Proof.
  destruct p; exact _.
Defined.

(* dp_apD of a non-dependent map is just a constant DPath *)
Definition dp_apD_const {A B} (f : A -> B) {a0 a1 : A}
  (p : a0 = a1) : dp_apD f p = dp_const (ap f p).
Proof.
  by destruct p.
Defined.

(* An alternate version useful for proving recursion computation rules from induction ones *)
Definition dp_apD_const' {A B : Type} {f : A -> B} {a0 a1 : A}
  {p : a0 = a1} : dp_const^-1 (dp_apD f p) = ap f p.
Proof.
  apply moveR_equiv_V.
  apply dp_apD_const.
Defined.

(* Concatenation of dependent paths *)
Definition dp_concat {A} {P : A -> Type} {a0 a1 a2}
  {p : a0 = a1} {q : a1 = a2} {b0 : P a0} {b1 : P a1} {b2 : P a2}
  : DPath P p b0 b1 -> DPath P q b1 b2 -> DPath P (p @ q) b0 b2.
Proof.
  destruct p, q.
  exact concat.
Defined.

(* TODO: Is level correct? *)
Notation "x '@D' y" := (dp_concat x y) (at level 10) : dpath_scope.

(* Inverse of dependent paths *)
Definition dp_inverse {A} {P : A -> Type} {a0 a1} {p : a0 = a1}
  {b0 : P a0} {b1 : P a1} : DPath P p b0 b1 -> DPath P p^ b1 b0.
Proof.
  destruct p.
  exact inverse.
Defined.

(* TODO: Is level correct? *)
Notation "x '^D'" := (dp_inverse x) (at level 20) : dpath_scope.

(* dp_apD distributes over concatenation *)
Definition dp_apD_pp (A : Type) (P : A -> Type) (f : forall a, P a)
  {a0 a1 a2 : A} (p : a0 = a1) (q : a1 = a2)
  : dp_apD f (p @ q) = (dp_apD f p) @D (dp_apD f q).
Proof.
  by destruct p, q.
Defined.

(* dp_apD respects inverses *)
Definition dp_apD_V (A : Type) (P : A -> Type) (f : forall a, P a)
  {a0 a1 : A} (p : a0 = a1) : dp_apD f p^ = (dp_apD f p)^D.
Proof.
  by destruct p.
Defined.

(* dp_const preserves concatenation *)
Definition dp_const_pp {A B : Type} {a0 a1 a2 : A}
  {p : a0 = a1} {q : a1 = a2} {x y z : B} (r : x = y) (s : y = z)
  : dp_const (p:=p @ q) (r @ s) = (dp_const (p:=p) r) @D (dp_const (p:=q) s).
Proof.
  by destruct p,q.
Defined.

Section DGroupoid.

  Context {A} {P : A -> Type} {a0 a1} {p : a0 = a1}
    {b0 : P a0} {b1 : P a1} {dp : DPath P p b0 b1}.

  Definition dp_concat_p1 : (dp @D 1) =[concat_p1 _] dp.
  Proof.
    destruct p.
    apply concat_p1.
  Defined.

  Definition dp_concat_1p : (1 @D dp) =[concat_1p _] dp.
  Proof.
    destruct p.
    apply concat_1p.
  Defined.

  Definition dp_concat_Vp : dp^D @D dp =[concat_Vp _] 1.
  Proof.
    destruct p.
    apply concat_Vp.
  Defined.

  Definition dp_concat_pV : dp @D (dp^D) =[concat_pV _] 1.
  Proof.
    destruct p.
    apply concat_pV.
  Defined.

  Section Concat.

    Context {a2 a3} {q : a1 = a2} {r : a2 = a3}
       {b2 : P a2} {b3 : P a3}
       (dq : DPath P q b1 b2) (dr : DPath P  r b2 b3).

    Definition dp_concat_pp_p
      : ((dp @D dq) @D dr) =[concat_pp_p _ _ _] (dp @D (dq @D dr)).
    Proof.
      destruct p, q, r.
      apply concat_pp_p.
    Defined.

    Definition dp_concat_p_pp
      : (dp @D (dq @D dr)) =[concat_p_pp _ _ _] ((dp @D dq) @D dr).
    Proof.
      destruct p, q, r.
      apply concat_p_pp.
    Defined.

  End Concat.

End DGroupoid.

(* Dependent paths over paths *)
(* These can be found under names such as dp_paths_l akin to transport_paths_l *)

Definition dp_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y) r
  : p^ @ q = r <~> DPath (fun x => x = y) p q r.
Proof.
  refine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_l.
Defined.

Definition dp_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1) r
  :  q @ p = r <~> DPath (fun y => x = y) p q r.
Proof.
  refine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_r.
Defined.

Definition dp_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1) r
  : (p^ @ q) @ p = r <~> DPath (fun x : A => x = x) p q r.
Proof.
  srefine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_lr.
Defined.

Definition dp_paths_Fl {A B} {f : A -> B} {x1 x2 : A} {y : B} (p : x1 = x2)
  (q : f x1 = y) r :  (ap f p)^ @ q = r <~> DPath (fun x => f x = y) p q r.
Proof.
  srefine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_Fl.
Defined.

Definition dp_paths_Fr {A B} {g : A -> B} {y1 y2 : A} {x : B} (p : y1 = y2)
  (q : x = g y1) r :  q @ ap g p = r <~> DPath (fun y : A => x = g y) p q r.
Proof.
  srefine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_Fr.
Defined.

Definition dp_paths_FFlr {A B} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1) r
  : ((ap g (ap f p))^ @ q) @ p = r <~> DPath (fun x : A => g (f x) = x) p q r.
Proof.
  refine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_FFlr.
Defined.

Definition dp_paths_FlFr {A B} {f g : A -> B} {x1 x2 : A} (p : x1 = x2)
  (q : f x1 = g x1) r
  : ((ap f p)^ @ q) @ ap g p = r <~> DPath (fun x : A => f x = g x) p q r.
Proof.
  srefine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_FlFr.
Defined.

Definition dp_paths_lFFr {A B} {f : A -> B} {g : B -> A} {x1 x2 : A} 
  (p : x1 = x2) (q : x1 = g (f x1)) r
  :  (p^ @ q) @ ap g (ap f p) = r <~> DPath (fun x : A => x = g (f x)) p q r.
Proof.
  srefine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_lFFr.
Defined.

Definition dp_paths_FlFr_D {A B} (f g : forall a : A, B a) 
  (x1 x2 : A) (p : x1 = x2) (q : f x1 = g x1) r
  : ((apD f p)^ @ ap (transport B p) q) @ apD g p = r
    <~> DPath (fun x : A => f x = g x) p q r.
Proof.
  srefine (equiv_composeR' _ (BuildEquiv _ _ dp_path_transport _)).
  apply equiv_concat_l, transport_paths_FlFr_D.
Defined.

Definition dp_compose {A B} (f : A -> B) (P : B -> Type) {x y : A}
  (p : x = y) (u : P (f x)) (v : P (f y))
  : DPath P (ap f p) u v <~> DPath (fun x => P (f x)) p u v.
Proof.
  by destruct p.
Defined.

(* Type constructors *)

(* Many of these lemmas exist already for transports but we prove them for
   DPaths anyway. If we change the definition of DPath to the transport,
   then these will no longer be needed. It is however, far more readable
   to keep such lemmas seperate, since it is difficult to otherwise search
   for a DPath lemma if they are all written using transports. *)

(* DPath over an arrow type *)
Definition dp_arrow `{Funext} {A} (B C : A -> Type) {x1 x2 : A} (p : x1 = x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  : (forall y1, DPath C p (f y1) (g (p # y1)))
    <~> DPath (fun x => B x -> C x) p f g.
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.

Definition path_sigma_dp {A P} {x x' : A} {y : P x} {y' : P x'}
  (p : x = x') (q : DPath P p y y') : (x; y) = (x'; y').
Proof.
  by destruct p, q.
Defined.

(* DPath over a forall *)
Definition dp_forall `{Funext} {A : Type} {B : A -> Type} {C : sig B -> Type}
  {a1 a2 : A} {p : a1 = a2} {f : forall x, C (a1; x)} {g : forall x, C (a2; x)}
  : DPath (fun a => forall x, C (a; x)) p f g
  <~> forall (x : B a1) (y : B a2) (q : DPath B p x y),
    DPath C (path_sigma_dp p q) (f x) (g y).
Proof.
  destruct p; cbn.
  refine (equiv_compose' _ (equiv_apD10 _ _ _)).
  apply equiv_functor_forall_id.
  intro a.
  serapply equiv_adjointify.
  + by intros ? ? [].
  + intro F; exact (F a 1).
  + repeat (intro; apply path_forall).
    by intros [].
  + by intro.
Defined.

(* Restricted version allowing us to pull the domain of a forall out *)
Definition dp_forall_domain `{Funext} {D : Type} {A : Type} {B : D -> A -> Type}
  {t1 t2 : D} {d : t1 = t2} {f : forall x, B t1 x} {g : forall x, B t2 x}
  : (forall x, DPath (fun t => B t x) d (f x) (g x))
   <~> DPath (fun t => forall x, B t x) d f g.
Proof.
  destruct d.
  apply equiv_path_forall.
Defined.

(* Useful for turning computation rules of HITs written with transports to
   ones written with DPaths. *)
Definition dp_apD_path_transport {A P} (f : forall a : A, P a)
  {a0 a1 : A} (p : a0 = a1) l
  : apD f p = dp_path_transport^-1 l -> dp_apD f p = l.
Proof.
  by destruct p.
Defined.

