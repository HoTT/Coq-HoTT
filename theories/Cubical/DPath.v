From HoTT Require Import Basics.
Require Import Types.Paths Types.Sigma Types.Forall.

Declare Scope dpath_scope.
Delimit Scope dpath_scope with dpath.

Local Open Scope dpath_scope.

Definition DPath {A} (P : A -> Type) {a0 a1} (p : a0 = a1)
  (b0 : P a0) (b1 : P a1) : Type
  := transport P p b0 = b1.

(** This allows [DPath]s to collapse to paths under [cbn] *)
Arguments DPath _ / _ _ _ : simpl nomatch.

Instance istrunc_dp {A : Type} {P : A -> Type} {n : trunc_index}
 {a0 a1} {p : a0 = a1} {b0 : P a0} {b1 : P a1} `{IsTrunc n.+1 (P a0)}
  `{IsTrunc n.+1 (P a1)} : IsTrunc n (DPath P p b0 b1) := _.

Definition dp_ishprop {A : Type} (P : A -> Type) {a0 a1} {p : a0 = a1}
  {b0 : P a0} {b1 : P a1} `{IsHProp (P a0)} `{IsHProp (P a1)}
  : DPath P p b0 b1.
Proof.
  apply path_ishprop.
Defined.

(** We have reflexivity for [DPath]s, this helps Coq guess later *)
Definition dp_id {A} {P : A -> Type} {a : A} {x : P a} : DPath P 1 x x := 1%path.

(** Although [1%dpath] is definitionally [1%path], when [1%path] is used where a dependent path is expected, Coq sometimes has trouble interpreting this. So we make a custom notation for [1] in [dpath_scope]. *)
Notation "1" := dp_id : dpath_scope.

(** [DPath] induction *)
Definition DPath_ind (A : Type) (P : A -> Type) (P0 : forall (a0 a1 : A)
  (p : a0 = a1) (b0 : P a0) (b1 : P a1), DPath P p b0 b1 -> Type)
  : (forall (x : A) (y : P x), P0 x x 1%path y y 1) ->
    forall (a0 a1 : A) (p : a0 = a1) (b0 : P a0) (b1 : P a1)
    (d : DPath P p b0 b1), P0 a0 a1 p b0 b1 d.
Proof.
  intros X a0 a1 [] b0 b1 []; apply X.
Defined.

(** A [DPath] over a constant family is just a path *)
Definition equiv_dp_const {A C} {a0 a1 : A} {p : a0 = a1} {x y}
  : (x = y) <~> DPath (fun _ => C) p x y.
Proof.
  by destruct p.
Defined.

Notation dp_const := equiv_dp_const.

(** [dp_apD] of a non-dependent map is just a constant [DPath] *)
Definition dp_apD_const {A B} (f : A -> B) {a0 a1 : A}
  (p : a0 = a1) : apD f p = dp_const (ap f p).
Proof.
  by destruct p.
Defined.

(** An alternate version useful for proving recursion computation rules from induction ones *)
Definition dp_apD_const' {A B : Type} {f : A -> B} {a0 a1 : A}
  {p : a0 = a1} : dp_const^-1 (apD f p) = ap f p.
Proof.
  apply moveR_equiv_V.
  apply dp_apD_const.
Defined.

(** Concatenation of dependent paths *)
Definition dp_concat {A} {P : A -> Type} {a0 a1 a2}
  {p : a0 = a1} {q : a1 = a2} {b0 : P a0} {b1 : P a1} {b2 : P a2}
  : DPath P p b0 b1 -> DPath P q b1 b2 -> DPath P (p @ q) b0 b2.
Proof.
  destruct p, q.
  exact concat.
Defined.

Notation "x '@Dp' y" := (dp_concat x y) : dpath_scope.

(** Concatenation of dependent paths with non-dependent paths *)
Definition dp_concat_r {A} {P : A -> Type} {a0 a1}
  {p : a0 = a1} {b0 : P a0} {b1 b2 : P a1}
  : DPath P p b0 b1 -> (b1 = b2) -> DPath P p b0 b2.
Proof.
  destruct p; exact concat.
Defined.

Notation "x '@Dr' y" := (dp_concat_r x y) : dpath_scope.

Definition dp_concat_l {A} {P : A -> Type} {a1 a2}
  {q : a1 = a2} {b0 b1 : P a1} {b2 : P a2}
  : (b0 = b1) -> DPath P q b1 b2 -> DPath P q b0 b2.
Proof.
  destruct q; exact concat.
Defined.

Notation "x '@Dl' y" := (dp_concat_l x y) : dpath_scope.

(** Inverse of dependent paths *)
Definition dp_inverse {A} {P : A -> Type} {a0 a1} {p : a0 = a1}
  {b0 : P a0} {b1 : P a1} : DPath P p b0 b1 -> DPath P p^ b1 b0.
Proof.
  destruct p.
  exact inverse.
Defined.

Notation "x '^D'" := (dp_inverse x) : dpath_scope.

(** [dp_apD] distributes over concatenation *)
Definition dp_apD_pp (A : Type) (P : A -> Type) (f : forall a, P a)
  {a0 a1 a2 : A} (p : a0 = a1) (q : a1 = a2)
  : apD f (p @ q) = (apD f p) @Dp (apD f q).
Proof.
  by destruct p, q.
Defined.

(** [dp_apD] respects inverses *)
Definition dp_apD_V (A : Type) (P : A -> Type) (f : forall a, P a)
  {a0 a1 : A} (p : a0 = a1) : apD f p^ = (apD f p)^D.
Proof.
  by destruct p.
Defined.

(** [dp_const] preserves concatenation *)
Definition dp_const_pp {A B : Type} {a0 a1 a2 : A}
  {p : a0 = a1} {q : a1 = a2} {x y z : B} (r : x = y) (s : y = z)
  : dp_const (p:=p @ q) (r @ s) = (dp_const (p:=p) r) @Dp (dp_const (p:=q) s).
Proof.
  by destruct p,q.
Defined.

(** [dp_const] preserves inverses *) 
Definition dp_const_V {A B : Type} {a0 a1 : A} {p : a0 = a1} {x y : B} (r : x = y)
  : dp_const r^ = (dp_const (p:=p) r)^D.
Proof.
  by destruct p.
Defined. 

(** Horizontal composition and whiskering of dependent paths *)
Definition dp_concat2 {A} {P : A -> Type} {a0 a1 a2}
  {p : a0 = a1} {q : a1 = a2} {b0 : P a0} {b1 : P a1} {b2 : P a2}
  {r r' : DPath P p b0 b1} {s s' : DPath P q b1 b2}
  (h : r = r') (k : s = s')
  : r @Dp s = r' @Dp s'.
Proof.
  by destruct h, k.
Defined.

Definition dp_whiskerL {A: Type} {P : A -> Type} {a0 a1 a2 : A}
  {p : a0 = a1} {q : a1 = a2} {b0 : P a0} {b1 : P a1} {b2 : P a2}
  (r : DPath P p b0 b1) {s s' : DPath P q b1 b2} (h : s = s')
  : r @Dp s = r @Dp s'
  := dp_concat2 1 h.

Definition dp_whiskerR {A: Type} {P : A -> Type} {a0 a1 a2 : A}
  {p : a0 = a1} {q : a1 = a2} {b0 : P a0} {b1 : P a1} {b2 : P a2}
  {r r' : DPath P p b0 b1} (s : DPath P q b1 b2) (h : r = r')
  : r @Dp s = r' @Dp s
  := dp_concat2 h 1.

Section DGroupoid.

  Context {A} {P : A -> Type} {a0 a1} {p : a0 = a1}
    {b0 : P a0} {b1 : P a1} {dp : DPath P p b0 b1}.

  Definition dp_concat_p1
    : DPath (fun t : a0 = a1 => DPath P t b0 b1) (concat_p1 p) (dp @Dp 1) dp.
  Proof.
    destruct p.
    apply concat_p1.
  Defined.

  Definition dp_concat_1p
    : DPath (fun t : a0 = a1 => DPath P t b0 b1) (concat_1p p) (1 @Dp dp) dp.
  Proof.
    destruct p.
    apply concat_1p.
  Defined.

  Definition dp_concat_Vp
    : DPath (fun t : a1 = a1 => DPath P t b1 b1) (concat_Vp p) (dp^D @Dp dp) 1.
  Proof.
    destruct p.
    apply concat_Vp.
  Defined.

  Definition dp_concat_pV
    : DPath (fun t : a0 = a0 => DPath P t b0 b0) (concat_pV p) (dp @Dp dp^D) 1.
  Proof.
    destruct p.
    apply concat_pV.
  Defined.

  Section Concat.

    Context {a2 a3} {q : a1 = a2} {r : a2 = a3}
       {b2 : P a2} {b3 : P a3}
       (dq : DPath P q b1 b2) (dr : DPath P  r b2 b3).

    Definition dp_concat_pp_p
      : DPath (fun t : a0 = a3 => DPath P t b0 b3) (concat_pp_p p q r)
        ((dp @Dp dq) @Dp dr) (dp @Dp (dq @Dp dr)).
    Proof.
      destruct p, q, r.
      apply concat_pp_p.
    Defined.

    Definition dp_concat_p_pp
      : DPath (fun t : a0 = a3 => DPath P t b0 b3) (concat_p_pp p q r)
        (dp @Dp (dq @Dp dr)) ((dp @Dp dq) @Dp dr).
    Proof.
      destruct p, q, r.
      apply concat_p_pp.
    Defined.

  End Concat.

End DGroupoid.

(** Dependent paths over paths *)
(** These can be found under names such as [dp_paths_l] akin to [transport_paths_l] *)

Definition equiv_dp_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y) r
  : p^ @ q = r <~> DPath (fun x => x = y) p q r.
Proof.
  apply equiv_concat_l, transport_paths_l.
Defined.

Notation dp_paths_l := equiv_dp_paths_l.

Definition equiv_dp_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1) r
  :  q @ p = r <~> DPath (fun y => x = y) p q r.
Proof.
  apply equiv_concat_l, transport_paths_r.
Defined.

Notation dp_paths_r := equiv_dp_paths_r.

Definition equiv_dp_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1) r
  : (p^ @ q) @ p = r <~> DPath (fun x : A => x = x) p q r.
Proof.
  apply equiv_concat_l, transport_paths_lr.
Defined.

Notation dp_paths_lr := equiv_dp_paths_lr.

Definition equiv_dp_paths_Fl {A B} {f : A -> B} {x1 x2 : A} {y : B} (p : x1 = x2)
  (q : f x1 = y) r :  (ap f p)^ @ q = r <~> DPath (fun x => f x = y) p q r.
Proof.
  apply equiv_concat_l, transport_paths_Fl.
Defined.

Notation dp_paths_Fl := equiv_dp_paths_Fl.

Definition equiv_dp_paths_Fr {A B} {g : A -> B} {y1 y2 : A} {x : B} (p : y1 = y2)
  (q : x = g y1) r :  q @ ap g p = r <~> DPath (fun y : A => x = g y) p q r.
Proof.
  apply equiv_concat_l, transport_paths_Fr.
Defined.

Notation dp_paths_Fr := equiv_dp_paths_Fr.

Definition equiv_dp_paths_FFlr {A B} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1) r
  : ((ap g (ap f p))^ @ q) @ p = r <~> DPath (fun x : A => g (f x) = x) p q r.
Proof.
  apply equiv_concat_l, transport_paths_FFlr.
Defined.

Notation dp_paths_FFlr := equiv_dp_paths_FFlr.

Definition equiv_dp_paths_FlFr {A B} {f g : A -> B} {x1 x2 : A} (p : x1 = x2)
  (q : f x1 = g x1) r
  : ((ap f p)^ @ q) @ ap g p = r <~> DPath (fun x : A => f x = g x) p q r.
Proof.
  apply equiv_concat_l, transport_paths_FlFr.
Defined.

Notation dp_paths_FlFr := equiv_dp_paths_FlFr.

Definition equiv_dp_paths_lFFr {A B} {f : A -> B} {g : B -> A} {x1 x2 : A} 
  (p : x1 = x2) (q : x1 = g (f x1)) r
  :  (p^ @ q) @ ap g (ap f p) = r <~> DPath (fun x : A => x = g (f x)) p q r.
Proof.
  apply equiv_concat_l, transport_paths_lFFr.
Defined.

Notation dp_paths_lFFr := equiv_dp_paths_lFFr.

Definition equiv_dp_paths_FlFr_D {A B} (f g : forall a : A, B a) 
  {x1 x2 : A} (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  : ((apD f p)^ @ ap (transport B p) q) @ apD g p = r
    <~> DPath (fun x : A => f x = g x) p q r.
Proof.
  apply equiv_concat_l, transport_paths_FlFr_D.
Defined.

Notation dp_paths_FlFr_D := equiv_dp_paths_FlFr_D.

Definition equiv_dp_compose' {A B} (f : A -> B) (P : B -> Type) {x y : A}
  {p : x = y} {q : f x = f y} (r : ap f p = q) {u : P (f x)} {v : P (f y)}
  : DPath (fun x => P (f x)) p u v <~> DPath P q u v.
Proof.
  by destruct r, p.
Defined.

Notation dp_compose' := equiv_dp_compose'.

Definition equiv_dp_compose {A B} (f : A -> B) (P : B -> Type) {x y : A}
  (p : x = y) {u : P (f x)} {v : P (f y)}
  : DPath (fun x => P (f x)) p u v <~> DPath P (ap f p) u v
  := dp_compose' f P (idpath (ap f p)).

Notation dp_compose := equiv_dp_compose.

Definition dp_apD_compose' {A B : Type} (f : A -> B) (P : B -> Type)
           {x y : A} {p : x = y} {q : f x = f y} (r : ap f p = q) (g : forall b:B, P b)
  : apD (g o f) p = (dp_compose' f P r)^-1 (apD g q).
Proof.
  by destruct r, p.
Defined.

Definition dp_apD_compose {A B : Type} (f : A -> B) (P : B -> Type)
           {x y : A} (p : x = y) (g : forall b:B, P b)
  : apD (g o f) p = (dp_compose f P p)^-1 (apD g (ap f p))
  := dp_apD_compose' f P (idpath (ap f p)) g.

Definition dp_apD_compose_inv' {A B : Type} (f : A -> B) (P : B -> Type)
  {x y : A} {p : x = y} {q : f x = f y} (r : ap f p = q) (g : forall b:B, P b)
  : apD g q = (dp_compose' f P r) (apD (g o f) p).
Proof.
  by destruct r, p.
Defined.

Definition dp_apD_compose_inv {A B : Type} (f : A -> B) (P : B -> Type)
  {x y : A} {p : x = y} (g : forall b:B, P b)
  : apD g (ap f p) = (dp_compose f P p) (apD (g o f) p)
  := dp_apD_compose_inv' f P (idpath (ap f p)) g.

(** Type constructors *)

(** Many of these lemmas exist already for transports but we prove them for
   [DPath]s anyway. If we change the definition of [DPath] to the transport,
   then these will no longer be needed. It is however, far more readable
   to keep such lemmas separate, since it is difficult to otherwise search
   for a [DPath] lemma if they are all written using transports. *)

(** A version of [equiv_path_sigma] for [DPath]s *)
Definition equiv_path_sigma_dp {A P} {x x' : A} {y : P x} {y' : P x'}
  : {p : x = x' & DPath P p y y'} <~> (x; y) = (x'; y')
  := equiv_path_sigma P (x; y) (x'; y').

Notation path_sigma_dp := equiv_path_sigma_dp.

Definition ap_pr1_path_sigma_dp {A : Type} {P : A -> Type}
  {x x' : A} {y : P x} {y' : P x'} (p : x = x') (q : DPath P p y y')
  : ap pr1 (path_sigma_dp (p; q)) = p.
Proof.
  apply ap_pr1_path_sigma.
Defined.

(* [DPath] over a forall *)
Definition equiv_dp_forall `{Funext} {A : Type} {B : A -> Type} {C : sig B -> Type}
  {a1 a2 : A} {p : a1 = a2} {f : forall x, C (a1; x)} {g : forall x, C (a2; x)}
  : (forall (x : B a1) (y : B a2) (q : DPath B p x y),
    DPath C (path_sigma_dp (p; q)) (f x) (g y))
    <~> DPath (fun a => forall x, C (a; x)) p f g.
Proof.
  symmetry.
  destruct p; cbn.
  refine (equiv_compose' _ (equiv_apD10 _ _ _)).
  apply equiv_functor_forall_id.
  intro a.
  srapply equiv_adjointify.
  + by intros ? ? [].
  + intro F; exact (F a 1).
  + repeat (intro; apply path_forall).
    by intros [].
  + by intro.
Defined.

Notation dp_forall := equiv_dp_forall.

(* [DPath] over an arrow *)
Definition equiv_dp_arrow `{Funext} {A : Type} {B C : A -> Type}
  {a1 a2 : A} {p : a1 = a2} {f :  B a1 -> C a1} {g : B a2 -> C a2}
  : (forall x, DPath C p (f x) (g (p # x)))
    <~> DPath (fun x => B x -> C x) p f g.
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.

Notation dp_arrow := equiv_dp_arrow.

(* Restricted version allowing us to pull the domain of a forall out *)
Definition equiv_dp_forall_domain `{Funext} {D : Type} {A : Type} {B : D -> A -> Type}
  {t1 t2 : D} {d : t1 = t2} {f : forall x, B t1 x} {g : forall x, B t2 x}
  : (forall x, DPath (fun t => B t x) d (f x) (g x))
   <~> DPath (fun t => forall x, B t x) d f g.
Proof.
  destruct d.
  apply equiv_path_forall.
Defined.

Notation dp_forall_domain := equiv_dp_forall_domain.

Definition equiv_dp_sigma {A : Type} {B : A -> Type}
  {C : sig B -> Type} {x1 x2 : A} {p : x1 = x2}
  (y1 : { y : B x1 & C (x1; y) }) (y2 : { y : B x2 & C (x2; y) })
  : {n : DPath B p y1.1 y2.1 & DPath C (path_sigma_dp (p; n)) y1.2 y2.2}
    <~> DPath (fun x => { y : B x & C (x; y) }) p y1 y2.
Proof.
  destruct p.
  refine (path_sigma_dp oE _).
  apply equiv_functor_sigma_id.
  cbn; intro q.
  destruct y1 as [y11 y12], y2 as [y21 y22].
  cbn in *.
  by destruct q.
Defined.

Notation dp_sigma := equiv_dp_sigma.
