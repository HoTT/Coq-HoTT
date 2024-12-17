(** * Theorems about dependent products *)

Require Import Basics.Overture Basics.Equivalences Basics.PathGroupoids
               Basics.Tactics Basics.Contractible Basics.Iff.

Require Export Basics.Trunc (istrunc_forall).

Local Open Scope path_scope.


Generalizable Variables A B C f g e n.

Section AssumeFunext.
Context `{Funext}.

(** ** Paths *)

(** Paths [p : f = g] in a function type [forall x:X, P x] are equivalent to functions taking values in path types, [H : forall x:X, f x = g x], or concisely, [H : f == g].

This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in the [Overture]:  *)

(** Now we show how these things compute. *)

Definition apD10_path_forall `{P : A -> Type}
  (f g : forall x, P x) (h : f == g)
  : apD10 (path_forall _ _ h) == h
  := apD10 (eisretr apD10 h).

Definition eta_path_forall `{P : A -> Type}
  (f g : forall x, P x) (p : f = g)
  : path_forall _ _ (apD10 p) = p
  := eissect apD10 p.

Definition path_forall_1 `{P : A -> Type} (f : forall x, P x)
  : (path_forall f f (fun x => 1)) = 1
  := eta_path_forall f f 1.

(** The identification of the path space of a dependent function space, up to equivalence, is of course just funext. *)

Definition equiv_apD10 {A : Type} (P : A -> Type) f g
: (f = g) <~> (f == g)
  := Build_Equiv _ _ (@apD10 A P f g) _.

Global Instance isequiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : IsEquiv (path_forall f g) | 0
  := @isequiv_inverse _ _ (@apD10 A P f g) _.

Definition equiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : (f == g)  <~>  (f = g)
  := Build_Equiv _ _ (path_forall f g) _.

Global Arguments equiv_path_forall {A%_type_scope P} (f g)%_function_scope.

(** ** Path algebra *)

Definition path_forall_pp `{P : A -> Type} (f g h : forall x, P x)
           (p : f == g) (q : g == h)
: path_forall f h (fun x => p x @ q x) = path_forall f g p @ path_forall g h q.
Proof.
  revert p q.
  equiv_intro (@apD10 A P f g) p.
  equiv_intro (@apD10 A P g h) q.
  transitivity (path_forall f h (apD10 (p @ q))).
  - apply ap, path_forall; intros x.
    symmetry; apply apD10_pp.
  - refine (eta_path_forall _ _ _ @ _).
    apply concat2; symmetry; apply eta_path_forall.
Defined.


Definition path_forall_V `{P : A -> Type} (f g : forall x, P x)
           (p : f == g)
  : path_forall _ _ (fun x => (p x)^) = (path_forall _ _ p)^.
Proof.
  transitivity (path_forall _ _ (fun x => (apD10 (path_forall _ _ p) x)^)).
  - f_ap. symmetry. apply (@ap _ _ (fun h x => (h x)^)). apply eisretr.
  - transitivity (path_forall _ _ (apD10 (path_forall _ _ p)^)).
    + apply ap, inverse. apply path_forall; intros x. apply apD10_V.
    + apply eissect.
Defined.

(** ** Transport *)

(** The concrete description of transport in sigmas and pis is rather trickier than in the other types. In particular, these cannot be described just in terms of transport in simpler types; they require the full Id-elim rule by way of "dependent transport" [transportD].

  In particular this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory). A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)
Definition transport_forall
  {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y)
  : (transport (fun x => forall y : P x, C x y) p f)
    == (fun y =>
       transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p^ # y))))
  := match p with idpath => fun _ => 1 end.

(** A special case of [transport_forall] where the type [P] does not depend on [A],
    and so it is just a fixed type [B]. *)
Definition transport_forall_constant
  {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B, C x1 y)
  : (transport (fun x => forall y : B, C x y) p f)
    == (fun y => transport (fun x => C x y) p (f y))
  := match p with idpath => fun _ => 1 end.

Definition apD_transport_forall_constant
  {A B : Type} (C : A -> B -> Type)
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B, C x1 y)
  {y1 y2 : B} (q : y1 = y2)
: apD (transport (fun x => forall y : B, C x y) p f) q
  = ap (transport (C x2) q) (transport_forall_constant p f y1)
    @ transport_transport C p q (f y1)
    @ ap (transport (fun x : A => C x y2) p) (apD f q)
    @ (transport_forall_constant p f y2)^.
Proof.
  destruct p, q; reflexivity.
Defined.

(** ** Maps on paths *)

(** The action of maps given by application. *)
Definition ap_apply_lD {A} {B : A -> Type} {f g : forall x, B x} (p : f = g) (z : A)
  : ap (fun f => f z) p = apD10 p z
:= 1.

Definition ap_apply_lD2 {A} {B : A -> Type} { C : forall x, B x -> Type}
           {f g : forall x y, C x y} (p : f = g) (z1 : A) (z2 : B z1)
  : ap (fun f => f z1 z2) p = apD10 (apD10 p z1) z2.
Proof.
    by path_induction.
Defined.


(** The action of maps given by lambda. *)
Definition ap_lambdaD {A B : Type} {C : B -> Type} {x y : A} (p : x = y) (M : forall a b, C b)
  : ap (fun a b => M a b) p =
      path_forall _ _ (fun b => ap (fun a => M a b) p).
Proof.
  destruct p;
  symmetry;
  simpl; apply path_forall_1.
Defined.

(** The action of pre-composition on a path between dependent functions.  See also [ap10_ap_precompose] in PathGroupoids.v and [ap_precompose] in Arrow.v. *)
Definition ap_precomposeD {B P Q : Type}
  {f g : Q -> P} (h : f = g) (i : B -> Q)
  : ap (fun (k : Q -> P) => k o i) h
    = path_forall (f o i) (g o i) (ap10 h o i)
  := ap_lambdaD _ _.

(** ** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". *)

Definition dpath_forall
  {A:Type} (B:A -> Type) (C:forall a, B a -> Type) (x1 x2:A) (p:x1=x2)
  (f:forall y1:B x1, C x1 y1) (g:forall (y2:B x2), C x2 y2)
  : (forall (y1:B x1), transportD B C p y1 (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => forall y:B x, C x y) p f = g).
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.

Definition dpath_forall_constant
  {A B:Type} (C : A -> B -> Type) (x1 x2:A) (p:x1=x2)
  (f:forall (y1:B), C x1 y1) (g:forall (y2:B), C x2 y2)
  : (forall (y1:B), transport (fun x => C x y1) p (f y1) = g y1)
  <~>
  (transport (fun x => forall y:B, C x y) p f = g).
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.

(** ** Functorial action *)

(** The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. *)

Definition functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b)
  := (fun g b => f1 _ (g (f0 b))).

Definition ap_functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
    (g g' : forall a:A, P a) (h : g == g')
  : ap (functor_forall f0 f1) (path_forall _ _ h)
    = path_forall _ _ (fun b:B => (ap (f1 b) (h (f0 b)))).
Proof.
  revert h.  equiv_intro (@apD10 A P g g') h.
  destruct h.  simpl.
  transitivity (idpath (functor_forall f0 f1 g)).
  - exact (ap (ap (functor_forall f0 f1)) (path_forall_1 g)).
  - symmetry.  apply path_forall_1.
Defined.

Definition functor_forall_compose
           `{P : A -> Type} `{Q : B -> Type} `{R : C -> Type}
           (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
           (g0 : C -> B) (g1 : forall c:C, Q (g0 c) -> R c)
           (k : forall a, P a)
  : functor_forall g0 g1 (functor_forall f0 f1 k) == functor_forall (f0 o g0) (fun c => g1 c o f1 (g0 c)) k
  := fun a => 1.

(** Some special cases appear when one or the other of the maps are equivalences. *)

Definition functor_forall_id `{P : A -> Type} `{Q : A -> Type}
    (f1 : forall a:A, P a -> Q a)
  : (forall a:A, P a) -> (forall a:A, Q a)
  := functor_forall idmap f1.

Definition functor_forall_pb {A B : Type} `{P : A -> Type}
    (f0 : B -> A)
  : (forall a:A, P a) -> (forall b:B, P (f0 b))
  := functor_forall f0 (fun _ => idmap).

(** If [f0] is an equivalence, then we can simply apply [functor_forall] to its inverse.  However, in this case it is sometimes more convenient to place the substitution on the other side of [f1]. *)

Definition functor_forall_equiv `{P : A -> Type} `{Q : B -> Type}
    (f0 : A -> B) `{!IsEquiv f0} (f1 : forall a:A, P a -> Q (f0 a))
  : (forall a:A, P a) -> (forall b:B, Q b).
Proof.
  nrapply (functor_forall f0^-1).
  intros b u.
  refine ((eisretr f0 b) # _).
  exact (f1 _ u).
Defined.

Definition functor_forall_equiv_pb {A B : Type} `{Q : B -> Type}
    (f0 : A -> B) `{!IsEquiv f0}
  : (forall a:A, Q (f0 a)) -> (forall b:B, Q b)
  := functor_forall_equiv f0 (fun _ => idmap).

(** Since there's a nontrivial transport here, it's useful to have a computation lemma. *)
Definition functor_forall_equiv_pb_beta {A B : Type} {P : B -> Type} (f : A -> B)
  `{!IsEquiv f} (h : forall a, P (f a))
  : forall a, functor_forall_equiv_pb f h (f a) = h a.
Proof.
  intro a; srapply (_ @ apD h (eissect f a)); srapply (_ @ (transport_compose _ _ _ _)^).
  srapply ap10; apply ap; apply eisadj.
Defined.

(** ** Equivalences *)

(** If *both* maps in [functor_forall] are equivalences, then so is the output. *)
Global Instance isequiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv B A f} `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : IsEquiv (functor_forall f g) | 1000.
Proof.
  simple refine (isequiv_adjointify (functor_forall f g)
    (functor_forall (f^-1)
      (fun (x:A) (y:Q (f^-1 x)) => eisretr f x # (g (f^-1 x))^-1 y
      )) _ _);
  intros h.
  - abstract (
        apply path_forall; intros b; unfold functor_forall;
        rewrite eisadj;
        rewrite <- transport_compose;
        rewrite ap_transport;
        rewrite eisretr;
        apply apD
      ).
  - abstract (
        apply path_forall; intros a; unfold functor_forall;
        rewrite eissect;
        apply apD
      ).
Defined.

Definition equiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  (f : B -> A) `{IsEquiv B A f}
  (g : forall b, P (f b) -> Q b)
  `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : (forall a, P a) <~> (forall b, Q b)
  := Build_Equiv _ _ (functor_forall f g) _.

Definition equiv_functor_forall' `{P : A -> Type} `{Q : B -> Type}
  (f : B <~> A) (g : forall b, P (f b) <~> Q b)
  : (forall a, P a) <~> (forall b, Q b)
  := equiv_functor_forall f g.

Definition equiv_functor_forall_id `{P : A -> Type} `{Q : A -> Type}
  (g : forall a, P a <~> Q a)
  : (forall a, P a) <~> (forall a, Q a)
  := equiv_functor_forall (equiv_idmap A) g.

Definition equiv_functor_forall_pb {A B : Type} {P : A -> Type}
  (f : B <~> A)
  : (forall a, P a) <~> (forall b, P (f b))
  := equiv_functor_forall' (Q := P o f) f (fun b => equiv_idmap).

(** Similarly, we have a version of [functor_forall_equiv] that acts on on equivalences both upstairs and downstairs. *)

Definition equiv_functor_forall_covariant
           `{P : A -> Type} `{Q : B -> Type}
           (f : A <~> B) (g : forall a, P a <~> Q (f a))
  : (forall a, P a) <~> (forall b, Q b)
  := (equiv_functor_forall' f (fun a => (g a)^-1%equiv))^-1.

Definition equiv_functor_forall_covariant_compose
           `{P : A -> Type} `{Q : B -> Type} `{R : C -> Type}
           (f0 : A <~> B) (f1 : forall a, P a <~> Q (f0 a))
           (g0 : B <~> C) (g1 : forall b, Q b <~> R (g0 b))
           (h : forall a, P a)
  : equiv_functor_forall_covariant g0 g1 (equiv_functor_forall_covariant f0 f1 h)
    == equiv_functor_forall_covariant (g0 oE f0) (fun a => g1 (f0 a) oE f1 a) h.
Proof.
  apply apD10.
  refine ((equiv_inverse_compose
             (equiv_functor_forall' g0 (fun a : B => (g1 a)^-1%equiv))
             (equiv_functor_forall' f0 (fun a : A => (f1 a)^-1%equiv))
             h)^ @ _).
  revert h; apply equiv_inverse_homotopy; intros h.
  apply path_forall; intros c.
  symmetry; rapply functor_forall_compose.
Defined.

(** ** Functoriality on logical equivalences *)

(** At least over a fixed base *)
Definition iff_functor_forall {A : Type} {P Q : A -> Type}
           (f : forall a, P a <-> Q a)
  : (forall a, P a) <-> (forall a, Q a)
  := (functor_forall idmap (fun a => fst (f a)),
    functor_forall idmap (fun a => snd (f a))).

(** ** Two variable versions for function extensionality. *)

Definition equiv_path_forall11 {A : Type} {B : A -> Type} {P : forall a : A, B a -> Type} (f g : forall a b, P a b)
  : (forall (a : A) (b : B a), f a b = g a b) <~> f = g
  := (equiv_path_forall f g) oE (equiv_functor_forall_id (fun a => equiv_path_forall (f a) (g a))).

Definition path_forall11 {A : Type} {B : A -> Type} {P : forall a : A, B a -> Type} (f g : forall a b, P a b)
  : (forall x y, f x y = g x y) -> f = g
  := equiv_path_forall11 f g.

Global Instance isequiv_path_forall11 {A : Type} {B : A -> Type} `{P : forall a : A, B a -> Type} (f g : forall a b, P a b)
  : IsEquiv (path_forall11 f g) | 0
  := _.

Global Arguments equiv_path_forall11 {A B}%_type_scope {P} (f g)%_function_scope.

Global Arguments path_forall11 {A B}%_type_scope {P} (f g)%_function_scope _.

(** ** Truncatedness: any dependent product of n-types is an n-type: see [contr_forall] and [istrunc_forall] in Basics.Trunc. *)

(** ** Contractibility: A product over a contractible type is equivalent to the fiber over the center. *)

Definition equiv_contr_forall `{Contr A} `(P : A -> Type)
: (forall a, P a) <~> P (center A).
Proof.
  simple refine (equiv_adjointify (fun (f:forall a, P a) => f (center A)) _ _ _).
  - intros p a; exact (transport P (path_contr _ _) p).
  - intros p.
    refine (transport2 P (q := 1) _ p).
    apply path_contr.
  - intros f; apply path_forall; intros a.
    apply apD.
Defined.

End AssumeFunext.

(** ** Symmetry of curried arguments *)

(** Using the standard Haskell name for this, as it’s a handy utility function.

Note: not sure if [P] will usually be deducible, or whether it would be better explicit. *)
Definition flip `{P : A -> B -> Type}
  : (forall a b, P a b) -> (forall b a, P a b)
  := fun f b a => f a b.

Arguments flip {A B P} f b a /.

Global Instance isequiv_flip `{P : A -> B -> Type}
  : IsEquiv (@flip _ _ P) | 0.
Proof.
  set (flip_P := @flip _ _ P).
  set (flip_P_inv := @flip _ _ (flip P)).
  set (flip_P_is_sect := (fun f => 1) : flip_P_inv o flip_P == idmap).
  set (flip_P_is_retr := (fun g => 1) : flip_P o flip_P_inv == idmap).
  exists flip_P_inv flip_P_is_retr flip_P_is_sect.
  intro g.  exact 1.
Defined.

Definition equiv_flip `(P : A -> B -> Type)
  : (forall a b, P a b) <~> (forall b a, P a b)
  := Build_Equiv _ _ (@flip _ _ P) _.
