(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Sigma-types (dependent sums) *)

Require Import Overture PathGroupoids Equivalences Contractible Trunc.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables X A B f g n.

(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x y] in Coq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [(x;y)] to mean [existT _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [projT1] and [projT2]. *)

(** *** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a pair [(projT1 u ; projT2 u)]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_sigma `{P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (projT1 u; projT2 u) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (projT1 u; projT2 u) -> Q u) := u in idmap) H.

(** *** Eta conversion *)

Definition eta_sigma `{P : A -> Type} (u : sigT P)
  : (projT1 u; projT2 u) = u
  := match u with existT x y => 1 end.

(** *** Paths *)

(** A path in a total space is commonly shown component wise. Because we use this over and over, we write down the proofs by hand to make sure they are what we think they should be. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (pq : {p : u.1 = v.1 &  p # u.2 = v.2})
  : u = v
  := match pq with
       | existT p q =>
         match u, v return (forall p0, (p0 # u.2 = v.2) -> (u=v)) with
           | (x;y), (x';y') => fun p1 q1 =>
             match p1 in (_ = x'') return (forall y'', (p1 # y = y'') -> (x;y)=(x'';y'')) with
               | idpath => fun y' q2 =>
                 match q2 with
                   | idpath => 1
                 end
             end y' q1
         end p q
     end.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : u = v
  := path_sigma_uncurried P u v (p;q).

(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of dependent sum types.  But it has the advantage that the components of those pairs can more often be inferred, so we make them implicit arguments. *)
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
  (p : x = x') (q : p # y = y')
  : (x;y) = (x';y')
  := path_sigma P (x;y) (x';y') p q.


(** Projections of paths from a total space. *)

Definition projT1_path `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.1 = v.1
  :=
  ap (@projT1 _ _) p.
  (* match p with idpath => 1 end. *)

Notation "p ..1" := (projT1_path p) (at level 3) : fibration_scope.

Definition projT2_path `{P : A -> Type} {u v : sigT P} (p : u = v)
  : p..1 # u.2 = v.2
  :=
  match p with idpath => 1 end.

Notation "p ..2" := (projT2_path p) (at level 3) : fibration_scope.

(** Now we show how these things compute. *)

Definition projT1_path_sigma `{P : A -> Type} {u v : sigT P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..1 = p.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition projT2_path_sigma `{P : A -> Type} {u v : sigT P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..2
    = ap (fun s => transport P s u.2) (projT1_path_sigma p q) @ q.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma `{P : A -> Type} {u v : sigT P} (p : u = v)
  : path_sigma _ _ _ (p..1) (p..2) = p.
Proof.
  destruct p. destruct u. reflexivity.
Defined.

(** This lets us identify the path space of a sigma-type, up to equivalence. *)

Instance isequiv_path_sigma `{P : A -> Type} {u v : sigT P}
  : IsEquiv (path_sigma_uncurried P u v).
  refine (isequiv_adjointify _
    (fun r => (existT (fun p : u.1 = v.1 => p # u.2 = v.2) r..1 r..2))
    eta_path_sigma
    _).
  destruct u as [u1 u2]; destruct v as [v1 v2]; intros [p q].
  simpl in p, q.
  destruct p; simpl in q.
  destruct q; reflexivity.
Defined.

Definition equiv_path_sigma `{P : A -> Type} {u v : sigT P}
  : {p : u.1 = v.1 &  p # u.2 = v.2} <~> (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried P u v) _.

(** *** Transport *)

(** The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)

Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
  : transport (fun x => { y : B x & C x y }) p yz
    = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
Proof.
  destruct p.  destruct yz as [y z]. reflexivity.
Defined.

(** The special case when the second variable doesn't depend on the first is simpler. *)
Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
  : transport (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.

(** *** Functorial action *)

Definition functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  : sigT P -> sigT Q
  := fun u => (f u.1 ; g u.1 u.2).

Definition ap_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  (u v : sigT P) (p : u.1 = v.1) (q : p # u.2 = v.2)
  : ap (functor_sigma f g) (path_sigma P u v p q)
  = path_sigma Q (functor_sigma f g u) (functor_sigma f g v)
               (ap f p)
               ((transport_compose Q f p (g u.1 u.2))^
               @ (@ap_transport _ P (fun x => Q (f x)) _ _ p g u.2)^
               @ ap (g v.1) q).
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in p, q.
  destruct p; simpl in q.
  destruct q.
  reflexivity.
Defined.

(** *** Equivalences *)

Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : IsEquiv (functor_sigma f g).
Proof.
  refine (isequiv_adjointify (functor_sigma f g)
    (functor_sigma (f^-1)
      (fun x y => ((g (f^-1 x))^-1 ((eisretr f x)^ # y)))) _ _);
  intros [x y].
  - refine (path_sigma' _ (eisretr f x) _); simpl.
    rewrite (eisretr (g (f^-1 x))).
    apply transport_pV.
  - refine (path_sigma' _ (eissect f x) _); simpl.
    refine ((ap_transport (eissect f x) (fun x' => (g x') ^-1)
              (transport Q (eisretr f (f x)) ^ (g x y)))^ @ _).
    rewrite transport_compose, eisadj, transport_pV.
    apply eissect.
Qed.

Definition equiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : sigT P <~> sigT Q
  := BuildEquiv _ _ (functor_sigma f g) _.

(** *** Universal mapping properties *)

(* The positive universal property. *)
Instance isequiv_sigT_rect `{Funext} `{P : A -> Type}
  (Q : sigT P -> Type)
  : IsEquiv (sigT_rect Q)
  := isequiv_adjointify (sigT_rect Q)
  (fun f x y => f (x;y))
  _ _.
Proof.
  - intros f; apply path_forall; intros [x y].
    reflexivity.
  - intros f; apply path_forall; intros x; apply path_forall; intros y.
    reflexivity.
Defined.

Definition equiv_sigT_rect `{Funext} `{P : A -> Type}
  (Q : sigT P -> Type)
  : (forall (x:A) (y:P x), Q (x;y)) <~> (forall xy, Q xy)
  := BuildEquiv _ _ (sigT_rect Q) _.

(* The negative universal property. *)

Definition sigT_corect_uncurried
  `{A : X -> Type} (P : forall x, A x -> Type)
  : { f : forall x, A x & forall x, P x (f x) }
     -> (forall x, sigT (P x))
  := fun fg => let (f,g) := fg in fun x => (f x ; g x).

Definition sigT_corect
  `{A : X -> Type} (P : forall x, A x -> Type)
  (f : forall x, A x) (g : forall x, P x (f x))
  : (forall x, sigT (P x))
  := sigT_corect_uncurried P (f;g).

Instance isequiv_sigT_corect `{Funext}
  `{A : X -> Type} {P : forall x, A x -> Type}
  : IsEquiv (sigT_corect_uncurried P)
  := isequiv_adjointify (sigT_corect_uncurried P)
  (fun h => existT (fun f => forall x, P x (f x))
    (fun x => (h x).1) (fun x => (h x).2))
  _ _.
Proof.
  - intros h; apply path_forall; intros x; simpl.
    apply eta_sigma.
  - intros [f g]; simpl; reflexivity.
Defined.

Definition equiv_sigT_corect `{Funext}
  `{A : X -> Type} {P : forall x, A x -> Type}
  : { f : forall x, A x & forall x, P x (f x) }
     <~> (forall x, sigT (P x))
  := BuildEquiv _ _ (sigT_corect_uncurried P) _.

(** *** Sigmas preserve truncation *)

Instance Trunc_sigma `{P : A -> Type}
  `{Trunc n A} `{forall a, Trunc n (P a)}
  : Trunc n (sigT P).
Proof.
  generalize dependent A.
  induction n; simpl; intros A P ac Pc.
  - exists (center A; center (P (center A))).
    intros [a ?].
    refine (path_sigma' P (contr a) (path_contr _ _)).
  - intros u v.
    refine (trunc_equiv _ _ (path_sigma_uncurried P u v)).
Defined.
