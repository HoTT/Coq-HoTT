(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Sigma-types (dependent sums) *)

Require Import Overture PathGroupoids Equivalences Contractible Trunc.
Require Import Arrow.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables X A B C f g n.

(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x y] in Coq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [(x;y)] to mean [existT _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [projT1] and [projT2]. *)

(** ** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a pair [(projT1 u ; projT2 u)]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_sigma `{P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (projT1 u; projT2 u) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (projT1 u; projT2 u) -> Q u) := u in idmap) H.

(** ** Eta conversion *)

Definition eta_sigma `{P : A -> Type} (u : sigT P)
  : (projT1 u; projT2 u) = u
  := match u with existT x y => 1 end.

Definition eta2_sigma `{P : forall (a : A) (b : B a), Type}
           (u : sigT (fun a => sigT (P a)))
  : (u.1; (u.2.1; u.2.2)) = u
  := match u with existT x (existT y z) => 1 end.

Definition eta3_sigma `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sigT (fun a => sigT (fun b => sigT (P a b))))
  : (u.1; (u.2.1; (u.2.2.1; u.2.2.2))) = u
  := match u with existT x (existT y (existT z w)) => 1 end.

(** ** Paths *)

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

(** A variant of [Forall.dpath_forall] from which uses dependent sums to package things. It cannot go into [Forall] because [Sigma] depends on [Forall]. *)

Definition dpath_forall'
  {A : Type } (P : A -> Type) (Q: sigT P -> Type) {x y : A} (h : x = y)
  (f : forall p, Q (x ; p)) (g : forall p, Q (y ; p))
 :
  (forall p, transport Q (path_sigma P (x ; p) (y; _) h 1) (f p) = g (h # p))
  <~>
  (forall p, transportD P (fun x => fun p => Q ( x ; p)) h p (f p) = g (transport P h p)).
Proof.
  destruct h.
  apply equiv_idmap.
Defined.


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
  := (transport_compose P (@projT1 _ _) p u.2)^
     @ (@apD {x:A & P x} _ (@projT2 _ _) _ _ p).

Notation "p ..2" := (projT2_path p) (at level 3) : fibration_scope.

(** Now we show how these things compute. *)

Definition projT1_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition projT2_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ _ pq)..2
    = ap (fun s => transport P s u.2) (projT1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
  (p : u = v)
  : path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p. destruct u. reflexivity.
Defined.

Lemma transport_projT1_path_sigma_uncurried
      `{P : A -> Type} {u v : sigT P}
      (pq : { p : u.1 = v.1 & transport P p u.2 = v.2 })
      Q
: transport (fun x => Q x.1) (@path_sigma_uncurried A P u v pq)
  = transport _ pq.1.
Proof.
  destruct pq as [p q], u, v; simpl in *.
  destruct p, q; simpl in *.
  reflexivity.
Defined.

Definition projT1_path_sigma `{P : A -> Type} {u v : sigT P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..1 = p
  := projT1_path_sigma_uncurried (p; q).

Definition projT2_path_sigma `{P : A -> Type} {u v : sigT P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..2
    = ap (fun s => transport P s u.2) (projT1_path_sigma p q) @ q
  := projT2_path_sigma_uncurried (p; q).

Definition eta_path_sigma `{P : A -> Type} {u v : sigT P} (p : u = v)
  : path_sigma _ _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition transport_projT1_path_sigma
      `{P : A -> Type} {u v : sigT P}
      (p : u.1 = v.1) (q : p # u.2 = v.2)
      Q
: transport (fun x => Q x.1) (@path_sigma A P u v p q)
  = transport _ p
  := transport_projT1_path_sigma_uncurried (p; q) Q.

(** This lets us identify the path space of a sigma-type, up to equivalence. *)

Instance isequiv_path_sigma `{P : A -> Type} {u v : sigT P}
  : IsEquiv (path_sigma_uncurried P u v) | 0.
  refine (isequiv_adjointify _
    (fun r => (existT (fun p : u.1 = v.1 => p # u.2 = v.2) r..1 r..2))
    eta_path_sigma
    _).
  destruct u as [u1 u2]; destruct v as [v1 v2]; intros [p q].
  simpl in p, q.
  destruct p; simpl in q.
  destruct q; reflexivity.
Defined.

Definition equiv_path_sigma `(P : A -> Type) (u v : sigT P)
  : {p : u.1 = v.1 &  p # u.2 = v.2} <~> (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried P u v) _.

(** This identification respects path concatenation. *)

Definition path_sigma_pp_pp {A : Type} (P : A -> Type) {u v w : sigT P}
  (p1 : u.1 = v.1) (q1 : p1 # u.2 = v.2)
  (p2 : v.1 = w.1) (q2 : p2 # v.2 = w.2)
  : path_sigma P u w (p1 @ p2)
      (transport_pp P p1 p2 u.2 @ ap (transport P p2) q1 @ q2)
  = path_sigma P u v p1 q1 @ path_sigma P v w p2 q2.
Proof.
  destruct u, v, w. simpl in *.
  destruct p1, p2, q1, q2.
  reflexivity.
Defined.

Definition path_sigma_pp_pp' {A : Type} (P : A -> Type)
  {u1 v1 w1 : A} {u2 : P u1} {v2 : P v1} {w2 : P w1}
  (p1 : u1 = v1) (q1 : p1 # u2 = v2)
  (p2 : v1 = w1) (q2 : p2 # v2 = w2)
  : path_sigma' P (p1 @ p2)
      (transport_pp P p1 p2 u2 @ ap (transport P p2) q1 @ q2)
  = path_sigma' P p1 q1 @ path_sigma' P p2 q2
  := @path_sigma_pp_pp A P (u1;u2) (v1;v2) (w1;w2) p1 q1 p2 q2.

Definition path_sigma_p1_1p' {A : Type} (P : A -> Type)
  {u1 v1 : A} {u2 : P u1} {v2 : P v1}
  (p : u1 = v1) (q : p # u2 = v2)
  : path_sigma' P p q
  = path_sigma' P p 1 @ path_sigma' P 1 q.
Proof.
  destruct p, q.
  reflexivity.
Defined.

(** [projT1_path] also commutes with the groupoid structure. *)

Definition projT1_path_1 {A : Type} {P : A -> Type} (u : sigT P)
: (idpath u) ..1 = idpath (u .1)
:= 1.

Definition projT1_path_pp {A : Type} {P : A -> Type} {u v w : sigT P}
  (p : u = v) (q : v = w)
: (p @ q) ..1 = (p ..1) @ (q ..1)
:= ap_pp _ _ _.

Definition projT1_path_V {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v)
: p^ ..1 = (p ..1)^
:= ap_V _ _.

(** Applying [existT] to one argument is the same as [path_sigma] with reflexivity in the first place. *)

Definition ap_existT {A : Type} (P : A -> Type) (x : A) (y1 y2 : P x)
  (q : y1 = y2)
  : ap (existT P x) q = path_sigma' P 1 q.
Proof.
  destruct q; reflexivity.
Defined.

(** Dependent transport is the same as transport along a [path_sigma]. *)

Definition transportD_is_transport
  {A:Type} (B:A->Type) (C:sigT B -> Type)
  (x1 x2:A) (p:x1=x2) (y:B x1) (z:C (x1;y))
  : transportD B (fun a b => C (a;b)) p y z
    = transport C (path_sigma' B p 1) z.
Proof.
  destruct p. reflexivity.
Defined.

(** Applying a function constructed with [sigT_rect] to a [path_sigma] can be computed.  Technically this computation should probably go by way of a 2-variable [ap], and should be done in the dependently typed case. *)

Definition ap_sigT_rectnd_path_sigma {A : Type} (P : A -> Type) {Q : Type}
  (x1 x2:A) (p:x1=x2) (y1:P x1) (y2:P x2) (q:p # y1 = y2)
  (d : forall a, P a -> Q)
  : ap (sigT_rect (fun _ => Q) d) (path_sigma' P p q)
  = (transport_const p _)^
  @ (ap ((transport (fun _ => Q) p) o (d x1)) (transport_Vp _ p y1))^

  @ (transport_arrow p _ _)^
  @ ap10 (apD d p) (p # y1)
  @ ap (d x2) q.
Proof.
  destruct p. destruct q. reflexivity.
Defined.


(** A path between paths in a total space is commonly shown component wise. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (p q : u = v)
  (rs : {r : p..1 = q..1 & transport (fun x => transport P x u.2 = v.2) r p..2 = q..2})
  : p = q.
Proof.
  destruct rs, p, u.
  etransitivity; [ | apply eta_path_sigma ].
  path_induction.
  reflexivity.
Defined.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (r : p..1 = q..1)
           (s : transport (fun x => transport P x u.2 = v.2) r p..2 = q..2)
: p = q
  := path_path_sigma_uncurried P u v p q (r; s).

(** ** Transport *)

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

(** ** Functorial action *)

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

(** ** Equivalences *)

Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : IsEquiv (functor_sigma f g) | 1000.
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
  (f : A -> B) `{IsEquiv A B f}
  (g : forall a, P a -> Q (f a))
  `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : sigT P <~> sigT Q
  := BuildEquiv _ _ (functor_sigma f g) _.

Definition equiv_functor_sigma' `{P : A -> Type} `{Q : B -> Type}
  (f : A <~> B)
  (g : forall a, P a <~> Q (f a))
  : sigT P <~> sigT Q
  := equiv_functor_sigma f g.

Definition equiv_functor_sigma_id `{P : A -> Type} `{Q : A -> Type}
  (g : forall a, P a <~> Q a)
  : sigT P <~> sigT Q
  := equiv_functor_sigma (equiv_idmap A) g.

(* Summing up a contractible family of types does nothing. *)
Definition equiv_sigma_contr {A : Type} (P : A -> Type)
  `{forall a, Contr (P a)}
  : sigT P <~> A.
Proof.
  refine (equiv_adjointify (@projT1 A P)
    (fun a => (a ; center (P a))) _ _).
  intros a; reflexivity.
  intros [a p]. apply path_sigma' with 1, contr.
Defined.

(** ** Associativity *)

Definition equiv_sigma_assoc `(P : A -> Type) (Q : {a : A & P a} -> Type)
  : {a : A & {p : P a & Q (a;p)}} <~> sigT Q.
Proof.
  refine (@equiv_adjointify {a : A & {p : P a & Q (a;p)}} (sigT Q)
    (fun apq => let (a,pq):=apq in let (p,q):=pq in ((a;p);q))
    (fun apq => let (ap,q):=apq in
      (let (a,p) return (Q ap -> {a : A & {p : P a & Q (a;p)}})
        := ap in fun q => (a ; existT (fun p:P a => Q (a;p)) p q)) q)
    _ _).
  - intros [[a p] q]; reflexivity.
  - intros [a [p q]]; reflexivity.
Defined.

Definition equiv_sigma_prod `(Q : (A * B) -> Type)
  : {a : A & {b : B & Q (a,b)}} <~> sigT Q.
Proof.
  refine (@equiv_adjointify {a : A & {b : B & Q (a,b)}} (sigT Q)
    (fun abq => let (a,bq):=abq in let (b,q):=bq in ((a,b);q))
    (fun abq => let (ab,q):=abq in
      (let (a,b) return (Q ab -> {a : A & {b : B & Q (a,b)}})
        := ab in fun q => (a ; existT (fun b:B => Q (a,b)) b q)) q)
    _ _).
  - intros [[a b] q]; reflexivity.
  - intros [a [b q]]; reflexivity.
Defined.

(** ** Universal mapping properties *)

(* The positive universal property. *)
Instance isequiv_sigT_rect `{Funext} `{P : A -> Type}
  (Q : sigT P -> Type)
  : IsEquiv (sigT_rect Q) | 0
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
  : IsEquiv (sigT_corect_uncurried P) | 0
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
  `(A : X -> Type) (P : forall x, A x -> Type)
  : { f : forall x, A x & forall x, P x (f x) }
     <~> (forall x, sigT (P x))
  := BuildEquiv _ _ (sigT_corect_uncurried P) _.

(** ** Sigmas preserve truncation *)

Instance trunc_sigma `{P : A -> Type}
  `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (sigT P) | 100.
Proof.
  generalize dependent A.
  induction n; simpl; intros A P ac Pc.
  - exists (center A; center (P (center A))).
    intros [a ?].
    refine (path_sigma' P (contr a) (path_contr _ _)).
  - intros u v.
    refine (trunc_equiv (path_sigma_uncurried P u v)).
Defined.
