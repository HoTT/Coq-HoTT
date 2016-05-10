(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Sigma-types (dependent sums) *)

Require Import HoTT.Basics.
Require Import Types.Arrow Types.Prod Types.Paths Types.Unit.
Local Open Scope path_scope.


Generalizable Variables X A B C f g n.

Scheme sig_ind := Induction for sig Sort Type.
Scheme sig_rec := Minimality for sig Sort Type.

(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x y] in Coq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [(x;y)] to mean [existT _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [pr1] and [pr2]. *)

(** ** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a pair [(pr1 u ; pr2 u)]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_sigma `{P : A -> Type} (Q : sigT P -> Type) (u : sigT P)
: Q (u.1; u.2) -> Q u
  := idmap.

Arguments unpack_sigma / .

(** ** Eta conversion *)

Definition eta_sigma `{P : A -> Type} (u : sigT P)
  : (u.1; u.2) = u
  := 1.

Arguments eta_sigma / .

Definition eta2_sigma `{P : forall (a : A) (b : B a), Type}
           (u : sigT (fun a => sigT (P a)))
  : (u.1; (u.2.1; u.2.2)) = u
  := 1.

Arguments eta2_sigma / .

Definition eta3_sigma `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sigT (fun a => sigT (fun b => sigT (P a b))))
  : (u.1; (u.2.1; (u.2.2.1; u.2.2.2))) = u
  := 1.

Arguments eta3_sigma / .

(** ** Paths *)

(** A path in a total space is commonly shown component wise. Because we use this over and over, we write down the proofs by hand to make sure they are what we think they should be. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & p # u.2 = v.2})
: u = v
  := match pq.2 in (_ = v2) return u = (v.1; v2) with
       | 1 => match pq.1 as p in (_ = v1) return u = (v1; p # u.2) with
                | 1 => 1
              end
     end.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v
  := path_sigma_uncurried P u v (p;q).

(** A contravariant instance of [path_sigma_uncurried] *)
Definition path_sigma_uncurried_contra {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & u.2 = p^ # v.2})
: u = v
  := (path_sigma_uncurried P v u (pq.1^;pq.2^))^.

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
  apply 1%equiv.
Defined.


(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of dependent sum types.  But it has the advantage that the components of those pairs can more often be inferred, so we make them implicit arguments. *)
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p # y = y')
: (x;y) = (x';y')
  := path_sigma P (x;y) (x';y') p q.


(** Projections of paths from a total space. *)

Definition pr1_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: u.1 = v.1
  :=
    ap pr1 p.
(* match p with idpath => 1 end. *)

Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.

Definition pr2_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: p..1 # u.2 = v.2
  := (transport_compose P pr1 p u.2)^
     @ (@apD {x:A & P x} _ pr2 _ _ p).

Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.

(** Now we show how these things compute. *)

Definition pr1_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition pr2_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ _ pq)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_pr1_path_sigma_uncurried
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

Definition pr1_path_sigma `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: (path_sigma _ _ _ p q)..1 = p
  := pr1_path_sigma_uncurried (p; q).

Definition pr2_path_sigma `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: (path_sigma _ _ _ p q)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma p q) @ q
  := pr2_path_sigma_uncurried (p; q).

Definition eta_path_sigma `{P : A -> Type} {u v : sigT P} (p : u = v)
: path_sigma _ _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition transport_pr1_path_sigma
           `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
           Q
: transport (fun x => Q x.1) (@path_sigma A P u v p q)
  = transport _ p
  := transport_pr1_path_sigma_uncurried (p; q) Q.

(** This lets us identify the path space of a sigma-type, up to equivalence. *)

Global Instance isequiv_path_sigma `{P : A -> Type} {u v : sigT P}
: IsEquiv (path_sigma_uncurried P u v) | 0.
Proof.
  simple refine (BuildIsEquiv
            _ _
            _ (fun r => (r..1; r..2))
            eta_path_sigma
            _ _).
  all: destruct u, v; intros [p q].
  all: simpl in *.
  all: destruct q, p; simpl in *.
  all: reflexivity.
Defined.

Definition equiv_path_sigma `(P : A -> Type) (u v : sigT P)
: {p : u.1 = v.1 &  p # u.2 = v.2} <~> (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried P u v) _.

(* A contravariant version of [isequiv_path_sigma'] *)
Instance isequiv_path_sigma_contra `{P : A -> Type} {u v : sigT P}
  : IsEquiv (path_sigma_uncurried_contra P u v) | 0.
  apply (isequiv_adjointify (path_sigma_uncurried_contra P u v)
        (fun r => match r with idpath => (1; 1) end)).
    by intro r; induction r; destruct u as [u1 u2]; reflexivity.
  destruct u, v; intros [p q].
  simpl in *.
  destruct p; simpl in q.
  destruct q; reflexivity.
Defined.

(* A contravariant version of [equiv_path_sigma] *)
Definition equiv_path_sigma_contra {A : Type} `(P : A -> Type) (u v : sigT P)
  : {p : u.1 = v.1 & u.2 = p^ # v.2} <~> (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried_contra P u v) _.

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

(** [pr1_path] also commutes with the groupoid structure. *)

Definition pr1_path_1 {A : Type} {P : A -> Type} (u : sigT P)
: (idpath u) ..1 = idpath (u .1)
  := 1.

Definition pr1_path_pp {A : Type} {P : A -> Type} {u v w : sigT P}
           (p : u = v) (q : v = w)
: (p @ q) ..1 = (p ..1) @ (q ..1)
  := ap_pp _ _ _.

Definition pr1_path_V {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v)
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

(** Applying a function constructed with [sigT_ind] to a [path_sigma] can be computed.  Technically this computation should probably go by way of a 2-variable [ap], and should be done in the dependently typed case. *)

Definition ap_sigT_rec_path_sigma {A : Type} (P : A -> Type) {Q : Type}
           (x1 x2:A) (p:x1=x2) (y1:P x1) (y2:P x2) (q:p # y1 = y2)
           (d : forall a, P a -> Q)
: ap (sigT_ind (fun _ => Q) d) (path_sigma' P p q)
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

(** Or if the second variable contains a first component that doesn't depend on the first.  Need to think about the naming of these. *)

Definition transport_sigma_' {A : Type} {B C : A -> Type}
           {D : forall a:A, B a -> C a -> Type}
           {x1 x2 : A} (p : x1 = x2)
           (yzw : { y : B x1 & { z : C x1 & D x1 y z } })
: transport (fun x => { y : B x & { z : C x & D x y z } }) p yzw
  = (p # yzw.1 ; (p # yzw.2.1 ; transportD2 _ _ _ p yzw.1 yzw.2.1 yzw.2.2)).
Proof.
  destruct p. reflexivity.
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

Global Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
         `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
: IsEquiv (functor_sigma f g) | 1000.
Proof.
  refine (isequiv_adjointify (functor_sigma f g)
                             (functor_sigma (f^-1)
                                            (fun x y => ((g (f^-1 x))^-1 ((eisretr f x)^ # y)))) _ _);
  intros [x y].
  - refine (path_sigma' _ (eisretr f x) _); simpl.
    abstract (
        rewrite (eisretr (g (f^-1 x)));
        apply transport_pV
      ).
  - refine (path_sigma' _ (eissect f x) _); simpl.
    refine ((ap_transport (eissect f x) (fun x' => (g x') ^-1)
                          (transport Q (eisretr f (f x)) ^ (g x y)))^ @ _).
    abstract (
        rewrite transport_compose, eisadj, transport_pV;
        apply eissect
      ).
Defined.

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
  := equiv_functor_sigma' 1 g.

(** Lemma 3.11.9(i): Summing up a contractible family of types does nothing. *)

Global Instance isequiv_pr1_contr {A} {P : A -> Type}
         `{forall a, Contr (P a)}
: IsEquiv (@pr1 A P) | 100.
Proof.
  refine (isequiv_adjointify (@pr1 A P)
                             (fun a => (a ; center (P a))) _ _).
  - intros a; reflexivity.
  - intros [a p].
    refine (path_sigma' P 1 (contr _)).
Defined.

Definition equiv_sigma_contr {A : Type} (P : A -> Type)
           `{forall a, Contr (P a)}
: sigT P <~> A
  := BuildEquiv _ _ pr1 _.

(** Lemma 3.11.9(ii): Dually, summing up over a contractible type does nothing. *)

Definition equiv_contr_sigma {A : Type} (P : A -> Type) `{Contr A}
: { x : A & P x } <~> P (center A).
Proof.
  refine (equiv_adjointify (fun xp => (contr xp.1)^ # xp.2)
                           (fun p => (center A ; p)) _ _).
  - intros p; simpl.
    exact (ap (fun q => q # p) (path_contr _ 1)).
  - intros [a p].
    refine (path_sigma' _ (contr a) _).
    apply transport_pV.
Defined.

(** ** Associativity *)

Definition equiv_sigma_assoc `(P : A -> Type) (Q : {a : A & P a} -> Type)
: {a : A & {p : P a & Q (a;p)}} <~> sigT Q
  := @BuildEquiv
       _ _ _
       (@BuildIsEquiv
          {a : A & {p : P a & Q (a;p)}} (sigT Q)
          (fun apq => ((apq.1; apq.2.1); apq.2.2))
          (fun apq => (apq.1.1; (apq.1.2; apq.2)))
          (fun _ => 1)
          (fun _ => 1)
          (fun _ => 1)).

Definition equiv_sigma_prod `(Q : (A * B) -> Type)
: {a : A & {b : B & Q (a,b)}} <~> sigT Q
  := @BuildEquiv
       _ _ _
       (@BuildIsEquiv
          {a : A & {b : B & Q (a,b)}} (sigT Q)
          (fun apq => ((apq.1, apq.2.1); apq.2.2))
          (fun apq => (fst apq.1; (snd apq.1; apq.2)))
          (fun _ => 1)
          (fun _ => 1)
          (fun _ => 1)).

Definition equiv_sigma_prod0 A B
: {a : A & B} <~> A * B
  := BuildEquiv _ _ _
       (BuildIsEquiv
          {a : A & B} (A * B)
          (fun (ab : {a:A & B}) => (ab.1 , ab.2))
          (fun (ab : A*B) => (fst ab ; snd ab))
          (fun _ => 1) (fun _ => 1) (fun _ => 1)).

(** ** Symmetry *)

Definition equiv_sigma_symm `(P : A -> B -> Type)
: {a : A & {b : B & P a b}} <~> {b : B & {a : A & P a b}}
  := ((equiv_sigma_prod (fun x => P (snd x) (fst x)))^-1)
       oE (equiv_functor_sigma' (equiv_prod_symm A B)
                                (fun x => equiv_idmap (P (fst x) (snd x))))
       oE (equiv_sigma_prod (fun x => P (fst x) (snd x))).

Definition equiv_sigma_symm0 (A B : Type)
: {a : A & B} <~> {b : B & A}.
Proof.
  refine (BuildEquiv _ _ (fun (w:{a:A & B}) => (w.2 ; w.1)) _).
  simple refine (BuildIsEquiv _ _ _ (fun (z:{b:B & A}) => (z.2 ; z.1))
                       _ _ _); intros [x y]; reflexivity.
Defined.

(** ** Universal mapping properties *)

(** *** The positive universal property. *)
Global Instance isequiv_sigT_ind `{P : A -> Type}
         (Q : sigT P -> Type)
: IsEquiv (sigT_ind Q) | 0
  := BuildIsEquiv
       _ _
       (sigT_ind Q)
       (fun f x y => f (x;y))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_sigT_ind `{P : A -> Type}
           (Q : sigT P -> Type)
: (forall (x:A) (y:P x), Q (x;y)) <~> (forall xy, Q xy)
  := BuildEquiv _ _ (sigT_ind Q) _.

(** *** The negative universal property. *)

Definition sigT_coind_uncurried
           `{A : X -> Type} (P : forall x, A x -> Type)
: { f : forall x, A x & forall x, P x (f x) }
  -> (forall x, sigT (P x))
  := fun fg => fun x => (fg.1 x ; fg.2 x).

Definition sigT_coind
           `{A : X -> Type} (P : forall x, A x -> Type)
           (f : forall x, A x) (g : forall x, P x (f x))
: (forall x, sigT (P x))
  := sigT_coind_uncurried P (f;g).

Global Instance isequiv_sigT_coind
         `{A : X -> Type} {P : forall x, A x -> Type}
: IsEquiv (sigT_coind_uncurried P) | 0
  := BuildIsEquiv
       _ _
       (sigT_coind_uncurried P)
       (fun h => existT (fun f => forall x, P x (f x))
                        (fun x => (h x).1)
                        (fun x => (h x).2))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_sigT_coind
           `(A : X -> Type) (P : forall x, A x -> Type)
: { f : forall x, A x & forall x, P x (f x) }
    <~> (forall x, sigT (P x))
  := BuildEquiv _ _ (sigT_coind_uncurried P) _.

(** ** Sigmas preserve truncation *)

Global Instance trunc_sigma `{P : A -> Type}
         `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sigT P) | 100.
Proof.
  generalize dependent A.
  induction n; simpl; intros A P ac Pc.
  { exists (center A; center (P (center A))).
    intros [a ?].
    refine (path_sigma' P (contr a) (path_contr _ _)). }
  { intros u v.
    refine (trunc_equiv _ (path_sigma_uncurried P u v)). }
Defined.

(** The sigma of an arbitrary family of *disjoint* hprops is an hprop. *)
Definition ishprop_sigma_disjoint
           `{P : A -> Type} `{forall a, IsHProp (P a)}
: (forall x y, P x -> P y -> x = y) -> IsHProp { x : A & P x }.
Proof.
  intros dj; apply hprop_allpath; intros [x px] [y py].
  refine (path_sigma' P (dj x y px py) _).
  apply path_ishprop.
Defined.

(** ** Subtypes (sigma types whose second components are hprops) *)

(** To prove equality in a subtype, we only need equality of the first component. *)
Definition path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)}
           (u v : sigT P)
: u.1 = v.1 -> u = v
  := path_sigma_uncurried P u v o pr1^-1.

Global Instance isequiv_path_sigma_hprop {A P} `{forall x : A, IsHProp (P x)} {u v : sigT P}
: IsEquiv (@path_sigma_hprop A P _ u v) | 100
  := isequiv_compose.

Hint Immediate isequiv_path_sigma_hprop : typeclass_instances.

Definition equiv_path_sigma_hprop {A : Type} {P : A -> Type}
           {HP : forall a, IsHProp (P a)} (u v : sigT P)
: (u.1 = v.1) <~> (u = v)
  := BuildEquiv _ _ (path_sigma_hprop _ _) _.

Definition isequiv_pr1_path_hprop {A} {P : A -> Type}
         `{forall a, IsHProp (P a)}
         x y
: IsEquiv (@pr1_path A P x y)
  := _ : IsEquiv (path_sigma_hprop x y)^-1.

Hint Immediate isequiv_pr1_path_hprop : typeclass_instances.

(** We define this for ease of [SearchAbout IsEquiv ap pr1] *)
Definition isequiv_ap_pr1_hprop {A} {P : A -> Type}
           `{forall a, IsHProp (P a)}
           x y
: IsEquiv (@ap _ _ (@pr1 A P) x y)
  := _.

Definition path_sigma_hprop_1 {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)} (u : sigT P)
: path_sigma_hprop u u 1 = 1.
Proof.
  unfold path_sigma_hprop.
  unfold isequiv_pr1_contr; simpl.
  (** Ugh *)
  refine (ap (fun p => match p in (_ = v2) return (u = (u.1; v2)) with 1 => 1 end)
             (contr (idpath u.2))).
Defined.

(** The inverse of [path_sigma_hprop] has its own name, so we give special names to the section and retraction homotopies to help [rewrite] out. *)
Definition path_sigma_hprop_ap_pr1 {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)} (u v : sigT P) (p : u = v)
: path_sigma_hprop u v (ap pr1 p) = p
  := eisretr (path_sigma_hprop u v) p.
Definition path_sigma_hprop_pr1_path {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)} (u v : sigT P) (p : u = v)
: path_sigma_hprop u v p..1 = p
  := eisretr (path_sigma_hprop u v) p.
Definition ap_pr1_path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)} (u v : sigT P) (p : u.1 = v.1)
: ap pr1 (path_sigma_hprop u v p) = p
  := eissect (path_sigma_hprop u v) p.
Definition pr1_path_path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)} (u v : sigT P) (p : u.1 = v.1)
: (path_sigma_hprop u v p)..1 = p
  := eissect (path_sigma_hprop u v) p.
