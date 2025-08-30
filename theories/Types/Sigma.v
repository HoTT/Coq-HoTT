(** * Theorems about Sigma-types (dependent sums) *)

Require Import HoTT.Basics.
Require Import Types.Arrow Types.Paths.
Local Open Scope path_scope.

Generalizable Variables X A B C f g n.

(** In homotopy type theory, we think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sig P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [exist P x y] in Coq, where [x : A] and [y : P x].  In [Overture.v], we defined the notation [(x; y)] to mean [exist _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [pr1] and [pr2]. *)

(** ** Eta conversion *)

Definition eta_sigma `{P : A -> Type} (u : sig P)
  : (u.1; u.2) = u
  := 1.

Arguments eta_sigma / .

Definition eta2_sigma `{P : forall (a : A) (b : B a), Type}
           (u : sig (fun a => sig (P a)))
  : (u.1; u.2.1; u.2.2) = u
  := 1.

Arguments eta2_sigma / .

Definition eta3_sigma `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sig (fun a => sig (fun b => sig (P a b))))
  : (u.1; u.2.1; u.2.2.1; u.2.2.2) = u
  := 1.

Arguments eta3_sigma / .

(** ** Paths *)

(** A path in a total space is commonly shown component wise. Because we use this over and over, we write down the proofs by hand to make sure they are what we think they should be. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sig P)
  (pq : {p : u.1 = v.1 & p # u.2 = v.2})
  : u = v
  := match pq.2 in (_ = v2) return u = (v.1; v2) with
       | 1 => match pq.1 as p in (_ = v1) return u = (v1; p # u.2) with
                | 1 => 1
              end
     end.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_sigma {A : Type} (P : A -> Type) (u v : sig P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : u = v
  := path_sigma_uncurried P u v (p;q).

(** A contravariant instance of [path_sigma_uncurried] *)
Definition path_sigma_uncurried_contra {A : Type} (P : A -> Type) (u v : sig P)
  (pq : {p : u.1 = v.1 & u.2 = p^ # v.2})
  : u = v
  := (path_sigma_uncurried P v u (pq.1^;pq.2^))^.

(** A variant of [Forall.dpath_forall] from which uses dependent sums to package things. It cannot go into [Forall] because [Sigma] depends on [Forall]. *)
Definition dpath_forall'
  {A : Type } (P : A -> Type) (Q: sig P -> Type) {x y : A} (h : x = y)
  (f : forall p, Q (x ; p)) (g : forall p, Q (y ; p))
  : (forall p, transport Q (path_sigma P (x ; p) (y; _) h 1) (f p) = g (h # p))
    <~> (forall p, transportD P (fun x => fun p => Q ( x ; p)) h p (f p) = g (transport P h p)).
Proof.
  destruct h.
  exact 1%equiv.
Defined.

(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of dependent sum types.  But it has the advantage that the components of those pairs can more often be inferred, so we make them implicit arguments. *)
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
  (p : x = x') (q : p # y = y')
  : (x;y) = (x';y')
  := path_sigma P (x;y) (x';y') p q.

(** Projections of paths from a total space. *)
Definition pr1_path `{P : A -> Type} {u v : sig P} (p : u = v)
  : u.1 = v.1
  := ap pr1 p.
(* match p with idpath => 1 end. *)

Notation "p ..1" := (pr1_path p) : fibration_scope.

Definition pr2_path `{P : A -> Type} {u v : sig P} (p : u = v)
  : p..1 # u.2 = v.2
  := (transport_compose P pr1 p u.2)^
     @ (@apD {x:A & P x} _ pr2 _ _ p).

Notation "p ..2" := (pr2_path p) : fibration_scope.

(** Now we show how these things compute. *)

Definition pr1_path_sigma_uncurried `{P : A -> Type} {u v : sig P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition pr2_path_sigma_uncurried `{P : A -> Type} {u v : sig P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ _ pq)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried `{P : A -> Type} {u v : sig P}
  (p : u = v)
  : path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_pr1_path_sigma_uncurried
  `{P : A -> Type} {u v : sig P}
  (pq : { p : u.1 = v.1 & transport P p u.2 = v.2 })
  Q
  : transport (fun x => Q x.1) (@path_sigma_uncurried A P u v pq)
    = transport _ pq.1.
Proof.
  destruct pq as [p q], u, v; simpl in *.
  destruct p, q; simpl in *.
  reflexivity.
Defined.

Definition pr1_path_sigma `{P : A -> Type} {u v : sig P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..1 = p
  := pr1_path_sigma_uncurried (p; q).

(* Writing it the other way can help [rewrite]. *)
Definition ap_pr1_path_sigma {A:Type} {P : A -> Type} {u v : sig P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : ap pr1 (path_sigma _ _ _ p q) = p
  := pr1_path_sigma p q.

Definition pr2_path_sigma `{P : A -> Type} {u v : sig P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : (path_sigma _ _ _ p q)..2
    = ap (fun s => transport P s u.2) (pr1_path_sigma p q) @ q
  := pr2_path_sigma_uncurried (p; q).

Definition eta_path_sigma `{P : A -> Type} {u v : sig P} (p : u = v)
  : path_sigma _ _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition transport_pr1_path_sigma
  `{P : A -> Type} {u v : sig P}
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  Q
  : transport (fun x => Q x.1) (@path_sigma A P u v p q)
    = transport _ p
  := transport_pr1_path_sigma_uncurried (p; q) Q.

(** This lets us identify the path space of a sigma-type, up to equivalence. *)

Instance isequiv_path_sigma `{P : A -> Type} {u v : sig P}
  : IsEquiv (path_sigma_uncurried P u v) | 0.
Proof.
  simple refine (Build_IsEquiv
            _ _
            _ (fun r => (r..1; r..2))
            eta_path_sigma
            _ _).
  all: destruct u, v; intros [p q].
  all: simpl in *.
  all: destruct q, p; simpl in *.
  all: reflexivity.
Defined.

Definition equiv_path_sigma `(P : A -> Type) (u v : sig P)
  : {p : u.1 = v.1 &  p # u.2 = v.2} <~> (u = v)
  := Build_Equiv _ _ (path_sigma_uncurried P u v) _.

(* A contravariant version of [isequiv_path_sigma'] *)
Instance isequiv_path_sigma_contra `{P : A -> Type} {u v : sig P}
  : IsEquiv (path_sigma_uncurried_contra P u v) | 0.
Proof.
  apply (isequiv_adjointify (path_sigma_uncurried_contra P u v)
        (fun r => match r with idpath => (1; 1) end)).
  - by intro r; induction r; destruct u as [u1 u2]; reflexivity.
  - destruct u, v; intros [p q].
    simpl in *.
    destruct p; simpl in q.
    destruct q; reflexivity.
Defined.

(* A contravariant version of [equiv_path_sigma] *)
Definition equiv_path_sigma_contra {A : Type} `(P : A -> Type) (u v : sig P)
  : {p : u.1 = v.1 & u.2 = p^ # v.2} <~> (u = v)
  := Build_Equiv _ _ (path_sigma_uncurried_contra P u v) _.

(** This identification respects path concatenation. *)

Definition path_sigma_pp_pp {A : Type} (P : A -> Type) {u v w : sig P}
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

Definition pr1_path_1 {A : Type} {P : A -> Type} (u : sig P)
  : (idpath u) ..1 = idpath (u .1)
  := 1.

Definition pr1_path_pp {A : Type} {P : A -> Type} {u v w : sig P}
  (p : u = v) (q : v = w)
  : (p @ q) ..1 = (p ..1) @ (q ..1)
  := ap_pp _ _ _.

Definition pr1_path_V {A : Type} {P : A -> Type} {u v : sig P} (p : u = v)
  : p^ ..1 = (p ..1)^
  := ap_V _ _.

(** Applying [exist] to one argument is the same as [path_sigma] with reflexivity in the first place. *)
Definition ap_exist {A : Type} (P : A -> Type) (x : A) (y1 y2 : P x)
  (q : y1 = y2)
  : ap (exist P x) q = path_sigma' P 1 q.
Proof.
  destruct q; reflexivity.
Defined.

(** Dependent transport is the same as transport along a [path_sigma]. *)
Definition transportD_is_transport
  {A:Type} (B:A->Type) (C:sig B -> Type)
  (x1 x2:A) (p:x1=x2) (y:B x1) (z:C (x1;y))
  : transportD B (fun a b => C (a;b)) p y z
    = transport C (path_sigma' B p 1) z.
Proof.
  destruct p. reflexivity.
Defined.

(** Doubly dependent transport is the same as transport along a [path_sigma]. *)
Definition transportDD_is_transport {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  (c1 : C a1 b1)
  : transportDD B C pA pB c1
    = transport (fun (ab : sig B) => C ab.1 ab.2) (path_sigma' B pA pB) c1.
Proof.
  by destruct pB, pA.
Defined.

(** Applying a two variable function to a [path_sigma]. *)
Definition ap_path_sigma {A B} (P : A -> Type) (F : forall a : A, P a -> B)
  {x x' : A} {y : P x} {y' : P x'} (p : x = x') (q : p # y = y')
  : ap (sig_rec F) (path_sigma' P p q)
    = ap _ (moveL_transport_V _ p _ _ q)
        @ (transport_arrow_toconst _ _ _)^ @ ap10 (apD F p) y'.
Proof.
  destruct p, q; reflexivity.
Defined.
(* Remark: this is also equal to: *)
(*     = ap10 (apD F p^)^ y @ transport_arrow_toconst _ _ _ *)
(*                          @ ap (F x') (transport2 _ (inv_V p) y @ q). *)

(** And we can simplify when the first equality is [1]. *)
Lemma ap_path_sigma_1p {A B : Type} {P : A -> Type} (F : forall a, P a -> B)
  (a : A) {x y : P a} (p : x = y)
  : ap (fun w => F w.1 w.2) (path_sigma' P 1 p) = ap (fun z => F a z) p.
Proof.
  destruct p; reflexivity.
Defined.

(** Applying a function constructed with [sig_rec] to a [path_sigma] can be computed.  Technically this computation should probably go by way of a 2-variable [ap], and should be done in the dependently typed case. *)
Definition ap_sig_rec_path_sigma {A : Type} (P : A -> Type) {Q : Type}
  (x1 x2 : A) (p : x1 = x2) (y1 : P x1) (y2 : P x2) (q : p # y1 = y2)
  (d : forall a, P a -> Q)
  : ap (sig_rec d) (path_sigma' P p q)
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
Definition path_path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sig P)
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
Definition path_path_sigma {A : Type} (P : A -> Type) (u v : sig P)
  (p q : u = v)
  (r : p..1 = q..1)
  (s : transport (fun x => transport P x u.2 = v.2) r p..2 = q..2)
  : p = q
  := path_path_sigma_uncurried P u v p q (r; s).

(** ** Transport *)

(** The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/[transportD] can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)

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
    = (p # yzw.1 ; p # yzw.2.1 ; transportD2 _ _ _ p yzw.1 yzw.2.1 yzw.2.2).
Proof.
  destruct p. reflexivity.
Defined.

(** ** Functorial action *)

Definition functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  : sig P -> sig Q
  := fun u => (f u.1 ; g u.1 u.2).

Definition ap_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  (u v : sig P) (p : u.1 = v.1) (q : p # u.2 = v.2)
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

(** The converse to [isequiv_functor_sigma] when [f] is [idmap] is [isequiv_from_functor_sigma] in Types/Equiv.v, which also contains Theorem 4.7.7 *)
Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : IsEquiv (functor_sigma f g) | 1000.
Proof.
  snapply isequiv_adjointify.
  - napply (functor_sigma f^-1).
    exact (fun b q => (g (f^-1 b))^-1 ((transport Q (eisretr f b)^) q)).
  - intros [b q].
    apply (path_sigma' _ (eisretr f _)); simpl.
    lhs napply (ap _ (eisretr (g (f^-1 _)) _)).
    apply transport_pV.
  - intros [a p].
    apply (path_sigma' _ (eissect f _)); simpl.
    lhs_V rapply (ap_transport _ (fun a' => (g a') ^-1) _).
    lhs napply (ap _ (transport_compose _ _ _ _)).
    lhs_V napply (ap (fun x => (g _)^-1 (transport Q x _)) (eisadj f _)).
    lhs napply (ap _ (transport_pV _ _ _)).
    apply eissect.
Defined.

Definition equiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) `{IsEquiv A B f}
  (g : forall a, P a -> Q (f a))
  `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
  : sig P <~> sig Q
  := Build_Equiv _ _ (functor_sigma f g) _.

Definition equiv_functor_sigma' `{P : A -> Type} `{Q : B -> Type}
  (f : A <~> B)
  (g : forall a, P a <~> Q (f a))
  : sig P <~> sig Q
  := equiv_functor_sigma f g.

Definition equiv_functor_sigma_id `{P : A -> Type} `{Q : A -> Type}
  (g : forall a, P a <~> Q a)
  : sig P <~> sig Q
  := equiv_functor_sigma' 1 g.

Definition equiv_functor_sigma_pb {A B : Type} {Q : B -> Type}
  (f : A <~> B)
  : sig (Q o f) <~> sig Q
  := equiv_functor_sigma f (fun a => 1%equiv).

(** ** Functoriality on logical equivalences *)

(** At least over a fixed base *)
Definition iff_functor_sigma {A : Type} {P Q : A -> Type}
           (f : forall a, P a <-> Q a)
  : sig P <-> sig Q
  := (functor_sigma idmap (fun a => fst (f a)),
    functor_sigma idmap (fun a => snd (f a))).

(** Lemma 3.11.9(i): Summing up a contractible family of types does nothing. *)
Instance isequiv_pr1_contr {A} {P : A -> Type}
  `{forall a, Contr (P a)}
  : IsEquiv (@pr1 A P) | 100.
Proof.
  refine (isequiv_adjointify (@pr1 A P)
                             (fun a => (a ; center (P a))) _ _).
  - intros a; reflexivity.
  - intros [a p].
    exact (path_sigma' P 1 (contr _)).
Defined.

Definition equiv_sigma_contr {A : Type} (P : A -> Type)
  `{forall a, Contr (P a)}
  : sig P <~> A
  := Build_Equiv _ _ pr1 _.

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

(** All of the following lemmas are proven easily with the [make_equiv] tactic.  If you have a more complicated rearrangement of sigma-types to do, it is usually possible to do it by putting together these equivalences, but it is often simpler and faster to just use [make_equiv] directly. *)

Definition equiv_sigma_assoc `(P : A -> Type) (Q : {a : A & P a} -> Type)
  : {a : A & {p : P a & Q (a;p)}} <~> sig Q.
Proof.
  make_equiv.
Defined.

Definition equiv_sigma_assoc' `(P : A -> Type) (Q : forall a : A, P a -> Type)
  : {a : A & {p : P a & Q a p}} <~> {ap : sig P & Q ap.1 ap.2}.
Proof.
  make_equiv.
Defined.

Definition equiv_sigma_prod `(Q : (A * B) -> Type)
  : {a : A & {b : B & Q (a,b)}} <~> sig Q.
Proof.
  make_equiv.
Defined.

Definition equiv_sigma_prod' `(Q : A -> B -> Type)
  : {a : A & {b : B & Q a b}} <~> sig (fun ab => Q (fst ab) (snd ab)).
Proof.
  make_equiv.
Defined.

Definition equiv_sigma_prod0 (A B : Type)
  : {a : A & B} <~> A * B.
Proof.
  make_equiv.
Defined.

Definition equiv_sigma_prod1 (A B C : Type)
  : {a : A & {b : B & C}} <~> A * B * C
  := ltac:(make_equiv).

Definition equiv_sigma_prod_prod {X Y : Type} (P : X -> Type) (Q : Y -> Type)
  : {z : X * Y & (P (fst z)) * (Q (snd z))} <~> (sig P) * (sig Q)
  := ltac:(make_equiv).

(** ** Symmetry *)

Definition equiv_sigma_symm `(P : A -> B -> Type)
  : {a : A & {b : B & P a b}} <~> {b : B & {a : A & P a b}}.
Proof.
  make_equiv.
Defined.

Definition equiv_sigma_symm' {A : Type} `(P : A -> Type) `(Q : A -> Type)
  : { ap : { a : A & P a } & Q ap.1 } <~> { aq : { a : A & Q a } & P aq.1 }.
Proof.
  make_equiv.
Defined.

Definition equiv_sigma_symm0 (A B : Type)
: {a : A & B} <~> {b : B & A}.
Proof.
  make_equiv.
Defined.

(** ** Universal mapping properties *)

(** *** The positive universal property. *)
Instance isequiv_sig_ind `{P : A -> Type} (Q : sig P -> Type)
  : IsEquiv (sig_ind Q) | 0
  := Build_IsEquiv
       _ _
       (sig_ind Q)
       (fun f x y => f (x;y))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_sig_ind `{P : A -> Type} (Q : sig P -> Type)
  : (forall (x:A) (y:P x), Q (x;y)) <~> (forall xy, Q xy)
  := Build_Equiv _ _ (sig_ind Q) _.

(** And a curried version *)
Definition equiv_sig_ind' `{P : A -> Type} (Q : forall a, P a -> Type)
  : (forall (x:A) (y:P x), Q x y) <~> (forall xy, Q xy.1 xy.2)
  := equiv_sig_ind (fun xy => Q xy.1 xy.2).

(** *** The negative universal property. *)

Definition sig_coind_uncurried
  `{A : X -> Type} (P : forall x, A x -> Type)
  : { f : forall x, A x & forall x, P x (f x) }
    -> (forall x, sig (P x))
  := fun fg => fun x => (fg.1 x ; fg.2 x).

Definition sig_coind
  `{A : X -> Type} (P : forall x, A x -> Type)
  (f : forall x, A x) (g : forall x, P x (f x))
  : (forall x, sig (P x))
  := sig_coind_uncurried P (f;g).

Instance isequiv_sig_coind
  `{A : X -> Type} {P : forall x, A x -> Type}
  : IsEquiv (sig_coind_uncurried P) | 0
  := Build_IsEquiv
       _ _
       (sig_coind_uncurried P)
       (fun h => exist (fun f => forall x, P x (f x))
                        (fun x => (h x).1)
                        (fun x => (h x).2))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_sig_coind
  `(A : X -> Type) (P : forall x, A x -> Type)
  : { f : forall x, A x & forall x, P x (f x) }
      <~> (forall x, sig (P x))
  := Build_Equiv _ _ (sig_coind_uncurried P) _.

(** ** Sigmas preserve truncation *)

Instance istrunc_sigma `{P : A -> Type}
  `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (sig P) | 100.
Proof.
  generalize dependent A.
  simple_induction' n; simpl; intros A P ac Pc.
  { apply (Build_Contr _ (center A; center (P (center A)))).
    intros [a ?].
    exact (path_sigma' P (contr a) (path_contr _ _)). }
  apply istrunc_S.
  intros u v.
  exact (istrunc_isequiv_istrunc _ (path_sigma_uncurried P u v)).
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
  (u v : sig P)
  : u.1 = v.1 -> u = v
  := path_sigma_uncurried P u v o pr1^-1.

Instance isequiv_path_sigma_hprop {A P} `{forall x : A, IsHProp (P x)} {u v : sig P}
  : IsEquiv (@path_sigma_hprop A P _ u v) | 100
  := isequiv_compose _ _.

#[export]
Hint Immediate isequiv_path_sigma_hprop : typeclass_instances.

Definition equiv_path_sigma_hprop {A : Type} {P : A -> Type}
  {HP : forall a, IsHProp (P a)} (u v : sig P)
  : (u.1 = v.1) <~> (u = v)
  := Build_Equiv _ _ (path_sigma_hprop _ _) _.

Definition isequiv_pr1_path_hprop {A} {P : A -> Type}
  `{forall a, IsHProp (P a)} (x y : sig P)
  : IsEquiv (@pr1_path A P x y)
  := _ : IsEquiv (path_sigma_hprop x y)^-1.

#[export]
Hint Immediate isequiv_pr1_path_hprop : typeclass_instances.

(** We define this for ease of [SearchAbout IsEquiv ap pr1] *)
Definition isequiv_ap_pr1_hprop {A} {P : A -> Type}
  `{forall a, IsHProp (P a)} (x y : sig P)
  : IsEquiv (@ap _ _ (@pr1 A P) x y)
  := _.

(** [path_sigma_hprop] is functorial *)
Definition path_sigma_hprop_1 {A : Type} {P : A -> Type}
  `{forall x, IsHProp (P x)} (u : sig P)
  : path_sigma_hprop u u 1 = 1.
Proof.
  unfold path_sigma_hprop.
  unfold isequiv_pr1_contr; simpl.
  (** Ugh *)
  exact (ap (fun p => match p in (_ = v2) return (u = (u.1; v2)) with 1 => 1 end)
             (contr (idpath u.2))).
Defined.

Definition path_sigma_hprop_V {A : Type} {P : A -> Type}
  `{forall x, IsHProp (P x)} {a b : A} (p : a = b)
  (x : P a) (y : P b)
  : path_sigma_hprop (b;y) (a;x) p^ = (path_sigma_hprop (a;x) (b;y) p)^.
Proof.
  destruct p; simpl.
  rewrite (path_ishprop x y).
  exact (path_sigma_hprop_1 _ @ (ap inverse (path_sigma_hprop_1 _))^).
Qed.

Definition path_sigma_hprop_pp {A : Type} {P : A -> Type}
  `{forall x, IsHProp (P x)}
  {a b c : A}
  (p : a = b) (q : b = c)
  (x : P a) (y : P b) (z : P c)
  : path_sigma_hprop (a;x) (c;z) (p @ q)
    = path_sigma_hprop (a;x) (b;y) p @ path_sigma_hprop (b;y) (c;z) q.
Proof.
  destruct p, q.
  rewrite (path_ishprop y x).
  rewrite (path_ishprop z x).
  refine (_ @ (ap (fun z => z @ _) (path_sigma_hprop_1 _))^).
  exact (concat_1p _)^.
Qed.

(** The inverse of [path_sigma_hprop] has its own name, so we give special names to the section and retraction homotopies to help [rewrite] out. *)
Definition path_sigma_hprop_ap_pr1 {A : Type} {P : A -> Type}
  `{forall x, IsHProp (P x)} (u v : sig P) (p : u = v)
  : path_sigma_hprop u v (ap pr1 p) = p
  := eisretr (path_sigma_hprop u v) p.

Definition path_sigma_hprop_pr1_path {A : Type} {P : A -> Type}
  `{forall x, IsHProp (P x)} (u v : sig P) (p : u = v)
  : path_sigma_hprop u v p..1 = p
  := eisretr (path_sigma_hprop u v) p.

Definition ap_pr1_path_sigma_hprop {A : Type} {P : A -> Type}
  `{forall x, IsHProp (P x)} (u v : sig P) (p : u.1 = v.1)
  : ap pr1 (path_sigma_hprop u v p) = p
  := eissect (path_sigma_hprop u v) p.

Definition pr1_path_path_sigma_hprop {A : Type} {P : A -> Type}
  `{forall x, IsHProp (P x)} (u v : sig P) (p : u.1 = v.1)
  : (path_sigma_hprop u v p)..1 = p
  := eissect (path_sigma_hprop u v) p.

(** ** Fibers of [functor_sigma] *)
Definition hfiber_functor_sigma {A B} (P : A -> Type) (Q : B -> Type)
  (f : A -> B) (g : forall a, P a -> Q (f a))
  (b : B) (v : Q b)
  : (hfiber (functor_sigma f g) (b; v)) <~>
      {w : hfiber f b & hfiber (g w.1) ((w.2)^ # v)}.
Proof.
  unfold hfiber, functor_sigma.
  refine (_ oE equiv_functor_sigma_id _).
  2:intros; symmetry; apply equiv_path_sigma.
  transitivity {w : {x : A & f x = b} & {x : P w.1 & (w.2) # (g w.1 x) = v}}.
  1:make_equiv.
  apply equiv_functor_sigma_id; intros [a p]; simpl.
  apply equiv_functor_sigma_id; intros u; simpl.
  apply equiv_moveL_transport_V.
Defined.

Instance istruncmap_functor_sigma n {A B P Q}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  {Hf : IsTruncMap n f} {Hg : forall a, IsTruncMap n (g a)}
  : IsTruncMap n (functor_sigma f g).
Proof.
  intros [a b].
  exact (istrunc_equiv_istrunc _ (hfiber_functor_sigma _ _ _ _ _ _)^-1).
Defined.

(** Theorem 4.7.6 *)
Definition hfiber_functor_sigma_idmap {A} (P Q : A -> Type)
  (g : forall a, P a -> Q a)
  (b : A) (v : Q b)
  : (hfiber (functor_sigma idmap g) (b; v))
      <~> hfiber (g b) v.
Proof.
  refine (_ oE hfiber_functor_sigma P Q idmap g b v).
  exact (equiv_contr_sigma
           (fun (w:hfiber idmap b) => hfiber (g w.1) (transport Q (w.2)^ v))).
Defined.

Definition istruncmap_from_functor_sigma n {A P Q}
  (g : forall a : A, P a -> Q a)
  `{!IsTruncMap n (functor_sigma idmap g)}
  : forall a, IsTruncMap n (g a).
Proof.
  intros a v.
  exact (istrunc_equiv_istrunc _ (hfiber_functor_sigma_idmap _ _ _ _ _)).
Defined.
