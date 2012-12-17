(** * Basic facts about fibrations *)

Require Import Paths.

Import PathNotations.
Local Open Scope path_scope.

(** Notes from discussion between AB & PL, 14 Dec: this file includes several
things that don’t really belong together: material on sigma-types (with hfiber as
an example); and material on transport.  So this file should be probably be reborn 
as Sigma.v, (possibly also HFiber.v), and Transport.v, and the transport lemmas
given more systematically.

Sigmas: the utility lemmas for assuming an element of a sigma-type is a pair by
replacing it with is projections; and theorems relating to paths in a sigma-type.
(Note that both of these are things which in principle generalise to other
inductive types.)

Transport: the transport lemmas are two main groups: firstly, interaction with the
groupoid structure; secondly, what precisely transport becomes in various fibrations. 

For now, we keep it in one file, but segregated into sections.  Todo: split the file?*)

(** There are a number of notations for operations involving fibrations (e.g. [p # x] 
for transport) which hide the fibration involved.  These are very readable
when they work, but often (especially in applications) don’t work, in that Coq cannot
infer the fibration from the rest.  We therefore put them in their own scope so that
they can be turned on and off as required. *)
Delimit Scope fib_scope with fib.


Section Transport.
(** ** Transport.

  We now study how dependent types interact with paths in their base.
  The fundamental fact is that we can transport elements of the fibers along such paths.

  This operation is very frequently used; so we need also to know how it interacts
  with operations on paths in the base, and also how it interacts with the standard
  constructions for forming dependent types. *)

(** [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with identity_refl => u end.

Arguments transport {A} P {x y} p%fib_scope u.

(** Transport is very common so it is worth introducing a parsing notation
for it.  However, we do not use the notation for output because it hides the
fibration, and so makes it very hard to read involved transport expression.*)
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

(** Having defined transport, we can talk about what a homotopy theorist
might see as “paths in a fibration over paths in the base”; and what a type
theorist might see as “heterogeneous eqality in a dependent type”.

  In particular, this allows us to define an analogue of [ap] for dependent functions. *)

Definition ap_dep {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with identity_refl => 1 end.

(** *** Transport and the groupoid structure of paths *)

(** Basic results on how transport interacts with the groupoid structure of paths. 

Todo: after some experience working with these, reconsider whether making
[P] implicit was a good idea.  (It needs to be explicit in transport, but may not need to be in these.) *)
Definition transport_1 {A : Type} {P : A -> Type} {x : A} (u : P x)
  : 1 # u = u
:= 1.

Definition transport_pp {A : Type} {P : A -> Type} {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with identity_refl =>
    match p with identity_refl => 1 end
  end.

(** Todo: the following two results follow directly from [transport_1] and
  [transport_pp].  Is it really necessary to give them separately. *)
Definition transport_pV {A : Type} {P : A -> Type} {x y : A} (p : x = y) (z : P y) :
  p # p^-1 # z = z :=
  (match p as i in (_ = y) return (forall z : P y, i # i^-1 # z = z)
     with identity_refl => fun _ => 1
   end) z.

Definition transport_V_p {A : Type} {P : A -> Type} {x y : A} (p : x = y) (z : P x) :
  p^-1 # p # z = z
  := 
  (match p as i return (forall z : P x, i^-1 # i # z = z)
     with identity_refl => fun _ => 1
   end) z.

(** In the future, we may expect to need some higher coherence for transport:
  for instance, that transport acting on the associator is trivial. *)
Definition transport_p_pp {A : Type} {P : A -> Type} 
  {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  (u : P x)
  : ap (fun e => e # u) (concat_p_pp p q r)
    @ (transport_pp (p@q) r u) @ ap (transport P r) (transport_pp p q u)
  = (transport_pp p (q@r) u) @ (transport_pp q r (p#u))
  :> ((p @ (q @ r)) # u = r # q # p # u) .
Proof.
  destruct p, q, r.  simpl.  exact 1.
Defined.

(** *** Transport in specific dependent types *)

(** Transport crops up very frequently, whether one wants it or not;
  so one frequently needs lemmas showing that transport in a certain 
  dependent type is equal to some more explicitly defined operation,
  defined according to the structure of that dependent type. *)

Definition transport_const {A B:Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.  exact 1.
Defined.

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^-1 @ q.
Proof.
  destruct p, q.  auto.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q.  auto.
Defined.

Definition transport_prod {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : (B x1) * (C x1))
  : transport (fun x => (B x) * (C x)) p yz
    = ((p # fst yz), (p # snd yz)). 
Proof.
  destruct p.  destruct yz as [y z].  exact 1.
Defined.

(* Note: conclusion should be [==] if that is defined in an earlier file. *) 
Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1)
  : forall y : B x2,
    (transport (fun x => B x -> C x) p f) y
    = p # (f (p^-1 # y)).
Proof.
  destruct p.  simpl.  auto.
Defined.

(** The concrete description of transport in sigmas and pis is rather
  trickier than in the other types.  In particular, these cannot be described
  just in terms of transport in simpler types; they require the full Id-elim
  rule, to construct “dependent transport”.

  In particular this indicates why “transport” alone cannot be fully defined
  by induction on the structure of types, although Id-elim/transport_dep
  can be (cf. Observational Type Theory).  A more thorough set of lemmas,
  along the lines of the present ones but dealing with Id-elim rather than
  just transport, might be nice to have eventually? *)
Definition transport_dep
  {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y) :
  C x2 (p # y)
  :=
  match p with identity_refl => z end.

(* Note: if notation [(x;y)] is available here, this should use it. *)
Definition transport_sigma
  {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y }) 
  : transport (fun x => { y : B x & C x y }) p yz
    = existT _ (p # (projT1 yz)) (transport_dep _ _ p (projT1 yz) (projT2 yz)).
Proof.
  destruct p.  destruct yz as [y z].  exact 1.
Defined.

Lemma transport_forall_unwound
  {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B x1, C x1 y) 
  : forall y : B x2, C x2 y.
Proof.
  intro y.
  pose (z0 := f (p^-1 # y)).
  pose (z1 := transport_dep _ _ p _ z0).
  apply (fun p => transport (C x2) p z1).
  path_via (transport B (p^-1 @ p) y).
    symmetry.  apply transport_pp.  
    apply (fun e => @ap (x2=x2) (B x2) (fun q => transport B q y) 
                      (p^-1 @ p) 1e).
  apply concat_Vp.
Defined.

(* Note: conclusion should be [==] if that is defined in an earlier file. *) 
Definition transport_forall
  {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B x1, C x1 y) 
  : forall y : B x2,
    (transport (fun x => forall y:B x, C x y) p f) y
  = (transport_forall_unwound p f) y.
Proof.
  destruct p.  auto.
Defined.

End Transport.

(** Temporarily commented out:

Section Sigmas.

(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or
   weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose
   base is [A] and whose fiber over [x] is [P x].

   From such a [P] we can build a total space over the base space [A] so that the fiber
   over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT
   P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x
   y] in Coq, where [x : A] and [y : P x].

   The base and fiber components of a point in the total space are extracted with the two
   projections [projT1] and [projT2].

   We define notation for dependent pairs because it is too annoying to write
   [existT P x y] all the time. *)

Notation "( x ; y )" := (existT _ x y) : path_scope.

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a
    pair [(projT1 u ; projT2 u)]. This is accomplished by [sigT_eta]. We want tight
    control over the proof, so we just write it down even though is looks a bit scary. *)
Definition sigT_unpack {A : Type} {P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (projT1 u; projT2 u) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (projT1 u; projT2 u) -> Q u) := u in idmap) H.

(** The space of sections of a fibration. *)
(* Todo: possibly eliminate this?? *)
Definition section {A} (P : A -> Type) := forall x : A, P x.

End Sigmas.

(* *** Homotopy fibers *)

(** Homotopy fibers are homotopical inverse images of points.  *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

(** A path in a total space is commonly shown component wise. Because we
    use this over and over, we write down the proofs by hand to make sure
    they are what we think they should be. *)

Definition sigT_path_unpacked {A : Type} (P : A -> Type) {x y : A} {u : P x} {v : P y} (p : x = y) (q : p # u = v) :
  (x ; u) = (y ; v)
  :=
  (match p as i in (_ = y) return (forall v : P y, i # u = v -> (x; u) = (y; v)) with
     identity_refl =>
       fun _ q => match q with identity_refl => 1 end
  end) v q.

Definition sigT_path {A : Type} (P : A -> Type) {u v : sigT P} (p : projT1 u = projT1 v) (q : p # projT2 u = projT2 v) :
  u = v :=
  sigT_unpack _ v
    (sigT_unpack (fun w => w = (projT1 v; projT2 v)) u
      (sigT_path_unpacked P p q)).

(** Projections of paths from a total space. *)

Definition path_projT1 {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v) :
  projT1 u = projT1 v
  :=
  match p with identity_refl => 1 end.

Definition path_projT2 {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v) :
  path_projT1 p # projT2 u = projT2 v
  :=
  match p with identity_refl => 1 end.

(** TEMPORARILY COMMENTED OUT. *)

(* (** And these operations are inverses.  See [total_paths_equiv], later *)
(*    on, for a more precise statement. *) *)

(* Lemma total_path_reconstruction {A : Type} {P : fibration A} {x y : total P} (p : x = y) : *)
(*   total_path (fiber_path p) = p. *)
(* Proof. *)
(*   induction p. *)
(*   destruct x. *)
(*   auto. *)
(* Defined. *)

(* Hint Rewrite @total_path_reconstruction : paths. *)

(* Lemma base_total_path {A : Type} {P : fibration A} {x y : total P} *)
(*   {p : pr1 x = pr1 y} (q : p # (pr2 x) = pr2 y) : *)
(*   (base_path (total_path q)) = p. *)
(* Proof. *)
(*   destruct x as [x H]. destruct y as [y K]. *)
(*   simpl in p. induction p. simpl in q. induction q. *)
(*   auto. *)
(* Defined. *)

(* Hint Rewrite @base_total_path : paths. *)

(* Lemma fiber_total_path (A : Type) (P : fibration A) (x y : total P) *)
(*   (p : pr1 x = pr1 y) (q : transport p (pr2 x) = pr2 y) : *)
(*   transport (P := fun p' : pr1 x = pr1 y => p' # (pr2 x) = pr2 y) *)
(*   (base_total_path q) (fiber_path (total_path q)) *)
(*   = q. *)
(* Proof. *)
(*   destruct x as [x H]. destruct y as [y K]. *)
(*   simpl in p. induction p. simpl in q. induction q. *)
(*   auto. *)
(* Defined. *)

(* Hint Rewrite fiber_total_path : paths. *)

(* (** This lemma tells us how to extract a commutative triangle in the *)
(*    base from a path in the homotopy fiber. *) *)

(* Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x = y) : *)
(*   (map f (base_path p)) @ (pr2 y) = (pr2 x). *)
(* Proof. *)
(*   induction p. *)
(*   hott_simpl. *)
(* Defined. *)

(* Hint Rewrite @hfiber_triangle : paths. *)

(* (** Transporting a path along another path is equivalent to *)
(*    concatenating the two paths. *) *)

(* Lemma trans_is_concat {A} {x y z : A} (p : x = y) (q : y = z) : *)
(*   q # p = p @ q. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* (** XXX This seems to violate the well-order described in Paths.v *)
(*     that guarantees termination of autorewriting with the [path] hints. *) *)
(* Hint Rewrite @trans_is_concat: paths. *)

(* (* This is also a special case of [transport_hfiber]. *) *)
(* Lemma trans_is_concat_opp {A} {x y z : A} (p : x = y) (q : x = z) : *)
(*   (transport (P := fun x' => (x' = z)) p q) = !p @ q. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* (** XXX This seems to violate the well-order described in Paths.v *)
(*     that guarantees termination of autorewriting with the [path] hints. *) *)
(* Hint Rewrite @trans_is_concat_opp: paths. *)

(* (** Transporting commutes with pulling back along a map. *) *)

(* Lemma map_trans {A B} {x y : A} (P : B -> Type) (f : A -> B) (p : x = y) (z : P (f x)) : *)
(*  (transport (P := (fun x => P (f x))) p z) = map f p # z. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* (** XXX This seems to violate the well-order described in Paths.v *)
(*     that guarantees termination of autorewriting with the [path] hints. *) *)
(* (* Hint Rewrite @map_trans : paths. *) *)

(* (** And also with applying fiberwise functions. *) *)

(* Lemma trans_map {A} {P Q : fibration A} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) : *)
(*   f y (p # z) = p # f x z. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Lemma trans_map2 {A} {P Q R : fibration A} {x y : A} (p : x = y) *)
(*   (f : forall x, P x -> Q x -> R x) (z : P x) (w: Q x) : *)
(*   f y (p # z) (p # w) = p # f x z w. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* (** A version of [map] for dependent functions. *) *)

(* Lemma map_dep {A} {P : fibration A} {x y : A} (f : section P) (p: x = y) : *)
(*   p # f x = f y. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Hint Rewrite @map_dep : paths. *)

(* (** Transporting in a non-dependent type does nothing. *) *)

(* Lemma trans_trivial {A B : Type} {x y : A} (p : x = y) (z : B) : *)
(*   transport (P := fun _ => B) p z = z. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Hint Rewrite @trans_trivial : paths. *)

(* (** And for a non-dependent type, [map_dep] reduces to [map], modulo [trans_trivial]. *) *)

(* Lemma map_dep_trivial {A B} {x y : A} (f : A -> B) (p: x = y): *)
(*   map_dep f p = trans_trivial p (f x) @ map f p.  *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Hint Rewrite @map_dep_trivial : paths. *)

(* (** Transporting commutes with summing along an unrelated variable. *) *)

(* Definition trans_sum A B (P : A -> B -> Type) *)
(*   (x y : A) (p : x = y) (z : B) (w : P x z) : *)
(*   transport (P := fun a => sigT (P a)) p (z ; w) = *)
(*   (z ; transport (P := fun a => P a z) p w). *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Hint Rewrite @trans_sum : paths. *)

(* (** And with taking fiberwise products. *) *)

(* Definition trans_prod A (P Q : fibration A) (x y : A) (p : x = y) (z : P x) (w : Q x) : *)
(*   transport (P := fun a => (P a * Q a)%type) p (z , w) = *)
(*   (p # z , p # w). *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Hint Rewrite @trans_prod : paths. *)

(* (** The action of map on a function of two variables, one dependent on the other. *) *)

(* Lemma map_twovar {A : Type} {P : fibration A} {B : Type} {x y : A} {a : P x} {b : P y} *)
(*   (f : forall x : A, P x -> B) (p : x = y) (q : p # a = b) : *)
(*   f x a = f y b. *)
(* Proof. *)
(*   induction p. *)
(*   simpl in q. *)
(*   induction q. *)
(*   apply idpath. *)
(* Defined. *)

(* (** 2-Paths in a total space. *) *)

(* Lemma total_path2 (A : Type) (P : fibration A) (x y : total P) *)
(*   (p q : x = y) (r : base_path p = base_path q) : *)
(*   (transport (P := fun s => s # pr2 x = pr2 y) r (fiber_path p) = fiber_path q) -> (p = q). *)
(* Proof. *)
(*   intro H. *)
(*   path_via (total_path (fiber_path p)) ; *)
(*   [ apply opposite, total_path_reconstruction | ]. *)
(*   path_via (total_path (fiber_path q)) ; *)
(*   [ | apply total_path_reconstruction ]. *)
(*   apply @map_twovar with *)
(*     (f := @total_path A P x y) *)
(*     (p := r). *)
(*   assumption. *)
(* Defined. *)

(* (** Transporting along a path between paths. *) *)

(* Definition trans2 {A : Type} {P : fibration A} {x y : A} {p q : x = y} *)
(*   (r : p = q) (z : P x) : *)
(*   p # z = q # z *)
(*   := map (fun p' => p' # z) r. *)

(* (** An alternative definition. *) *)
(* Lemma trans2_is_happly {A : Type} {Q : fibration A} {x y : A} {p q : x = y} *)
(*   (r : p = q) (z : Q x) : *)
(*   trans2 r z = happly (map transport r) z. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Lemma trans2_opp {A : Type} {Q : fibration A} {x y : A} {p q : x = y} *)
(*   (r : p = q) (z : Q x) : *)
(*   trans2 (!r) z = !trans2 r z. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Lemma trans2_naturality {A : Type} {P : fibration A} {x y : A} {p q : x = y} *)
(*   {z w : P x} (r : p = q) (s : z = w) : *)
(*   map (transport p) s @ trans2 r w = trans2 r z @ map (transport q) s. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Lemma trans2_trivial {A B : Type} {x y : A} {p q : x = y} *)
(*   (r : p = q) (z : B) : *)
(*   trans_trivial p z = trans2 (P := fun _ => B) r z @ trans_trivial q z. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* Lemma trans_trans_opp2 A P (x y : A) (p q : x = y) (r : p = q) (z : P y) : *)
(*   trans_trans_opp p z = *)
(*   map (transport p) (trans2 (opposite2 r) z) *)
(*   @ trans2 r (!q #  z) *)
(*   @ trans_trans_opp q z. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* (** Transporting in an iterated fibration. *) *)

(* Definition trans_trans {A} {P : fibration A} *)
(*   {Q : forall a, fibration (P a)} *)
(*   {a1 a2 : A} (s : a1 = a2) {p1 : P a1} : *)
(*   Q a1 p1 -> Q a2 (s # p1). *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)

(* (** Transporting in a fibration of paths. *) *)

(* Lemma trans_paths A B (f g : A -> B) (x y : A) (p : x = y) (q : f x = g x) : *)
(*   transport (P := fun a => f a = g a) p q *)
(*   = *)
(*   !map f p @ q @ map g p. *)
(* Proof. *)
(*   path_induction. *)
(*   hott_simpl. *)
(* Defined. *)

(* (** A dependent version of [map2]. *) *)

(* Lemma map2_dep {A : Type} {P : fibration A} {x y : A} {p q : x = y} *)
(*   (f : section P) (r : p = q) : *)
(*   map_dep f p = trans2 r (f x) @ map_dep f q. *)
(* Proof. *)
(*   path_induction. *)
(* Defined. *)
*)