(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Sigma-types (dependent sums) *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x y] in Coq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [(x;y)] to mean [existT _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [projT1] and [projT2]. *)

(** *** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a pair [(projT1 u ; projT2 u)]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_sigma {A : Type} {P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (projT1 u; projT2 u) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (projT1 u; projT2 u) -> Q u) := u in idmap) H.

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

(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of dependent sum types.  But it has the advantage that the components of those pairs can more often be inferred. *)
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
  (p : x = x') (q : p # y = y')
  : (x;y) = (x';y')
  := path_sigma P (x;y) (x';y') p q.


(** Projections of paths from a total space. *)

Definition path_projT1 {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v) :
  projT1 u = projT1 v
  :=
  ap (@projT1 _ _) p.
  (* match p with idpath => 1 end. *)

Definition path_projT2 {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v) :
  path_projT1 p # projT2 u = projT2 v
  :=
  match p with idpath => 1 end.


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

(* Lemma base_total_path {A : Type} {P : fibration A} {x y : total P} *)
(*   {p : pr1 x = pr1 y} (q : p # (pr2 x) = pr2 y) : *)
(*   (base_path (total_path q)) = p. *)
(* Proof. *)
(*   destruct x as [x H]. destruct y as [y K]. *)
(*   simpl in p. induction p. simpl in q. induction q. *)
(*   auto. *)
(* Defined. *)

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

(** *** Equivalences *)

(** *** H-Level *)

(*
(** Props are closed under sums (with prop base) and arbitrary
   dependent products. *)

Definition sum_isprop X (P : X -> Type) :
  is_prop X -> (forall x, is_prop (P x)) -> is_prop (sigT P).
Proof.
  intros Xp Pp.
  apply allpath_prop.
  intros [x p] [y q].
  apply @total_path with (prop_path Xp x y).
  apply prop_path, Pp.
Defined.
*)

(** And by dependent sums *)

(*
Definition total_hlevel: forall n A (P : A -> Type),
  is_hlevel n A -> (forall a, is_hlevel n (P a)) ->
  is_hlevel n (sigT P).
Proof.
  intros n; induction n.
  intros A P [a ac] Pc.
  exists (a; pr1 (Pc a)).
  intros [a' p'].
  apply @total_path with (ac a').
  apply contr_path; apply (Pc a).
  intros A P Ah Ph [a1 p1] [a2 p2].
  apply @hlevel_equiv with
    (A := {p : a1 = a2 & transport p p1 = p2}).
  apply equiv_inverse, total_paths_equiv.
  apply IHn.
  apply Ah.
  intros p; apply (Ph a2).
Defined.

*)