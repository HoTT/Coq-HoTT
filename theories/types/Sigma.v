(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about Sigma-types (dependent sums) *)

Require Import Common Paths Contractible Equivalences.
Open Scope path_scope.
Open Scope equiv_scope.

(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

   From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x y] in Coq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [(x;y)] to mean [existT _ x y].

   The base and fiber components of a point in the total space are extracted with the two projections [projT1] and [projT2]. *)

(** *** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a pair [(projT1 u ; projT2 u)]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition sigT_unpack {A : Type} {P : A -> Type} (Q : sigT P -> Type) (u : sigT P) :
  Q (projT1 u; projT2 u) -> Q u
  :=
  fun H =>
    (let (x,p) as u return (Q (projT1 u; projT2 u) -> Q u) := u in idmap) H.

(** *** Paths *)

(** A path in a total space is commonly shown component wise. Because we use this over and over, we write down the proofs by hand to make sure they are what we think they should be. *)

Definition sigT_path_unpacked {A : Type} (P : A -> Type) {x y : A}
  {u : P x} {v : P y} (p : x = y) (q : p # u = v)
  : (x ; u) = (y ; v)
  :=
  (match p as i in (_ = y) return (forall v : P y, i # u = v -> (x; u) = (y; v)) with
     idpath =>
       fun _ q => match q with idpath => 1 end
  end) v q.

Definition sigT_path {A : Type} (P : A -> Type) {u v : sigT P}
  (p : projT1 u = projT1 v) (q : p # projT2 u = projT2 v)
  : u = v
  := sigT_unpack _ v
      (sigT_unpack (fun w => w = (projT1 v; projT2 v)) u
        (sigT_path_unpacked P p q)).

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

(** *** H-Level *)

(** *** Functorial action *)

(** *** Equivalences *)

