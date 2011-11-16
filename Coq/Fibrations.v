Require Export Paths.

(** In homotopy type theory, We think of elements of [Type] as spaces
   or homotopy types, while a type family [P : A -> Type] corresponds
   to a fibration whose base is [A] and whose fiber over [x] is [P x].

   From such a [P] we can build a total space over the base space [A]
   so that the fiber over [x : A] is [P x].  This is just Coq's
   dependent sum construction, written as [{x : A & P x}].  The
   elements of [{x : A & P x}] are pairs, written [existT P x y] in
   Coq, where [x : A] and [y : P x].

   The primitive notation for dependent sum is [sigT P].  Note,
   though, that in the absence of definitional eta expansion, this is
   not actually identical with [{x : A & P x}], since the latter
   desugars to [sigT (fun x => P x)].
   
   Finally, the base and fiber components of a point in the total
   space are extracted with [projT1] and [projT2]. *)
   
(** We can also define more familiar homotopy-looking aliases for all
   of these functions. *)

Notation total := sigT.
Notation tpair := (@existT _ _).
Notation pr1 := (@projT1 _ _).
Notation pr2 := (@projT2 _ _).

(** An element of [section P] is a global section of fibration [P]. *)

Definition section {A} (P : A -> Type) := forall x : A, P x.

(** We now study how paths interact with fibrations.  The most basic
   fact is that we can transport points in the fibers along paths in
   the base space.  This is actually a special case of the
   [paths_rect] induction principle in which the fibration [P] does
   not depend on paths in the base space but rather just on points of
   the base space. *)

Theorem transport {A} {P : A -> Type} {x y : A} (p : x ~~> y) : P x -> P y.
Proof.
  path_induction.
Defined.

(** A homotopy fiber for a map [f] at [y] is the space of paths of the
   form [f x ~~> y].
   *)

Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x ~~> y}.

(** We prove a lemma that explains how to transport a point in the
   homotopy fiber along a path in the domain of the map. *)

Lemma transport_hfiber A B (f : A -> B) (x y : A) (z : B) (p : x ~~> y) (q : f x ~~> z) :
  transport (P := fun x => f x ~~> z) p q ~~> !(map f p) @ q.
Proof.
  induction p.
  cancel_units.
Defined.

(** The following lemma tells us how to construct a path in the total space from
   a path in the base space and a path in the fiber. *)

Lemma total_path (A : Type) (P : A -> Type) (x y : sigT P) (p : projT1 x ~~> projT1 y) :
  (transport p (projT2 x) ~~> projT2 y) -> (x ~~> y).
Proof.
  intros q.
  destruct x as [x H].
  destruct y as [y G].
  simpl in * |- *.
  induction p.
  simpl in q.
  path_induction.
Defined.

(** Conversely, a path in the total space can be projected down to the base. *)

Definition base_path {A} {P : A -> Type} {u v : sigT P} :
  (u ~~> v) -> (projT1 u ~~> projT1 v) :=
  map pr1.

(** And similarly to the fiber.  *)

Definition fiber_path {A} {P : A -> Type} {u v : sigT P}
  (p : u ~~> v) : (transport (map pr1 p) (projT2 u) ~~> projT2 v).
Proof.
  path_induction.
Defined.

(** And these operations are inverses.  See [total_paths_equiv], later
   on, for a more precise statement. *)

Lemma total_path_reconstruction (A : Type) (P : A -> Type) (x y : sigT P) (p : x ~~> y) :
  total_path A P x y (base_path p) (fiber_path p) ~~> p.
Proof.
  induction p.
  induction x. 
  auto.
Defined.

Lemma base_total_path (A : Type) (P : A -> Type) (x y : sigT P)
  (p : projT1 x ~~> projT1 y) (q : transport p (projT2 x) ~~> projT2 y) :
  (base_path (total_path A P x y p q)) ~~> p.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  auto.
Defined.

Lemma fiber_total_path (A : Type) (P : A -> Type) (x y : sigT P)
  (p : projT1 x ~~> projT1 y) (q : transport p (projT2 x) ~~> projT2 y) :
  transport (P := fun p' : pr1 x ~~> pr1 y => transport p' (pr2 x) ~~> pr2 y)
  (base_total_path A P x y p q) (fiber_path (total_path A P x y p q))
  ~~> q.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  auto.
Defined.

(** This lemma tells us how to extract a commutative triangle in the
   base from a path in the homotopy fiber. *)

Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x ~~> y) :
  (map f (base_path p)) @ (projT2 y) ~~> (projT2 x).
Proof.
  unfold base_path.
  induction p.
  cancel_units.
Defined.

(** Transporting a path along another path is equivalent to
   concatenating the two paths. *)

Lemma trans_is_concat {A} {x y z : A} (p : x ~~> y) (q : y ~~> z) :
  (transport q p) ~~> p @ q.
Proof.
  path_induction.
Defined.

(* This is also a special case of [transport_hfiber]. *)
Lemma trans_is_concat_opp {A} {x y z : A} (p : x ~~> y) (q : x ~~> z) :
  (transport (P := fun x' => (x' ~~> z)) p q) ~~> !p @ q.
Proof.
  path_induction.
Defined.

(** Transporting along a concatenation is transporting twice. *)

Lemma trans_concat {A} {P : A -> Type} {x y z : A} (p : x ~~> y) (q : y ~~> z) (t : P x) :
  transport (p @ q) t ~~> transport q (transport p t).
Proof.
  path_induction.
Defined.

(** Transporting commutes with pulling back along a map. *)

Lemma map_trans {A B} {x y : A} (P : B -> Type) (f : A -> B) (p : x ~~> y) (z : P (f x)) :
 (transport (P := (fun x => P (f x))) p z) ~~> (transport (map f p) z).
Proof.
  path_induction.
Defined.

(** And also with applying fiberwise functions. *)

Lemma trans_map {A} {P Q : A -> Type} {x y : A} (p : x ~~> y) (f : forall x, P x -> Q x) (z : P x) :
  f y (transport p z) ~~> (transport p (f x z)).
Proof.
  path_induction.
Defined.

(** A version of [map] for dependent functions. *)

Lemma map_dep {A} {P : A -> Type} {x y : A} (f : forall x, P x) (p: x ~~> y) :
  transport p (f x) ~~> f y.
Proof.
  path_induction.
Defined.

(* Transporting in a non-dependent type does nothing. *)

Lemma trans_trivial {A B : Type} {x y : A} (p : x ~~> y) (z : B) :
  transport (P := fun x => B) p z ~~> z.
Proof.
  path_induction.
Defined.

(* And for a non-dependent type, [map_dep] reduces to [map], modulo [trans_trivial]. *)

Lemma map_dep_trivial {A B} {x y : A} (f : A -> B) (p: x ~~> y):
  map_dep f p ~~> trans_trivial p (f x) @ map f p. 
Proof.
  path_induction.
Defined.

(* 2-Paths in a total space. *)

Lemma map_twovar {A : Type} {P : A -> Type} {B : Type} {x y : A} {a : P x} {b : P y}
  (f : forall x : A, P x -> B) (p : x ~~> y) (q : transport p a ~~> b) :
  f x a ~~> f y b.
Proof.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Defined.

Lemma total_path2 (A : Type) (P : A -> Type) (x y : sigT P)
  (p q : x ~~> y) (r : base_path p ~~> base_path q) :
  (transport (P := fun s => transport s (pr2 x) ~~> (pr2 y)) r (fiber_path p) ~~> fiber_path q) -> (p ~~> q).
Proof.
  intro H.
  path_via (total_path A P x y (base_path p) (fiber_path p)) ;
  [ apply opposite, total_path_reconstruction | ].
  path_via (total_path A P x y (base_path q) (fiber_path q)) ;
  [ | apply total_path_reconstruction ].
  apply @map_twovar with
    (f := total_path A P x y)
    (p := r).
  assumption.
Defined.
