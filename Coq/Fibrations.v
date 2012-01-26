Require Export Paths.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

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

Notation "( x  ; y )" := (existT _ x y).
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

Theorem transport {A} {P : A -> Type} {x y : A} (p : x == y) : P x -> P y.
Proof.
  path_induction.
Defined.

(** A homotopy fiber for a map [f] at [y] is the space of paths of the
   form [f x == y].
   *)

Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x == y}.

(** We prove a lemma that explains how to transport a point in the
   homotopy fiber along a path in the domain of the map. *)

Lemma transport_hfiber A B (f : A -> B) (x y : A) (z : B) (p : x == y) (q : f x == z) :
  transport (P := fun x => f x == z) p q == !(map f p) @ q.
Proof.
  intros A B f x y z p q.
  induction p.
  cancel_units.
Defined.

(** The following lemma tells us how to construct a path in the total space from
   a path in the base space and a path in the fiber. *)

Lemma total_path (A : Type) (P : A -> Type) (x y : sigT P) (p : projT1 x == projT1 y) :
  (transport p (projT2 x) == projT2 y) -> (x == y).
Proof.
  intros A P x y p.
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
  (u == v) -> (projT1 u == projT1 v) :=
  map pr1.

(** And similarly to the fiber.  *)

Definition fiber_path {A} {P : A -> Type} {u v : sigT P}
  (p : u == v) : (transport (map pr1 p) (projT2 u) == projT2 v).
Proof.
  path_induction.
Defined.

(** And these operations are inverses.  See [total_paths_equiv], later
   on, for a more precise statement. *)

Lemma total_path_reconstruction (A : Type) (P : A -> Type) (x y : sigT P) (p : x == y) :
  total_path A P x y (base_path p) (fiber_path p) == p.
Proof.
  intros A P x y p.
  induction p.
  induction x. 
  auto.
Defined.

Lemma base_total_path (A : Type) (P : A -> Type) (x y : sigT P)
  (p : projT1 x == projT1 y) (q : transport p (projT2 x) == projT2 y) :
  (base_path (total_path A P x y p q)) == p.
Proof.
  destruct x as [x H]. destruct y as [y K]. intros p q.
  simpl in p. induction p. simpl in q. induction q.
  auto.
Defined.

Lemma fiber_total_path (A : Type) (P : A -> Type) (x y : sigT P)
  (p : projT1 x == projT1 y) (q : transport p (projT2 x) == projT2 y) :
  transport (P := fun p' : pr1 x == pr1 y => transport p' (pr2 x) == pr2 y)
  (base_total_path A P x y p q) (fiber_path (total_path A P x y p q))
  == q.
Proof.
  destruct x as [x H]. destruct y as [y K]. intros p q.
  simpl in p. induction p. simpl in q. induction q.
  auto.
Defined.

(** This lemma tells us how to extract a commutative triangle in the
   base from a path in the homotopy fiber. *)

Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x == y) :
  (map f (base_path p)) @ (projT2 y) == (projT2 x).
Proof.
  intros. induction p.
  unfold base_path.
  cancel_units.
Defined.

(** Transporting a path along another path is equivalent to
   concatenating the two paths. *)

Lemma trans_is_concat {A} {x y z : A} (p : x == y) (q : y == z) :
  (transport q p) == p @ q.
Proof.
  path_induction.
Defined.

(* This is also a special case of [transport_hfiber]. *)
Lemma trans_is_concat_opp {A} {x y z : A} (p : x == y) (q : x == z) :
  (transport (P := fun x' => (x' == z)) p q) == !p @ q.
Proof.
  path_induction.
Defined.

(** Transporting along a concatenation is transporting twice. *)

Lemma trans_concat {A} {P : A -> Type} {x y z : A} (p : x == y) (q : y == z) (z : P x) :
  transport (p @ q) z == transport q (transport p z).
Proof.
  path_induction.
Defined.

(** Transporting and transporting back again is the identity. *)

Lemma trans_trans_opp {A} {P : A -> Type} {x y : A} (p : x == y) (z : P y) :
  transport p (transport (!p) z) == z.
Proof.
  path_induction.
Defined.

Lemma trans_opp_trans {A} {P : A -> Type} {x y : A} (p : x == y) (z : P x) :
  transport (!p) (transport p z) == z.
Proof.
  path_induction.
Defined.

(** Transporting commutes with pulling back along a map. *)

Lemma map_trans {A B} {x y : A} (P : B -> Type) (f : A -> B) (p : x == y) (z : P (f x)) :
 (transport (P := (fun x => P (f x))) p z) == (transport (map f p) z).
Proof.
  path_induction.
Defined.

(** And also with applying fiberwise functions. *)

Lemma trans_map {A} {P Q : A -> Type} {x y : A} (p : x == y) (f : forall x, P x -> Q x) (z : P x) :
  f y (transport p z) == (transport p (f x z)).
Proof.
  path_induction.
Defined.

Lemma trans_map2 {A} {P Q R : A -> Type} {x y : A} (p : x == y)
  (f : forall x, P x -> Q x -> R x) (z : P x) (w: Q x) :
  f y (transport p z) (transport p w) == (transport p (f x z w)).
Proof.
  path_induction.
Defined.

(** A version of [map] for dependent functions. *)

Lemma map_dep {A} {P : A -> Type} {x y : A} (f : forall x, P x) (p: x == y) :
  transport p (f x) == f y.
Proof.
  path_induction.
Defined.

(** Transporting in a non-dependent type does nothing. *)

Lemma trans_trivial {A B : Type} {x y : A} (p : x == y) (z : B) :
  transport (P := fun x => B) p z == z.
Proof.
  path_induction.
Defined.

(** And for a non-dependent type, [map_dep] reduces to [map], modulo [trans_trivial]. *)

Lemma map_dep_trivial {A B} {x y : A} (f : A -> B) (p: x == y):
  map_dep f p == trans_trivial p (f x) @ map f p. 
Proof.
  path_induction.
Defined.

(** Transporting commutes with summing along an unrelated variable. *)

Definition trans_sum A B (P : A -> B -> Type)
  (x y : A) (p : x == y) (z : B) (w : P x z) :
  transport (P := fun a => sigT (P a)) p (z ; w) ==
  (z ; transport (P := fun a => P a z) p w).
Proof.
  path_induction.
Defined.

(** And with taking fiberwise products. *)

Definition trans_prod A (P Q : A -> Type) (x y : A) (p : x == y) (z : P x) (w : Q x) :
  transport (P := fun a => (P a * Q a)%type) p (z , w) ==
  (transport p z , transport p w).
Proof.
  path_induction.
Defined.

(** The action of map on a function of two variables, one dependent on the other. *)

Lemma map_twovar {A : Type} {P : A -> Type} {B : Type} {x y : A} {a : P x} {b : P y}
  (f : forall x : A, P x -> B) (p : x == y) (q : transport p a == b) :
  f x a == f y b.
Proof.
  intros A P B x y a b f p q.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Defined.

(** 2-Paths in a total space. *)

Lemma total_path2 (A : Type) (P : A -> Type) (x y : sigT P)
  (p q : x == y) (r : base_path p == base_path q) :
  (transport (P := fun s => transport s (pr2 x) == (pr2 y)) r (fiber_path p) == fiber_path q) -> (p == q).
Proof.
  intros A P x y p q r H.
  path_via (total_path A P x y (base_path p) (fiber_path p)) ;
  [ apply opposite, total_path_reconstruction | ].
  path_via (total_path A P x y (base_path q) (fiber_path q)) ;
  [ | apply total_path_reconstruction ].
  apply @map_twovar with
    (f := total_path A P x y)
    (p := r).
  assumption.
Defined.

(** Transporting along a path between paths. *)

Definition trans2 {A : Type} {P : A -> Type} {x y : A} {p q : x == y}
  (r : p == q) (z : P x) :
  transport p z == transport q z
  := map (fun p' => transport p' z) r.

(** An alternative definition. *)
Lemma trans2_is_happly {A : Type} {Q : A -> Type} {x y : A} {p q : x == y}
  (r : p == q) (z : Q x) :
  trans2 r z == happly (map transport r) z.
Proof.
  path_induction.
Defined.

Lemma trans2_opp {A : Type} {Q : A -> Type} {x y : A} {p q : x == y}
  (r : p == q) (z : Q x) :
  trans2 (!r) z == !trans2 r z.
Proof.
  path_induction.
Defined.

Lemma trans2_naturality {A : Type} {P : A -> Type} {x y : A} {p q : x == y}
  {z w : P x} (r : p == q) (s : z == w) :
  map (transport p) s @ trans2 r w == trans2 r z @ map (transport q) s.
Proof.
  path_induction.
Defined.

Lemma trans2_trivial {A B : Type} {x y : A} {p q : x == y}
  (r : p == q) (z : B) :
  trans_trivial p z == trans2 (P := fun _ => B) r z @ trans_trivial q z.
Proof.
  path_induction.
Defined.

Lemma trans_trans_opp2 A P (x y : A) (p q : x == y) (r : p == q) (z : P y) :
  trans_trans_opp p z ==
  map (transport p) (trans2 (opposite2 r) z)
  @ trans2 r (transport (!q) z)
  @ trans_trans_opp q z.
Proof.
  path_induction.
Defined.

(** Transporting in an iterated fibration. *)

Definition trans_trans {A} {P : A -> Type}
  {Q : forall a, P a -> Type}
  {a1 a2 : A} (s : a1 == a2) {p1 : P a1} :
  Q a1 p1 -> Q a2 (transport s p1).
Proof.
  path_induction.
Defined.

(** Transporting in a fibration of paths. *)

Lemma trans_paths A B (f g : A -> B) (x y : A) (p : x == y) (q : f x == g x) :
  transport (P := fun a => f a == g a) p q
  ==
  !map f p @ q @ map g p.
Proof.
  path_induction.
  cancel_units.
Defined.

(** A dependent version of [map2]. *)

Lemma map2_dep {A : Type} {P : A -> Type} {x y : A} {p q : x == y}
  (f : forall a, P a) (r : p == q) :
  map_dep f p
  ==
  trans2 r (f x)
  @
  map_dep f q.
Proof.
  path_induction.
Defined.
