Require Export Paths.

(** In homotopy type theory, We think of elements of [Type] as spaces
   or homotopy types, while a type family [P : A -> Type] corresponds
   to a fibration whose base is [A] and whose fiber over [x] is [P x].
*)

Definition fibration (A : Type) := A -> Type.

(*
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

Definition total {A} (P : fibration A) := @sigT A P.
   
(** We can also define more familiar homotopy-looking aliases for all
   of these functions. *)

Notation "( x ; y )" := (existT _ x y).
Notation pr1 := (@projT1 _ _).
Notation pr2 := (@projT2 _ _).

(** An element of [section P] is a global section of fibration [P]. *)

Definition section {A} (P : fibration A) := forall x : A, P x.

(** We now study how paths interact with fibrations.  The most basic
   fact is that we can transport points in the fibers along paths in
   the base space.  This is actually a special case of the
   [paths_rect] induction principle in which the fibration [P] does
   not depend on paths in the base space but rather just on points of
   the base space. *)

(* The following coercion allows us to apply paths to arguments
   instead of having to use [transport] directly. *)

Theorem transport {A} {P : fibration A} {x y : A} (p : x == y) : P x -> P y.
Proof.
  path_induction.
Defined.

(* Transport is very common so it is worth introducing a notation for it. *)
Notation "p # x" := (transport p x) (right associativity, at level 60).

Lemma transport_idpath {A} {P : fibration A} {x : A} (u : P x) :
  (idpath x) # u == u.
Proof.
  apply idpath.
Defined.

Hint Rewrite @transport_idpath : paths.

(** A homotopy fiber for a map [f] at [y] is the space of paths of the
   form [f x == y]. *)

Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x == y}.

(** We prove a lemma that explains how to transport a point in the
   homotopy fiber along a path in the domain of the map. *)

Lemma transport_hfiber A B (f : A -> B) (x y : A) (z : B) (p : x == y) (q : f x == z) :
  transport (P := fun x => f x == z) p q == !(map f p) @ q.
Proof.
  induction p.
  hott_simpl.
Defined.

(** The following lemma tells us how to construct a path in the total space from
   a path in the base space and a path in the fiber. *)

Lemma total_path {A : Type} {P : fibration A} {x y : total P} {p : pr1 x == pr1 y} :
  p # pr2 x == pr2 y -> (x == y).
Proof.
  intros q.
  destruct x as [x u].
  destruct y as [y v].
  simpl in * |- *.
  induction p.
  simpl in q.
  path_induction.
Defined.

(** Conversely, a path in the total space can be projected down to the base. *)

Definition base_path {A} {P : fibration A} {u v : total P} :
  (u == v) -> (pr1 u == pr1 v) := map pr1.

(** And similarly to the fiber.  *)

Definition fiber_path {A} {P : fibration A} {u v : total P}
  (p : u == v) : map pr1 p # pr2 u == pr2 v.
Proof.
  path_induction.
Defined.

Hint Rewrite @fiber_path : paths.

(** And these operations are inverses.  See [total_paths_equiv], later
   on, for a more precise statement. *)

Lemma total_path_reconstruction {A : Type} {P : fibration A} {x y : total P} (p : x == y) :
  total_path (fiber_path p) == p.
Proof.
  induction p.
  destruct x.
  auto.
Defined.

Hint Rewrite @total_path_reconstruction : paths.

Lemma base_total_path {A : Type} {P : fibration A} {x y : total P}
  {p : pr1 x == pr1 y} (q : p # (pr2 x) == pr2 y) :
  (base_path (total_path q)) == p.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  auto.
Defined.

Hint Rewrite @base_total_path : paths.

Lemma fiber_total_path (A : Type) (P : fibration A) (x y : total P)
  (p : pr1 x == pr1 y) (q : transport p (pr2 x) == pr2 y) :
  transport (P := fun p' : pr1 x == pr1 y => p' # (pr2 x) == pr2 y)
  (base_total_path q) (fiber_path (total_path q))
  == q.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  auto.
Defined.

Hint Rewrite fiber_total_path : paths.

(** This lemma tells us how to extract a commutative triangle in the
   base from a path in the homotopy fiber. *)

Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x == y) :
  (map f (base_path p)) @ (pr2 y) == (pr2 x).
Proof.
  induction p.
  hott_simpl.
Defined.

Hint Rewrite @hfiber_triangle : paths.

(** Transporting a path along another path is equivalent to
   concatenating the two paths. *)

Lemma trans_is_concat {A} {x y z : A} (p : x == y) (q : y == z) :
  q # p == p @ q.
Proof.
  path_induction.
Defined.

Hint Rewrite @trans_is_concat : paths.

(* This is also a special case of [transport_hfiber]. *)
Lemma trans_is_concat_opp {A} {x y z : A} (p : x == y) (q : x == z) :
  (transport (P := fun x' => (x' == z)) p q) == !p @ q.
Proof.
  path_induction.
Defined.

Hint Rewrite @trans_is_concat_opp : paths.

(** Transporting along a concatenation is transporting twice. *)

Lemma trans_concat {A} {P : fibration A} {x y z : A} (p : x == y) (q : y == z) (u : P x) :
  p @ q # u == q # p # u.
Proof.
  path_induction.
Defined.

Hint Rewrite @trans_concat : paths.

(** Transporting and transporting back again is the identity. *)

Lemma trans_trans_opp {A} {P : fibration A} {x y : A} (p : x == y) (z : P y) :
  p # !p # z == z.
Proof.
  path_induction.
Defined.

Hint Rewrite @trans_trans_opp : paths.

Lemma trans_opp_trans {A} {P : fibration A} {x y : A} (p : x == y) (z : P x) :
  !p # p # z == z.
Proof.
  path_induction.
Defined.

Hint Rewrite @trans_opp_trans : paths.

(** Transporting commutes with pulling back along a map. *)

Lemma map_trans {A B} {x y : A} (P : B -> Type) (f : A -> B) (p : x == y) (z : P (f x)) :
 (transport (P := (fun x => P (f x))) p z) == map f p # z.
Proof.
  path_induction.
Defined.

Hint Rewrite @map_trans : paths.

(** And also with applying fiberwise functions. *)

Lemma trans_map {A} {P Q : fibration A} {x y : A} (p : x == y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) == p # f x z.
Proof.
  path_induction.
Defined.

Lemma trans_map2 {A} {P Q R : fibration A} {x y : A} (p : x == y)
  (f : forall x, P x -> Q x -> R x) (z : P x) (w: Q x) :
  f y (p # z) (p # w) == p # f x z w.
Proof.
  path_induction.
Defined.

(** A version of [map] for dependent functions. *)

Lemma map_dep {A} {P : fibration A} {x y : A} (f : section P) (p: x == y) :
  p # f x == f y.
Proof.
  path_induction.
Defined.

Hint Rewrite @map_dep : paths.

(** Transporting in a non-dependent type does nothing. *)

Lemma trans_trivial {A B : Type} {x y : A} (p : x == y) (z : B) :
  transport (P := fun _ => B) p z == z.
Proof.
  path_induction.
Defined.

Hint Rewrite @map_dep : paths.

(** And for a non-dependent type, [map_dep] reduces to [map], modulo [trans_trivial]. *)

Lemma map_dep_trivial {A B} {x y : A} (f : A -> B) (p: x == y):
  map_dep f p == trans_trivial p (f x) @ map f p. 
Proof.
  path_induction.
Defined.

Hint Rewrite @map_dep_trivial : paths.

(** Transporting commutes with summing along an unrelated variable. *)

Definition trans_sum A B (P : A -> B -> Type)
  (x y : A) (p : x == y) (z : B) (w : P x z) :
  transport (P := fun a => sigT (P a)) p (z ; w) ==
  (z ; transport (P := fun a => P a z) p w).
Proof.
  path_induction.
Defined.

Hint Rewrite @trans_sum : paths.

(** And with taking fiberwise products. *)

Definition trans_prod A (P Q : fibration A) (x y : A) (p : x == y) (z : P x) (w : Q x) :
  transport (P := fun a => (P a * Q a)%type) p (z , w) ==
  (p # z , p # w).
Proof.
  path_induction.
Defined.

Hint Rewrite @trans_prod : paths.

(** The action of map on a function of two variables, one dependent on the other. *)

Lemma map_twovar {A : Type} {P : fibration A} {B : Type} {x y : A} {a : P x} {b : P y}
  (f : forall x : A, P x -> B) (p : x == y) (q : p # a == b) :
  f x a == f y b.
Proof.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Defined.

(** 2-Paths in a total space. *)

Lemma total_path2 (A : Type) (P : fibration A) (x y : total P)
  (p q : x == y) (r : base_path p == base_path q) :
  (transport (P := fun s => s # pr2 x == pr2 y) r (fiber_path p) == fiber_path q) -> (p == q).
Proof.
  intro H.
  path_via (total_path (fiber_path p)) ;
  [ apply opposite, total_path_reconstruction | ].
  path_via (total_path (fiber_path q)) ;
  [ | apply total_path_reconstruction ].
  apply @map_twovar with
    (f := @total_path A P x y)
    (p := r).
  assumption.
Defined.

(** Transporting along a path between paths. *)

Definition trans2 {A : Type} {P : fibration A} {x y : A} {p q : x == y}
  (r : p == q) (z : P x) :
  p # z == q # z
  := map (fun p' => p' # z) r.

(** An alternative definition. *)
Lemma trans2_is_happly {A : Type} {Q : fibration A} {x y : A} {p q : x == y}
  (r : p == q) (z : Q x) :
  trans2 r z == happly (map transport r) z.
Proof.
  path_induction.
Defined.

Lemma trans2_opp {A : Type} {Q : fibration A} {x y : A} {p q : x == y}
  (r : p == q) (z : Q x) :
  trans2 (!r) z == !trans2 r z.
Proof.
  path_induction.
Defined.

Lemma trans2_naturality {A : Type} {P : fibration A} {x y : A} {p q : x == y}
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
  @ trans2 r (!q #  z)
  @ trans_trans_opp q z.
Proof.
  path_induction.
Defined.

(** Transporting in an iterated fibration. *)

Definition trans_trans {A} {P : fibration A}
  {Q : forall a, fibration (P a)}
  {a1 a2 : A} (s : a1 == a2) {p1 : P a1} :
  Q a1 p1 -> Q a2 (s # p1).
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
  hott_simpl.
Defined.

(** A dependent version of [map2]. *)

Lemma map2_dep {A : Type} {P : fibration A} {x y : A} {p q : x == y}
  (f : section P) (r : p == q) :
  map_dep f p
  ==
  trans2 r (f x)
  @
  map_dep f q.
Proof.
  path_induction.
Defined.
