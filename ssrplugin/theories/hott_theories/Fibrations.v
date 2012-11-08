Require Import ssreflect.
Require Export Paths.

Import PathNotations.

Local Open Scope path_scope.
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

Definition transport {A} (P : fibration A) {x y : A} (p : x = y) : P x -> P y.
Proof. rewrite p; exact. Defined.

(* We modify the status of the arguments of P wrt its original version : the*)
(* fibration is now a non-implicit argument, so that we can provide its *)
(* value explicitly when needed. When the fibration is implicit because we*)
(* apply it to a (px : P x), one can use the # infiix notation below, *)
(* which is crafted to hide P and let coq infer it from the context. *)

Arguments transport {A} P {x y} p px.

(* Transport is very common so it is worth introducing a notation for it. *)
Notation "p # px" := (transport _ p px) (right associativity, at level 65).

Lemma transport_idpath {A} {P : fibration A} {x : A} (u : P x) : 1 # u = u.
Proof. exact 1. Defined.

Lemma transport_idpath_right {A} {x y : A} (p : x = y) : p # 1 = p.
Proof. case p. exact 1. Qed.

(** A homotopy fiber for a map [f] at [y] is the space of paths of the
   form [f x = y]. *)

(* assia : Why do we use the eta-expanded version for the def of hfiber and not *)
(* for fibration?*)
Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x = y}.

(** We prove a lemma that explains how to transport a point in the
   homotopy fiber along a path in the domain of the map. *)

Lemma transport_hfiber A B (f : A -> B) (x y : A) (z : B) (p : x = y) (q : f x = z) :
  transport (fun x => f x = z) p q = (f`_* p)^-1 * q.
Proof. 
case p. rewrite transport_idpath. rewrite resp1f. rewrite path1V. rewrite mul1p.
reflexivity.
Qed.

(** The following lemma tells us how to construct a path in the total space from
   a path in the base space and a path in the fiber. *)

Definition total_path {A : Type} {P : fibration A} {x y : total P} {p : pr1 x = pr1 y} :
  p # pr2 x = pr2 y -> (x = y).
Proof.
move: x y p => [x u] [y v] /= p; move: u v.
case p => u v; rewrite transport_idpath => ->.
exact 1.
Defined.

(* We require by this command that the 'simpl' tactic (or the /= ssr switch *)
(* does not expand the body of total_path, in order not to expose its *)
(* body. May be the nomatch version would be enough but for the time being *)
(* I bet we never want to unfold total_path *)
Arguments total_path : simpl never.

(** Conversely, a path in the total space can be projected down to the base. *)

Definition base_path {A} {P : fibration A} {u v : total P} :
  (u = v) -> (pr1 u = pr1 v) := resp pr1.

(** And similarly to the fiber.  *)

Definition fiber_path {A} {P : fibration A} {u v : total P}
  (p : u = v) : resp pr1 p # pr2 u = pr2 v.
Proof.
  case p; rewrite transport_idpath. reflexivity.
Defined.

Arguments fiber_path {A} {P} {u v} p : simpl never.

(** And these operations are inverses.  See [total_paths_equiv], later
   on, for a more precise statement. *)
Lemma total_path_reconstruction {A : Type} {P : fibration A} {x y : total P} (p : x = y) :
  total_path (fiber_path p) = p.
Proof.
case p; case: x p => u v p; exact: 1.
Qed.

(* Here the /= of the first line of the script benefits from the *)
(* 'simpl never' behaviour we have requested on total_path *)
Definition base_total_path {A : Type} {P : fibration A} {x y : total P}
  {p : pr1 x = pr1 y} (q : p # (pr2 x) = pr2 y) :
  (base_path (total_path q)) = p.
Proof.
  case: x p q => [x H]; case: y => [y K] /= p q.
  move: H K q; case p => H K q; case q.
  exact 1.
Defined.

Arguments base_total_path {A} {P} {x y} {p} q : simpl never.

Lemma fiber_total_path (A : Type) (P : fibration A) (x y : total P)
  (p : pr1 x = pr1 y) (q : p # (pr2 x) = pr2 y) :
  transport (fun p' : pr1 x = pr1 y => p' # (pr2 x) = pr2 y)
  (base_total_path q) (fiber_path (total_path q))
  = q.
Proof.
  case: x p q => [x H]; case: y => [y K] /= p q.
  move: H K q; case p => H K q; case q.
  exact: 1.
Qed.

(** This lemma tells us how to extract a commutative triangle in the
   base from a path in the homotopy fiber. *)

Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x = y) :
  (f`_* (base_path p)) * (pr2 y) = (pr2 x).
Proof.
  case p => /=; rewrite mul1p; exact 1.
  (* Was: induction p. hott_simpl.*)
Qed.

(** Transporting a path along another path is equivalent to
   concatenating the two paths. *)

Lemma trans_is_concat {A} {x y z : A} (p : x = y) (q : y = z) :
  q # p = p * q.
Proof.
  move: q; case p => q; rewrite transport_idpath_right mul1p; exact: 1.
Qed.

(* This is also a special case of [transport_hfiber]. *)
Lemma trans_is_concat_opp {A} {x y z : A} (p : x = y) (q : x = z) :
  (transport (fun x' => (x' = z)) p q) = p^-1 * q.
Proof.
 move: q; case p => q. rewrite path1V transport_idpath mul1p; exact: 1.
Qed.

(** Transporting along a concatenation is transporting twice. *)
Lemma trans_concat {A} {P : fibration A} {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p * q # u = q # p # u.
Proof.
  move: q u; case p => q u; rewrite mul1p transport_idpath; exact: 1.
Qed.

(** Transporting and transporting back again is the identity. *)

(* We could as well remove the 'rewrite !transport_idpath' and let unification*)
(* do its job *)
Lemma trans_trans_opp {A} {P : fibration A} {x y : A} (p : x = y) (z : P y) :
  p # p^-1 # z = z.
Proof.
  move: z; case p => z. rewrite 2!transport_idpath. exact: 1.
Qed.

Lemma trans_opp_trans {A} {P : fibration A} {x y : A} (p : x = y) (z : P x) :
  p^-1 # p # z = z.
Proof.
  move: z; case p => z. exact: 1.
Qed.

(** Transporting commutes with pulling back along a map. *)

Lemma map_trans {A B} {x y : A} (P : B -> Type) (f : A -> B) (p : x = y) (z : P (f x)) :
 (transport ((fun x => P (f x))) p z) = resp f p # z.
Proof.
  move: z; case p => z. exact: 1.
Qed.

(** And also with applying fiberwise functions. *)

Lemma trans_map {A} {P Q : fibration A} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = p # f x z.
Proof.
  move: z; case p => z. exact: 1.
Qed.

Lemma trans_map2 {A} {P Q R : fibration A} {x y : A} (p : x = y)
  (f : forall x, P x -> Q x -> R x) (z : P x) (w: Q x) :
  f y (p # z) (p # w) = p # f x z w.
Proof.
move: z; case p => z. exact: 1.
Qed.


(** Transporting in a non-dependent type does nothing. *)

Definition trans_trivial {A B : Type} {x y : A} (p : x = y) (z : B) :
  transport (fun _ => B) p z = z.
Proof.
  case p. exact: 1.
Defined.

(** A version of [map] for dependent functions. *)
Definition map_dep {A} {P : fibration A} {x y : A} (f : section P) (p: x = y) :
  p # f x = f y.
Proof.
 case p. exact 1.
Defined.

(** And for a non-dependent type, [map_dep] reduces to [map], modulo [trans_trivial]. *)

Lemma map_dep_trivial {A B} {x y : A} (f : A -> B) (p: x = y) :
  map_dep f p = trans_trivial p (f x) * f`_* p. 
Proof.
  case p; exact: 1.
Qed.

(** Transporting commutes with summing along an unrelated variable. *)
(* We need to provide the functional argument of transport otherwise coq *)
(* does not infer it *)
Lemma trans_sum A B (P : A -> B -> Type)
  (x y : A) (p : x = y) (z : B) (w : P x z) :
  transport (fun a => sigT (P a)) p (z ; w) =
  (z ; transport (fun a => P a z) p w).
Proof.
  move: w; case p => w; exact 1.
Qed.


(** And with taking fiberwise products. *)

Lemma trans_prod A (P Q : fibration A) (x y : A) (p : x = y) (z : P x) (w : Q x) :
  transport (fun a => (P a * Q a)%type) p (z , w) =
  (p # z , p # w).
Proof.
  move: w z; case p => w z; exact 1.
Qed.

(** The action of map on a function of two variables, one dependent on the other. *)
(* we rearrange the order of the arguments here *)
Lemma map_twovar {A : Type} {P : fibration A} {B : Type} {x y : A} 
  (f : forall x : A, P x -> B) (p : x = y)  : forall (a : P x)(b : P y),
 p # a = b -> f x a = f y b.
Proof.
  case p => a b; rewrite transport_idpath => q; rewrite q.
  exact: 1.
Qed.

(** 2-Paths in a total space. *)
(* assia : why do I need to unfold base_path here? *)
Lemma total_path2 (A : Type) (P : fibration A) (x y : total P)
  (p q : x = y) (r : base_path p = base_path q) :
  (transport (fun s => s # pr2 x = pr2 y) r (fiber_path p) = fiber_path q) -> (p = q).
Proof.
move: p q r; case: x => x H; case: y => y K p; case p => q r h.
rewrite -(total_path_reconstruction q) -{}h /=.
move: r; rewrite /base_path => r. case r.
reflexivity.
Qed.

(** Transporting along a path between paths. *)

Definition trans2 {A : Type} {P : fibration A} {x y : A} {p q : x = y}
  (r : p = q) (z : P x) :
  p # z = q # z
  := resp (fun p' => p' # z) r.

Lemma trans2_is_happly {A : Type} {Q : fibration A} {x y : A} {p q : x = y}
  (r : p = q) (z : Q x) :
  trans2 r z = happly (resp (transport Q) r) z.
Proof.
  move: q r; case p => q r; case r. exact: 1.
Qed.

Lemma trans2_opp {A : Type} {Q : fibration A} {x y : A} {p q : x = y}
  (r : p = q) (z : Q x) :
  trans2 (r^-1) z = (trans2 r z)^-1.
Proof.
  move: q r; case p => q r; case r; exact: 1.
Qed.

Lemma trans2_naturality {A : Type} {P : fibration A} {x y : A} {p q : x = y}
  {z w : P x} (r : p = q) (s : z = w) :
  resp ((transport P) p) s * trans2 r w = trans2 r z * resp ((transport P) q) s.
Proof.
  move: q r s; case p => q r; case r => s; case s. exact: 1.
Qed.

Lemma trans2_trivial {A B : Type} {x y : A} {p q : x = y}
  (r : p = q) (z : B) :
  trans_trivial p z = trans2 (P := fun _ => B) r z * trans_trivial q z.
Proof.
  move: q r; case p => q r; case r. exact: 1.
Qed.

(* It seems we do not need trans_trans_opp to be transparent so far, even if*)
(* we use it as an operation here *)
Lemma trans_trans_opp2 A P (x y : A) (p q : x = y) (r : p = q) (z : P y) :
  trans_trans_opp p z =
  resp (transport P p) (trans2 (opposite2 r) z)
  * trans2 r (q^-1 #  z)
  * trans_trans_opp q z.
Proof.
  move: q r z; case p => q r; case r => z /=; rewrite mul1p.
  exact: 1.
Qed.

(** Transporting in an iterated fibration. *)

Definition trans_trans {A} {P : fibration A}
  {Q : forall a, fibration (P a)}
  {a1 a2 : A} (s : a1 = a2) {p1 : P a1} :
  Q a1 p1 -> Q a2 (s # p1).
Proof.
  case s; rewrite transport_idpath. exact.
Qed.

(** Transporting in a fibration of paths. *)

Lemma trans_paths A B (f g : A -> B) (x y : A) (p : x = y) (q : f x = g x) :
  transport (fun a => f a = g a) p q
  =
  (f`_* p)^-1 * q * g`_* p.
Proof.
  move: q; case p => q /=; rewrite mul1p transport_idpath. exact: 1.
Qed.

(** A dependent version of [map2]. *)
(* Should this be the definition ? *)
Lemma map2_dep {A : Type} {P : fibration A} {x y : A} {p q : x = y}
  (f : section P) (r : p = q) :
  map_dep f p = trans2 r (f x) * map_dep f q.
Proof.
  move: q r; case p => q r; case r; exact: 1.
Qed.
