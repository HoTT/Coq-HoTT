Require Import ssreflect ssrfun.
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

(* This is the legacy definition of transport (as in the original file) : 
Definition transport {A} (P : fibration A) {x y : A} (p : x = y) : P x -> P y.
Proof. rewrite p; exact. Defined.

This was an other interesting case when it happened to be a bad idea to define
such terms in tactic mode, even without automation : in order to optimize slightly,
the ssreflect rewrite tactic is using a subtly different elimination scheme from Coq:

one (Coq) is using a scheme of type : 
... -> forall y : A, a = y -> P y

and (ssr) the other : 
... -> forall y : A, y = a -> P y

for rewriting a hypothesis from left to right. And these are not convertible of course.
Hence once again we carfully provide an explicit body for this transparent definition.
*)

Definition transport (A : Type) (P : fibration A) {x y : A} (p : x = y) : P x -> P y :=
  fun u => match p with identity_refl => u end.

(* We modify the status of the arguments of P wrt its original version : the*)
(* fibration is now a non-implicit argument, so that we can provide its *)
(* value explicitly when needed. When the fibration is implicit because we*)
(* apply it to a (px : P x), one can use the # infiix notation below, *)
(* which is crafted to hide P and let coq infer it from the context. *)

Arguments transport {A} P {x y} p%path_scope px.

(* Transport is very common so it is worth introducing a notation for it. *)
Notation "p # px" := (transport _ p px) (right associativity, at level 65, only parsing).

(* Sanity check : two easy lemmas *)
Lemma transport1p {A} {P : fibration A} {x : A} (u : P x) : 1 # u = u.
Proof. exact 1. Defined.

Lemma transportp1 {A} {x y : A} (p : x = y) : p # 1 = p.
Proof. case p. exact 1. Qed.

(** A homotopy fiber for a map [f] at [y] is the space of paths of the
   form [f x = y]. *)

(* assia : Why do we use the eta-expanded version for the def of hfiber and not *)
(* for fibration?*)
Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x = y}.

(* assia : it proves convenient to import also Cyril's alternate constructors *)
(* of inhabitants of a hfiber *)

Definition hfiber_def {A B} (f : A -> B) (y : B) 
           (x : A) (Hx : f x = y) : hfiber f y := exist (fun x => f x = _) _ Hx.

(* nice constructors for elements of the preimage: *)

(* If (Hx : f x = y), the element of the fiber (x, Hx) *)
Notation Hfiber f Hx := (@hfiber_def _ _ f _ _ Hx).

(* The element (f x, 1) of the fiber above f x *)
Notation in_hfiber f x := (@hfiber_def _ _ f _ x (erefl _)).

Lemma hfiberP {A B} (f : A -> B) (y : B) (x : hfiber f y) : f (projT1 x) = y.
Proof. by case: x. Qed.
