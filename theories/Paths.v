(** * The groupoid structure of identity types *)

Require Import Logic_Type.

(** In this file we study the groupoid structure of identity types. The results are used
   everywhere else, so we need to be extra careful about how we define and prove things.
   We prefer hand-written terms that give us precise control over proofs. *)

(** We declare a scope in which we shall place path notations. This way they can
   be turned on and off by the user. To make things even easier, we define below
   a module [PathNotations] which the user can import. *)

Delimit Scope path_scope with path.

Module Import PathNotations.

  (** The identity path. *)
  Notation "1" := identity_refl : path_scope.
  
  (* The composition of two paths. *)
  Notation "p @ q" := (identity_trans p q) (at level 20) : path_scope.
  
  (* The inverse of a path. *)
  Notation "p ^-1" := (identity_sym p) (at level 3) : path_scope.
  
  (* If [f : A -> B] and [p : x = y] is a path in [A] then [pmap f p : f x = f y]. *)
  Notation "'pmap'" := f_equal : path_scope.
End PathNotations.

Local Open Scope path_scope.

(** ** Naming conventions

   We need good naming conventions that allow us to name theorems without
   looking them up. The names should indicate the structure of the theorem,
   but they may sometimes be ambiguous, in which case you just have to know
   what is going on.
   
   We shall adopt the following principles:

   - we are not afraid of long names
   - we are not afraid of short names when they are used frequently
   - we use underscores
   - all names are lower-case, except for letters which indicate special entities

   Theorems about concatenation of paths are called [concat_XXX] where [XXX] tells
   us what is on the left-hand side of the equation. You have to guess the right-hand
   side. We use the following symbols in [XXX]:

   - [1] means the identity path
   - [p] means 'the path'
   - [V] means 'the inverse path'
   - [P] means '[pmap]'

   Associativity is indicated with an underscore. Here are some examples of how the
   name gives hints about the left-hand side of the equation.

   - [concat_1p] means [1 * p]
   - [concat_Vp] means [p^-1 * p]
   - [concat_p_pp] means [p * (q * r)]
   - [concat_pp_p] means [(p * q) * r]
   - [concat_V_pp] means [p^-1 * (p * q)]
   - [concat_pV_p] means [(q * p^-1) * p] or [(p * p^-1) * q], you just have to look

   Laws about inverse of something are of the form [inv_XXX], and those about
   [pmap] are of the form [pmap_XXX]. For example:

   - [inv_concat] is about [(p @ q)^-1]
   - [inv_inv] is about [(p^-1)^-1]
   - [inv_pmap] is about [(pmap f p)^-1]
   - [pmap_inv] is about [pmap f (p^-1)]
   - [pmap_concat] is about [pmap f (p @ q)]
   - [pmap_idmap] is about [pmap idmap p]
   - [pmap_1] is about [pmap f 1]
   
   Then we have laws which move things around in an equation. The naming scheme here is
   [moveD_XXX]. The direction [D] indicates where to move to: [L] means that we move
   something to the left-hand side, whereas [R] means we are moving something to the
   right-hand side. The part [XXX] describes the shape of the side _from_ which we are
   moving where the thing that is getting moves is called [M]. Examples:

   - [moveL_pM] means that we transform [p = q @ r] to [p @ r^-1 = q] because
     we are moving something to the left-hand side, and we are moving the right
     argument of concat.
 
   - [moveR_Mp] means that we transform [p @ q = r] to [q = p^-1 @ r] because
     we move to the right-hand side, and we are moving the left argument of concat.

   - [moveR_1M] means that we transform [p = 1 * q] to [p * q^-1 = 1]

   Lastly, there are cancelation laws. These are called [cancelR] and [cancelL].

   We may now proceed with the groupoid structure proper.
*)

(** ** The 1-dimensional groupoid structure. *)

(** The identity path is a right unit. *)
Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p
  :=
  match p with identity_refl => 1 end.

(** The identity is a left unit. *)
Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p
  :=
  match p with identity_refl => 1 end.

(** Concatenation is associative. *)
Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with identity_refl =>
    match q with | identity_refl => 1 end
  end.

(** The left inverse law. *)
Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p ^-1 = 1
  :=
  match p with identity_refl => 1 end.
  
(** The right inverse law. *)
Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p^-1 @ p = 1
  :=
  match p with identity_refl => 1 end.

(** Several auxiliary theorems about canceling inverses across associativity. *)

Definition concat_V_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p^-1 @ (p @ q) = q
  :=
  match q with identity_refl =>
    match p with identity_refl => 1 end
  end.

Definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (p^-1 @ q) = q
  :=
  match q with identity_refl =>
    match p with identity_refl => 1 end
  end.

Definition concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ q^-1 = p
  :=
  match q with identity_refl =>
    match p with identity_refl => 1 end
  end.

Definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^-1) @ q = p
  :=
  (match q as i return forall p, (p @ i^-1) @ i = p with
    identity_refl =>
    fun p =>
      match p with identity_refl => 1 end
  end) p.

(** Inverse distributes over contactenation *)
Definition inv_concat {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^-1 = q^-1 @ p^-1
  :=
  match q with identity_refl =>
    match p with identity_refl => 1 end
  end.
  
(** Inverse is an involution. *)
Definition inv_inv {A : Type} {x y : A} (p : x = y) :
  p ^-1 ^-1 = p
  :=
  match p with identity_refl => 1 end.

(** A random result, not sure it is used anywhere. *)
Definition inv_pVinv {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^-1)^-1 = q @ p^-1.
Proof.
  destruct q.
  destruct p.
  reflexivity.
Defined.


(* *** Theorems for moving things around in equations. *)

Lemma moveR_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  p = r^-1 @ q -> r @ p = q.
Proof.
  intro h; rewrite h.
  apply concat_p_Vp.
Qed.

Lemma moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^-1 -> r @ p = q.
Proof. 
  intro h; rewrite h.
  apply concat_pV_p.
Qed.

Lemma moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r^-1 @ q = p -> q = r @ p.
Proof.
  intro h; rewrite <- h.
  symmetry; apply concat_p_Vp.
Qed.

Definition moveL_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^-1 = r -> q = r @ p.
Proof.
  intro h; rewrite <- h.
  symmetry; apply concat_pV_p.
Defined.

Definition moveL_M {A : Type} {x y : A} (p q : x = y) :
  p @ q^-1 = 1 -> p = q.
Proof.
  destruct q.
  intro h.
  exact h.
Defined.

Definition moveL_V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1 -> p = q^-1.
Proof.
  destruct q.
  intro h.
  assumption.
Defined.

(** Cancelation laws. *)

Definition cancelL {A : Type} {x y z : A} (p : x = y) (q r: y = z) (h : q = r) :
  p @ q = p @ r :=
  pmap (fun s : y = z => p @ s) h.

Definition cancelR {A : Type} {x y z : A} (p q : x = y) (r: y = z) (h : p = q) :
  p @ r = q @ r
  :=
  pmap (fun s : x = y => s @ r) h.

(** *** Functoriality of functions *)

(** Here we prove that functions behave like functors between groupoids,
   and that [pmap] itself is functorial. *)

(** Functions take identity paths to identity paths. *)
Definition pmap_1 {A B : Type} (x : A) (f : A -> B) :
  pmap f 1 = 1 :> (f x = f x)
  :=
  1.

(** Functions commute with concatenation. *)
Definition pmap_concat {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  pmap f (p @ q) = (pmap f p) @ (pmap f q)
  :=
  match q with
    identity_refl =>
    match p with identity_refl => 1 end
  end.

(** Functions commute with path inverses. *)
Definition inverse_pmap {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  (pmap f p)^-1 = pmap f (p^-1)
  :=
  match p with identity_refl => 1 end.

(** [pmap] itself is functorial in the first argument. *)

Definition pmap_idmap {A : Type} {x y : A} (p : x = y) :
  pmap idmap p = p
  :=
  match p with identity_refl => 1 end.

Definition pmap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  pmap (compose g f) p = pmap g (pmap f p)
  :=
  match p with identity_refl => 1 end.

(** Naturality of [pmap]. *)
Definition concat_Pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (pmap f q) @ (p y) = (p x) @ (pmap g q)
  :=
  match q with
    | identity_refl => concat_1p _
  end.

(** Naturality of [pmap] at identity. *)
Definition concat_P1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (pmap f q) @ (p y) = (p x) @ q
  :=
  match q with
    | identity_refl => concat_1p _
  end.

Definition concat_pP1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (pmap f q) =  q @ (p y)
  :=
  match q as i in (_ = y) return (p x @ pmap f i = i @ p y) with
    | identity_refl => (concat_1p _)^-1
  end.

(** ** The 2-dimensional groupoid structure *)

(** Horizontal composition of 2-dimensional paths. *)
Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q') :
  p @ q = p' @ q'
  :=
  match h, h' with identity_refl, identity_refl => 1 end.

Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.

(** *** Whiskering *)

Definition whiskerL {A : Type} {x y z : A} (p : x = y) {q r : y = z} (h : q = r) : p @ q = p @ r
  :=
  1 @@ h.

Definition whiskerR {A : Type} {x y z : A} {p q : x = y} (h : p = q) (r : y = z) :
  p @ r = q @ r
  :=
  h @@ 1.

(** Whiskering and identity paths. *)

Definition whiskerR_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  whiskerR h 1 = h
  :=
  match h with identity_refl => 1 end.

Definition whiskerR_1p {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerR 1 q = 1 :> (p @ q = p @ q)
  :=
  match q with identity_refl => 1 end.

Definition whiskerL_p1 {A : Type} {x y z : A} (p q : x = y) (q : y = z) :
  whiskerL p 1 = 1 :> (p @ q = p @ q)
  :=
  match q with identity_refl => 1 end.

Definition concat2_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  h @@ 1 = h :> (p @ 1 = q @ 1)
  :=
  whiskerR_p1 h.

(** The interchange law for whiskering. *)
Definition concat_whisker {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whiskerR a q) @ (whiskerL p' b) = (whiskerL p b) @ (whiskerR a q')
  :=
  match b with
    identity_refl =>
    match a with identity_refl =>
      (concat_1p _)^-1
    end
  end.

(** The interchange law for concatenation. *)
Definition concat_concat2 {A : Type} {x y z : A} {p p' p'' : x = y} {q q' q'' : y = z}
  (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
  (a @@ c) @ (b @@ d) = (a @ b) @@ (c @ d).
Proof.
  case d.
  case c.
  case b.
  case a.
  reflexivity.
Defined.
