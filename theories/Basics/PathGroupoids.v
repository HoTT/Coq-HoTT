(* -*- mode: coq; mode: visual-line -*-  *)

(** * The groupid structure of paths *)

Require Import Overture.

Local Open Scope path_scope.

(** ** Naming conventions

   We need good naming conventions that allow us to name theorems without looking them up. The names should indicate the structure of the theorem, but they may sometimes be ambiguous, in which case you just have to know what is going on.    We shall adopt the following principles:

   - we are not afraid of long names
   - we are not afraid of short names when they are used frequently
   - we use underscores
   - name of theorems and lemmas are lower-case
   - records and other types may be upper or lower case

   Theorems about concatenation of paths are called [concat_XXX] where [XXX] tells us what is on the left-hand side of the equation. You have to guess the right-hand side. We use the following symbols in [XXX]:

   - [1] means the identity path
   - [p] means 'the path'
   - [V] means 'the inverse path'
   - [A] means '[ap]'
   - [M] means the thing we are moving across equality
   - [x] means 'the point' which is not a path, e.g. in [transport p x]
   - [2] means relating to 2-dimensional paths
   - [3] means relating to 3-dimensional paths, and so on

   Associativity is indicated with an underscore. Here are some examples of how the name gives hints about the left-hand side of the equation.

   - [concat_1p] means [1 * p]
   - [concat_Vp] means [p^ * p]
   - [concat_p_pp] means [p * (q * r)]
   - [concat_pp_p] means [(p * q) * r]
   - [concat_V_pp] means [p^ * (p * q)]
   - [concat_pV_p] means [(q * p^) * p] or [(p * p^) * q], but probably the former because for the latter you could just use [concat_pV].

   Laws about inverse of something are of the form [inv_XXX], and those about [ap] are of the form [ap_XXX], and so on. For example:

   - [inv_pp] is about [(p @ q)^]
   - [inv_V] is about [(p^)^]
   - [inv_A] is about [(ap f p)^]
   - [ap_V] is about [ap f (p^)]
   - [ap_pp] is about [ap f (p @ q)]
   - [ap_idmap] is about [ap idmap p]
   - [ap_1] is about [ap f 1]
   - [ap02_p2p] is about [ap02 f (p @@ q)]

   Then we have laws which move things around in an equation. The naming scheme here is [moveD_XXX]. The direction [D] indicates where to move to: [L] means that we move something to the left-hand side, whereas [R] means we are moving something to the right-hand side. The part [XXX] describes the shape of the side _from_ which we are moving where the thing that is getting moves is called [M].  The presence of 1 next to an [M] generally indicates an *implied* identity path which is inserted automatically after the movement.  Examples:

   - [moveL_pM] means that we transform [p = q @ r] to [p @ r^ = q]
     because we are moving something to the left-hand side, and we are
     moving the right argument of concat.

   - [moveR_Mp] means that we transform [p @ q = r] to [q = p^ @ r]
     because we move to the right-hand side, and we are moving the left
     argument of concat.

   - [moveR_1M] means that we transform [p = q] (rather than [p = 1 @ q]) to [p * q^ = 1].

   There are also cancellation laws called [cancelR] and [cancelL], which are inverse to the 2-dimensional 'whiskering' operations [whiskerR] and [whiskerL].

   We may now proceed with the groupoid structure proper.
*)

(** ** The 1-dimensional groupoid structure. *)

(** The identity path is a right unit. *)
Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p
  :=
  match p with idpath => 1 end.

(** The identity is a left unit. *)
Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p
  :=
  match p with idpath => 1 end.

(** Concatenation is associative. *)
Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r) :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

(** The left inverse law. *)
Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = 1
  :=
  match p with idpath => 1 end.

(** The right inverse law. *)
Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p^ @ p = 1
  :=
  match p with idpath => 1 end.

(** Several auxiliary theorems about canceling inverses across associativity.  These are somewhat redundant, following from earlier theorems.  *)

Definition concat_V_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p^ @ (p @ q) = q
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (p^ @ q) = q
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ q^ = p
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^) @ q = p
  :=
  (match q as i return forall p, (p @ i^) @ i = p with
    idpath =>
    fun p =>
      match p with idpath => 1 end
  end) p.

(** Inverse distributes over concatenation *)
Definition inv_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition inv_Vp {A : Type} {x y z : A} (p : y = x) (q : y = z) :
  (p^ @ q)^ = q^ @ p
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition inv_pV {A : Type} {x y z : A} (p : x = y) (q : z = y) :
  (p @ q^)^ = q @ p^.
Proof.
  destruct p. destruct q. reflexivity.
Defined.

Definition inv_VV {A : Type} {x y z : A} (p : y = x) (q : z = y) :
  (p^ @ q^)^ = q @ p.
Proof.
  destruct p. destruct q. reflexivity.
Defined.

(** Inverse is an involution. *)
Definition inv_V {A : Type} {x y : A} (p : x = y) :
  p^^ = p
  :=
  match p with idpath => 1 end.


(** *** Theorems for moving things around in equations. *)

Definition moveR_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  p = r^ @ q -> r @ p = q.
Proof.
  destruct r.
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^ -> r @ p = q.
Proof.
  destruct p.
  intro h. exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveR_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
Proof.
  destruct r.
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  r = q @ p -> r @ p^ = q.
Proof.
  destruct p.
  intro h. exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r^ @ q = p -> q = r @ p.
Proof.
  destruct r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r -> q = r @ p.
Proof.
  destruct p.
  intro h. exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  destruct r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  q @ p = r -> q = r @ p^.
Proof.
  destruct p.
  intro h. exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p @ q^ = 1 -> p = q.
Proof.
  destruct q.
  intro h. exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = 1 -> p = q.
Proof.
  destruct q.
  intro h. exact ((concat_1p _)^ @ h).
Defined.

Definition moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1 -> p = q^.
Proof.
  destruct q.
  intro h. exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q @ p = 1 -> p = q^.
Proof.
  destruct q.
  intro h. exact ((concat_1p _)^ @ h).
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition moveR_1M {A : Type} {x y : A} (p q : x = y) :
  1 = q @ p^ -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_p1 _)).
Defined.

Definition moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = q @ p -> p^ = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_p1 _)).
Defined.

Definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = p @ q -> p^ = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_1p _)).
Defined.

(* In general, the path we want to move might be arbitrarily deeply nested at the beginning of a long concatenation.  Thus, instead of defining functions such as [moveL_Mp_p], we define a tactical that can repeatedly rewrite with associativity to expose it. *)
Ltac with_rassoc tac :=
  repeat rewrite concat_pp_p;
  tac;
  (* After moving, we reassociate to the left (the canonical direction for paths). *)
  repeat rewrite concat_p_pp.

Ltac rewrite_moveL_Mp_p := with_rassoc ltac:(apply moveL_Mp).
Ltac rewrite_moveL_Vp_p := with_rassoc ltac:(apply moveL_Vp).
Ltac rewrite_moveR_Mp_p := with_rassoc ltac:(apply moveR_Mp).
Ltac rewrite_moveR_Vp_p := with_rassoc ltac:(apply moveR_Vp).

Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = p^ # v -> p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> p^ # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p # u = v -> u = p^ # v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : p^ # u = v -> u = p # v.
Proof.
  destruct p.
  exact idmap.
Defined.

(* We have some coherences between those proofs. *)
Definition moveR_transport_p_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : u = p^ # v)
  : (moveR_transport_p P p u v q)^ = moveL_transport_p P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveR_transport_V_V {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : u = p # v)
  : (moveR_transport_V P p u v q)^ = moveL_transport_V P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_transport_V_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : p # u = v)
  : (moveL_transport_V P p u v q)^ = moveR_transport_V P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_transport_p_V {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : p^ # u = v)
  : (moveL_transport_p P p u v q)^ = moveR_transport_p P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.


(** *** Functoriality of functions *)

(** Here we prove that functions behave like functors between groupoids, and that [ap] itself is functorial. *)

(** Functions take identity paths to identity paths. *)
Definition ap_1 {A B : Type} (x : A) (f : A -> B) :
  ap f 1 = 1 :> (f x = f x)
  :=
  1.

Definition apD_1 {A B} (x : A) (f : forall x : A, B x) :
  apD f 1 = 1 :> (f x = f x)
  :=
  1.

(** Functions commute with concatenation. *)
Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q)
  :=
  match q with
    idpath =>
    match p with idpath => 1 end
  end.

Definition ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q).
Proof.
  destruct p, q. simpl. exact (concat_p_pp r 1 1).
Defined.

Definition ap_pp_p {A B : Type} (f : A -> B) {x y z : A} {w : B}
  (p : x = y) (q : y = z) (r : f z = w) :
  (ap f (p @ q)) @ r = (ap f p) @ (ap f q @ r).
Proof.
  destruct p, q. simpl. exact (concat_pp_p 1 1 r).
Defined.

(** Functions commute with path inverses. *)
Definition inverse_ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  (ap f p)^ = ap f (p^)
  :=
  match p with idpath => 1 end.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^
  :=
  match p with idpath => 1 end.

(** [ap] itself is functorial in the first argument. *)

Definition ap_idmap {A : Type} {x y : A} (p : x = y) :
  ap idmap p = p
  :=
  match p with idpath => 1 end.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.

(* Sometimes we don't have the actual function [compose]. *)
Definition ap_compose' {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun a => g (f a)) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.

(** The action of constant maps. *)
Definition ap_const {A B : Type} {x y : A} (p : x = y) (z : B) :
  ap (fun _ => z) p = 1
  :=
  match p with idpath => idpath end.

(** Naturality of [ap]. *)
Definition concat_Ap {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ (ap g q)
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.

(** Naturality of [ap] at identity. *)
Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y)
  :=
  match q as i in (_ = y) return (p x @ ap f i = i @ p y) with
    | idpath => concat_p1 _ @ (concat_1p _)^
  end.

(** Naturality with other paths hanging around. *)
Definition concat_pA_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w z : B} (r : w = f x) (s : g y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (ap g q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA_p {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w : B} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ ap g q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {z : B} (s : g y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (ap g q @ s).
Proof.
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pA1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = f x) (s : y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pp_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = x) (s : g y = z)
  :
  (r @ p x) @ (ap g q @ s) = (r @ q) @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {z : A} (s : y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (q @ s).
Proof.
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
  (r @ p x) @ ap g q = (r @ q) @ p y.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_p_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {z : A} (s : g y = z)
  :
  p x @ (ap g q @ s) = q @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

(** Some coherence lemmas for functoriality *)

Lemma concat_1p_1 {A} {x : A} (p : x = x) (q : p = 1)
: concat_1p p @ q = ap (fun p' => 1 @ p') q.
Proof.
  rewrite <- (inv_V q).
  set (r := q^). clearbody r; clear q; destruct r.
  reflexivity.
Defined.

Lemma concat_p1_1 {A} {x : A} (p : x = x) (q : p = 1)
: concat_p1 p @ q = ap (fun p' => p' @ 1) q.
Proof.
  rewrite <- (inv_V q).
  set (r := q^). clearbody r; clear q; destruct r.
  reflexivity.
Defined.

(** *** Action of [apD10] and [ap10] on paths. *)

(** Application of paths between functions preserves the groupoid structure *)

Definition apD10_1 {A} {B:A->Type} (f : forall x, B x) (x:A)
  : apD10 (idpath f) x = 1
:= 1.

Definition apD10_pp {A} {B:A->Type} {f f' f'' : forall x, B x}
  (h:f=f') (h':f'=f'') (x:A)
: apD10 (h @ h') x = apD10 h x @ apD10 h' x.
Proof.
  case h, h'; reflexivity.
Defined.

Definition apD10_V {A} {B:A->Type} {f g : forall x, B x} (h:f=g) (x:A)
  : apD10 (h^) x = (apD10 h x)^
:= match h with idpath => 1 end.

Definition ap10_1 {A B} {f:A->B} (x:A) : ap10 (idpath f) x = 1
  := 1.

Definition ap10_pp {A B} {f f' f'':A->B} (h:f=f') (h':f'=f'') (x:A)
  : ap10 (h @ h') x = ap10 h x @ ap10 h' x
:= apD10_pp h h' x.

Definition ap10_V {A B} {f g : A->B} (h : f = g) (x:A)
  : ap10 (h^) x = (ap10 h x)^
:= apD10_V h x.

(** [apD10] and [ap10] also behave nicely on paths produced by [ap] *)
Definition apD10_ap_precompose {A B C} (f : A -> B) {g g' : forall x:B, C x} (p : g = g') a
: apD10 (ap (fun h : forall x:B, C x => h oD f) p) a = apD10 p (f a).
Proof.
  destruct p; reflexivity.
Defined.

Definition ap10_ap_precompose {A B C} (f : A -> B) {g g' : B -> C} (p : g = g') a
: ap10 (ap (fun h : B -> C => h o f) p) a = ap10 p (f a)
:= apD10_ap_precompose f p a.

Definition apD10_ap_postcompose {A B C} (f : forall x, B x -> C) {g g' : forall x:A, B x} (p : g = g') a
: apD10 (ap (fun h : forall x:A, B x => fun x => f x (h x)) p) a = ap (f a) (apD10 p a).
Proof.
  destruct p; reflexivity.
Defined.

Definition ap10_ap_postcompose {A B C} (f : B -> C) {g g' : A -> B} (p : g = g') a
: ap10 (ap (fun h : A -> B => f o h) p) a = ap f (ap10 p a)
:= apD10_ap_postcompose (fun a => f) p a.

(** *** Transport and the groupoid structure of paths *)

Definition transport_1 {A : Type} (P : A -> Type) {x : A} (u : P x)
  : 1 # u = u
:= 1.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z
  := (transport_pp P p^ p z)^
  @ ap (fun r => transport P r z) (concat_Vp p).

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P x)
  : p^ # p # z = z
  := (transport_pp P p p^ z)^
  @ ap (fun r => transport P r z) (concat_pV p).

(** In the future, we may expect to need some higher coherence for transport:
  for instance, that transport acting on the associator is trivial. *)
Definition transport_p_pp {A : Type} (P : A -> Type)
  {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  (u : P x)
  : ap (fun e => e # u) (concat_p_pp p q r)
    @ (transport_pp P (p@q) r u) @ ap (transport P r) (transport_pp P p q u)
  = (transport_pp P p (q@r) u) @ (transport_pp P q r (p#u))
  :> ((p @ (q @ r)) # u = r # q # p # u) .
Proof.
  destruct p, q, r.  simpl.  exact 1.
Defined.

(* Here are other coherence lemmas for transport. *)
Definition transport_pVp {A} (P : A -> Type) {x y:A} (p:x=y) (z:P x)
  : transport_pV P p (transport P p z)
  = ap (transport P p) (transport_Vp P p z).
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_VpV {A} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : transport_Vp P p (transport P p^ z)
    = ap (transport P p^) (transport_pV P p z).
Proof.
  destruct p; reflexivity.
Defined.

Definition ap_transport_transport_pV {A} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (e : transport P p u = v)
  : ap (transport P p) (moveL_transport_V P p u v e)
       @ transport_pV P p v = e.
Proof.
    by destruct e, p.
Defined.

Definition moveL_transport_V_1 {A} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x)
  : moveL_transport_V P p u (p # u) 1 = (transport_Vp P p u)^.
    (* moveL_transport_V P p (transport P p^ v) (transport P p (transport P p^ v)) 1 *)
    (* = ap (transport P p^) (transport_pV P p v)^. *)
Proof.
  (* pose (u := p^ # v).  *)
  (* assert (moveL_transport_V P p u (p # u) 1 = (transport_Vp P p u)^). *)
  destruct p; reflexivity.
  (* subst u. rewrite X. *)
Defined.


(** ** [ap11] *)

Definition ap11_is_ap10_ap01 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y)
: ap11 h p = ap10 h x @ ap g p.
Proof.
  by path_induction.
Defined.

(** Dependent transport in doubly dependent types and more. *)

Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with idpath => z end.

Definition transportD2 {A : Type} (B C : A -> Type) (D : forall a:A, B a -> C a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z)
  : D x2 (p # y) (p # z)
  :=
  match p with idpath => w end.

(** *** [ap] for multivariable functions *)

Definition ap011 {A B C} (f : A -> B -> C) {x x' y y'} (p : x = x') (q : y = y')
: f x y = f x' y'
:= ap11 (ap f p) q.

(** It would be nice to have a consistent way to name the different ways in which this can be dependent.  The following are a sort of half-hearted attempt. *)

Definition ap011D {A B C} (f : forall (a:A), B a -> C)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: f x y = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition ap01D1 {A B C} (f : forall (a:A), B a -> C a)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport C p (f x y) = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition apD011 {A B C} (f : forall (a:A) (b:B a), C a b)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport (C x') q (transportD B C p y (f x y)) = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

(** Transporting along higher-dimensional paths *)

Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P x)
  : p # z = q # z
  := ap (fun p' => p' # z) r.

(** An alternative definition. *)
Definition transport2_is_ap10 {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q r z = ap10 (ap (transport Q) r) z
  := match r with idpath => 1 end.

Definition transport2_p2p {A : Type} (P : A -> Type) {x y : A} {p1 p2 p3 : x = y}
  (r1 : p1 = p2) (r2 : p2 = p3) (z : P x)
  : transport2 P (r1 @ r2) z = transport2 P r1 z @ transport2 P r2 z.
Proof.
  destruct r1, r2; reflexivity.
Defined.

Definition transport2_V {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q (r^) z = (transport2 Q r z)^
  := match r with idpath => 1 end.

Definition concat_AT {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  {z w : P x} (r : p = q) (s : z = w)
  : ap (transport P p) s  @  transport2 P r w
    = transport2 P r z  @  ap (transport P q) s
  := match r with idpath => (concat_p1 _ @ (concat_1p _)^) end.

(* TODO: What should this be called? *)
Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof.
  by induction p.
Defined.

Lemma ap_transportD {A : Type}
      (B : A -> Type) (C1 C2 : forall a : A, B a -> Type)
      (f : forall a b, C1 a b -> C2 a b)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C1 x1 y)
: f x2 (p # y) (transportD B C1 p y z)
  = transportD B C2 p y (f x1 y z).
Proof.
  by induction p.
Defined.

Lemma ap_transportD2 {A : Type}
      (B C : A -> Type) (D1 D2 : forall a, B a -> C a -> Type)
      (f : forall a b c, D1 a b c -> D2 a b c)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D1 x1 y z)
: f x2 (p # y) (p # z) (transportD2 B C D1 p y z w)
  = transportD2 B C D2 p y z (f x1 y z w).
Proof.
  by induction p.
Defined.

(* TODO: What should this be called? *)
Lemma ap_transport_pV {X} (Y : X -> Type) {x1 x2 : X} (p : x1 = x2)
      {y1 y2 : Y x2} (q : y1 = y2)
: ap (transport Y p) (ap (transport Y p^) q) =
  transport_pV Y p y1 @ q @ (transport_pV Y p y2)^.
Proof.
  destruct p, q; reflexivity.
Defined.

(* TODO: And this? *)
Definition transport_pV_ap {X} (P : X -> Type) (f : forall x, P x)
      {x1 x2 : X} (p : x1 = x2)
: ap (transport P p) (apD f p^) @ apD f p = transport_pV P p (f x2).
Proof.
  destruct p; reflexivity.
Defined.

Definition apD_pp {A} {P : A -> Type} (f : forall x, P x)
           {x y z : A} (p : x = y) (q : y = z)
  : apD f (p @ q)
    = transport_pp P p q (f x) @ ap (transport P q) (apD f p) @ apD f q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition apD_V {A} {P : A -> Type} (f : forall x, P x)
           {x y : A} (p : x = y)
  : apD f p^ = moveR_transport_V _ _ _ _ (apD f p)^.
Proof.
  destruct p; reflexivity.
Defined.


(** *** Transporting in particular fibrations. *)

(** One frequently needs lemmas showing that transport in a certain dependent type is equal to some more explicitly defined operation, defined according to the structure of that dependent type.  For most dependent types, we prove these lemmas in the appropriate file in the types/ subdirectory.  Here we consider only the most basic cases. *)

(** Transporting in a constant fibration. *)
Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.  exact 1.
Defined.

Definition transport2_const {A B : Type} {x1 x2 : A} {p q : x1 = x2}
  (r : p = q) (y : B)
  : transport_const p y = transport2 (fun _ => B) r y @ transport_const q y
  := match r with idpath => (concat_1p _)^ end.

(** Transporting in a pulled back fibration. *)
Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Proof.
  destruct p; reflexivity.
Defined.

Lemma transportD_compose {A A'} B {x x' : A} (C : forall x : A', B x -> Type) (f : A -> A')
      (p : x = x') y (z : C (f x) y)
: transportD (B o f) (C oD f) p y z
  = transport (C (f x')) (transport_compose B f p y)^ (transportD B C (ap f p) y z).
Proof.
  destruct p; reflexivity.
Defined.

(* TODO: Is there a lemma like [transportD_compose], but for [apD], which subsumes this? *)
Lemma transport_apD_transportD {A} B (f : forall x : A, B x) (C : forall x, B x -> Type)
      {x1 x2 : A} (p : x1 = x2) (z : C x1 (f x1))
: apD f p # transportD B C p _ z
  = transport (fun x => C x (f x)) p z.
Proof.
  destruct p; reflexivity.
Defined.

Lemma transport_precompose {A B C} (f : A -> B) (g g' : B -> C) (p : g = g')
: transport (fun h : B -> C => g o f = h o f) p 1 =
  ap (fun h => h o f) p.
Proof.
  destruct p; reflexivity.
Defined.

(** A special case of [transport_compose] which seems to come up a lot. *)
Definition transport_idmap_ap A (P : A -> Type) x y (p : x = y) (u : P x)
: transport P p u = transport idmap (ap P p) u
  := match p with idpath => idpath end.

(** Sometimes, it's useful to have the goal be in terms of [ap], so we can use lemmas about [ap].  However, we can't just [rewrite !transport_idmap_ap], as that's likely to loop.  So, instead, we provide a tactic [transport_to_ap], that replaces all [transport P p u] with [transport idmap (ap P p) u] for non-[idmap] [P]. *)
Ltac transport_to_ap :=
  repeat match goal with
           | [ |- context[transport ?P ?p ?u] ]
             => match P with
                  | idmap => fail 1 (* we don't want to turn [transport idmap (ap _ _)] into [transport idmap (ap idmap (ap _ _))] *)
                  | _ => idtac
                end;
               progress rewrite (transport_idmap_ap _ P _ _ p u)
         end.

(** Transporting in a fibration dependent on two independent types commutes. *)
Definition transport_transport {A B} (C : A -> B -> Type)
           {x1 x2 : A} (p : x1 = x2) {y1 y2 : B} (q : y1 = y2)
           (c : C x1 y1)
: transport (C x2) q (transport (fun x => C x y1) p c)
  = transport (fun x => C x y2) p (transport (C x1) q c).
Proof.
  destruct p, q; reflexivity.
Defined.

(** *** The behavior of [ap] and [apD]. *)

(** In a constant fibration, [apD] reduces to [ap], modulo [transport_const]. *)
Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
Proof.
  destruct p; reflexivity.
Defined.

Definition apD_compose {A A' : Type} {B : A' -> Type} (g : A -> A')
  (f : forall a, B a) {x y : A} (p : x = y)
  : apD (f o g) p  = (transport_compose _ _ _ _) @ apD f (ap g p).
Proof.
  by destruct p.
Defined.

Definition apD_compose' {A A' : Type} {B : A' -> Type} (g : A -> A')
  (f : forall a, B a) {x y : A} (p : x = y)
  : apD f (ap g p) = (transport_compose B _ _ _)^ @ apD (f o g) p.
Proof.
  by destruct p.
Defined.

(** ** The 2-dimensional groupoid structure *)

(** Horizontal composition of 2-dimensional paths. *)
Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'
:= match h, h' with idpath, idpath => 1 end.

Notation "p @@ q" := (concat2 p q)%path : path_scope.

Arguments concat2 : simpl nomatch.

Lemma concat2_ap_ap {A B : Type} {x' y' z' : B}
           (f : A -> (x' = y')) (g : A -> (y' = z'))
           {x y : A} (p : x = y)
: (ap f p) @@ (ap g p) = ap (fun u => f u @ g u) p.
Proof.
    by path_induction.
Defined.

(** 2-dimensional path inversion *)
Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
  : p^ = q^
:= ap inverse h.

(** Some higher coherences *)

Lemma ap_pp_concat_pV {A B} (f : A -> B) {x y : A} (p : x = y)
: ap_pp f p p^ @ ((1 @@ ap_V f p) @ concat_pV (ap f p))
  = ap (ap f) (concat_pV p).
Proof.
  destruct p; reflexivity.
Defined.

Lemma ap_pp_concat_Vp {A B} (f : A -> B) {x y : A} (p : x = y)
: ap_pp f p^ p @ ((ap_V f p @@ 1) @ concat_Vp (ap f p))
  = ap (ap f) (concat_Vp p).
Proof.
  destruct p; reflexivity.
Defined.

Lemma concat_pV_inverse2 {A} {x y : A} (p q : x = y) (r : p = q)
: (r @@ inverse2 r) @ concat_pV q = concat_pV p.
Proof.
  destruct r, p; reflexivity.
Defined.

Lemma concat_Vp_inverse2 {A} {x y : A} (p q : x = y) (r : p = q)
: (inverse2 r @@ r) @ concat_Vp q = concat_Vp p.
Proof.
  destruct r, p; reflexivity.
Defined.

(** *** Whiskering *)

Definition whiskerL {A : Type} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p @ q = p @ r
:= 1 @@ h.

Definition whiskerR {A : Type} {x y z : A} {p q : x = y}
  (h : p = q) (r : y = z) : p @ r = q @ r
:= h @@ 1.

(** *** Unwhiskering, a.k.a. cancelling. *)

Definition cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) -> (q = r)
:= fun h => (concat_V_pp p q)^ @ whiskerL p^ h @ (concat_V_pp p r).

Definition cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p @ r = q @ r) -> (p = q)
:= fun h => (concat_pp_V p r)^ @ whiskerR h r^ @ (concat_pp_V q r).

(** Whiskering and identity paths. *)

Definition whiskerR_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_p1 p) ^ @ whiskerR h 1 @ concat_p1 q = h
  :=
  match h with idpath =>
    match p with idpath =>
      1
    end end.

Definition whiskerR_1p {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerR 1 q = 1 :> (p @ q = p @ q)
  :=
  match q with idpath => 1 end.

Definition whiskerL_p1 {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerL p 1 = 1 :> (p @ q = p @ q)
  :=
  match q with idpath => 1 end.

Definition whiskerL_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_1p p) ^ @ whiskerL 1 h @ concat_1p q = h
  :=
  match h with idpath =>
    match p with idpath =>
      1
    end end.

Definition whiskerR_p1_1 {A} {x : A} (h : idpath x = idpath x)
: whiskerR h 1 = h.
Proof.
  refine (_ @ whiskerR_p1 h); simpl.
  symmetry; refine (concat_p1 _ @ concat_1p _).
Defined.

Definition whiskerL_1p_1 {A} {x : A} (h : idpath x = idpath x)
: whiskerL 1 h = h.
Proof.
  refine (_ @ whiskerL_1p h); simpl.
  symmetry; refine (concat_p1 _ @ concat_1p _).
Defined.

Definition concat2_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  h @@ 1 = whiskerR h 1 :> (p @ 1 = q @ 1)
  :=
  match h with idpath => 1 end.

Definition concat2_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  1 @@ h = whiskerL 1 h :> (1 @ p = 1 @ q)
  :=
  match h with idpath => 1 end.

Definition cancel2L {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
           (g : p = p') (h k : q = q')
: (g @@ h = g @@ k) -> (h = k).
Proof.
  intro r. induction g, p, q.
  refine ((whiskerL_1p h)^ @ _). refine (_ @ (whiskerL_1p k)).
  refine (whiskerR _ _). refine (whiskerL _ _).
  apply r.
Defined.

Definition cancel2R {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
           (g h : p = p') (k : q = q')
: (g @@ k = h @@ k) -> (g = h).
Proof.
  intro r. induction k, p, q.
  refine ((whiskerR_p1 g)^ @ _). refine (_ @ (whiskerR_p1 h)).
  refine (whiskerR _ _). refine (whiskerL _ _).
  apply r.
Defined.


(** Whiskering and composition *)

(* The naming scheme for these is a little unclear; should [pp] refer to concatenation of the 2-paths being whiskered or of the paths we are whiskering by? *)
Definition whiskerL_pp {A} {x y z : A} (p : x = y) {q q' q'' : y = z}
           (r : q = q') (s : q' = q'')
: whiskerL p (r @ s) = whiskerL p r @ whiskerL p s.
Proof.
  destruct p, r, s; reflexivity.
Defined.

Definition whiskerR_pp {A} {x y z : A} {p p' p'' : x = y} (q : y = z)
           (r : p = p') (s : p' = p'')
: whiskerR (r @ s) q = whiskerR r q @ whiskerR s q.
Proof.
  destruct q, r, s; reflexivity.
Defined.

(* For now, I've put an [L] or [R] to mark when we're referring to the whiskering paths. *)
Definition whiskerL_VpL {A} {x y z : A} (p : x = y)
           {q q' : y = z} (r : q = q')
: (concat_V_pp p q)^ @ whiskerL p^ (whiskerL p r) @ concat_V_pp p q'
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

Definition whiskerL_pVL {A} {x y z : A} (p : y = x)
           {q q' : y = z} (r : q = q')
: (concat_p_Vp p q)^ @ whiskerL p (whiskerL p^ r) @ concat_p_Vp p q'
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

Definition whiskerR_pVR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : y = z)
: (concat_pp_V p q)^ @ whiskerR (whiskerR r q) q^ @ concat_pp_V p' q
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

Definition whiskerR_VpR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : z = y)
: (concat_pV_p p q)^ @ whiskerR (whiskerR r q^) q @ concat_pV_p p' q
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

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

(** The interchange law for whiskering.  Special case of [concat_concat2]. *)
Definition concat_whisker {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whiskerR a q) @ (whiskerL p' b) = (whiskerL p b) @ (whiskerR a q')
  :=
  match b with
    idpath =>
    match a with idpath =>
      (concat_1p _)^
    end
  end.

(** Structure corresponding to the coherence equations of a bicategory. *)

(** The "pentagonator": the 3-cell witnessing the associativity pentagon. *)
Definition pentagon {A : Type} {v w x y z : A} (p : v = w) (q : w = x) (r : x = y) (s : y = z)
  : whiskerL p (concat_p_pp q r s)
      @ concat_p_pp p (q@r) s
      @ whiskerR (concat_p_pp p q r) s
  = concat_p_pp p q (r@s) @ concat_p_pp (p@q) r s.
Proof.
  case p, q, r, s.  reflexivity.
Defined.

(** The 3-cell witnessing the left unit triangle. *)
Definition triangulator {A : Type} {x y z : A} (p : x = y) (q : y = z)
  : concat_p_pp p 1 q @ whiskerR (concat_p1 p) q
  = whiskerL p (concat_1p q).
Proof.
  case p, q.  reflexivity.
Defined.

(** The Eckmann-Hilton argument *)
Definition eckmann_hilton {A : Type} {x:A} (p q : 1 = 1 :> (x = x)) : p @ q = q @ p :=
  (whiskerR_p1 p @@ whiskerL_1p q)^
  @ (concat_p1 _ @@ concat_p1 _)
  @ (concat_1p _ @@ concat_1p _)
  @ (concat_whisker _ _ _ _ p q)
  @ (concat_1p _ @@ concat_1p _)^
  @ (concat_p1 _ @@ concat_p1 _)^
  @ (whiskerL_1p q @@ whiskerR_p1 p).

(** The action of functions on 2-dimensional paths *)

Definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q
  := match r with idpath => 1 end.

Definition ap02_pp {A B} (f:A->B) {x y:A} {p p' p'':x=y} (r:p=p') (r':p'=p'')
  : ap02 f (r @ r') = ap02 f r @ ap02 f r'.
Proof.
  case r, r'; reflexivity.
Defined.

Definition ap02_p2p {A B} (f:A->B) {x y z:A} {p p':x=y} {q q':y=z} (r:p=p') (s:q=q')
  : ap02 f (r @@ s) =   ap_pp f p q
                      @ (ap02 f r  @@  ap02 f s)
                      @ (ap_pp f p' q')^.
Proof.
  case r, s, p, q. reflexivity.
Defined.

Definition apD02 {A : Type} {B : A -> Type} {x y : A} {p q : x = y}
  (f : forall x, B x) (r : p = q)
  : apD f p = transport2 B r (f x) @ apD f q
  := match r with idpath => (concat_1p _)^ end.

Definition apD02_const {A B : Type} (f : A -> B) {x y : A} {p q : x = y} (r : p = q)
: apD02 f r = (apD_const f p)
              @ (transport2_const r (f x) @@ ap02 f r)
              @ (concat_p_pp _ _ _)^
              @ (whiskerL (transport2 _ r (f x)) (apD_const f q)^)
:=
  match r with idpath =>
    match p with idpath => 1
    end end.

(* And now for a lemma whose statement is much longer than its proof. *)
Definition apD02_pp {A} (B : A -> Type) (f : forall x:A, B x) {x y : A}
  {p1 p2 p3 : x = y} (r1 : p1 = p2) (r2 : p2 = p3)
  : apD02 f (r1 @ r2)
  = apD02 f r1
  @ whiskerL (transport2 B r1 (f x)) (apD02 f r2)
  @ concat_p_pp _ _ _
  @ (whiskerR (transport2_p2p B r1 r2 (f x))^ (apD f p3)).
Proof.
  destruct r1, r2. destruct p1. reflexivity.
Defined.

(** These lemmas need better names. *)
Definition ap_transport_Vp_idmap {A B} (p q : A = B) (r : q = p) (z : A)
: ap (transport idmap q^) (ap (fun s => transport idmap s z) r)
  @ ap (fun s => transport idmap s (p # z)) (inverse2 r)
  @ transport_Vp idmap p z
  = transport_Vp idmap q z.
Proof.
  by path_induction.
Defined.

Definition ap_transport_pV_idmap {A B} (p q : A = B) (r : q = p) (z : B)
: ap (transport idmap q) (ap (fun s => transport idmap s^ z) r)
  @ ap (fun s => transport idmap s (p^ # z)) r
  @ transport_pV idmap p z
  = transport_pV idmap q z.
Proof.
  by path_induction.
Defined.

(** ** Tactics, hints, and aliases *)

(** [concat], with arguments flipped. Useful mainly in the idiom [apply (concatR (expression))]. Given as a notation not a definition so that the resultant terms are literally instances of [concat], with no unfolding required. *)
Notation concatR := (fun p q => concat q p).

Hint Resolve
  concat_1p concat_p1 concat_p_pp
  inv_pp inv_V
 : path_hints.

(* First try at a paths db
We want the RHS of the equation to become strictly simpler *)
Hint Rewrite
@concat_p1
@concat_1p
@concat_p_pp (* there is a choice here !*)
@concat_pV
@concat_Vp
@concat_V_pp
@concat_p_Vp
@concat_pp_V
@concat_pV_p
(*@inv_pp*) (* I am not sure about this one *)
@inv_V
@moveR_Mp
@moveR_pM
@moveL_Mp
@moveL_pM
@moveL_1M
@moveL_M1
@moveR_M1
@moveR_1M
@ap_1
(* @ap_pp
@ap_p_pp ?*)
@inverse_ap
@ap_idmap
(* @ap_compose
@ap_compose'*)
@ap_const
(* Unsure about naturality of [ap], was absent in the old implementation*)
@apD10_1
:paths.

Ltac hott_simpl :=
  autorewrite with paths in * |- * ; auto with path_hints.
