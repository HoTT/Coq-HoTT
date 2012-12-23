(* -*- mode: coq; mode: visual-line -*-  *)
(** * Basic definitions of homotopy type theory, particularly the groupoid structure of identity types. *)

(** ** Basic definitions *)

(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation "'idmap'" := (fun x => x).

(** We define notation for dependent pairs because it is too annoying to write and see [existT P x y] all the time.  However, we put it in its own scope, because sometimes it is necessary to give the particular dependent type, so we'd like to be able to turn off this notation selectively. *)
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.

Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.

(** Composition of functions. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

(** These funny looking types are used to trigger the canonical structures mechanism.
   TODO: No longer needed as we are using typeclasses? *)
Inductive batman T (p : T) := Batman. (* Known as [phantom] in ssreflect. *)
Inductive robin (p : Type) := Robin. (* Known as [phant] in ssreflect. *)

(** ** The groupoid structure of identity types. *)

(** The results in this file are used everywhere else, so we need to be extra careful about how we define and prove things.  We prefer hand-written terms, or at least tactics that allow us to retain clear control over the proof-term produced. *)

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Arguments paths_ind [A] a P f y p.
Arguments paths_rec [A] a P f y p.
Arguments paths_rect [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

(** We declare a scope in which we shall place path notations. This way they can be turned on and off by the user. *)

Delimit Scope path_scope with path.
Local Open Scope path_scope.

(** An important instance of [paths_rect] is that given any dependent type, one can _transport_ elements of instances of the type along equalities in the base.

   [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Arguments transport {A} P {x y} p%path_scope u : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression.*)
Delimit Scope fib_scope with fib.
Local Open Scope fib_scope.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

(** Having defined transport, we can use it to talk about what a homotopy theorist might see as "paths in a fibration over paths in the base"; and what a type theorist might see as "heterogeneous eqality in a dependent type". 

We will first see this appearing in the type of [apD]. *)


(** Functions act on paths: if [f : A -> B] and [p : x = y] is a path in [A], then [ap f p : f x = f y].  

   We typically pronounce [ap] as a single syllable, short for "application"; but it may also be considered as an acronym, "action on paths". *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Arguments ap {A B} f {x y} p : simpl nomatch.

(** Similarly, dependent functions act on paths; but the type is a bit more subtle.  If  [f : forall a:A, B a] and [p : x = y] is a path in [A], then [apD f p] should somehow be a path between [f x : B x] and [f y : B y].  Since these live in different types, we use transport along [p] to make them comparable: [apD f p : p # f x = f y].

  The type [p # f x = f y] can profitably be considered as a heterogeneous or dependent equality type, of "paths from [f x] to [f y] over [p]". *)

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.

Arguments apD {A B} f {x y} p : simpl nomatch.

(** We define equality concatenation by destructing on both its arguments, so that it only computes when both arguments are [idpath].  This makes proofs more robust and symmetrical.  Compare with the definition of [identity_trans].  *)

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Arguments concat {A x y z} p q : simpl nomatch.

(** The inverse of a path. *)
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Arguments inverse {A x y} p : simpl nomatch.

(** Note that you can use the built-in Coq tactics "reflexivity" and "transitivity" when working with paths, but not "symmetry", because it is too smart for its own good.  But you can say "apply inverse" instead.   *)

(** The identity path. *)
Notation "1" := idpath : path_scope.

(* The composition of two paths. *)
Notation "p @ q" := (concat p q) (at level 20) : path_scope.

(* The inverse of a path. *)
Notation "p ^" := (inverse p) (at level 3) : path_scope.

(* An alternative notation which puts each path on its own line.  Useful as a temporary device during proofs of equalities between very long composites; to turn it on inside a section, say [Open Scope long_path_scope]. *)
Notation "p @' q" := (concat p q) (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'") : long_path_scope.

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

   There are also cancelation laws called [cancelR] and [cancelL], which are identical to the 2-dimensional 'whiskering' operations [whiskerR] and [whiskerL].

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
  
(** Inverse is an involution. *)
Definition inv_V {A : Type} {x y : A} (p : x = y) :
  p^^ = p
  :=
  match p with idpath => 1 end.


(* *** Theorems for moving things around in equations. *)

Definition moveR_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  p = r^ @ q -> r @ p = q.
Proof.
  intro h; rewrite h.
  apply concat_p_Vp.
Defined.

Definition moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^ -> r @ p = q.
Proof. 
  intro h; rewrite h.
  apply concat_pV_p.
Defined.

Definition moveR_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
Proof.
  intro h; rewrite h.
  apply concat_V_pp.
Defined.

Definition moveR_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  r = q @ p -> r @ p^ = q.
Proof. 
  intro h; rewrite h.
  apply concat_pp_V.
Defined.

Definition moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r^ @ q = p -> q = r @ p.
Proof.
  intro h; rewrite <- h.
  apply inverse, concat_p_Vp.
Defined.

Definition moveL_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r -> q = r @ p.
Proof.
  intro h; rewrite <- h.
  apply inverse; apply concat_pV_p.
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  intro h; rewrite <- h.
  apply inverse, concat_V_pp.
Defined.

Definition moveL_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  q @ p = r -> q = r @ p^.
Proof.
  intro h; rewrite <- h.
  apply inverse; apply concat_pp_V.
Defined.

Definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p @ q^ = 1 -> p = q.
Proof.
  destruct q.
  simpl. rewrite (concat_p1 p).
  trivial.
Defined.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = 1 -> p = q.
Proof.
  destruct q.
  simpl. rewrite (concat_1p p).
  trivial.
Defined.

Definition moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1 -> p = q^.
Proof.
  destruct q.
  rewrite (concat_p1 p).
  trivial.
Defined.

Definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q @ p = 1 -> p = q^.
Proof.
  destruct q.
  rewrite (concat_1p p).
  trivial.
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  destruct p.
  simpl. rewrite (concat_1p q).
  trivial.
Defined.

Definition moveR_1M {A : Type} {x y : A} (p q : x = y) :
  1 = q @ p^ -> p = q.
Proof.
  destruct p.
  simpl.
  rewrite (concat_p1 q).
  trivial.
Defined.

Definition moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = q @ p -> p^ = q.
Proof.
  destruct p.
  rewrite (concat_p1 q).
  trivial.
Defined.

Definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = p @ q -> p^ = q.
Proof.
  destruct p.
  rewrite (concat_1p q).
  trivial.
Defined.


(** *** Functoriality of functions *)

(** Here we prove that functions behave like functors between groupoids, and that [ap] itself is functorial. *)

(** Functions take identity paths to identity paths. *)
Definition ap_1 {A B : Type} (x : A) (f : A -> B) :
  ap f 1 = 1 :> (f x = f x)
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

Definition ap_p_pp {A B : Type} (f : A -> B) {w x y z : A}
  (r : f w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q).
Proof.
  destruct p, q. simpl. exact (concat_p_pp r 1 1).
Defined.

Definition ap_pp_p {A B : Type} (f : A -> B) {w x y z : A}
  (p : x = y) (q : y = z) (r : f z = f w) :
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
  ap (compose g f) p = ap g (ap f p)
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
  destruct q, s; simpl.
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
  destruct q, s; simpl.
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

(** [ap] for paths between functions. *)

(* We introduce the convention that [apKN] denotes the application of a K-path between functions to an N-path between elements, where a 0-path is simply a function or an element.  Thus, [ap] is a shorthand for [ap01].  *)

Notation ap01 := ap (only parsing).

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g) (x:A)
  : f x = g x
  := match h with idpath => 1 end.

Definition ap10 {A B} {f g:A->B} (h:f=g) (x:A) : f x = g x
  := apD10 h x.

Definition ap10_1 {A B} {f:A->B} (x:A) : ap10 (idpath f) x = 1
  := 1.

Definition ap10_pp {A B} {f f' f'':A->B} (h:f=f') (h':f'=f'') (x:A) :
  ap10 h x @ ap10 h' x = ap10 (h @ h') x.
Proof.
  case h, h'; reflexivity.
Defined.

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.

(** *** Transport and the groupoid structure of paths *)

Definition transport_1 {A : Type} (P : A -> Type) {x : A} (u : P x)
  : 1 # u = u
:= 1.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

(** TODO: The following two results follow directly from [transport_1] and
  [transport_pp].  Is it really necessary to give them separately? *)
Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y) :
  p # p^ # z = z :=
  (match p as i in (_ = y) return (forall z : P y, i # i^ # z = z)
     with idpath => fun _ => 1
   end) z.

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P x) :
  p^ # p # z = z
  := 
  (match p as i return (forall z : P x, i^ # i # z = z)
     with idpath => fun _ => 1
   end) z.

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

(** Dependent transport in a doubly dependent type. *)

Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with idpath => z end.

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

(** *** The behavior of [ap] and [apD]. *)

(** In a constant fibration, [apD] reduces to [ap], modulo [transport_const]. *)
Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
Proof.
  destruct p; reflexivity.
Defined.

(** ** The 2-dimensional groupoid structure *)

(** Horizontal composition of 2-dimensional paths. *)
Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q') :
  p @ q = p' @ q'
  :=
  match h, h' with idpath, idpath => 1 end.

Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.

(** 2-dimensional path inversion *)
Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
  : p^ = q^
  := match h with idpath => 1 end.

(** *** Whiskering, a.k.a. cancellation laws *)

Definition whiskerL {A : Type} {x y z : A} (p : x = y) {q r : y = z} (h : q = r) : p @ q = p @ r
  :=
  1 @@ h.

Notation cancelL := whiskerL (only parsing).

Definition whiskerR {A : Type} {x y z : A} {p q : x = y} (h : p = q) (r : y = z) :
  p @ r = q @ r
  :=
  h @@ 1.

Notation cancelR := whiskerR (only parsing).

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

Definition concat2_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  h @@ 1 = whiskerR h 1 :> (p @ 1 = q @ 1)
  :=
  match h with idpath => 1 end.

Definition concat2_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  1 @@ h = whiskerL 1 h :> (1 @ p = 1 @ q)
  :=
  match h with idpath => 1 end.


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

(** *** Tactics *)

(** We declare some more [Hint Resolve] hints, now in the "hint database" [path_hints].  In general various hints (resolve, rewrite, unfold hints) can be grouped into "databases". This is necessary as sometimes different kinds of hints cannot be mixed, for example because they would cause a combinatorial explosion or rewriting cycles.

   A specific [Hint Resolve] database [db] can be used with [auto with db].

   The hints in [path_hints] are designed to push concatenation *outwards*, eliminate identities and inverses, and associate to the left as far as  possible. *)

(* TODO: think more carefully about this.  Perhaps associating to the right would be more convenient? *)
Hint Resolve
  @idpath @inverse
  concat_1p concat_p1 concat_p_pp
  inv_pp inv_V
 : path_hints.

Hint Resolve @idpath : core.

Ltac path_via mid :=
  apply @concat with (y := mid); auto with path_hints.

