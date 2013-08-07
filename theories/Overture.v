(* -*- mode: coq; mode: visual-line -*-  *)

(** * Basic definitions of homotopy type theory, particularly the groupoid structure of identity types. *)

(** ** Type classes *)
Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  refine (@transitivity _ R _ x y z _ _).

Tactic Notation "etransitivity" := etransitivity _.

Tactic Notation "symmetry" := refine (@symmetry _ _ _ _ _ _).

(** ** Basic definitions *)

(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation idmap := (fun x => x).

(** We define notation for dependent pairs because it is too annoying to write and see [existT P x y] all the time.  However, we put it in its own scope, because sometimes it is necessary to give the particular dependent type, so we'd like to be able to turn off this notation selectively. *)
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.

(** The following notation is very convenient, although it unfortunately clashes with Proof General's "electric period". *)
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.

(** Composition of functions. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

Hint Unfold compose.

(* We put the following notation in a scope because leaving it unscoped causes it to override identical notations in other scopes.  It's convenient to use the same notation for, e.g., function composition, morphism composition in a category, and functor composition, and let Coq automatically infer which one we mean by scopes.  We can't do this if this notation isn't scoped.  Unfortunately, Coq doesn't have a built-in [function_scope] like [type_scope]; [type_scope] is automatically opened wherever Coq is expecting a [Sort], and it would be nice if [function_scope] were automatically opened whenever Coq expects a thing of type [forall _, _] or [_ -> _].  To work around this, we open [function_scope] globally. *)
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.

(** ** The groupoid structure of identity types. *)

(** The results in this file are used everywhere else, so we need to be extra careful about how we define and prove things.  We prefer hand-written terms, or at least tactics that allow us to retain clear control over the proof-term produced. *)

(** We define our own identity type, rather than using the one in the Coq standard library, so as to have more control over transitivity, symmetry and inverse.  It seems impossible to change these for the standard eq/identity type (or its Type-valued version) because it breaks various other standard things.  Merely changing notations also doesn't seem to quite work. *)
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Arguments paths_ind [A] a P f y p.
Arguments paths_rec [A] a P f y p.
Arguments paths_rect [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Instance reflexive_paths {A} : Reflexive (@paths A) | 0 := @idpath A.

(** We declare a scope in which we shall place path notations. This way they can be turned on and off by the user. *)

Delimit Scope path_scope with path.
Local Open Scope path_scope.

(** We define equality concatenation by destructing on both its arguments, so that it only computes when both arguments are [idpath].  This makes proofs more robust and symmetrical.  Compare with the definition of [identity_trans].  *)

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments concat {A x y z} p q : simpl nomatch.

Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.

(** The inverse of a path. *)
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

(** Declaring this as [simpl nomatch] prevents the tactic [simpl] from expanding it out into [match] statements.  We only want [inverse] to simplify when applied to an identity path. *)
Arguments inverse {A x y} p : simpl nomatch.

Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.


(** Note that you can use the built-in Coq tactics [reflexivity] and [transitivity] when working with paths, but not [symmetry], because it is too smart for its own good.  Hence we have provided replacement [symmetry] and [etransitivity] tactics above. *)

(** The identity path. *)
Notation "1" := idpath : path_scope.

(* The composition of two paths. *)
Notation "p @ q" := (concat p q) (at level 20) : path_scope.

(* The inverse of a path. *)
Notation "p ^" := (inverse p) (at level 3) : path_scope.

(* An alternative notation which puts each path on its own line.  Useful as a temporary device during proofs of equalities between very long composites; to turn it on inside a section, say [Open Scope long_path_scope]. *)
Notation "p @' q" := (concat p q) (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'") : long_path_scope.


(** An important instance of [paths_rect] is that given any dependent type, one can _transport_ elements of instances of the type along equalities in the base.

   [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

(** See above for the meaning of [simpl nomatch]. *)
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

(* We introduce the convention that [apKN] denotes the application of a K-path between
   functions to an N-path between elements, where a 0-path is simply a function or an
   element. Thus, [ap] is a shorthand for [ap01]. *)

Notation ap01 := ap (only parsing).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with idpath => 1 end.

Definition ap10 {A B} {f g:A->B} (h:f=g) : f == g
  := apD10 h.

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.

(** See above for the meaning of [simpl nomatch]. *)
Arguments ap {A B} f {x y} p : simpl nomatch.

(** Similarly, dependent functions act on paths; but the type is a bit more subtle. If [f : forall a:A, B a] and [p : x = y] is a path in [A], then [apD f p] should somehow be a path between [f x : B x] and [f y : B y]. Since these live in different types, we use transport along [p] to make them comparable: [apD f p : p # f x = f y].

  The type [p # f x = f y] can profitably be considered as a heterogeneous or dependent equality type, of "paths from [f x] to [f y] over [p]". *)

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments apD {A B} f {x y} p : simpl nomatch.

(** *** Contractibility *)

(** A space [A] is contractible if there is a point [x : A] and a (pointwise) homotopy connecting the identity on [A] to the constant map at [x].  Thus an element of [contr A] is a pair whose first component is a point [x] and the second component is a pointwise retraction of [A] to [x]. *)

(** We use the [Contr_internal] record so as not to pollute typeclass search; we only do truncation typeclass search on the [IsTrunc] datatype, usually.  We will define a notation [Contr] which is equivalent to [Contr_internal], but picked up by typeclass search.  However, we must make [Contr_internal] a class so that we pick up typeclasses on [center] and [contr].  However, the only typeclass rule we register is the one that turns it into a [Contr]/[IsTrunc]. *)
Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.

(** ** Equivalences *)

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define equivalences, let us consider when two types [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are inverses of each other, up to homotopy.  Homotopically speaking, we should also require a certain condition on these homotopies, which is one of the triangle identities for adjunctions in category theory.  Thus, we call this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the higher coherences, so it is reasonable to only assume one of them.  Moreover, as we will see, if we have maps which are inverses up to homotopy, it is always possible to make the triangle identity hold by modifying one of the homotopies.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map whose homotopy fibers are contractible.  We call this notion a *homotopy bijection*.

   An interesting third option was suggested by André Joyal: a map [f] which has separate left and right homotopy inverses.  We call this notion a *homotopy isomorphism*.

   While the second option was the one used originally, and it is the most concise one, it makes more sense to use the first one in a formalized development, since it exposes most directly equivalence as a structure.  In particular, it is easier to extract directly from it the data of a homotopy inverse to [f], which is what we care about having most in practice.  Thus, adjoint equivalences are what we will refer to merely as *equivalences*. *)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote types of equivalences, and [isequiv] and [IsEquiv] systematically to denote the assertion that a given map is an equivalence. *)

(** The fact that [r] is a left inverse of [s]. It is called [cancel] in ssreflect.  As a mnemonic, note that the partially applied type [Sect s] is the type of proofs that [s] is a section. *)
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Existing Instance equiv_isequiv.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

(** A notation for the inverse of an equivalence.  We can apply this to a function as long as there is a typeclass instance asserting it to be an equivalence.  We can also apply it to an element of [A <~> B], since there is an implicit coercion to [A -> B] and also an existing instance of [IsEquiv]. *)

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

(** *** Truncation levels *)

(* Truncation measures how complicated a type is in terms of higher path spaces. The (-2)-truncated types are the contractible ones, whose homotopy is completely trivial. The (n+1)-truncated types are those whose path spaces are n-truncated.

   Thus, (-1)-truncated means "the space of paths between any two points is contactible". Such a space is necessarily a sub-singleton: any two points are connected by a path which is unique up to homotopy. In other words, (-1)-truncated spaces are truth values (we call them "propositions").

   Next, 0-truncated means "the space of paths between any two points is a sub-singleton". Thus, two points might not have any paths between them, or they have a unique path. Such a space may have many points but it is discrete in the sense that all paths are trivial. We call such spaces "sets".
*)

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

(* We will use [Notation] for [trunc_index]es, so define a scope for them here. *)
Delimit Scope trunc_scope with trunc.
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Notation minus_one:=(trunc_S minus_two).

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

(** We use the priciple that we should always be doing typeclass resolution on truncation of non-equality types.  We try to change the hypotheses and goals so that they never mention something like [IsTrunc n (_ = _)] and instead say [IsTrunc (S n) _].  If you're evil enough that some of your paths [a = b] are n-truncated, but others are not, then you'll have to either reason manually or add some (local) hints with higher priority than the hint below, or generalize your equality type so that it's not a path anymore. *)

Typeclasses Opaque IsTrunc. (* don't auto-unfold [IsTrunc] in typeclass search *)

Arguments IsTrunc : simpl never. (* don't auto-unfold [IsTrunc] with [simpl] *)

Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y)
  := H x y. (* but do fold [IsTrunc] *)

Hint Extern 0 => progress change IsTrunc_internal with IsTrunc in * : typeclass_instances. (* Also fold [IsTrunc_internal] *)

(** Picking up the [forall x y, IsTrunc n (x = y)] instances in the hypotheses is much tricker.  We could do something evil where we declare an empty typeclass like [IsTruncSimplification] and use the typeclass as a proxy for allowing typeclass machinery to factor nested [forall]s into the [IsTrunc] via backward reasoning on the type of the hypothesis... but, that's rather complicated, so we instead explicitly list out a few common cases.  It should be clear how to extend the pattern. *)
Hint Extern 10 =>
progress match goal with
           | [ H : forall x y : ?T, IsTrunc ?n (x = y) |- _ ]
             => change (IsTrunc (trunc_S n) T) in H
           | [ H : forall (a : ?A) (x y : @?T a), IsTrunc ?n (x = y) |- _ ]
             => change (forall a : A, IsTrunc (trunc_S n) (T a)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (x y : @?T a b), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a), IsTrunc (trunc_S n) (T a b)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (x y : @?T a b c), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b), IsTrunc (trunc_S n) (T a b c)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (d : @?D a b c) (x y : @?T a b c d), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b) (d : D a b c), IsTrunc (trunc_S n) (T a b c d)) in H; cbv beta in H
         end.

Notation Contr := (IsTrunc minus_two).
Notation IsHProp := (IsTrunc minus_one).
Notation IsHSet := (IsTrunc 0).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

(** *** Function extensionality *)

(** The function extensionality axiom is formulated as a class. To use it in a theorem, just assume it with [`{Funext}], and then you can use [path_forall], defined below.  If you need function extensionality for a whole development, you can assume it for an entire Section with [Context `{Funext}].  *)
Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

Definition path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y = g x y) -> f = g
  :=
  (fun E => path_forall f g (fun x => path_forall (f x) (g x) (E x))).


(** *** Tactics *)

(** We declare some more [Hint Resolve] hints, now in the "hint database" [path_hints].  In general various hints (resolve, rewrite, unfold hints) can be grouped into "databases". This is necessary as sometimes different kinds of hints cannot be mixed, for example because they would cause a combinatorial explosion or rewriting cycles.

   A specific [Hint Resolve] database [db] can be used with [auto with db].

   The hints in [path_hints] are designed to push concatenation *outwards*, eliminate identities and inverses, and associate to the left as far as  possible. *)

(* TODO: think more carefully about this.  Perhaps associating to the right would be more convenient? *)
Hint Resolve
  @idpath @inverse
 : path_hints.

Hint Resolve @idpath : core.

Ltac path_via mid :=
  apply @concat with (y := mid); auto with path_hints.

(* We put [Empty] here, instead of in [Empty.v], because [Ltac done] uses it. *)
Inductive Empty : Type := .

Definition not (A:Type) : Type := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Hint Unfold not: core.

(* Ssreflect tactics, adapted by Robbert Krebbers *)
Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [apply symmetry; trivial]
      | reflexivity
      (* Discriminate should be here, but it doesn't work yet *)
      (* | discriminate *)
      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

(* A convenient tactic for using function extensionality. *)
Ltac by_extensionality x :=
  intros; unfold compose;
  match goal with
  | [ |- ?f = ?g ] => eapply path_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with path_hints
  end.

(* Removed auto. We can write "by (path_induction;auto with path_hints)"
 if we want to.*)
Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : _ = _  |- _ ] => induction p
      | _ => idtac
    end
  ).

(* The tactic [f_ap] is a replacement for the previously existing standard library tactic [f_equal].  This tactic works by repeatedly applying the fact that [f = g -> x = y -> f x = g y] to turn, e.g., [f x y = f z w] first into [f x = f z] and [y = w], and then turns the first of these into [f = f] and [x = z].  The [done] tactic is used to detect the [f = f] case and finish, and the [trivial] is used to solve, e.g., [x = x] when using [f_ap] on [f y x = f z x].  This tactic only works for non-dependently-typed functions; we cannot express [y = w] in the first example if [y] and [w] have different types.  If and when Arnaud's new-tacticals branch lands, and we can have a goal which depends on the term used to discharge another goal, then this tactic should probably be generalized to deal with dependent functions. *)
Ltac f_ap :=
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g);
                             try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.
