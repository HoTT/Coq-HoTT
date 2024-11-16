(** * Basic definitions of homotopy type theory *)

(** This file defines some of the most basic types and type formers, such as sums, products, Sigma types and path types.  It defines the action of functions on paths [ap], transport, equivalences, and function extensionality.  It also defines truncatedness, and a number of other fundamental definitions used throughout the library. *)

(** Import the file of reserved notations so we maintain consistent level notations throughout the library. *)
Require Export Basics.Settings Basics.Notations.

Local Set Polymorphic Inductive Cumulativity.

(** This command prevents Coq from automatically defining the eliminator functions for inductive types.  We will define them ourselves to match the naming scheme of the HoTT Book.  In principle we ought to make this [Global], but unfortunately the tactics [induction] and [elim] assume that the eliminators are named in Coq's way, e.g. [thing_rect], so making it global could cause unpleasant surprises for people defining new inductive types.  However, when you do define your own inductive types you are encouraged to also do [Local Unset Elimination Schemes] and then use [Scheme] to define [thing_ind], [thing_rec], and (for compatibility with [induction] and [elim]) [thing_rect], as we have done below for [paths], [Empty], [Unit], etc.  We are hoping that this will be fixed eventually; see https://github.com/coq/coq/issues/3745.  *)
Local Unset Elimination Schemes.

(** ** Datatypes *)

(** *** Functions *)

(** Notation for non-dependent function types *)
Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** *** Option type *)

(** [option A] is the extension of [A] with an extra element [None] *)
Inductive option (A : Type) : Type :=
| Some : A -> option A
| None : option A.

Scheme option_rect := Induction for option Sort Type.

Arguments Some {A} a.
Arguments None {A}.

Register option as core.option.type.

(** *** Sum type *)

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)
Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.

Scheme sum_rect := Induction for sum Sort Type.
Scheme sum_ind := Induction for sum Sort Type.
Arguments sum_ind {A B} P f g : rename.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* A notation for coproduct that's less overloaded than [+] *)
Notation "x |_| y" := (sum x y) (only parsing) : type_scope.

(** *** Product type *)

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)
Record prod (A B : Type) := pair { fst : A ; snd : B }.

Scheme prod_rect := Induction for prod Sort Type.
Scheme prod_ind := Induction for prod Sort Type.
Arguments prod_ind {A B} P _. 

Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "A /\ B" := (prod A B) (only parsing) : type_scope.
Notation and := prod (only parsing).
Notation conj := pair (only parsing).

#[export] Hint Resolve pair inl inr : core.

(** ** Type classes *)

(** This command prevents Coq from trying to guess the values of existential variables while doing typeclass resolution.  If you don't know what that means, ignore it. *)
Local Set Typeclasses Strict Resolution.

Definition Relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : Relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : Relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : Relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

(** A [PreOrder] is both Reflexive and Transitive. *)
Class PreOrder {A} (R : Relation A) :=
  { PreOrder_Reflexive : Reflexive R | 2 ;
    PreOrder_Transitive : Transitive R | 2 }.

Global Existing Instance PreOrder_Reflexive.
Global Existing Instance PreOrder_Transitive.

Arguments reflexivity {A R _} / _.
Arguments symmetry {A R _} / _ _ _.
Arguments transitivity {A R _} / {_ _ _} _ _.

(** Above, we have made [reflexivity], [symmetry], and [transitivity] reduce under [cbn]/[simpl] to their underlying instances.  This allows the tactics to build proof terms referencing, e.g., [concat].  We use [change] after the fact to make sure that we didn't [cbn] away the original form of the relation.

    If we want to remove the use of [cbn], we can play tricks with [Module Type]s and [Module]s to declare [inverse] directly as an instance of [Symmetric] without changing its type.  Then we can simply [unfold symmetry].  See the comments around the definition of [inverse]. *)

(** Overwrite [reflexivity] so that we use our version of [Reflexive] rather than having the tactic look for it in the standard library.  We make use of the built-in reflexivity to handle, e.g., single-constructor inductives. *)
Ltac old_reflexivity := reflexivity.
Tactic Notation "reflexivity" :=
  old_reflexivity
|| (intros;
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let pre_proof_term_head := constr:(@reflexivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  apply (proof_term_head : forall x, R x x)).

(** Even if we weren't using [cbn], we would have to redefine symmetry, since the built-in Coq version is sometimes too smart for its own good, and will occasionally fail when it should not. *)
Tactic Notation "symmetry" :=
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let x := match goal with |- ?R ?x ?y => constr:(x) end in
  let y := match goal with |- ?R ?x ?y => constr:(y) end in
  let pre_proof_term_head := constr:(@symmetry _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head y x _); change (R y x).

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].

Tactic Notation "etransitivity" := etransitivity _.

(** We redefine [transitivity] to work without needing to include [Setoid] or be using Leibniz equality, and to give proofs that unfold to [concat]. *)
Tactic Notation "transitivity" constr(x) := etransitivity x.

(** ** Basic definitions *)

(** Define an alias for [Set], which is really [Type₀]. *)
Notation Type0 := Set.

(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation idmap := (fun x => x).

(** *** Constant functions *)
Definition const {A B} (b : B) := fun x : A => b.

(** ** Sigma types *)

(** [(sig A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type. *)
Record sig {A} (P : A -> Type) := exist {
  proj1 : A ;
  proj2 : P proj1 ;
}.

Scheme sig_rect := Induction for sig Sort Type.
Scheme sig_ind := Induction for sig Sort Type.
Scheme sig_rec := Minimality for sig Sort Type.

Arguments sig_ind {_ _}.
Arguments sig_rec {_ _ _}.

(** We make the parameters maximally inserted so that we can pass around [pr1] as a function and have it actually mean "first projection" in, e.g., [ap]. *)

Arguments exist {A}%_type P%_type _ _.
Arguments proj1 {A P} _ / .
Arguments proj2 {A P} _ / .

Arguments sig (A P)%_type.

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
Notation "{ x : A | P }" := (sig (A := A) (fun x => P)) : type_scope.
Notation "'exists' x .. y , p" := (sig (fun x => .. (sig (fun y => p)) ..)) : type_scope.
Notation "{ x : A  & P }" := (sig (fun x:A => P)) : type_scope.

(** This lets us pattern match sigma types in let expressions *)
Add Printing Let sig.
  
Register sig as core.sigT.type.
Register exist as core.sigT.intro.
Register sig_rect as core.sigT.rect.
Register proj1 as core.sigT.proj1.
Register proj2 as core.sigT.proj2.

#[export] Hint Resolve exist : core.

(** We define notation for dependent pairs because it is too annoying to write and see [exist P x y] all the time.  However, we put it in its own scope, because sometimes it is necessary to give the particular dependent type, so we'd like to be able to turn off this notation selectively. *)
Notation "( x ; y )" := (exist _ x y) : fibration_scope.
Notation "( x ; .. ; y ; z )" := (exist _ x .. (exist _ y z) ..) : fibration_scope.
(** We bind [fibration_scope] with [sig] so that we are automatically in [fibration_scope] when we are passing an argument of type [sig]. *)
Bind Scope fibration_scope with sig.

Notation pr1 := proj1.
Notation pr2 := proj2.

(** The following notation is very convenient, although it unfortunately clashes with Proof General's "electric period".  We have added [format] specifiers in Notations.v so that it will display without an extra space, as [x.1] rather than as [x .1]. *)
Notation "x .1" := (pr1 x) : fibration_scope.
Notation "x .2" := (pr2 x) : fibration_scope.

Definition uncurry {A B C} (f : A -> B -> C) (p : A * B) : C := f (fst p) (snd p).

Arguments uncurry {A B C} f%_function_scope p /. 

(** Composition of functions. *)

Notation compose := (fun g f x => g (f x)).

(** We put the following notation in a scope because leaving it unscoped causes it to override identical notations in other scopes.  It's convenient to use the same notation for, e.g., function composition, morphism composition in a category, and functor composition, and let Coq automatically infer which one we mean by scopes.  We can't do this if this notation isn't scoped.  Unfortunately, Coq doesn't have a built-in [function_scope] like [type_scope]; [type_scope] is automatically opened wherever Coq is expecting a [Sort], and it would be nice if [function_scope] were automatically opened whenever Coq expects a thing of type [forall _, _] or [_ -> _].  To work around this, we open [function_scope] globally. *)

(** We allow writing [(f o g)%function] to force [function_scope] over, e.g., [morphism_scope]. *)

Notation "g 'o' f" := (compose g%function f%function) : function_scope.

(** This definition helps guide typeclass inference. *)
Definition Compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := compose g f.

(** Dependent composition of functions. *)
Definition composeD {A B C} (g : forall b, C b) (f : A -> B) := fun x : A => g (f x).

Global Arguments composeD {A B C}%_type_scope (g f)%_function_scope x.

#[export] Hint Unfold composeD : core.

Notation "g 'oD' f" := (composeD g f) : function_scope.

(** ** The groupoid structure of identity types. *)

(** The results in this file are used everywhere else, so we need to be extra careful about how we define and prove things.  We prefer hand-written terms, or at least tactics that allow us to retain clear control over the proof-term produced. *)

(** We define our own identity type, rather than using the one in the Coq standard library, so as to have more control over transitivity, symmetry and inverse.  It seems impossible to change these for the standard eq/identity type (or its Type-valued version) because it breaks various other standard things.  Merely changing notations also doesn't seem to quite work. *)
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

#[export] Hint Resolve idpath : core.

Scheme paths_ind := Induction for paths Sort Type.
Arguments paths_ind [A] a P f y p : rename.
Scheme paths_rec := Minimality for paths Sort Type.
Arguments paths_rec [A] a P f y p : rename.

(* See comment above about the tactic [induction]. *)
Definition paths_rect := paths_ind.

Register paths as core.identity.type.
Register idpath as core.identity.refl.
Register paths_rect as core.identity.ind.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Global Instance reflexive_paths {A} : Reflexive (@paths A) | 0 := @idpath A.
Arguments reflexive_paths / .

(** Our identity type is the Paulin-Mohring style.  We derive the Martin-Lof eliminator. *)

Definition paths_ind' {A : Type} (P : forall (a b : A), (a = b) -> Type)
  : (forall (a : A), P a a idpath) -> forall (a b : A) (p : a = b), P a b p.
Proof.
  intros H ? ? [].
  apply H.
Defined.

(** And here's the "right-sided" Paulin-Mohring eliminator. *)

Definition paths_ind_r {A : Type} (a : A)
           (P : forall b : A, b = a -> Type) (u : P a idpath)
  : forall (y : A) (p : y = a), P y p.
Proof.
  intros y p.
  destruct p.
  exact u.
Defined.

(** We declare a scope in which we shall place path notations. This way they can be turned on and off by the user. *)

(** We bind [path_scope] to [paths] so that when we are constructing arguments to things like [concat], we automatically are in [path_scope]. *)
Bind Scope path_scope with paths.

Local Open Scope path_scope.

(** The inverse of a path. *)
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Register inverse as core.identity.sym.

(** Declaring this as [simpl nomatch] prevents the tactic [simpl] from expanding it out into [match] statements.  We only want [inverse] to simplify when applied to an identity path. *)
Arguments inverse {A x y} p : simpl nomatch.

Global Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.
Arguments symmetric_paths / .

(** If we wanted to not have the constant [symmetric_paths] floating around, and wanted to resolve [inverse] directly, instead, we could play this trick, discovered by Georges Gonthier to fool Coq's restriction on [Identity Coercion]s:

<<
Module Export inverse.
  Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with idpath => idpath end.
End inverse.

Module Type inverseT.
  Parameter inverse : forall {A}, Symmetric (@paths A).
End inverseT.

Module inverseSymmetric (inverse : inverseT).
  Global Existing Instance inverse.inverse.
End inverseSymmetric.

Module Export symmetric_paths := inverseSymmetric inverse.
>>
*)


(** We define equality concatenation by destructing on both its arguments, so that it only computes when both arguments are [idpath].  This makes proofs more robust and symmetrical.  Compare with the definition of [identity_trans].  *)

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments concat {A x y z} p q : simpl nomatch.

Global Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.
Arguments transitive_paths / .

Register concat as core.identity.trans.

(** Note that you can use the Coq tactics [reflexivity], [transitivity], [etransitivity], and [symmetry] when working with paths; we've redefined them above to use typeclasses and to unfold the instances so you get proof terms with [concat] and [inverse]. *)

(** The identity path. *)
Notation "1" := idpath : path_scope.

(** The composition of two paths. *)
(** We put [p] and [q] in [path_scope] explicitly.  This is a partial work-around for https://coq.inria.fr/bugs/show_bug.cgi?id=3990, which is that implicitly bound scopes don't nest well. *)
Notation "p @ q" := (concat p%path q%path) : path_scope.

(** The inverse of a path. *)
(** See above about explicitly placing [p] in [path_scope]. *)
Notation "p ^" := (inverse p%path) : path_scope.

(** An alternative notation which puts each path on its own line, via the [format] specification in Notations.v.  Useful as a temporary device during proofs of equalities between very long composites; to turn it on inside a section, say [Open Scope long_path_scope]. *)
Notation "p @' q" := (concat p q) : long_path_scope.

(** An important instance of [paths_ind] is that given any dependent type, one can _transport_ elements of instances of the type along equalities in the base:  [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y
  := match p with idpath => u end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments transport {A}%_type_scope P%_function_scope {x y} p%_path_scope u : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression. *)
Notation "p # u" := (transport _ p u) (only parsing) : path_scope.

(** The first time [rewrite] is used in each direction, it creates transport lemmas called [internal_paths_rew] and [internal_paths_rew_r].  See ../Tactics.v for how these compare to [transport].  We use [rewrite] here to trigger the creation of these lemmas.  This ensures that they are defined outside of sections, so they are not unnecessarily polymorphic.  The lemmas below are not used in the library. *)
(** TODO: If Coq PR#18299 is merged (possibly in Coq 8.20), then we can instead register wrappers for [transport] to be used for rewriting.  See the comment by Dan Christensen in that PR for how to do this.  Then the tactics [internal_paths_rew_to_transport] and [rewrite_to_transport] can be removed from ../Tactics.v. *)
Local Lemma define_internal_paths_rew A x y P (u : P x) (H : x = y :> A) : P y.
Proof. rewrite <- H. exact u. Defined.

Local Lemma define_internal_paths_rew_r A x y P (u : P y) (H : x = y :> A) : P x.
Proof. rewrite -> H. exact u. Defined.

Arguments internal_paths_rew {A%_type_scope} {a} P%_function_scope f {a0} p.
Arguments internal_paths_rew_r {A%_type_scope} {a y} P%_function_scope HC X.

(** Having defined transport, we can use it to talk about what a homotopy theorist might see as "paths in a fibration over paths in the base"; and what a type theorist might see as "heterogeneous equality in a dependent type".  We will first see this appearing in the type of [apD]. *)

(** Functions act on paths: if [f : A -> B] and [p : x = y] is a path in [A], then [ap f p : f x = f y].  We typically pronounce [ap] as a single syllable, short for "application"; but it may also be considered as an acronym, "action on paths". *)

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y
  := match p with idpath => idpath end.

Global Arguments ap {A B}%_type_scope f%_function_scope {x y} p%_path_scope : simpl nomatch.

Register ap as core.identity.congr.

(** We introduce the convention that [apKN] denotes the application of a K-path between functions to an N-path between elements, where a 0-path is simply a function or an element. Thus, [ap] is a shorthand for [ap01]. *)
Notation ap01 := ap (only parsing).

(** Similarly, dependent functions act on paths; but the type is a bit more subtle. If [f : forall a:A, B a] and [p : x = y] is a path in [A], then [apD f p] should somehow be a path between [f x : B x] and [f y : B y]. Since these live in different types, we use transport along [p] to make them comparable: [apD f p : p # f x = f y].

  The type [p # f x = f y] can profitably be considered as a heterogeneous or dependent equality type, of "paths from [f x] to [f y] over [p]". *)

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments apD {A%_type_scope B} f%_function_scope {x y} p%_path_scope : simpl nomatch.

(** *** Homotopies between functions *)

Definition pointwise_paths A (P : A -> Type) (f g : forall x, P x)
  := forall x, f x = g x.

Definition pointwise_paths_concat {A} {P : A -> Type} {f g h : forall x, P x}
  : pointwise_paths A P f g -> pointwise_paths A P g h
    -> pointwise_paths A P f h := fun p q x => p x @ q x.

Global Instance reflexive_pointwise_paths A P
  : Reflexive (pointwise_paths A P).
Proof.
  intros ? ?; reflexivity.
Defined.

Global Instance transitive_pointwise_paths A P
  : Transitive (pointwise_paths A P).
Proof.
  intros f g h.
  apply pointwise_paths_concat.
Defined.

Global Instance symmetric_pointwise_paths A P
  : Symmetric (pointwise_paths A P).
Proof.
  intros ? ? p ?; symmetry; apply p.
Defined.

Global Arguments pointwise_paths {A}%_type_scope {P} (f g)%_function_scope.
Global Arguments reflexive_pointwise_paths /.
Global Arguments transitive_pointwise_paths /.
Global Arguments symmetric_pointwise_paths /.

#[export]
Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) : type_scope.

Definition apD10 {A} {B : A -> Type} {f g : forall x, B x} (h : f = g)
  : f == g
  := fun x => match h with idpath => 1 end.

Global Arguments apD10 {A%_type_scope B} {f g}%_function_scope h%_path_scope _.

Definition ap10 {A B} {f g : A -> B} (h : f = g) : f == g
  := apD10 h.

Global Arguments ap10 {A B}%_type_scope {f g}%_function_scope h%_path_scope _.

(** For the benefit of readers of the HoTT Book: *)
Notation happly := ap10 (only parsing).

Definition ap11 {A B} {f g : A -> B} (h : f = g) {x y : A} (p : x = y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.

Global Arguments ap11 {A B}%_type_scope {f g}%_function_scope h%_path_scope {x y} p%_path_scope.

(** ** Equivalences *)

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define equivalences, let us consider when two types [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are inverses of each other, up to homotopy.  Homotopically speaking, we should also require a certain condition on these homotopies, which is one of the triangle identities for adjunctions in category theory.  Thus, we call this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the higher coherences, so it is reasonable to only assume one of them.  Moreover, as we will see, if we have maps which are inverses up to homotopy, it is always possible to make the triangle identity hold by modifying one of the homotopies.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map whose homotopy fibers are contractible.  We call this notion a *homotopy bijection*.

   An interesting third option was suggested by André Joyal: a map [f] which has separate left and right homotopy inverses.  We call this notion a *homotopy isomorphism*.

   While the second option was the one used originally, and it is the most concise one, it makes more sense to use the first one in a formalized development, since it exposes most directly equivalence as a structure.  In particular, it is easier to extract directly from it the data of a homotopy inverse to [f], which is what we care about having most in practice.  Thus, adjoint equivalences are what we will refer to merely as *equivalences*. *)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote types of equivalences, and [isequiv] and [IsEquiv] systematically to denote the assertion that a given map is an equivalence. *)

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := {
  equiv_inv : B -> A ;
  eisretr : f o equiv_inv == idmap ;
  eissect : equiv_inv o f == idmap ;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x) ;
}.

Arguments eisretr {A B}%_type_scope f%_function_scope {_} _.
Arguments eissect {A B}%_type_scope f%_function_scope {_} _.
Arguments eisadj {A B}%_type_scope f%_function_scope {_} _.
Arguments IsEquiv {A B}%_type_scope f%_function_scope.

(** We mark [eisadj] as Opaque to deter Coq from unfolding it when simplifying. Since proofs of [eisadj] typically have larger proofs than the rest of the equivalence data, we gain some speed up as a result. *)
Global Opaque eisadj.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Arguments equiv_fun {A B} _ _.
Arguments equiv_isequiv {A B} _.

Bind Scope equiv_scope with Equiv.

Notation "A <~> B" := (Equiv A B) : type_scope.

(** A notation for the inverse of an equivalence.  We can apply this to a function as long as there is a typeclass instance asserting it to be an equivalence.  We can also apply it to an element of [A <~> B], since there is an implicit coercion to [A -> B] and also an existing instance of [IsEquiv]. *)

Notation "f ^-1" := (@equiv_inv _ _ f _) : function_scope.

(** A shorthand for applying paths between equivalences like functions. *)

Definition ap10_equiv {A B : Type} {f g : A <~> B} (h : f = g) : f == g
  := ap10 (ap equiv_fun h).

(** ** Function extensionality *)

(** The function extensionality axiom is formulated as a class. To use it in a theorem, just assume it with [`{Funext}], and then you can use [path_forall], defined below.  If you need function extensionality for a whole development, you can assume it for an entire Section with [Context `{Funext}].  *)

(** We use a dummy class and an axiom to get universe polymorphism of [Funext] while still tracking its uses.  Coq's universe polymorphism is parametric; in all definitions, all universes are quantified over before any other variables.  It's impossible to state a theorem like [(forall i : Level, P i) -> Q] (e.g., "if [C] has all limits of all sizes, then [C] is a preorder" isn't statable)*.  By making [isequiv_apD10] an [Axiom] rather than a per-theorem hypothesis, we can use it at multiple incompatible universe levels.  By only allowing use of the axiom when we have a [Funext] in the context, we can still track what theorems depend on it (because their type will mention [Funext]).

    By giving [Funext] a field whose type is an axiom, we guarantee that we cannot construct a fresh instance of [Funext] without [admit]; there's no term of type [dummy_funext_type] floating around.  If we did not give [Funext] any fields, then we could accidentally manifest a [Funext] using, e.g., [constructor], and then we wouldn't have a tag on the theorem that did this.

    As [Funext] is never actually used productively, we toss it in [Type0] and make it [Monomorphic] so it doesn't add more universes.

    * That's not technically true; it might be possible to get non-parametric universe polymorphism using [Module]s and ([Module]) Functors; we can use functors to quantify over a [Module Type] which requires a polymorphic proof of a given hypothesis, and then use that hypothesis polymorphically in any theorem we prove in our new [Module] Functor.  But that is far beyond the scope of this file. *)

Monomorphic Axiom Funext : Type0.
Existing Class Funext.
Axiom isequiv_apD10 : forall `{Funext} (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
Global Existing Instance isequiv_apD10.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x)
  : f == g -> f = g
  := (@apD10 A P f g)^-1.

Global Arguments path_forall {_ A%_type_scope P} (f g)%_function_scope _.

(** ** Contractibility and truncation levels *)

(** Truncation measures how complicated a type is in terms of higher path types. The (-2)-truncated types are the contractible ones, whose homotopy is completely trivial.  More precisely, a type [A] is contractible if there is a point [x : A] and a (pointwise) homotopy connecting the identity on [A] to the constant map at [x].

   The (n+1)-truncated types are those whose path types are n-truncated.

   Thus, (-1)-truncated means "the type of paths between any two points is contractible". Such a type is necessarily a sub-singleton: any two points are connected by a path which is unique up to homotopy. In other words, (-1)-truncated types are truth values.  We call such types "propositions" or "h-propositions".

   Next, 0-truncated means "the type of paths between any two points is a sub-singleton". Thus, two points might not have any paths between them, or they have a unique path. Such a type may have many points but it is discrete in the sense that all paths are trivial. We call such types "sets" or "h-sets".

    In this library, a witness that a type is n-truncated is formalized by the [IsTrunc n] typeclass.  In many cases, the typeclass machinery of Coq can automatically infer a witness for a type being n-truncated.  Because [IsTrunc n A] itself has no computational content (that is, all witnesses of n-truncation of a type are provably equal), it does not matter much which witness Coq infers.  Therefore, the primary concerns in making use of the typeclass machinery are coverage (how many goals can be automatically solved) and speed (how long does it take to solve a goal, and how long does it take to error on a goal we cannot automatically solve).  Careful use of typeclass instances and priorities, which determine the order of typeclass resolution, can be used to effectively increase both the coverage and the speed in cases where the goal is solvable.  Unfortunately, typeclass resolution tends to spin for a while before failing unless you're very, very, very careful.  We currently aim to achieve moderate coverage and fast speed in solvable cases.  How long it takes to fail typeclass resolution is not currently considered, though it would be nice someday to be even more careful about things.

In order to achieve moderate coverage and speedy resolution, we currently follow the following principles.  They set up a kind of directed flow of information, intended to prevent cycles and potentially infinite chains, which are often the ways that typeclass resolution gets stuck.

- We prefer to reason about [IsTrunc (S n) A] rather than [IsTrunc n (@paths A a b)].  Whenever we see a statement (or goal) about truncation of paths, we try to turn it into a statement (or goal) about truncation of a (non-[paths]) type.  We do not allow typeclass resolution to go in the reverse direction from [IsTrunc (S n) A] to [forall a b : A, IsTrunc n (a = b)].

- We prefer to reason about syntactically smaller types.  That is, typeclass instances should turn goals of type [IsTrunc n (forall a : A, P a)] into goals of type [forall a : A, IsTrunc n (P a)]; and goals of type [IsTrunc n (A * B)] into the pair of goals of type [IsTrunc n A] and [IsTrunc n B]; rather than the other way around.  Ideally, we would add similar rules to transform hypotheses in the cases where we can do so.  This rule is not always the one we want, but it seems to heuristically capture the shape of most cases that we want the typeclass machinery to automatically infer.  That is, we often want to infer [IsTrunc n (A * B)] from [IsTrunc n A] and [IsTrunc n B], but we (probably) don't often need to do other simple things with [IsTrunc n (A * B)] which are broken by that reduction.

   We begin by defining the type that indexes the truncation levels.
*)

Inductive trunc_index : Type0 :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Scheme trunc_index_ind := Induction for trunc_index Sort Type.
Scheme trunc_index_rec := Minimality for trunc_index Sort Type.

(* See comment above about the tactic [induction]. *)
Definition trunc_index_rect := trunc_index_ind.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. Numeral notation for [trunc_index]es is set up in Basics/Trunc.v. *)
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%_trunc_scope.

Notation "n .+1" := (trunc_S n) : trunc_scope.
Notation "n .+2" := (n.+1.+1)%trunc : trunc_scope.
Notation "n .+3" := (n.+1.+2)%trunc : trunc_scope.
Notation "n .+4" := (n.+1.+3)%trunc : trunc_scope.
Notation "n .+5" := (n.+1.+4)%trunc : trunc_scope.
Local Open Scope trunc_scope.

(** We define truncatedness using an inductive type [IsTrunc_internal A n].  We use a notation [IsTrunc n A] simply to swap the orders of arguments, and notations [Contr], [IsHProp] and [IsHSet] which specialize to [n] being [-2], [-1] and [0], respectively.  An alternative is to use a [Fixpoint], and that was done in the past.  The advantages of the inductive approach are:  [IsTrunc_internal] is cumulative; typeclass inherence works smoothly; the library builds faster.  Some disadvantages are that we need to manually apply the constructors when proving that something is truncated, and that the induction principle is awkward to work with. *)

Inductive IsTrunc_internal (A : Type@{u}) : trunc_index -> Type@{u} :=
| Build_Contr : forall (center : A) (contr : forall y, center = y), IsTrunc_internal A minus_two
| istrunc_S : forall {n:trunc_index}, (forall x y:A, IsTrunc_internal (x = y) n) -> IsTrunc_internal A (trunc_S n).

Existing Class IsTrunc_internal.

Notation IsTrunc n A := (IsTrunc_internal A n).

Scheme IsTrunc_internal_ind := Induction for IsTrunc_internal Sort Type.
Scheme IsTrunc_internal_rec := Minimality for IsTrunc_internal Sort Type.
Definition IsTrunc_internal_rect := IsTrunc_internal_ind.

Definition IsTrunc_unfolded (n : trunc_index) (A : Type)
  := match n with
    | minus_two => { center : A & forall y, center = y }
    | n.+1 => forall x y : A, IsTrunc n (x = y)
    end.

Definition istrunc_unfold (n : trunc_index) (A : Type)
  : IsTrunc n A -> IsTrunc_unfolded n A.
Proof.
  intros [center contr|k istrunc].
  - exact (center; contr).
  - exact istrunc.
Defined.

Definition isequiv_istrunc_unfold (n : trunc_index) (A : Type)
  : IsEquiv (istrunc_unfold n A).
Proof.
  simple refine (Build_IsEquiv _ _ (istrunc_unfold n A) _ _ _ _).
  - destruct n.
    + intros [center contr]; exact (Build_Contr _ center contr).
    + intros H. exact (istrunc_S _ H).
  - destruct n; reflexivity.
  - intros [center contr|k istrunc]; reflexivity.
  - intros [center contr|k istrunc]; reflexivity.
Defined.

Definition equiv_istrunc_unfold (n : trunc_index) (A : Type)
  := Build_Equiv _ _ _  (isequiv_istrunc_unfold n A).

(** A version of [istrunc_unfold] for successors. *)
Global Instance istrunc_paths (A : Type) n `{H : IsTrunc n.+1 A} (x y : A)
  : IsTrunc n (x = y)
  := istrunc_unfold n.+1 A H x y.

Notation Contr A := (IsTrunc minus_two A).
Notation IsHProp A := (IsTrunc minus_two.+1 A).
Notation IsHSet A := (IsTrunc minus_two.+2 A).

Definition center (A : Type) {H : Contr A} : A := pr1 (istrunc_unfold _ _ H).
Definition contr {A : Type} {H : Contr A} (y : A) : center A = y := pr2 (istrunc_unfold _ _ H) y.

(** We define a slight variation of [istrunc_unfold], which differs only it what it does for [n = -2].  It will produce a section of the following type family. *)
Definition istrunc_codomain_fam {n : trunc_index} {A : Type} (istrunc : IsTrunc n A) : A -> Type.
Proof.
  intro y.
  destruct n.
  - exact (center A = y).
  - exact (forall x : A, IsTrunc n (y = x)).
Defined.

(** The variant of [istrunc_unfold] lets us treat any proof of truncation as a function.  For [n = -2], it produces the contracting homotopy. *)
Definition istrunc_fun {n : trunc_index} {A : Type} (istrunc : IsTrunc n A)
  : forall y : A, istrunc_codomain_fam istrunc y.
Proof.
  destruct n.
  - exact (@contr A istrunc).
  - exact (istrunc_unfold _ _ istrunc).
Defined.

(** We add this as a coercion. *)
#[warning="-uniform-inheritance"] 
Coercion istrunc_fun : IsTrunc >-> Funclass.

(** *** Truncated relations  *)

(** Hprop-valued relations.  Making this a [Notation] rather than a [Definition] enables typeclass resolution to pick it up easily.  We include the base type [A] in the notation since otherwise e.g. [forall (x y : A) (z : B x y), IsHProp (C x y z)] will get displayed as [forall (x : A), is_mere_relation (C x)].  *)
Notation is_mere_relation A R := (forall (x y : A), IsHProp (R x y)).

(** ** Natural numbers *)

Inductive nat : Type0 :=
| O : nat
| S : nat -> nat.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rect := Induction for nat Sort Type.
Scheme nat_rec := Induction for nat Sort Type.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%_nat.

(** ** Misc *)

(** We put [Empty] here, instead of in [Empty.v], because [Ltac done] uses it. *)
Inductive Empty : Type0 := .
Register Empty as core.False.type.

Scheme Empty_ind := Induction for Empty Sort Type.
Scheme Empty_rec := Minimality for Empty Sort Type.
Definition Empty_rect := Empty_ind.

Definition not (A : Type) := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Notation "~~ x" := (~ ~x) : type_scope.
#[export]
Hint Unfold not: core.
Notation "x <> y  :>  T" := (not (x = y :> T)) : type_scope.
Notation "x <> y" := (x <> y :> _) : type_scope.

Definition symmetric_neq {A} {x y : A} : x <> y -> y <> x
  := fun np p => np (p^).

Definition complement {A} (R : Relation A) : Relation A :=
  fun x y => ~ (R x y).

#[global] Typeclasses Opaque complement.

Class Irreflexive {A} (R : Relation A) :=
  irreflexivity : Reflexive (complement R).

Class Asymmetric {A} (R : Relation A) :=
  asymmetry : forall {x y}, R x y -> (complement R y x : Type).

(** Likewise, we put [Unit] here, instead of in [Unit.v], because [Trunc] uses it. *)
Inductive Unit : Type0 := tt : Unit.

Scheme Unit_ind := Induction for Unit Sort Type.
Scheme Unit_rec := Minimality for Unit Sort Type.
Definition Unit_rect := Unit_ind.

(** A [Unit] goal should be resolved by [auto] and [trivial]. *)
#[export]
Hint Resolve tt : core.

Register Unit as core.IDProp.type.
Register Unit as core.True.type.
Register tt as core.IDProp.idProp.
Register tt as core.True.I.

(** *** Pointed types *)

(** A space is pointed if that space has a point. *)
Class IsPointed (A : Type) := point : A.

#[global] Typeclasses Transparent IsPointed.

Arguments point A {_}.

Record pType :=
  { pointed_type : Type ;
    ispointed_type : IsPointed pointed_type }.

Coercion pointed_type : pType >-> Sortclass.

Global Existing Instance ispointed_type.

(** *** Homotopy fibers *)

(** Homotopy fibers are homotopical inverse images of points.  *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

Global Arguments hfiber {A B}%_type_scope f%_function_scope y.

(** ** Smallness *)

(** We say that [X : Type@{j}] is small (relative to Type@{i}) if it is equivalent to a type in [Type@{i}].  We use a record to avoid an extra universe variable.  This version has no constraints on [i] and [j].  It lands in [max(i+1,j)], as expected.  We mark the [i] variable as being invariant, so that Coq is better at guessing universe variables when this is used. *)
Class IsSmall@{=i j | } (X : Type@{j}) := {
  smalltype : Type@{i} ;
  equiv_smalltype : smalltype <~> X ;
}.
Arguments smalltype X {_}.
Arguments equiv_smalltype X {_}.

(** *** Propositional resizing *)

(** See the note by [Funext] above regarding classes for axioms. *)
Monomorphic Axiom PropResizing : Type0.
Existing Class PropResizing.

(** Propositional resizing says that every (-1)-truncated type is small. *)
Axiom issmall_hprop@{i j | } : forall `{PropResizing} (X : Type@{j})
  (T : IsHProp X), IsSmall@{i j} X.
Existing Instance issmall_hprop.
