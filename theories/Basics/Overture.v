(* -*- mode: coq; mode: visual-line -*-  *)

(** * Basic definitions of homotopy type theory, particularly the groupoid structure of identity types. *)
(** Import the file of reserved notations so we maintain consistent level notations throughout the library *)
Require Export Basics.Notations.

(** Currently, Coq 8.12 complains when we use the numeral notations from the Decimal module. Since we only use a copy of the real standard library we will supress this warning. In the future, our copy of the standard library will be completely removed together with this warning. *)
Global Set Warnings "-decimal-numeral-notation".

(** ** Type classes *)

(** This command prevents Coq from trying to guess the values of existential variables while doing typeclass resolution.  If you don't know what that means, ignore it. *)
Local Set Typeclasses Strict Resolution.

(** This command prevents Coq from automatically defining the eliminator functions for inductive types.  We will define them ourselves to match the naming scheme of the HoTT Book.  In principle we ought to make this [Global], but unfortunately the tactics [induction] and [elim] assume that the eliminators are named in Coq's way, e.g. [thing_rect], so making it global could cause unpleasant surprises for people defining new inductive types.  However, when you do define your own inductive types you are encouraged to also do [Local Unset Elimination Schemes] and then use [Scheme] to define [thing_ind], [thing_rec], and (for compatibility with [induction] and [elim]) [thing_rect], as we have done below for [paths], [Empty], [Unit], etc.  We are hoping that this will be fixed eventually; see https://coq.inria.fr/bugs/show_bug.cgi?id=3745.  *)
Local Unset Elimination Schemes.

(** This command changes Coq's subterm selection to always use full conversion after finding a subterm whose head/key matches the key of the term we're looking for.  This applies to [rewrite] and higher-order unification in [apply]/[elim]/[destruct].  Again, if you don't know what that means, ignore it. *)
Global Set Keyed Unification.

(** This command makes it so that you don't have to declare universes explicitly when mentioning them in the type.  (Without this command, if you want to say [Definition foo := Type@{i}.], you must instead say [Definition foo@{i} := Type@{i}.]. *)
Global Unset Strict Universe Declaration.

(** This command makes it so that when we say something like [IsHSet nat] we get [IsHSet@{i} nat] instead of [IsHSet@{Set} nat]. *)
Global Unset Universe Minimization ToSet.

(** Force to use bullets in proofs. *)
Global Set Default Goal Selector "!".

(** Currently Coq doesn't print equivalences correctly (8.6). This fixes that. See https://github.com/HoTT/HoTT/issues/1000 *)
Global Set Printing Primitive Projection Parameters.

(** This tells Coq that when we [Require] a module without [Import]ing it, typeclass instances defined in that module should also not be imported.  In other words, the only effect of [Require] without [Import] is to make qualified names available. *)
Global Set Loose Hint Behavior "Strict".

(** Apply using the same opacity information as typeclass proof search. *)
Ltac class_apply c := autoapply c with typeclass_instances.

Definition Relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : Relation A) :=
  reflexivity : forall x : A, R x x.
Arguments reflexivity {A R} _.

Class Symmetric {A} (R : Relation A) :=
  symmetry : forall x y, R x y -> R y x.
Arguments symmetry {A R _ _}.

Class Transitive {A} (R : Relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.
Arguments transitivity {A R _ _ _}.

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
Ltac reflexivity :=
  Coq.Init.Notations.reflexivity
  || (intros;
      let R := match goal with |- ?R ?x ?y => constr:(R) end in
      let pre_proof_term_head := constr:(@reflexivity _ R _) in
      let proof_term_head := (eval cbn in pre_proof_term_head) in
      apply (proof_term_head : forall x, R x x)).

(** Even if we weren't using [cbn], we would have to redefine symmetry, since the built-in Coq version is sometimes too smart for its own good, and will occasionally fail when it should not. *)
Ltac symmetry :=
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
Ltac transitivity x := etransitivity x.


(** ** Basic definitions *)

(** Define an alias for [Set], which is really [Type₀]. *)
Notation Type0 := Set.

(** Define [Type₁] (really, [Type_i] for any [i > 0]) so that we can enforce having universes that are not [Set].  In trunk, universes will not be unified with [Set] in most places, so we want to never use [Set] at all. *)
Definition Type1@{i} := Eval hnf in let gt := (Set : Type@{i}) in Type@{i}.
Arguments Type1 / .
Identity Coercion unfold_Type1 : Type1 >-> Sortclass.

(** We also define "the next couple of universes", which are actually an arbitrary universe with another one or two strictly below it.  Note when giving universe annotations to these that their universe parameters appear in order of *decreasing* size. *)
Definition Type2@{i j} := Eval hnf in let gt := (Type1@{j} : Type@{i}) in Type@{i}.
Arguments Type2 / .
Identity Coercion unfold_Type2 : Type2 >-> Sortclass.

Definition Type3@{i j k} := Eval hnf in let gt := (Type2@{j k} : Type@{i}) in Type@{i}.
Arguments Type3 / .
Identity Coercion unfold_Type3 : Type3 >-> Sortclass.

(** Along the same lines, here is a universe with an extra universe parameter that's less than or equal to it in size.  The [gt] isn't necessary to force the larger universe to be bigger than [Set] (since we refer to the smaller universe by [Type1] which is already bigger than [Set]), but we include it anyway to make the universe parameters occur again in (now non-strictly) decreasing order. *)
Definition Type2le@{i j} := Eval hnf in let gt := (Set : Type@{i}) in
                                        let ge := ((fun x => x) : Type1@{j} -> Type@{i}) in Type@{i}.
Arguments Type2le / .
Identity Coercion unfold_Type2le : Type2le >-> Sortclass.

Definition Type3le@{i j k} := Eval hnf in let gt := (Set : Type@{i}) in
                                          let ge := ((fun x => x) : Type2le@{j k} -> Type@{i}) in Type@{i}.
Arguments Type3le / .
Identity Coercion unfold_Type3le : Type3le >-> Sortclass.


(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation idmap := (fun x => x).

(** We define various scopes and open them in the order we expect to use them. *)
Declare Scope equiv_scope.
Declare Scope function_scope.
Declare Scope path_scope.
Declare Scope fibration_scope.
Declare Scope trunc_scope.
Declare Scope long_path_scope.

Delimit Scope equiv_scope with equiv.
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Delimit Scope trunc_scope with trunc.

Open Scope trunc_scope.
Open Scope equiv_scope.
Open Scope path_scope.
Open Scope fibration_scope.
Open Scope nat_scope.
Open Scope function_scope.
Open Scope type_scope.
Open Scope core_scope.

(** *** Constant functions *)
Definition const {A B} (b : B) := fun x : A => b.

(** We define notation for dependent pairs because it is too annoying to write and see [existT P x y] all the time.  However, we put it in its own scope, because sometimes it is necessary to give the particular dependent type, so we'd like to be able to turn off this notation selectively. *)
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Notation "( x ; .. ; y ; z )" := (existT _ x .. (existT _ y z) ..) : fibration_scope.
(** We bind [fibration_scope] with [sigT] so that we are automatically in [fibration_scope] when we are passing an argument of type [sigT]. *)
Bind Scope fibration_scope with sigT.

(** We have unified [sig] and [sigT] of the standard Coq, and so we introduce a new notation to not annoy newcomers with the [T] in [projT1] and [projT2] nor the [_sig] in [proj1_sig] and [proj2_sig], and to not confuse Coq veterans by stealing [proj1] and [proj2], which Coq uses for [and]. *)
Notation pr1 := projT1.
Notation pr2 := projT2.

(** The following notation is very convenient, although it unfortunately clashes with Proof General's "electric period".  We have added [format] specifiers in Notations.v so that it will display without an extra space, as [x.1] rather than as [x .1]. *)
Notation "x .1" := (pr1 x) : fibration_scope.
Notation "x .2" := (pr2 x) : fibration_scope.

Definition uncurry {A B C} (f : A -> B -> C) (p : A * B) : C := f (fst p) (snd p).

(** Composition of functions. *)

Notation compose := (fun g f x => g (f x)).

(** We put the following notation in a scope because leaving it unscoped causes it to override identical notations in other scopes.  It's convenient to use the same notation for, e.g., function composition, morphism composition in a category, and functor composition, and let Coq automatically infer which one we mean by scopes.  We can't do this if this notation isn't scoped.  Unfortunately, Coq doesn't have a built-in [function_scope] like [type_scope]; [type_scope] is automatically opened wherever Coq is expecting a [Sort], and it would be nice if [function_scope] were automatically opened whenever Coq expects a thing of type [forall _, _] or [_ -> _].  To work around this, we open [function_scope] globally. *)

(** We allow writing [(f o g)%function] to force [function_scope] over, e.g., [morphism_scope]. *)

Notation "g 'o' f" := (compose g%function f%function) : function_scope.

(** This definition helps guide typeclass inference. *)
Definition Compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := compose g f.

(** Composition of logical equivalences *)
Instance iff_compose : Transitive iff | 1
  := fun A B C f g => (fst g o fst f , snd f o snd g).
Arguments iff_compose {A B C} f g : rename.

(** While we're at it, inverses of logical equivalences *)
Instance iff_inverse : Symmetric iff | 1
  := fun A B f => (snd f , fst f).
Arguments iff_inverse {A B} f : rename.

(** And reflexivity of them *)
Instance iff_reflexive : Reflexive iff | 1
  := fun A => (idmap , idmap).

(** Dependent composition of functions. *)
Definition composeD {A B C} (g : forall b, C b) (f : A -> B) := fun x : A => g (f x).

Global Arguments composeD {A B C}%type_scope (g f)%function_scope x.

Hint Unfold composeD : core.

Notation "g 'oD' f" := (composeD g f) : function_scope.

(** ** The groupoid structure of identity types. *)

(** The results in this file are used everywhere else, so we need to be extra careful about how we define and prove things.  We prefer hand-written terms, or at least tactics that allow us to retain clear control over the proof-term produced. *)

(** We define our own identity type, rather than using the one in the Coq standard library, so as to have more control over transitivity, symmetry and inverse.  It seems impossible to change these for the standard eq/identity type (or its Type-valued version) because it breaks various other standard things.  Merely changing notations also doesn't seem to quite work. *)
Cumulative Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Scheme paths_ind := Induction for paths Sort Type.
Arguments paths_ind [A] a P f y p.
Scheme paths_rec := Minimality for paths Sort Type.
Arguments paths_rec [A] a P f y p.

Register idpath as core.identity.refl.

(* See comment above about the tactic [induction]. *)
Definition paths_rect := paths_ind.

Register paths_rect as core.identity.ind.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

(** Ensure [internal_paths_rew] and [internal_paths_rew_r] are defined outside sections, so they are not unnecessarily polymorphic. *)
Lemma paths_rew A a y P (X : P a) (H : a = y :> A) : P y.
Proof. rewrite <- H. exact X. Defined.

Lemma paths_rew_r A a y P (X : P y) (H : a = y :> A) : P a.
Proof. rewrite -> H. exact X. Defined.

Register paths as core.identity.type.

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

(** This allows [rewrite] to both in left-to-right and right-to left directions. *)
Definition paths_rect_r (A : Type) (x : A) (P : A -> Type) (p : P x) (y : A) (e : paths y x) : P y :=
  paths_rect A x (fun y e => P y) p y (inverse e).

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
>> *)


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
(** We put [p] and [q] in [path_scope] explcitly.  This is a partial work-around for https://coq.inria.fr/bugs/show_bug.cgi?id=3990, which is that implicitly bound scopes don't nest well. *)
Notation "p @ q" := (concat p%path q%path) : path_scope.

(** The inverse of a path. *)
(** See above about explicitly placing [p] in [path_scope]. *)
Notation "p ^" := (inverse p%path) : path_scope.

(** An alternative notation which puts each path on its own line, via the [format] specification in Notations.v.  Useful as a temporary device during proofs of equalities between very long composites; to turn it on inside a section, say [Open Scope long_path_scope]. *)
Notation "p @' q" := (concat p q) : long_path_scope.


(** An important instance of [paths_ind] is that given any dependent type, one can _transport_ elements of instances of the type along equalities in the base.

   [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments transport {A}%type_scope P%function_scope {x y} p%path_scope u : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression.*)

Notation "p # x" := (transport _ p x) (only parsing) : path_scope.

(** Having defined transport, we can use it to talk about what a homotopy theorist might see as "paths in a fibration over paths in the base"; and what a type theorist might see as "heterogeneous eqality in a dependent type".

We will first see this appearing in the type of [apD]. *)

(** Functions act on paths: if [f : A -> B] and [p : x = y] is a path in [A], then [ap f p : f x = f y].

   We typically pronounce [ap] as a single syllable, short for "application"; but it may also be considered as an acronym, "action on paths". *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Global Arguments ap {A B}%type_scope f%function_scope {x y} p%path_scope.

Register ap as core.identity.congr.

(** We introduce the convention that [apKN] denotes the application of a K-path between functions to an N-path between elements, where a 0-path is simply a function or an element. Thus, [ap] is a shorthand for [ap01]. *)

Notation ap01 := ap (only parsing).

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

Global Arguments pointwise_paths {A}%type_scope {P} (f g)%function_scope.
Global Arguments reflexive_pointwise_paths /.
Global Arguments transitive_pointwise_paths /.
Global Arguments symmetric_pointwise_paths /.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with idpath => 1 end.

Global Arguments apD10 {A%type_scope B} {f g}%function_scope h%path_scope _.

Definition ap10 {A B} {f g:A->B} (h:f=g) : f == g
  := apD10 h.

Global Arguments ap10 {A B}%type_scope {f g}%function_scope h%path_scope _.

(** For the benefit of readers of the HoTT Book: *)
Notation happly := ap10 (only parsing).

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.

Global Arguments ap11 {A B}%type_scope {f g}%function_scope h%path_scope {x y} p%path_scope.

(** See above for the meaning of [simpl nomatch]. *)
Arguments ap {A B} f {x y} p : simpl nomatch.

(** Similarly, dependent functions act on paths; but the type is a bit more subtle. If [f : forall a:A, B a] and [p : x = y] is a path in [A], then [apD f p] should somehow be a path between [f x : B x] and [f y : B y]. Since these live in different types, we use transport along [p] to make them comparable: [apD f p : p # f x = f y].

  The type [p # f x = f y] can profitably be considered as a heterogeneous or dependent equality type, of "paths from [f x] to [f y] over [p]". *)

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments apD {A%type_scope B} f%function_scope {x y} p%path_scope : simpl nomatch.

(** ** Equivalences *)

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define equivalences, let us consider when two types [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are inverses of each other, up to homotopy.  Homotopically speaking, we should also require a certain condition on these homotopies, which is one of the triangle identities for adjunctions in category theory.  Thus, we call this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the higher coherences, so it is reasonable to only assume one of them.  Moreover, as we will see, if we have maps which are inverses up to homotopy, it is always possible to make the triangle identity hold by modifying one of the homotopies.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map whose homotopy fibers are contractible.  We call this notion a *homotopy bijection*.

   An interesting third option was suggested by André Joyal: a map [f] which has separate left and right homotopy inverses.  We call this notion a *homotopy isomorphism*.

   While the second option was the one used originally, and it is the most concise one, it makes more sense to use the first one in a formalized development, since it exposes most directly equivalence as a structure.  In particular, it is easier to extract directly from it the data of a homotopy inverse to [f], which is what we care about having most in practice.  Thus, adjoint equivalences are what we will refer to merely as *equivalences*. *)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote types of equivalences, and [isequiv] and [IsEquiv] systematically to denote the assertion that a given map is an equivalence. *)

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Cumulative Class IsEquiv {A B : Type} (f : A -> B) := {
  equiv_inv : B -> A ;
  eisretr : f o equiv_inv == idmap ;
  eissect : equiv_inv o f == idmap ;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x) ;
}.

Arguments eisretr {A B}%type_scope f%function_scope {_} _.
Arguments eissect {A B}%type_scope f%function_scope {_} _.
Arguments eisadj {A B}%type_scope f%function_scope {_} _.
Arguments IsEquiv {A B}%type_scope f%function_scope.

(** A record that includes all the data of an adjoint equivalence. *)
Cumulative Record Equiv A B := {
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

(** ** Applying paths between equivalences like functions *)

Definition ap10_equiv {A B : Type} {f g : A <~> B} (h : f = g) : f == g
  := ap10 (ap equiv_fun h).

(** ** Contractibility and truncation levels *)

(** Truncation measures how complicated a type is.  In this library, a witness that a type is n-truncated is formalized by the [IsTrunc n] typeclass.  In many cases, the typeclass machinery of Coq can automatically infer a witness for a type being n-truncated.  Because [IsTrunc n A] itself has no computational content (that is, all witnesses of n-truncation of a type are provably equal), it does not matter much which witness Coq infers.  Therefore, the primary concerns in making use of the typeclass machinery are coverage (how many goals can be automatically solved) and speed (how long does it take to solve a goal, and how long does it take to error on a goal we cannot automatically solve).  Careful use of typeclass instances and priorities, which determine the order of typeclass resolution, can be used to effectively increase both the coverage and the speed in cases where the goal is solvable.  Unfortunately, typeclass resolution tends to spin for a while before failing unless you're very, very, very careful.  We currently aim to achieve moderate coverage and fast speed in solvable cases.  How long it takes to fail typeclass resolution is not currently considered, though it would be nice someday to be even more careful about things.

In order to achieve moderate coverage and speedy resolution, we currently follow the following principles.  They set up a kind of directed flow of information, intended to prevent cycles and potentially infinite chains, which are often the ways that typeclass resolution gets stuck.

- We prefer to reason about [IsTrunc (S n) A] rather than [IsTrunc n (@paths A a b)].  Whenever we see a statement (or goal) about truncation of paths, we try to turn it into a statement (or goal) about truncation of a (non-[paths]) type.  We do not allow typeclass resolution to go in the reverse direction from [IsTrunc (S n) A] to [forall a b : A, IsTrunc n (a = b)].

- We prefer to reason about syntactically smaller types.  That is, typeclass instances should turn goals of type [IsTrunc n (forall a : A, P a)] into goals of type [forall a : A, IsTrunc n (P a)]; and goals of type [IsTrunc n (A * B)] into the pair of goals of type [IsTrunc n A] and [IsTrunc n B]; rather than the other way around.  Ideally, we would add similar rules to transform hypotheses in the cases where we can do so.  This rule is not always the one we want, but it seems to heuristically capture the shape of most cases that we want the typeclass machinery to automatically infer.  That is, we often want to infer [IsTrunc n (A * B)] from [IsTrunc n A] and [IsTrunc n B], but we (probably) don't often need to do other simple things with [IsTrunc n (A * B)] which are broken by that reduction.
*)

(** *** Contractibility *)

(** A space [A] is contractible if there is a point [x : A] and a (pointwise) homotopy connecting the identity on [A] to the constant map at [x].  Thus an element of [contr A] is a pair whose first component is a point [x] and the second component is a pointwise retraction of [A] to [x]. *)

(** We use the [Contr_internal] record so as not to pollute typeclass search; we only do truncation typeclass search on the [IsTrunc] datatype, usually.  We will define a notation [Contr] which is equivalent to [Contr_internal], but picked up by typeclass search.  However, we must make [Contr_internal] a class so that we pick up typeclasses on [center] and [contr].  However, the only typeclass rule we register is the one that turns it into a [Contr]/[IsTrunc].  Unfortunately, this means that declaring an instance like [Instance contr_foo : Contr foo := { center := bar }.] will fail with mismatched instances/contexts.  Instead, we must iota expand such definitions to get around Coq's deficiencies, and write [Instance contr_foo : Contr foo := let x := {| center := bar |} in x.] *)
Class Contr_internal (A : Type) := Build_Contr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.

(** *** Truncation levels *)

(** Truncation measures how complicated a type is in terms of higher path spaces. The (-2)-truncated types are the contractible ones, whose homotopy is completely trivial. The (n+1)-truncated types are those whose path spaces are n-truncated.

   Thus, (-1)-truncated means "the space of paths between any two points is contactible". Such a space is necessarily a sub-singleton: any two points are connected by a path which is unique up to homotopy. In other words, (-1)-truncated spaces are truth values (we call them "propositions").

   Next, 0-truncated means "the space of paths between any two points is a sub-singleton". Thus, two points might not have any paths between them, or they have a unique path. Such a space may have many points but it is discrete in the sense that all paths are trivial. We call such spaces "sets".
*)

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Scheme trunc_index_ind := Induction for trunc_index Sort Type.
Scheme trunc_index_rec := Minimality for trunc_index Sort Type.

(* See comment above about the tactic [induction]. *)
Definition trunc_index_rect := trunc_index_ind.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. *)
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.

(** Include the basic numerals, so we don't need to go through the coercion from [nat], and so that we get the right binding with [trunc_scope]. *)
(** Note that putting the negative numbers at level 0 allows us to override the [- _] notation for negative numbers. *)
Notation "n .+1" := (trunc_S n) : trunc_scope.
Notation "n .+1" := (S n) : nat_scope.
Notation "n .+2" := (n.+1.+1)%trunc : trunc_scope.
Notation "n .+2" := (n.+1.+1)%nat   : nat_scope.
Notation "n .+3" := (n.+1.+2)%trunc : trunc_scope.
Notation "n .+3" := (n.+1.+2)%nat   : nat_scope.
Notation "n .+4" := (n.+1.+3)%trunc : trunc_scope.
Notation "n .+4" := (n.+1.+3)%nat   : nat_scope.
Notation "n .+5" := (n.+1.+4)%trunc : trunc_scope.
Notation "n .+5" := (n.+1.+4)%nat   : nat_scope.
Local Open Scope trunc_scope.

(** Further notation for truncation levels is introducted in Trunc.v. *)

(** n-truncatedness is defined by recursion on [n].  We could simply define [IsTrunc] as a fixpoint and an [Existing Class], but we want to also declare [IsTrunc] to be [simpl nomatch], so that when we say [simpl] or [cbn], [IsTrunc n.+1 A] doesn't get unfolded to [forall x y:A, IsTrunc n (x = y)].  But we also want to be able to use this equality, e.g. by proving [IsTrunc n.+1 A] starting with [intros x y], and if [IsTrunc] is a fixpoint declared as [simpl nomatch] then that doesn't work, because [intros] uses [hnf] to expose a [forall] and [hnf] respects [simpl nomatch] on fixpoints.  But we can make it work if we define the fixpoint separately as [IsTrunc_internal] and then take the class [IsTrunc] to be a definitional wrapper around it, since [hnf] is willing to unfold non-fixpoints even if they are defined as [simpl never].  This behavior of [hnf] is arguably questionable (see https://github.com/coq/coq/issues/11619), but it is useful for us here. *)

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

(** We use the principle that we should always be doing typeclass resolution on truncation of non-equality types.  We try to change the hypotheses and goals so that they never mention something like [IsTrunc n (_ = _)] and instead say [IsTrunc (S n) _].  If you're evil enough that some of your paths [a = b] are n-truncated, but others are not, then you'll have to either reason manually or add some (local) hints with higher priority than the hint below, or generalize your equality type so that it's not a path anymore. *)

Typeclasses Opaque IsTrunc. (* don't auto-unfold [IsTrunc] in typeclass search *)

Arguments IsTrunc : simpl never. (* don't auto-unfold [IsTrunc] with [simpl] *)

Global Instance istrunc_paths (A : Type) n `{H : IsTrunc n.+1 A} (x y : A)
: IsTrunc n (x = y)
  := H x y. (* but do fold [IsTrunc] *)

Existing Class IsTrunc_internal.

Hint Extern 0 (IsTrunc_internal _ _) => progress change IsTrunc_internal with IsTrunc in * : typeclass_instances. (* Also fold [IsTrunc_internal] *)

Hint Extern 0 (IsTrunc _ _) => progress change IsTrunc_internal with IsTrunc in * : typeclass_instances. (* Also fold [IsTrunc_internal] *)

(** Picking up the [forall x y, IsTrunc n (x = y)] instances in the hypotheses is much tricker.  We could do something evil where we declare an empty typeclass like [IsTruncSimplification] and use the typeclass as a proxy for allowing typeclass machinery to factor nested [forall]s into the [IsTrunc] via backward reasoning on the type of the hypothesis... but, that's rather complicated, so we instead explicitly list out a few common cases.  It should be clear how to extend the pattern. *)
Hint Extern 10 =>
progress match goal with
           | [ H : forall x y : ?T, IsTrunc ?n (x = y) |- _ ]
             => change (IsTrunc n.+1 T) in H
           | [ H : forall (a : ?A) (x y : @?T a), IsTrunc ?n (x = y) |- _ ]
             => change (forall a : A, IsTrunc n.+1 (T a)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (x y : @?T a b), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a), IsTrunc n.+1 (T a b)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (x y : @?T a b c), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b), IsTrunc n.+1 (T a b c)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (d : @?D a b c) (x y : @?T a b c d), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b) (d : D a b c), IsTrunc n.+1 (T a b c d)) in H; cbv beta in H
         end : core.

Notation Contr := (IsTrunc minus_two).
Notation IsHProp := (IsTrunc minus_two.+1).
Notation IsHSet := (IsTrunc minus_two.+2).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

(** *** Simple induction *)

(** The following tactic is designed to be more or less interchangeable with [induction n as [ | n' IH ]] whenever [n] is a [nat] or a [trunc_index].  The difference is that it produces proof terms involving [match] and [fix] explicitly rather than [nat_ind] or [trunc_index_ind], and therefore does not introduce higher universe parameters. *)

Ltac simple_induction n n' IH :=
  generalize dependent n;
  fix IH 1;
  intros [| n'];
  [ clear IH | specialize (IH n') ].

(** *** Truncated relations  *)

(** Hprop-valued relations.  Making this a [Notation] rather than a [Definition] enables typeclass resolution to pick it up easily.  We include the base type [A] in the notation since otherwise e.g. [forall (x y : A) (z : B x y), IsHProp (C x y z)] will get displayed as [forall (x : A), is_mere_relation (C x)].  *)
Notation is_mere_relation A R := (forall (x y : A), IsHProp (R x y)).

(** *** Function extensionality *)

(** The function extensionality axiom is formulated as a class. To use it in a theorem, just assume it with [`{Funext}], and then you can use [path_forall], defined below.  If you need function extensionality for a whole development, you can assume it for an entire Section with [Context `{Funext}].  *)
(** We use a dummy class and an axiom to get universe polymorphism of [Funext] while still tracking its uses.  Coq's universe polymorphism is parametric; in all definitions, all universes are quantified over before any other variables.  It's impossible to state a theorem like [(forall i : Level, P i) -> Q] (e.g., "if [C] has all limits of all sizes, then [C] is a preorder" isn't statable).*  By making [isequiv_apD10] an [Axiom] rather than a per-theorem hypothesis, we can use it at multiple incompatible universe levels.  By only allowing use of the axiom when we have a [Funext] in the context, we can still track what theorems depend on it (because their type will mention [Funext]).

    By giving [Funext] a field who's type is an axiom, we guarantee that we cannot construct a fresh instance of [Funext] without [admit]; there's no term of type [dummy_funext_type] floating around.  If we did not give [Funext] and fields, then we could accidentally manifest a [Funext] using, e.g., [constructor], and then we wouldn't have a tag on the theorem that did this.

    As [Funext] is never actually used productively, we toss it in [Type0] and make it [Monomorphic] so it doesn't add more universes.

    * That's not technically true; it might be possible to get non-parametric universe polymorphism using [Module]s and ([Module]) Functors; we can use functors to quantify over a [Module Type] which requires a polymorphic proof of a given hypothesis, and then use that hypothesis polymorphically in any theorem we prove in our new [Module] Functor.  But that is far beyond the scope of this file. *)
Monomorphic Axiom Funext : Type0.
Existing Class Funext.
Axiom isequiv_apD10 : forall `{Funext} (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
Global Existing Instance isequiv_apD10.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

Global Arguments path_forall {_ A%type_scope P} (f g)%function_scope _.

(** *** Tactics *)

(** We declare some more [Hint Resolve] hints, now in the "hint database" [path_hints].  In general various hints (resolve, rewrite, unfold hints) can be grouped into "databases". This is necessary as sometimes different kinds of hints cannot be mixed, for example because they would cause a combinatorial explosion or rewriting cycles.

   A specific [Hint Resolve] database [db] can be used with [auto with db].

   The hints in [path_hints] are designed to push concatenation *outwards*, eliminate identities and inverses, and associate to the left as far as  possible. *)

(** TODO: think more carefully about this.  Perhaps associating to the right would be more convenient? *)
Hint Resolve idpath inverse : path_hints.
Hint Resolve idpath : core.

Ltac path_via mid :=
  apply @concat with (y := mid); auto with path_hints.

(** We put [Empty] here, instead of in [Empty.v], because [Ltac done] uses it. *)
Inductive Empty : Type0 := .
Register Empty as core.False.type.

Scheme Empty_ind := Induction for Empty Sort Type.
Scheme Empty_rec := Minimality for Empty Sort Type.
Definition Empty_rect := Empty_ind.

Definition not (A:Type) : Type := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Notation "~~ x" := (~ ~x) : type_scope.
Hint Unfold not: core.
Notation "x <> y  :>  T" := (not (x = y :> T)) : type_scope.
Notation "x <> y" := (x <> y :> _) : type_scope.

Definition symmetric_neq {A} {x y : A} : x <> y -> y <> x
  := fun np p => np (p^).

Definition complement {A} (R : Relation A) : Relation A :=
  fun x y => ~ (R x y).

Typeclasses Opaque complement.

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
Hint Resolve tt : core.

Register Unit as core.IDProp.type.
Register Unit as core.True.type.
Register tt as core.IDProp.idProp.
Register tt as core.True.I.

(** *** Pointed types *)

(** A space is pointed if that space has a point. *)
Class IsPointed (A : Type) := point : A.

Arguments point A {_}.

Record pType :=
  { pointed_type : Type ;
    ispointed_type : IsPointed pointed_type }.

Coercion pointed_type : pType >-> Sortclass.

Global Existing Instance ispointed_type.

(** *** Homotopy fibers *)

(** Homotopy fibers are homotopical inverse images of points.  *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

Global Arguments hfiber {A B}%type_scope f%function_scope y.

(** *** More tactics *)

(** Clear a hypothesis and also its dependencies.  Taken from Coq stdlib, with the performance-enhancing change to [lazymatch] suggested at [https://github.com/coq/coq/issues/11689]. *)
Tactic Notation "clear" "dependent" hyp(h) :=
  let rec depclear h :=
  clear h ||
  lazymatch goal with
   | H : context [ h ] |- _ => depclear H; depclear h
  end ||
  fail "hypothesis to clear is used in the conclusion (maybe indirectly)"
 in depclear h.


(** A version of [generalize dependent] that applies only to a hypothesis.  Taken from Coq stdlib. *)
Tactic Notation "revert" "dependent" hyp(h) :=
  generalize dependent h.

(** Applying a tactic to a term with increasingly many arguments *)
Tactic Notation "do_with_holes" tactic3(x) uconstr(p) :=
  x uconstr:(p) ||
  x uconstr:(p _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(** Same thing but starting with many holes first *)
Tactic Notation "do_with_holes'" tactic3(x) uconstr(p) :=
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _) ||
  x uconstr:(p).

(** A shorter name for [simple refine]. *)
Tactic Notation "srefine" uconstr(term) := simple refine term.
(** A shorter name for [notypeclasses refine]. *)
Tactic Notation "nrefine" uconstr(term) := notypeclasses refine term.
(** A shorter name for [simple notypeclasses refine]. *)
Tactic Notation "snrefine" uconstr(term) := simple notypeclasses refine term.

(** Note that the Coq standard library has a [rapply], but it is like our [rapply'] with many-holes first.  We prefer fewer-holes first, for instance so that a theorem producing an equivalence will by preference be used to produce an equivalence rather than to apply the coercion of that equivalence to a function. *)
Tactic Notation "rapply" uconstr(term)
  := do_with_holes ltac:(fun x => refine x) term.
Tactic Notation "rapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => refine x) term.

Tactic Notation "srapply" uconstr(term)
  := do_with_holes ltac:(fun x => srefine x) term.
Tactic Notation "srapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => srefine x) term.

Tactic Notation "nrapply" uconstr(term)
  := do_with_holes ltac:(fun x => nrefine x) term.
Tactic Notation "nrapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => nrefine x) term.

Tactic Notation "snrapply" uconstr(term)
  := do_with_holes ltac:(fun x => snrefine x) term.
Tactic Notation "snrapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => snrefine x) term.

(** Ssreflect tactics, adapted by Robbert Krebbers *)
Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [symmetry; trivial]
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

(** A convenient tactic for using function extensionality. *)
Ltac by_extensionality x :=
  intros;
  match goal with
  | [ |- ?f = ?g ] => eapply path_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with path_hints
  end.

(** [funext] apply functional extensionality ([path_forall]) to the goal and the introduce the arguments in the context. *)
(** For instance, if you have to prove [f = g] where [f] and [g] take two arguments, you can use [funext x y], and the goal become [f x y = g x y]. *)
Tactic Notation "funext" simple_intropattern(a)
  := apply path_forall; intros a.
Tactic Notation "funext" simple_intropattern(a)  simple_intropattern(b)
  := funext a; funext b.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c)
  := funext a; funext b; funext c.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d)
  := funext a; funext b; funext c; funext d.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e)
  := funext a; funext b; funext c; funext d; funext e.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e) simple_intropattern(f)
  := funext a; funext b; funext c; funext d; funext e; funext f.

(* Test whether a tactic fails or succeeds, without actually doing anything.  Taken from Coq stdlib. *)
Ltac assert_fails tac :=
  tryif (once tac) then gfail 0 tac "succeeds" else idtac.
Ltac assert_succeeds tac :=
  tryif (assert_fails tac) then gfail 0 tac "fails" else idtac.
Tactic Notation "assert_succeeds" tactic3(tac) :=
  assert_succeeds tac.
Tactic Notation "assert_fails" tactic3(tac) :=
  assert_fails tac.

(** This tactic doesn't end with [auto], but you can always write "by (path_induction;auto with path_hints)" if you want.*)
Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : ?x = ?y  |- _ ] => assert_fails constr_eq x y; induction p
    end
  ).

(** The tactic [f_ap] is a replacement for the previously existing standard library tactic [f_equal].  This tactic works by repeatedly applying the fact that [f = g -> x = y -> f x = g y] to turn, e.g., [f x y = f z w] first into [f x = f z] and [y = w], and then turns the first of these into [f = f] and [x = z].  The [done] tactic is used to detect the [f = f] case and finish, and the [trivial] is used to solve, e.g., [x = x] when using [f_ap] on [f y x = f z x].  This tactic only works for non-dependently-typed functions; we cannot express [y = w] in the first example if [y] and [w] have different types.  If and when Arnaud's new-tacticals branch lands, and we can have a goal which depends on the term used to discharge another goal, then this tactic should probably be generalized to deal with dependent functions. *)
Ltac f_ap :=
  idtac;
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g);
                             try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.

(** [expand] replaces both terms of an equality (either [paths] or [pointwise_paths] in the goal with their head normal forms *)
Ltac expand :=
  idtac;
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

(** [atomic x] is the same as [idtac] if [x] is a variable or hypothesis, but is [fail 0] if [x] has internal structure.  This is useful, for example, to easily destruct all variables that show up as the discriminees of [match] statements, without destructing more complicated terms whose structures might matter. *)
Ltac atomic x :=
  idtac;
  match x with
    | _ => is_evar x; fail 1 x "is not atomic (evar)"
    | ?f _ => fail 1 x "is not atomic (application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | let x := _ in _ => fail 1 x "is not atomic (let in)"
    | match _ with _ => _ end => fail 1 x "is not atomic (match)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | _ => is_cofix x; fail 1 x "is not atomic (cofix)"
    | context[?E] => (* catch-all *) (assert_fails constr_eq E x); fail 1 x "is not atomic (has subterm" E ")"
    | _ => idtac
  end.

(** Find the head of the given expression. *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

(** This tactic gets the constructor of any one-constructor inductive type. *)
Ltac get_constructor_head T :=
  let x := fresh in
  let x' := fresh in
  let h := open_constr:(_) in
  let __ := constr:(fun (x : T)
                    => let x' := x in
                       ltac:(destruct x;
                             let x' := (eval cbv delta [x'] in x') in
                             let x' := head x' in
                             unify h x';
                             exact I)) in
  h.

(* A version of econstructor that doesn't resolve typeclasses. *)
Ltac ntc_constructor :=
  lazymatch goal with
  | [ |- ?G ] => let build := get_constructor_head G in
                 nrapply build
  end.

(** [case_path] is a HoTT replacement for [case_eq]; [case_path x] is like [destruct x], but it remembers the original value of [x] in an equation to be introduced. *)
Ltac case_path x :=
  let x' := fresh "x" in
  set (x' := x);
    generalize (idpath : x' = x);
    clearbody x';
    destruct x'.

(** [revert_opaque x] is like [revert x], except that it fails if [x] is not an opaque variable (i.e. if it has a [:=] definition rather than just a type). *)
Ltac revert_opaque x :=
  revert x;
  match goal with
    | [ |- forall _, _ ] => idtac
    | _ => fail 1 "Reverted constant is not an opaque variable"
  end.

(** [transparent assert (H : T)] is like [assert (H : T)], but leaves the body transparent. *)
(** Since binders don't respect [fresh], we use a name unlikely to be reused. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let __transparent_assert_hypothesis := (_ : type) in _);
  [
  | ((* We cannot use the name [__transparent_assert_hypothesis], due to some infelicities in the naming of bound variables.  So instead we pull the bottommost hypothesis. *)
    let H := match goal with H := _ |- _ => constr:(H) end in
    rename H into name) ].

(** [transparent eassert] is like [transparent assert], but allows holes in the type, which will be turned into evars. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" "by" tactic3(tac) := let name := fresh "H" in transparent assert (name : type); [ solve [ tac ] | ].
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" := transparent assert (name : type).
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" "by" tactic3(tac) := transparent assert (name : type) by tac.

(** A version of Coq's [remember] that uses our equality. *)
Ltac remember_as term name eqname :=
  set (name := term) in *;
  pose (eqname := idpath : term = name);
  clearbody eqname name.

Tactic Notation "remember" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  remember_as term name eqname.

(** A variant that doesn't substitute in the goal and hypotheses. *)
Ltac recall_as term name eqname :=
  pose (name := term);
  pose (eqname := idpath : term = name);
  clearbody eqname name.

Tactic Notation "recall" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  recall_as term name eqname.

(** [rel_hnf], when given a goal of the form [R x y] for any relation [R], puts [x] and [y] in head normal form. *)
Ltac rel_hnf :=
  idtac;
  match goal with
    | [ |- ?R ?x ?y ] => let x' := (eval hnf in x) in
                         let y' := (eval hnf in y) in
                         change (R x' y')
  end.

(** This tactic is a version of [tryif require () then if_yes () else if_no ()] which is suitable for use in constructing constrs by virtue of being evaluated during the Ltac expression evaluation phase rather than during the tactic running phase.
All three arguments are expected to be tactic thunks which will be passed a dummy unit argument.*)
Ltac tryif_cps require if_yes if_no :=
  let res := match constr:(Set) with
             | _ => let __ := match constr:(Set) with _ => require () end in
                    ltac:(if_yes)
             | _ => ltac:(if_no)
             end in res ().

(** The following tactic [issig] proves automatically that a record type is equivalent to a nested Sigma-type. Specifically, it proves a goal that looks like

<<
   { x : A & B x } <~> Some_Record
>>

In fact you don't even have to write down the sigma type. Though it is good practice to write it out anyway, this tactic can work out the sigma type and tell you what it should look like.

The following should generate the desired equivalence. You can check the definition to see what type it has and therefore what the sigma type should be.

<<
  Definition issig_myrecord
    : _ <~> MyRecord := ltac:(issig).

  Check issig_myrecord.
>>

In order to define this tactic we have many helper tactics.

*)


Local Ltac peel_evars term :=
  lazymatch term with
  | ?f ?x
    => tryif_cps
         ltac:(fun _ => has_evar x)
         ltac:(fun _ => peel_evars f)
         ltac:(fun _ => term)
  | _ => term
  end.

Local Ltac pi_to_sig ty :=
  lazymatch (eval cbv beta in ty) with
  | forall (x : ?T) (y : @?A x), @?P x y
    => let x' := fresh in
       constr:(@sigT T (fun x' : T =>
        ltac:(let res := pi_to_sig
          (forall y : A x', P x' y) in exact res)))
  | ?T -> _ => T
  end.

Local Ltac ctor_to_sig ctor :=
  let ctor := peel_evars ctor in
  let t := type of ctor in
  pi_to_sig t.

Local Ltac unify_first_evar_with term u :=
  lazymatch term with
  | ?f ?x
    => tryif has_evar f
    then unify_first_evar_with f u
    else unify x u
  end.

Local Ltac unify_with_projections term u :=
  (unify_first_evar_with term u.1; unify_with_projections term u.2) +
  (unify_first_evar_with term u;
   tryif has_evar term then fail 0 term "has evars remaining" else idtac).

(* Completely destroys v into it's pieces and trys to put pieces in sigma. *)
Local Ltac refine_with_existT_as_much_as_needed_then_destruct v :=
  ((destruct v; shelve) +
   (snrefine (_ ; _);
    [ destruct v; shelve
    | refine_with_existT_as_much_as_needed_then_destruct v ])).


(* Finally we can define our issig tactic: *)
Ltac issig :=
  hnf; (* First we make sure things are normalised. *)
  (* We get the types either side of the equivalence. *)
  let A := match goal with |- ?sigma <~> ?record => constr:(sigma) end in
  let B := match goal with |- ?sigma <~> ?record => constr:(record) end in
  let u := fresh "u" in
  let v := fresh "v" in
  (** We build an equivalence with 5 holes. *)
  snrefine  (* We don't want typeclass search running. *)
    (Build_Equiv A B _ (Build_IsEquiv A B (fun u => _) (fun v => _)
      (fun v => _) (fun u => _) (fun _ => _)));
  (** Going from a sigma type to a record *)
  [ (* let built be the constructor of T *)
    let T := match goal with |- ?T => T end in
    (* We want to get the constructor of the record. Note that we use [ntc_constructor] instead of [econstructor] since we don't want to resolve typeclasses. If we used [econstructor] then the constructor would be wrong for many records whose fields are classes. [ntc_constructor] is defined in Overture.v. *)
    let built := open_constr:(ltac:(ntc_constructor) : T) in
    let A' := ctor_to_sig built in
    unify A A';
    unify_with_projections built u;
    refine built
  (** Going from a record to a sigma type *)
  | refine_with_existT_as_much_as_needed_then_destruct v
  (** Proving eissect *)
  | destruct v; cbn [pr1 pr2]; reflexivity
  (** Proving eisretr *)
  | reflexivity
  (** Proving eisadj *)
  | reflexivity ].

(** We show how the tactic works in a couple of examples. *)

Definition issig_contr (A : Type)
  : {x : A & forall y, x = y} <~> Contr A.
Proof.
  issig.
Defined.

Definition issig_equiv (A B : Type)
  : {f : A -> B & IsEquiv f} <~> Equiv A B.
Proof.
  issig.
Defined.

Definition issig_isequiv {A B : Type} (f : A -> B)
  : {g : B -> A & {r : f o g == idmap & { s : g o f == idmap
    & forall x : A, r (f x) = ap f (s x)}}}
  <~> IsEquiv f.
Proof.
  issig.
Defined.

(** The general reasoning behind the issig tactic is: if we know the type of the record, econstructor will give us the constructor applied to evars for each field. If we assume that there are no evars in the type, we can unify the first evar with u.1, the next evar with u.2.1, the next with u.2.2.1, etc, and if we run out of evars or projections, we backtrack and instead fill the final evar with u.2.2....2. (Note that if we strip the trailing evars from the constructor before unifying them, we get a term with a Pi type, and if we drop the final codomain and turn the Pi type into a Sigma, this lets us autogenerate the Sigma type we should be using; this is how the versions that don't need a hand-crafted Sigma type work: they unify the generated type with the term in the goal that should be the Sigma type.)

Generating the function the other way is a bit trickier, because there's no easy way to get our hands on all the projections of the record, and moreover we don't even know how many pairings we'll need. The thing we want to do is introduce the right number of pairings, destruct the variable of record type in the goal for each component, and then magically use the right projection. I'll get back to the magic in a moment; first we need to take care of the "right number" of pairings. We could pull a trick where we infer the number by looking at the term we get from econstructor in a goal whose type is the record. Instead, I chose the more concise route of coding a tactic that introduces the minimum number of pairings needed to make the magic work. How does it know the minimum number? It doesn't need to! The wonder of (recursive) multisuccess tactics is that you can say "try no pairings, and if that makes any future tactic fail, backtrack and try one pairing, and if that doesn't work, backtrack and try two pairings, etc". (The downside is that the error messages you get when you set things up wrong are truly incomprehensible, because if you make a typo in any of the fields of the Sigma type the error message you end up getting is something like "(_; _) is a Sigma type but it was expected to have the type of the final field" (and it's always about the final field, regardless of which field you made a typo in). So plausibly it's worth it to still do the small issig tactics by hand, and only use this tactic for >= 5 fields or something.)

Okay, now onto the magic. How do we know which field is the right one? Well, there's only one answer that lets us prove the section and retraction by destruct+reflexivity, so we can let unification solve this problem for us. It's important to have destructed the record variable in each of the pair-component evars, because unification is not (yet) smart enough to invert records for us; this is what the destruct before shelve in the inverse function generation tactic is. We cbn pr1 and pr2 to make the unification problem be completely syntactic (no need to unfold anything during unification). This is probably not strictly necessary, but seems like good form to me.

Finally, we can prove the other one of the section/retraction pair (I can never recall which is which), and the adjoint, by reflexively. (Perhaps it would be better to use exact idpath, if we want to not have to unfold reflexivity when using equivalences generated by these tactics.) *)
