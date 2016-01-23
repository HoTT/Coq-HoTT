(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext EquivalenceVarieties Extensions Fibrations HProp.
Require Import HoTT.Tactics.
Require Import hit.Coeq.
Require Import Tactics.RewriteModuloAssociativity.

Local Open Scope path_scope.


(** * Reflective Subuniverses *)

(** We will define reflective subuniverses using modules.  Since modules are one of the more difficult parts of Coq to understand, and the documentation in the reference manual is a bit sparse, we include here a brief introduction to modules.

For our purposes here, it is appropriate to think of a [Module Type] as analogous to a [Record] type, and a [Module] having that module type (called an "implementation" of it) as analogous to an element of that record type.  For instance, instead of

<<
Record foo :=
  { bar : Type ;
    baz : bar -> Type
  }.
>>

we could write

<<
Module Type foo.
  Parameter bar : Type.
  Parameter baz : bar -> Type
End foo.
>>

and then instead of

<<
Definition qux : foo
  := Build_foo Bool (fun b => if b then Unit else Empty).
>>

we could write

<<
Module qux <: foo.
  Definition bar : Type
    := Bool.
  Definition baz : bar -> Type
    := fun b => if b then Unit else Empty.
End qux.
>>

Given these definitions, where we refer to [bar qux] and [baz qux] in the record case, in the module case we would write [qux.bar] and [qux.baz].  However, there are a few essential differences (apart from these syntactic ones).

Firstly, while elements of records are (like everything else in Coq's type theory) strongly typed, modules are duck-typed.  In other words, [qux] is a module of type [foo] simply by virtue of containing fields [bar] and [baz] that have the same types as those declared for the parameters of [foo]; the type declaration [<: foo] only serves to document and enforce this fact.

Secondly, modules do not have to be declared to have any type, or they can have more than one type.  A module is free to contain as many definitions (and other things such as notations, coercions, instances, etc.) as you like, and to "implement" as many module types as you like.  In particular, [qux] could contain additional definitions and it would still be of type [foo].

Thirdly, and more importantly, modules are *second-class*: you cannot pass them around as arguments to functions.  Nor can you construct them "on the fly"; they can only be defined at top level.  However, you can pass a module as an argument to *another module*.  For instance, here is a module which takes a module of type [foo] as an argument.

<<
Module htns (f : foo).
  Definition qjkx : Type
    := { x : f.bar & f.baz x }.
End htns.
>>

Now if we have a [foo], such as [qux], we can pass it as an argument to [htns] and get a new module (again, only at top level):

<<
Module gcrl := htns qux.
>>

After this, we can refer to [gcrl.qjkx] and get [{ x : qux.bar & qux.baz x }].  Together with the fact that modules don't need to have a type, this sort of gives us a way to pass a module as an argument to a collection of functions; we can define a module like [htns] which takes a [foo] as an argument and in which we define many functions depending on [foo]; then whenever we want to apply these functions to a [foo] (such as [qux]) we do the application at top-level, as above with [gcrl].

Unfortunately, Coq does not allow modules to take elements of ordinary types as arguments either; if you want to pass a [nat], say, as an argument to a module, you have to first wrap the [nat] in another module.  You can think of types and module-types as "parallel universes" of types; never the twain shall meet.

Given these annoying limitations, why would anyone ever use modules instead of records?  One reason is that modules are good at (indeed, are more or less designed for) *namespacing*.  In particular, it is possible to [Import] a module, so that all of its fields can be accessed without a dot-prefix.  In fact, every file in Coq is implicitly its own module, and when you say [Require Import Filename.] you are actually [Import]ing a module.  Similarly, modules are used for access control in the private-inductive-types hack that we use to define HITs that compute.

Another reason to use modules, which is the primary reason we choose to use them here, is that the fields of a module are *individually* universe polymorphic.  In other words, in order to define a module of type [foo], as above, you need to give a *polymorphic* definition of [bar] and a *polymorphic* definition of [baz], and the resulting module remembers the polymorphism of each of those fields.  By contrast, a definition of an element of a record type may be itself polymorphic, but an individual *instance* of that definition will pertain only to a fixed collection of universes.

Note that the possibility of individually polymorphic fields practically mandates that modules *must* be second-class.  For a polymorphic field involves an implicit quantification over all universes; hence if the record itself were a first-class object, what universe would it live in?  A mathematician can think of modules as analogous to the proper classes in NBG set theory: they can be "large" without impacting the consistency strength, *because* we are limited in what we can do with them.

In the case in point, if a reflective subuniverse were a record, then "a reflective subuniverse" would be a reflective subuniverse of only *one* universe.  A polymorphic definition of a particular reflective subuniverse would result in defining related reflective subuniverses of every universe, but the relation *between* these subuniverses would not be specified.  In particular, if we have types [X : Type@{i}] and [Y : Type@{j}] in different universes and a map [f : X -> Y], while [Y] is in the subuniverse of [Type@{j}], we could not apply the universal property to extend [f] to a map [O X -> Y], since the universal property asserted for [O@{i} X] would only refer to maps with target also in [Type@{i}].  This is at best annoying; for instance, it means that we couldn't define, say, [Trunc_functor] by using [O_functor] and then proceed to apply it to maps between types in different universes (which turns out to be necessary sometimes).  At worst, such as when trying to prove that the universe of modal types for a lex modalities is itself modal, this approach seems more or less unworkable.

Therefore, we choose to make a reflective subuniverse a module.  This means that in order to define "a reflective subuniverse", you have to give a *polymorphic* definition of the reflector, the universal property, etc.  In particular, the universal property must be polymorphic enough to allow the situation with [X : Type@{i}] and [Y : Type@{j}] considered above.

There are some issues involving this choice that must be addressed.  One of them is that when implementing a polymorphic module types, Coq is *very* strict about matching up the polymorphism.  Specifically, each [Definition] in the implementing module must have *exactly* the same number of universe parameters as the corresponding [Parameter] in the module type, and all the constraints in the former must be implied by those in the latter.  This ensures that the implementation is "at least as polymorphic" as the specification.

Now normally, a polymorphic definition will end up with many more universes than it needs, and we have little control over how many those are.  Therefore, in order to have a chance of ensuring that our implementations of module types match up in polymorphism, we almost always need to add explicit universe annotations in order to control how many universe parameters they end up with.  This is slightly annoying, but fortunately it only needs to be dealt with when *defining* a particular reflective subuniverse; to users the polymorphism should be invisible and automatic.

This also means it is important that we know exactly how many universe parameters each field of our module types is *expected* to take.  It would be nice if Coq had a feature for declaring (and verifying) the universe parameters of a definition in the same way that we declare the type parameters.  In the absence of this (requested at https://coq.inria.fr/bugs/show_bug.cgi?id=3818), we write [Check foo@{a b c}.] after the definition of [foo] to declare that [foo] takes three universe parameters.  Note that this will fail with an [Error] unless [foo] does in fact take exactly three universe parameters.

Another issue that must be dealt with is the fact, mentioned above, that a module cannot be parametrized over an ordinary type.  However, it frequently happens that we do want to define a family of reflective subuniverses, e.g. the n-truncation modalities for all [n : trunc_index], or the open and closed modalities for all [U : hProp].  The solution we choose is for our basic [Module Type] to represent not a *single* reflective subuniverse, but an entire *family* of them, parametrized by some type.  This can be regarded as analogous to how when doing mathematics relative to a base topos, the correct notion of "large category" is an *indexed category* (a.k.a. fibration), which comes with a basic notion of "[I]-indexed family of objects" for all [I] in the base topos.
*)

Module Type ReflectiveSubuniverses.

  (** As mentioned above, an implementation of this module type is a *family* of reflective subuniverses, indexed by the below type [ReflectiveSubuniverse].  If we just wrote [ReflectiveSubuniverse : Type], then it would end up parametrized by one universe, but in many examples the natural definition of the parametrizing type involves also a smaller universe, which would cause problems with Coq's strict polymorphism enforcement for module type implementations.  Thus, we use [Type2] instead, which takes two universe parameters. *)
  Parameter ReflectiveSubuniverse : Type2@{u a}.
  Check ReflectiveSubuniverse@{u a}.

  (** The universe parameters occurring in the definitions here play one of four roles, which we indicate consistently by [u], [a], [i], and [j].

  - [u] is the size of the parametrizing type [ReflectiveSubuniverse] (and, later, also [Modality]).
  - [a] is the size of smaller type-data occurring in that type, such as the family of generators for a localization.  This generally must be strictly smaller than [u].
  - [i] is the size of a type that we are reflecting or testing to be in the subuniverse.  This is generally at least as big as [a].
  - [j] is the size of a type that we are eliminating into (out of a type in [i]) with a universal property.  Also generally at least as big as [a].
  - [k] is a universe at least as large as both [i] and [j], in which statements about types in both of them can live. *)

  Parameter O_reflector : forall (O : ReflectiveSubuniverse@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.
  Check O_reflector@{u a i}.    (** Verify that we have the right number of universes *)

  (** For reflective subuniverses (and hence also modalities), it will turn out that [In O T] is equivalent to [IsEquiv (O_unit T)].  We could define the former as the latter, and it would simplify some of the general theory.  However, in many examples there is a "more basic" definition of [In O] which is equivalent, but not definitionally identical, to [IsEquiv (O_unit T)].  Thus, including [In O] as data makes more things turn out to be judgmentally what we would expect. *)
  Parameter In : forall (O : ReflectiveSubuniverse@{u a}),
                   Type2le@{i a} -> Type2le@{i a}.
  Check In@{u a i}.

  Parameter O_inO : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T).
  Check O_inO@{u a i}.

  Parameter to : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.
  Check to@{u a i}.

  Parameter inO_equiv_inO :
      forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        (** We add an extra universe parameter that's bigger than both [i] and [j].  This seems to be necessary for the proof of repleteness in some examples, such as easy modalities. *)
        let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
        let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
        In@{u a j} O U.
  Check inO_equiv_inO@{u a i j k}.

  (** In most examples, [Funext] is necessary to prove that the predicate of being in the subuniverse is an hprop.  To avoid needing to assume [Funext] as a global hypothesis when constructing such examples, and since [Funext] is often not needed for any of the rest of the theory, we add it as a hypothesis to this specific field. *)
  Parameter hprop_inO
  : Funext -> forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T).
  Check hprop_inO@{u a i}.

  (** We express the universal property using the representation [ooExtendableAlong] of precomposition equivalences.  This has the advantage that it avoids the funext redexes that otherwise infect the theory, thereby simplifying the proofs and proof terms.  We never have to worry about whether we have a path between functions or a homotopy; we use only homotopies, with no need for [ap10] or [path_arrow] to mediate.  Furthermore, the data in [ooExtendableAlong] are all special cases of the induction principle of a modality.  Thus, all the theorems we prove about reflective subuniverses will, when interpreted for a modality (coerced as above to a reflective subuniverse), reduce definitionally to "the way we would have proved them directly for a modality".  *)
  Parameter extendable_to_O
  : forall (O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}} {Q : Type2le@{j a}} {Q_inO : In@{u a j} O Q},
      ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).
  Check extendable_to_O@{u a i j k}.

End ReflectiveSubuniverses.


(** We now begin a parametrized module to incorporate most of the theory of reflective subuniverses.  Thus, after defining a particular family of reflective subuniverses, you can apply this module and [Import] it to get all of the theory.  (Some suggested naming conventions for these modules can be found in Modality.v.)  *)
Module ReflectiveSubuniverses_Theory (Os : ReflectiveSubuniverses).
Export Os.

(** Membership in the subuniverse is a typeclass. *)
Existing Class In.

(** The type of types in the subuniverse *)
Definition Type_ (O : ReflectiveSubuniverse@{u a}) : Type@{j}
  := sig@{j i} (fun (T : Type@{i}) => In@{u a i} O T).
Check Type_@{u a j i}.

(** Before going on, we declare some coercions in a module, so that they can be imported separately.  In fact, this submodule should be exported by any file that defines a reflective subuniverse.  *)
Module Export Coercions.

  (** We allow the name of a subuniverse or modality to be used as the name of its reflector.  This means that when defining a particular example, you should generally put the parametrizing family in a wrapper, so that you can notate the subuniverse as parametrized by, rather than identical to, its parameter.  See Modality.v, Truncations.v, and Localization.v for examples. *)
  Coercion O_reflector : ReflectiveSubuniverse >-> Funclass.

  (** Obviously, every element of [Type_ O] is a type. *)
  Coercion TypeO_pr1 O (T : Type_ O) := @pr1 Type (In O) T.

End Coercions.

(** We assumed repleteness of the subuniverse in the definition.  Of course, with univalence this would be automatic, but we include it as a hypothesis since this is the only appearance of univalence in the theory of reflective subuniverses and non-lex modalities, and most or all examples can be shown to be replete without using univalence. *)
Arguments inO_equiv_inO {O} T {U} {_} f {_}.

(** Being in the subuniverse is a mere predicate (by hypothesis) *)
Global Existing Instance hprop_inO.

(** [O T] is always in the subuniverse (by hypothesis).  This needs a universe annotation to become sufficiently polymorphic. *)
Arguments O_inO {O} T.
Global Existing Instance O_inO.

(** The second component of [TypeO] is unique *)
Definition path_TypeO {fs : Funext} O (T T' : Type_ O) (p : T.1 = T'.1)
  : T = T'
  := path_sigma_hprop T T' p.

Definition equiv_path_TypeO {fs : Funext} O (T T' : Type_ O)
: (T.1 = T'.1) <~> (T = T')
:= equiv_path_sigma_hprop T T'.

(** Types in [TypeO] are always in [O]. *)
Global Instance inO_TypeO {O : ReflectiveSubuniverse} (A : Type_ O)
: In O A
:= A.2.

Definition extendable_to_O (O : ReflectiveSubuniverse)
           {P Q : Type} {Q_inO : In O Q}
: ooExtendableAlong (to O P) (fun _ => Q)
  := @extendable_to_O O P Q Q_inO.

(** We now extract the recursion principle and the restricted induction principles for paths. *)
Section ORecursion.
  Context {O : ReflectiveSubuniverse}.

  Definition O_rec {P Q : Type} {Q_inO : In O Q}
             (f : P -> Q)
  : O P -> Q
  := (fst (extendable_to_O O 1%nat) f).1.

  Definition O_rec_beta {P Q : Type} {Q_inO : In O Q}
             (f : P -> Q) (x : P)
  : O_rec f (to O P x) = f x
  := (fst (extendable_to_O O 1%nat) f).2 x.

  Definition O_indpaths {P Q : Type} {Q_inO : In O Q}
             (g h : O P -> Q) (p : g o to O P == h o to O P)
  : g == h
  := (fst (snd (extendable_to_O O 2) g h) p).1.

  Definition O_indpaths_beta {P Q : Type} {Q_inO : In O Q}
             (g h : O P -> Q) (p : g o (to O P) == h o (to O P)) (x : P)
  : O_indpaths g h p (to O P x) = p x
  := (fst (snd (extendable_to_O O 2) g h) p).2 x.

  Definition O_ind2paths {P Q : Type} {Q_inO : In O Q}
             {g h : O P -> Q} (p q : g == h)
             (r : p oD (to O P) == q oD (to O P))
  : p == q
  := (fst (snd (snd (extendable_to_O O 3) g h) p q) r).1.

  Definition O_ind2paths_beta {P Q : Type} {Q_inO : In O Q}
             {g h : O P -> Q} (p q : g == h)
             (r : p oD (to O P) == q oD (to O P)) (x : P)
  : O_ind2paths p q r (to O P x) = r x
  := (fst (snd (snd (extendable_to_O O 3) g h) p q) r).2 x.

  (** Clearly we can continue indefinitely as needed. *)

End ORecursion.

(* We never want to see [extendable_to_O]. *)
Arguments O_rec : simpl never.
Arguments O_rec_beta : simpl never.
Arguments O_indpaths : simpl never.
Arguments O_indpaths_beta : simpl never.
Arguments O_ind2paths : simpl never.
Arguments O_ind2paths_beta : simpl never.

(** Given [Funext], we prove the definition of reflective subuniverse in the book. *)
Global Instance isequiv_o_to_O `{Funext}
       (O : ReflectiveSubuniverse) (P Q : Type) `{In O Q}
: IsEquiv (fun g : O P -> Q => g o to O P)
:= isequiv_ooextendable _ _ (extendable_to_O O).

Definition equiv_o_to_O `{Funext}
           (O : ReflectiveSubuniverse) (P Q : Type) `{In O Q}
: (O P -> Q) <~> (P -> Q)
:= BuildEquiv _ _ (fun g : O P -> Q => g o to O P) _.

(** ** Properties of Reflective Subuniverses *)

(** We now prove a bunch of things about an arbitrary reflective subuniverse. *)
Section Reflective_Subuniverse.
  Context (O : ReflectiveSubuniverse).

  (** Functoriality of [O_rec] homotopies *)
  Definition O_rec_homotopy {P Q : Type} `{In O Q} (f g : P -> Q) (pi : f == g)
  : O_rec f == O_rec g.
  Proof.
    apply O_indpaths; intro x.
    etransitivity.
    { apply O_rec_beta. }
    { etransitivity.
      { exact (pi _). }
      { symmetry; apply O_rec_beta. } }
  Defined.

  (** If [T] is in the subuniverse, then [to O T] is an equivalence. *)
  Global Instance isequiv_to_O_inO (T : Type@{i}) `{In O T} : IsEquiv@{i i} (to O T).
  Proof.
    (** Using universe annotations to reduce superfluous universes *)
    pose (g := O_rec@{u a i i i i i} idmap).
    refine (isequiv_adjointify (to O T) g _ _).
    - refine (O_indpaths@{u a i i i i i} (to O T o g) idmap _).
      intros x.
      apply ap.
      apply O_rec_beta.
    - intros x.
      apply O_rec_beta.
  Defined.

  Definition equiv_to_O (T : Type) `{In O T} : T <~> O T
    := BuildEquiv T (O T) (to O T) _.

  Section Functor.

    (** In this section, we see that [O] is a functor. *)

    Definition O_functor {A B : Type} (f : A -> B) : O A -> O B
      := O_rec (to O B o f).

    (** Naturality of [to O] *)
    Definition to_O_natural {A B : Type} (f : A -> B)
    : (O_functor f) o (to O A) == (to O B) o f
    := (O_rec_beta _).

    (** Functoriality on composition *)
    Definition O_functor_compose {A B C : Type} (f : A -> B) (g : B -> C)
    : (O_functor (g o f)) == (O_functor g) o (O_functor f).
    Proof.
      apply O_indpaths; intros x.
      refine (to_O_natural (g o f) x @ _).
      transitivity (O_functor g (to O B (f x))).
      - symmetry. exact (to_O_natural g (f x)).
      - apply ap; symmetry.
        exact (to_O_natural f x).
    Defined.

    (** Functoriality on homotopies (2-functoriality) *)
    Definition O_functor_homotopy {A B : Type} (f g : A -> B) (pi : f == g)
    : O_functor f == O_functor g.
    Proof.
      refine (O_indpaths _ _ _); intros x.
      refine (to_O_natural f x @ _).
      refine (_ @ (to_O_natural g x)^).
      apply ap, pi.
    Defined.

    (** Functoriality for inverses of homotopies *)
    Definition O_functor_homotopy_V
               {A B : Type} (f g : A -> B) (pi : f == g)
    : O_functor_homotopy g f (fun x => (pi x)^)
      == fun x => (O_functor_homotopy f g pi x)^.
    Proof.
      refine (O_ind2paths _ _ _); intros x.
      unfold composeD, O_functor_homotopy.
      rewrite !O_indpaths_beta, !ap_V, !inv_pp, inv_V, !concat_p_pp.
      reflexivity.
    Qed.

    (** Hence functoriality on commutative squares *)
    Definition O_functor_square {A B C X : Type} (pi1 : X -> A) (pi2 : X -> B)
               (f : A -> C) (g : B -> C) (comm : (f o pi1) == (g o pi2))
    : ( (O_functor f) o (O_functor pi1) )
      == ( (O_functor g) o (O_functor pi2) ).
    Proof.
      intros x.
      transitivity (O_functor (f o pi1) x).
      - symmetry; erapply O_functor_compose.
      - transitivity (O_functor (g o pi2) x).
        * apply O_functor_homotopy, comm.
        * erapply O_functor_compose.
    Defined.

    (** Functoriality on identities *)
    Definition O_functor_idmap (A : Type)
    : @O_functor A A idmap == idmap.
    Proof.
      refine (O_indpaths _ _ _); intros x.
      apply O_rec_beta.
    Qed.

    (** 3-functoriality, as an example use of [O_ind2paths] *)
    Definition O_functor_2homotopy {A B : Type} {f g : A -> B}
               (p q : f == g) (r : p == q)
    : O_functor_homotopy f g p == O_functor_homotopy f g q.
    Proof.
      refine (O_ind2paths _ _ _); intros x.
      unfold O_functor_homotopy, composeD.
      do 2 rewrite O_indpaths_beta.
      apply whiskerL, whiskerR, ap, r.
    (** Of course, if we wanted to prove 4-functoriality, we'd need to make this transparent. *)
    Qed.

    (** 2-naturality: Functoriality on homotopies is also natural *)
    Definition O_functor_homotopy_beta
               {A B : Type} (f g : A -> B) (pi : f == g) (x : A)
    : O_functor_homotopy f g pi (to O A x)
      = to_O_natural f x
      @ ap (to O B) (pi x)
      @ (to_O_natural g x)^.
    Proof.
      unfold O_functor_homotopy, to_O_natural.
      refine (O_indpaths_beta _ _ _ x @ _).
      refine (concat_p_pp _ _ _).
    Defined.

    (** The pointed endofunctor ([O],[to O]) is well-pointed *)
    Definition O_functor_wellpointed (A : Type)
    : O_functor (to O A) == to O (O A).
    Proof.
      refine (O_indpaths _ _ _); intros x.
      apply to_O_natural.
    Defined.

    (** "Functoriality of naturality": the pseudonaturality axiom for composition *)
    Definition to_O_natural_compose {A B C : Type}
               (f : A -> B) (g : B -> C) (a : A)
    : ap (O_functor g) (to_O_natural f a)
      @ to_O_natural g (f a)
      = (O_functor_compose f g (to O A a))^
      @ to_O_natural (g o f) a.
    Proof.
      unfold O_functor_compose, to_O_natural.
      rewrite O_indpaths_beta.
      rewrite !inv_pp, ap_V, !inv_V, !concat_pp_p.
      rewrite concat_Vp, concat_p1; reflexivity.
    Qed.

    (** The pseudofunctoriality axiom *)
    Definition O_functor_compose_compose
               {A B C D : Type} (f : A -> B) (g : B -> C) (h : C -> D)
               (a : O A)
    : O_functor_compose f (h o g) a
      @ O_functor_compose g h (O_functor f a)
      = O_functor_compose (g o f) h a
        @ ap (O_functor h) (O_functor_compose f g a).
    Proof.
      revert a; refine (O_ind2paths _ _ _).
      intros a; unfold composeD, O_functor_compose; cbn.
      Open Scope long_path_scope.
      rewrite !O_indpaths_beta, !ap_pp, !ap_V, !concat_p_pp.
      refine (whiskerL _ (apD _ (to_O_natural f a)^)^ @ _).
      rewrite O_indpaths_beta.
      rewrite transport_paths_FlFr, !concat_p_pp.
      rewrite !ap_V, inv_V.
      rewrite !concat_pV_p.
      apply whiskerL. apply inverse2.
      apply ap_compose.
      Close Scope long_path_scope.
    Qed.

    (** Preservation of equivalences *)
    Global Instance isequiv_O_functor {A B : Type} (f : A -> B) `{IsEquiv _ _ f}
    : IsEquiv (O_functor f).
    Proof.
      refine (isequiv_adjointify (O_functor f) (O_functor f^-1) _ _).
      - intros x.
        refine ((O_functor_compose _ _ x)^ @ _).
        refine (O_functor_homotopy _ idmap _ x @ _).
        + intros y; apply eisretr.
        + apply O_functor_idmap.
      - intros x.
        refine ((O_functor_compose _ _ x)^ @ _).
        refine (O_functor_homotopy _ idmap _ x @ _).
        + intros y; apply eissect.
        + apply O_functor_idmap.
    Defined.

    Definition equiv_O_functor {A B : Type} (f : A <~> B)
    : O A <~> O B
    := BuildEquiv _ _ (O_functor f) _.

    (** This corresponds to [ap O] on the universe. *)
    Definition ap_O_path_universe' `{Univalence}
               {A B : Type} (f : A <~> B)
    : ap O (path_universe_uncurried f)
      = path_universe_uncurried (equiv_O_functor f).
    Proof.
      revert f.
      equiv_intro (equiv_path A B) p.
      refine (ap (ap O) (eta_path_universe p) @ _).
      destruct p; simpl.
      apply moveL_equiv_V.
      apply path_equiv, path_arrow, O_indpaths; intros x.
      symmetry; apply to_O_natural.
    Defined.

    Definition ap_O_path_universe `{Univalence}
               {A B : Type} (f : A -> B) `{IsEquiv _ _ f}
    : ap O (path_universe f) = path_universe (O_functor f)
    := ap_O_path_universe' (BuildEquiv _ _ f _).

    (** Postcomposition respects [O_rec] *)
    Definition O_rec_postcompose {A B C : Type} `{In O B} {C_inO : In O C}
               (f : A -> B) (g : B -> C)
    : g o O_rec f == O_rec (g o f).
    Proof.
      refine (O_indpaths _ _ _); intros x.
      transitivity (g (f x)).
      - apply ap. apply O_rec_beta.
      - symmetry. exact (O_rec_beta (g o f) x).
    Defined.

  End Functor.

  Section Replete.

    (** An equivalent formulation of repleteness is that a type lies in the subuniverse as soon as its unit map is an equivalence. *)
    Definition inO_isequiv_to_O (T:Type)
    : IsEquiv (to O T) -> In O T
    := fun _ => inO_equiv_inO (O T) (to O T)^-1.

    (* We don't make this an ordinary instance, but we allow it to solve [In O] constraints if we already have [IsEquiv] as a hypothesis.  *)
    Hint Immediate inO_isequiv_to_O : typeclass_instances.

    Definition inO_iff_isequiv_to_O (T:Type)
    : In O T <-> IsEquiv (to O T).
    Proof.
      split; exact _.
    Defined.

    (** Thus, [T] is in a subuniverse as soon as [to O T] admits a retraction. *)
    Definition inO_to_O_retract (T:Type) (mu : O T -> T)
    : Sect (to O T) mu -> In O T.
    Proof.
      unfold Sect; intros H.
      apply inO_isequiv_to_O.
      apply isequiv_adjointify with (g:=mu).
      - refine (O_indpaths (to O T o mu) idmap _).
        intros x; exact (ap (to O T) (H x)).
      - exact H.
    Defined.

  End Replete.

  Section OInverts.

    (** The maps that are inverted by the reflector.  Note that this notation is NOT GLOBAL, it only exists in this section. *)
    Local Notation O_inverts f := (IsEquiv (O_functor f)).

    Global Instance O_inverts_O_unit (A : Type)
    : O_inverts (to O A).
    Proof.
      refine (isequiv_homotopic (to O (O A)) _).
      intros x; symmetry; apply O_functor_wellpointed.
    Defined.

    (** A map between modal types that is inverted by [O] is already an equivalence.  This can't be an [Instance], probably because it causes an infinite regress applying more and more [O_functor]. *)
    Definition isequiv_O_inverts {A B : Type} `{In O A} `{In O B}
      (f : A -> B) `{O_inverts f}
    : IsEquiv f.
    Proof.
      refine (isequiv_commsq' f (O_functor f) (to O A) (to O B) _).
      apply to_O_natural.
    Defined.

    (** Strangely, even this seems to cause infinite loops *)
    (** [Hint Immediate isequiv_O_inverts : typeclass_instances.] *)

    Definition equiv_O_inverts {A B : Type} `{In O A} `{In O B}
      (f : A -> B) `{O_inverts f}
    : A <~> B
    := BuildEquiv _ _ f (isequiv_O_inverts f).

    Definition isequiv_O_rec_O_inverts
           {A B : Type} `{In O B} (f : A -> B) `{O_inverts f}
    : IsEquiv (O_rec f).
    Proof.
      apply isequiv_O_inverts.
      refine (cancelR_isequiv (O_functor (to O A))).
      refine (isequiv_homotopic (O_functor (O_rec f o to O A))
                                (O_functor_compose _ _)).
      refine (isequiv_homotopic (O_functor f)
               (O_functor_homotopy _ _ (fun x => (O_rec_beta f x)^))).
    Defined.

    Definition to_O_inv_natural {A B : Type} `{In O A} `{In O B}
               (f : A -> B)
    : (to O B)^-1 o (O_functor f) == f o (to O A)^-1.
    Proof.
      refine (O_indpaths _ _ _); intros x.
      apply moveR_equiv_V.
      refine (to_O_natural f x @ _).
      do 2 apply ap.
      symmetry; apply eissect.
    Defined.

    (** Two maps between modal types that become equal after applying [O_functor] are already equal. *)
    Definition O_functor_faithful_inO {A B : Type} `{In O A} `{In O B}
      (f g : A -> B) (e : O_functor f == O_functor g)
      : f == g.
    Proof.
      intros x.
      refine (ap f (eissect (to O A) x)^ @ _).
      refine (_ @ ap g (eissect (to O A) x)).
      transitivity ((to O B)^-1 (O_functor f (to O A x))).
      + symmetry; apply to_O_inv_natural.
      + transitivity ((to O B)^-1 (O_functor g (to O A x))).
        * apply ap, e.
        * apply to_O_inv_natural.
    Defined.

    (** Any map to a type in the subuniverse that is inverted by [O] must be equivalent to [to O].  More precisely, the type of such maps is contractible. *)
    Definition typeof_to_O (A : Type)
      := { OA : Type & { Ou : A -> OA & ((In O OA) * (O_inverts Ou)) }}.

    Global Instance contr_typeof_O_unit `{Univalence} (A : Type)
    : Contr (typeof_to_O A).
    Proof.
      exists (O A ; (to O A ; (_ , _))).
      intros [OA [Ou [? ?]]].
      pose (f := O_rec Ou : O A -> OA).
      pose (g := (O_functor Ou)^-1 o to O OA : (OA -> O A)).
      assert (IsEquiv f).
      { refine (isequiv_adjointify f g _ _).
        - apply O_functor_faithful_inO; intros x.
          rewrite O_functor_idmap.
          rewrite O_functor_compose.
          unfold g.
          rewrite (O_functor_compose (to O OA) (O_functor Ou)^-1).
          rewrite O_functor_wellpointed.
          rewrite (to_O_natural (O_functor Ou)^-1 x).
          refine (to_O_natural f _ @ _).
          set (y := (O_functor Ou)^-1 x).
          transitivity (O_functor Ou y); try apply eisretr.
          unfold f, O_functor.
          apply O_rec_postcompose.
        - refine (O_indpaths _ _ _); intros x.
          unfold f.
          rewrite O_rec_beta. unfold g.
          apply moveR_equiv_V.
          symmetry; apply to_O_natural.
      }
      simple refine (path_sigma _ _ _ _ _); cbn.
      - exact (path_universe f).
      - rewrite transport_sigma.
        simple refine (path_sigma _ _ _ _ _); cbn; try apply path_ishprop.
        apply path_arrow; intros x.
        rewrite transport_arrow_fromconst.
        rewrite transport_path_universe.
        unfold f; apply O_rec_beta.
    Qed.

  End OInverts.

  Section Types.

    (** ** The [Unit] type *)
    Global Instance inO_unit : In O Unit.
    Proof.
      apply inO_to_O_retract with (mu := fun x => tt).
      exact (@contr Unit _).
    Defined.

    (** It follows that any contractible type is in [O]. *)
    Global Instance inO_contr {A : Type} `{Contr A} : In O A.
    Proof.
      exact (inO_equiv_inO Unit equiv_contr_unit^-1).
    Defined.

    (** And that the reflection of a contractible type is still contractible. *)
    Global Instance contr_O_contr {A : Type} `{Contr A} : Contr (O A).
    Proof.
      exact (contr_equiv A (to O A)).
    Defined.

    (** ** Dependent product and arrows *)
    (** Theorem 7.7.2 *)
    Global Instance inO_forall {fs : Funext} (A:Type) (B:A -> Type)
    : (forall x, (In O (B x)))
      -> (In O (forall x:A, (B x))).
    Proof.
      intro H.
      pose (ev := fun x => (fun (f:(forall x, (B x))) => f x)).
      pose (zz := fun x:A => O_rec (ev x)).
      apply inO_to_O_retract with (mu := fun z => fun x => zz x z).
      intro phi.
      unfold zz, ev; clear zz; clear ev.
      apply path_forall; intro x.
      exact (O_rec_beta (fun f : forall x0, (B x0) => f x) phi).
    Defined.

    Global Instance inO_arrow {fs : Funext} (A B : Type) `{In O B}
    : In O (A -> B).
    Proof.
      apply inO_forall.
      intro a. exact _.
    Defined.

    (** ** Product *)
    Global Instance inO_prod (A B : Type) `{In O A} `{In O B}
    : In O (A*B).
    Proof.
      apply inO_to_O_retract with
        (mu := fun X => (@O_rec _ (A * B) A _ fst X , O_rec snd X)).
      intros [a b]; apply path_prod; simpl.
      - exact (O_rec_beta fst (a,b)).
      - exact (O_rec_beta snd (a,b)).
    Defined.

    (** We show that [OA*OB] has the same universal property as [O(A*B)] *)

    Definition equiv_O_prod_unit_precompose
               {fs : Funext} (A B C : Type) `{In O C}
    : ((O A) * (O B) -> C) <~> (A * B -> C).
    Proof.
      refine (equiv_uncurry A B C oE _).
      refine (_ oE (equiv_uncurry (O A) (O B) C)^-1).
      refine (equiv_o_to_O _ A (B -> C) oE _); simpl.
      apply equiv_postcompose'.
      exact (equiv_o_to_O _ B C).
    Defined.

    (** The preceding equivalence turns out to be actually (judgmentally!) precomposition with the following function. *)
    Definition O_prod_unit (A B : Type) : A * B -> O A * O B
      := functor_prod (to O A) (to O B).

    (** From this, we can define the comparison map for products, and show that precomposing with it is also an equivalence. *)
    Definition O_prod_cmp (A B : Type) : O (A * B) -> O A * O B
      := O_rec (O_prod_unit A B).

    Global Instance isequiv_O_prod_cmp (A B : Type)
    : IsEquiv (O_prod_cmp A B).
    Proof.
      simple refine (isequiv_adjointify _ _ _ _).
      { apply prod_ind; intro a.
        apply O_rec; intro b; revert a.
        apply O_rec; intro a.
        apply (to O).
        exact (a, b). }
      { unfold prod_ind, O_prod_cmp, O_prod_unit.
        intros [oa ob].
        revert ob; refine (O_indpaths _ _ _); intros b.
        revert oa; refine (O_indpaths _ _ _); intros a.
        cbn. abstract (repeat rewrite O_rec_beta; reflexivity). }
      { unfold prod_ind, O_prod_cmp, O_prod_unit.
        refine (O_indpaths _ _ _); intros [a b]; cbn.
        abstract (repeat (rewrite O_rec_beta; cbn); reflexivity). }
    Defined.

    Definition isequiv_O_prod_cmp_precompose
      {fs : Funext} (A B C : Type) {C_inO : In O C}
    : IsEquiv (fun h : O A * O B -> C => h o O_prod_cmp A B).
    Proof.
      apply isequiv_precompose; exact _.
    Defined.

    Definition equiv_O_prod_cmp {fs : Funext} (A B : Type)
    : O (A * B) <~> (O A * O B)
    := BuildEquiv _ _ (O_prod_cmp A B) _.

    (** ** Dependent sums *)
    (** Theorem 7.7.4 *)
    Definition inO_sigma_from_O_ind
    : (forall (A:Type@{i}) (B: (O A) -> Type@{j}) `{forall a, In@{u a j} O (B a)}
              (g : forall (a:A), (B (to O A a))),
         {f : forall (z:O A), (B z) & forall a:A, f (to@{u a i} O A a) = g a})
      ->
      (forall (A:Type@{i}) (B:A -> Type@{j}) `{In@{u a i} O A} `{forall a, In@{u a j} O (B a)},
         (In@{u a j} O (sig@{i j} (fun x:A => B x)))).
    Proof.
      intros H A B ? ?.
             pose (h := fun x => @O_rec _ ({x:A & B x}) A _ pr1 x).
      pose (p := (fun z => O_rec_beta pr1 z)
                 : h o (to O _) == pr1).
      pose (g := fun z => (transport B ((p z)^) z.2)).
      simpl in *.
      specialize (H ({x:A & B x}) (B o h) _ g).
      destruct H as [f q].
      apply inO_to_O_retract with (mu := fun w => (h w; f w)).
      intros [x1 x2].
      simple refine (path_sigma B _ _ _ _); simpl.
      - apply p.
      - rewrite (q (x1;x2)).
        unfold g; simpl. exact (transport_pV B _ _).
    Qed.

    Definition O_ind_from_inO_sigma
    (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3811 *)
    : (forall (A:Type@{i}) (B:A -> Type@{j}) {A_inO : In@{u a i} O A} `{forall a, In@{u a j} O (B a)},
         (In@{u a j} O (sig@{i j} (fun x:A => B x))))
      ->
      (forall (A:Type@{i}) (B: (O A) -> Type@{j}) `{forall a, In@{u a j} O (B a)}
              (g : forall (a:A), (B (to O A a))),
         {f : forall (z:O A), (B z) & forall a:A, f (to@{u a i} O A a) = g a}).
    Proof.
      intro H. intros A B ? g.
      pose (Z := sigT B).
      assert (In@{u a j} O Z).
      { apply H; [ exact _ | assumption ]. }
      pose (g' := (fun a:A => (to O A a ; g a)) : A -> Z).
      pose (f' := O_rec g').
      pose (eqf := (O_rec_beta g')  : f' o to O A == g').
      pose (eqid := O_indpaths (pr1 o f') idmap
                               (fun x => ap pr1 (eqf x))).
      exists (fun z => transport B (eqid z) ((f' z).2)); intros a.
      unfold eqid. rewrite O_indpaths_beta.
      exact (pr2_path (O_rec_beta g' a)).
    Defined.

    (** ** Fibers *)

    Global Instance inO_hfiber {A B : Type} `{In O A} `{In O B}
           (f : A -> B) (b : B)
    : In O (hfiber f b).
    Proof.
      simple refine (inO_to_O_retract _ _ _).
      - intros x; simple refine (_;_).
        + exact (O_rec pr1 x).
        + revert x; apply O_indpaths; intros x; simpl.
          refine (ap f (O_rec_beta pr1 x) @ _).
          exact (x.2).
      - intros [a p]; simple refine (path_sigma' _ _ _).
        + exact (O_rec_beta pr1 (a;p)).
        + refine (ap (transport _ _) (O_indpaths_beta _ _ _ _) @ _); simpl.
          refine (transport_paths_Fl _ _ @ _).
          apply concat_V_pp.
    Defined.

    Definition inO_unsigma {A : Type} (B : A -> Type)
               `{In O A} {B_inO : In O {x:A & B x}} (x : A)
    : In O (B x).
    Proof.
      refine (inO_equiv_inO _ (hfiber_fibration x B)^-1).
      (** TODO: Why doesn't Coq find this instance? *)
      refine (inO_hfiber pr1 x); assumption.
    Defined.

    Hint Immediate inO_unsigma : typeclass_instances.

    (** The reflector preserving hfibers is a characterization of lex modalities.  Here is the comparison map. *)
    Definition O_functor_hfiber {A B} (f : A -> B) (b : B)
    : O (hfiber f b) -> hfiber (O_functor f) (to O B b).
    Proof.
      apply O_rec. intros [a p].
      exists (to O A a).
      refine (to_O_natural f a @ _).
      apply ap, p.
    Defined.

    (** ** Paths *)

    Global Instance inO_paths (S : Type) {S_inO : In O S} (x y : S)
    : In O (x=y).
    Proof.
      simple refine (inO_to_O_retract _ _ _); intro u.
      - assert (p : (fun _ : O (x=y) => x) == (fun _=> y)).
        { refine (O_indpaths _ _ _); simpl.
          intro v; exact v. }
        exact (p u).
      - hnf.
        rewrite O_indpaths_beta; reflexivity.
    Qed.

    (** ** Truncations  *)

    (** The reflector preserves hprops (and, as we have already seen, contractible types), although it doesn't generally preserve [n]-types for other [n]. *)
    Global Instance ishprop_O_ishprop {A} `{IsHProp A} : IsHProp (O A).
    Proof.
      refine ishprop_isequiv_diag.
      refine (isequiv_homotopic (O_prod_cmp A A
                               o O_functor (fun (a:A) => (a,a))) _).
      apply O_indpaths; intros x; simpl.
      refine (ap (O_prod_cmp A A) (to_O_natural (fun (a:A) => (a,a)) x) @ _).
      unfold O_prod_cmp; apply O_rec_beta.
    Defined.

    (** If [A] is [In O], then so is [IsTrunc n A]. *)
    Global Instance inO_istrunc `{Funext} {n} {A} `{In O A}
    : In O (IsTrunc n A).
    Proof.
      generalize dependent A; simple_induction n n IH; intros A ?.
      - (** We have to be slightly clever here: the actual definition of [Contr] involves a sigma, which [O] is not generally closed under, but fortunately we have [equiv_contr_inhabited_allpath]. *)
        refine (inO_equiv_inO _ equiv_contr_inhabited_allpath^-1).
      - change (In O (forall x y:A, IsTrunc n (x=y))).
        exact _.
    Defined.

    (** ** Coproducts *)

    Definition equiv_O_sum {A B} :
      O (A + B) <~> O (O A + O B).
    Proof.
      simple refine (equiv_adjointify _ _ _ _).
      - apply O_rec; intros x.
        exact (to O _ (functor_sum (to O A) (to O B) x)).
      - apply O_rec; intros [x|x].
        + (* Work around https://coq.inria.fr/bugs/show_bug.cgi?id=4525, stack overflow in exact *)
          let lem := constr:(fun A B => to O _ o @inl A B) in
          exact (O_rec (lem _ _) x).
        + let lem := constr:(fun A B => to O _ o @inr A B) in
          exact (O_rec (lem _ _) x).
      - apply O_indpaths; intros [x|x].
        all:revert x; apply O_indpaths; intros x.
        all:abstract (rewrite !O_rec_beta; reflexivity).
      - apply O_indpaths; intros [x|x].
        all:abstract (rewrite !O_rec_beta; cbn;
                      rewrite !O_rec_beta; reflexivity).
    Defined.

    (** ** Coequalizers *)

    Section OCoeq.
      Context {B A : Type} (f g : B -> A).

      Definition O_coeq_cmp
      : O (Coeq f g) -> O (Coeq (O_functor f) (O_functor g)).
      Proof.
        apply O_functor.
        exact (functor_coeq (to O B) (to O A)
                            (fun y => (to_O_natural f y)^)
                            (fun y => (to_O_natural g y)^)).
      Defined.

      Definition O_coeq_cmp_inverse
      : O (Coeq (O_functor f) (O_functor g)) -> O (Coeq f g).
      Proof.
        apply O_rec; simple refine (Coeq_rec _ _ _).
        - apply O_functor, coeq.
        - intros b.
          refine ((O_functor_compose f coeq b)^ @ _).
          refine (_ @ (O_functor_compose g coeq b)).
          apply O_functor_homotopy.
          intros z; apply cp.
      Defined.

      Local Definition O_coeq_cmp_eisretr
      : Sect O_coeq_cmp_inverse O_coeq_cmp.
      Proof.
        unfold O_coeq_cmp, O_coeq_cmp_inverse.
        apply O_indpaths; intros z.
        rewrite O_rec_beta.
        revert z; simple refine (Coeq_ind _ _ _).
        - cbn; intros a.
          refine ((O_functor_compose _ _ _)^ @ _); cbn.
          revert a; apply O_indpaths, to_O_natural.
        - set (coeq_to :=
                 functor_coeq (to O B) (to O A)
                              (fun y : B => (to_O_natural f y)^)
                              (fun y : B => (to_O_natural g y)^)).
          apply O_ind2paths; intros b; unfold composeD; cbn.
          rewrite transport_paths_FlFr, concat_pp_p; apply moveR_Vp.
          rewrite <- (apD (O_indpaths _ _ _) (to_O_natural f b)^).
          rewrite <- (apD (O_indpaths _ _ _) (to_O_natural g b)^).
          rewrite !O_indpaths_beta, !transport_paths_FlFr.
          Open Scope long_path_scope.
          rewrite !ap_V, !inv_V, !concat_p_pp.
          rewrite (ap_compose _ (O_functor coeq_to)).
          rewrite Coeq_rec_beta_cp.
          rewrite !ap_pp, !concat_p_pp.
          unfold O_functor_homotopy; rewrite O_indpaths_beta.
          rewrite !ap_pp, !concat_p_pp.
          pose (p := O_functor_compose_compose g coeq coeq_to (to O B b)).
          apply moveL_pV in p; rewrite concat_pp_p in p; apply moveR_Vp in p.
          rewrite@A <- p. clear p.
          rewrite@A (to_O_natural_compose g
                       (fun x => @coeq _ _ (O_functor f) (O_functor g)
                                       (to O A x)) b).
          rewrite concat_pp_V.
          rewrite@A (to_O_natural_compose f
                     (fun x => @coeq _ _ (O_functor f) (O_functor g)
                                     (to O A x)) b).
          rewrite <- inv_pp.
          rewrite (O_functor_compose_compose f coeq coeq_to (to O B b)).
          rewrite inv_pp, ap_V.
          rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
          (** The trick here is to notice that [(fun x => coeq (to O A (f x)))] is definitionally equal to [(fun x => coeq_to (coeq (f x)))]. *)
          rewrite <- (to_O_natural_compose
                        (fun x => coeq (f x)) coeq_to b).
          rewrite <- ap_compose.
          rewrite !concat_pp_p; apply whiskerL, moveR_Mp; rewrite !concat_p_pp.
          rewrite <- (concat_Ap (fun x => (to_O_natural coeq_to x)^) (cp b)).
          rewrite !concat_pp_p; apply moveL_Mp; rewrite !concat_p_pp.
          rewrite ap_V, <- !inv_pp, @to_O_natural_compose.
          rewrite concat_p_Vp, concat_Vp, concat_1p.
          rewrite (ap_compose coeq_to (to O (Coeq (O_functor f) (O_functor g)))).
          subst coeq_to; rewrite functor_coeq_beta_cp.
          rewrite !ap_pp, <- !ap_compose, !inv_pp, !concat_p_pp, !ap_V, !inv_V.
          rewrite concat_pp_V, concat_pV_p; reflexivity.
          Close Scope long_path_scope.
      Qed.

      Local Definition O_coeq_cmp_eissect
      : Sect O_coeq_cmp O_coeq_cmp_inverse.
      Proof.
        unfold O_coeq_cmp, O_coeq_cmp_inverse.
        apply O_indpaths; intros z.
        rewrite to_O_natural, O_rec_beta.
        revert z; simple refine (Coeq_ind _ _ _).
        - intros a. cbn.
          apply to_O_natural.
        - intros b; cbn.
          rewrite transport_paths_FlFr, ap_compose.
          rewrite functor_coeq_beta_cp.
          rewrite !ap_pp, <- !ap_compose; cbn.
          rewrite Coeq_rec_beta_cp.
          Open Scope long_path_scope.
          rewrite !inv_pp, !concat_p_pp, !ap_V, !inv_V.
          apply moveR_pM; rewrite !concat_pp_p.
          rewrite (to_O_natural_compose f (@coeq B A f g) b).
          rewrite concat_p_Vp.
          rewrite <- O_functor_homotopy_V.
          rewrite O_functor_homotopy_beta.
          rewrite concat_pV_p, !concat_p_pp, ap_V; apply whiskerR.
          rewrite !concat_pp_p; apply moveR_Vp.
          symmetry; apply to_O_natural_compose.
          Close Scope long_path_scope.
      Qed.

      Global Instance isequiv_O_coeq_cmp
      : IsEquiv O_coeq_cmp
        := isequiv_adjointify _ O_coeq_cmp_inverse
                              O_coeq_cmp_eisretr O_coeq_cmp_eissect.

      Definition equiv_O_coeq
      : O (Coeq f g) <~> O (Coeq (O_functor f) (O_functor g))
        := BuildEquiv _ _ O_coeq_cmp _.

    End OCoeq.

  End Types.

  Section Decidable.

    (** If [Empty] belongs to [O], then [O] preserves decidability. *)
    Global Instance decidable_O `{In O Empty} (A : Type) `{Decidable A}
    : Decidable (O A).
    Proof.
      destruct (dec A) as [y|n].
      - exact (inl (to O A y)).
      - exact (inr (O_rec n)).
    Defined.

    (** Dually, if [O A] is decidable, then [O (Decidable A)]. *)
    Definition O_decidable (A : Type) `{Decidable (O A)}
    : O (Decidable A).
    Proof.
      destruct (dec (O A)) as [y|n].
      - exact (O_functor inl y).
      - refine (O_functor inr _).
        apply to; intros a.
        exact (n (to O A a)).
    Defined.

  End Decidable.

  Section Monad.

    Definition O_monad_mult (A : Type) : O (O A) -> O A
      := O_rec idmap.

    Definition O_monad_mult_natural {A B} (f : A -> B)
    : O_functor f o O_monad_mult A == O_monad_mult B o O_functor (O_functor f).
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult.
      rewrite (to_O_natural (O_functor f) x).
      rewrite (O_rec_beta idmap x).
      rewrite (O_rec_beta idmap (O_functor f x)).
      reflexivity.
    Qed.

    Definition O_monad_unitlaw1 (A : Type)
    : O_monad_mult A o (to O (O A)) == idmap.
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult.
      exact (O_rec_beta idmap (to O A x)).
    Defined.

    Definition O_monad_unitlaw2 (A : Type)
    : O_monad_mult A o (O_functor (to O A)) == idmap.
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult, O_functor.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_mult_assoc (A : Type)
    : O_monad_mult A o O_monad_mult (O A) == O_monad_mult A o O_functor (O_monad_mult A).
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult, O_functor.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

  End Monad.

  Section StrongMonad.
    Context {fs : Funext}.

    Definition O_monad_strength (A B : Type) : A * O B -> O (A * B)
      := fun aob => O_rec (fun b a => to O (A*B) (a,b)) (snd aob) (fst aob).

    Definition O_monad_strength_natural (A A' B B' : Type) (f : A -> A') (g : B -> B')
    : O_functor (functor_prod f g) o O_monad_strength A B ==
      O_monad_strength A' B' o functor_prod f (O_functor g).
    Proof.
      intros [a ob]. revert a. apply ap10.
      revert ob; apply O_indpaths.
      intros b; simpl.
      apply path_arrow; intros a.
      unfold O_monad_strength, O_functor; simpl.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    (** The diagrams for strength, see http://en.wikipedia.org/wiki/Strong_monad *)
    Definition O_monad_strength_unitlaw1 (A : Type)
    : O_functor (@snd Unit A) o O_monad_strength Unit A == @snd Unit (O A).
    Proof.
      intros [[] oa]; revert oa.
      apply O_indpaths; intros x; unfold O_monad_strength, O_functor. simpl.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_unitlaw2 (A B : Type)
    : O_monad_strength A B o functor_prod idmap (to O B) == to O (A*B).
    Proof.
      intros [a b].
      unfold O_monad_strength, functor_prod. simpl.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_assoc1 (A B C : Type)
    : O_functor (equiv_prod_assoc A B C)^-1 o O_monad_strength (A*B) C ==
      O_monad_strength A (B*C) o functor_prod idmap (O_monad_strength B C) o (equiv_prod_assoc A B (O C))^-1.
    Proof.
      intros [[a b] oc].
      revert a; apply ap10. revert b; apply ap10.
      revert oc; apply O_indpaths.
      intros c; simpl.
      apply path_arrow; intros b. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, functor_prod. simpl.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    Definition O_monad_strength_assoc2 (A B : Type)
    : O_monad_mult (A*B) o O_functor (O_monad_strength A B) o O_monad_strength A (O B) ==
      O_monad_strength A B o functor_prod idmap (O_monad_mult B).
    Proof.
      intros [a oob]. revert a; apply ap10.
      revert oob; apply O_indpaths. apply O_indpaths.
      intros b; simpl. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, O_monad_mult, functor_prod. simpl.
      repeat (rewrite O_rec_beta; simpl).
      reflexivity.
    Qed.

  End StrongMonad.

End Reflective_Subuniverse.

(** Make the [O_inverts] notation global. *)
Notation O_inverts O f := (IsEquiv (O_functor O f)).

End ReflectiveSubuniverses_Theory.

(** ** Restriction of a family of reflective subuniverses *)

(** Recall that an implementation of [ReflectiveSubuniverses] is a family of reflective subuniverses indexed by the type [ReflectiveSubuniverse].  Sometimes we want to consider only a subfamily of a known one, or more generally a restriction of such a family along a function.  The second-class nature of modules makes this a bit of a pain to construct, but we can do it. *)
Module Type ReflectiveSubuniverses_Restriction_Data (Os : ReflectiveSubuniverses).

  Parameter New_ReflectiveSubuniverse : Type2@{u a}.
  Check New_ReflectiveSubuniverse@{u a}.    (** Verify that we have the right number of universes *)

  Parameter ReflectiveSubuniverses_restriction
  : New_ReflectiveSubuniverse@{u a} -> Os.ReflectiveSubuniverse@{u a}.
  Check ReflectiveSubuniverses_restriction@{u a}.

End ReflectiveSubuniverses_Restriction_Data.

Module ReflectiveSubuniverses_Restriction
       (Os : ReflectiveSubuniverses)
       (Res : ReflectiveSubuniverses_Restriction_Data Os)
<: ReflectiveSubuniverses.

  Definition ReflectiveSubuniverse := Res.New_ReflectiveSubuniverse.

  Definition O_reflector (O : ReflectiveSubuniverse@{u a})
    := Os.O_reflector@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition In (O : ReflectiveSubuniverse@{u a})
    := Os.In@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition O_inO (O : ReflectiveSubuniverse@{u a})
    := Os.O_inO@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition to (O : ReflectiveSubuniverse@{u a})
    := Os.to@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition inO_equiv_inO (O : ReflectiveSubuniverse@{u a})
    := Os.inO_equiv_inO@{u a i j k} (Res.ReflectiveSubuniverses_restriction O).
  Definition hprop_inO (H : Funext) (O : ReflectiveSubuniverse@{u a})
    := Os.hprop_inO@{u a i} H (Res.ReflectiveSubuniverses_restriction O).
  Definition extendable_to_O (O : ReflectiveSubuniverse@{u a})
    := @Os.extendable_to_O@{u a i j k} (Res.ReflectiveSubuniverses_restriction@{u a} O).

End ReflectiveSubuniverses_Restriction.

(** ** Union of families of reflective subuniverses *)

Module ReflectiveSubuniverses_FamUnion
       (Os1 Os2 : ReflectiveSubuniverses)
<: ReflectiveSubuniverses.

  Definition ReflectiveSubuniverse : Type2@{u a}
    := Os1.ReflectiveSubuniverse@{u a} + Os2.ReflectiveSubuniverse@{u a}.

  Coercion RSU_inl := inl : Os1.ReflectiveSubuniverse -> ReflectiveSubuniverse.
  Coercion RSU_inr := inr : Os2.ReflectiveSubuniverse -> ReflectiveSubuniverse.

  Definition O_reflector : forall (O : ReflectiveSubuniverse@{u a}),
                             Type2le@{i a} -> Type2le@{i a}.
  Proof.
    intros [O|O]; [ exact (Os1.O_reflector@{u a i} O)
                  | exact (Os2.O_reflector@{u a i} O) ].
  Defined.

  Definition In : forall (O : ReflectiveSubuniverse@{u a}),
                             Type2le@{i a} -> Type2le@{i a}.
  Proof.
    intros [O|O]; [ exact (Os1.In@{u a i} O)
                  | exact (Os2.In@{u a i} O) ].
  Defined.

  Definition O_inO
  : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
      In@{u a i} O (O_reflector@{u a i} O T).
  Proof.
    intros [O|O]; [ exact (Os1.O_inO@{u a i} O)
                  | exact (Os2.O_inO@{u a i} O) ].
  Defined.

  Definition to : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.
  Proof.
    intros [O|O]; [ exact (Os1.to@{u a i} O)
                  | exact (Os2.to@{u a i} O) ].
  Defined.

  Definition inO_equiv_inO :
      forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        In@{u a j} O U.
  Proof.
    intros [O|O]; [ exact (Os1.inO_equiv_inO@{u a i j k} O)
                  | exact (Os2.inO_equiv_inO@{u a i j k} O) ].
  Defined.

  Definition hprop_inO
  : Funext -> forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T).
  Proof.
    intros ? [O|O]; [ exact (Os1.hprop_inO@{u a i} _ O)
                    | exact (Os2.hprop_inO@{u a i} _ O) ].
  Defined.

  Definition extendable_to_O
  : forall (O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}} {Q : Type2le@{j a}} {Q_inO : In@{u a j} O Q},
      ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).
  Proof.
    intros [O|O]; [ exact (@Os1.extendable_to_O@{u a i j k} O)
                  | exact (@Os2.extendable_to_O@{u a i j k} O) ].
  Defined.

End ReflectiveSubuniverses_FamUnion.

(** For examples of reflective subuniverses, see the examples of modalities listed in the file [Modality], and also [Localization]. *)
