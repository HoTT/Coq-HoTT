(** * Notions of Structure *)
Require Import Category.Core.
Require Import HProp HSet Types.Sigma Types.Record Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** * Structures *)

Declare Scope structure_scope.
Declare Scope long_structure_scope.
Delimit Scope structure_scope with structure.
Delimit Scope long_structure_scope with long_structure.
Local Open Scope structure_scope.

(** Quoting the Homotopy Type Theory Book (with slight changes for
    notational consistency): *)

(** ** 9.8 The structure identity principle

    The _structure identity principle_ is an informal principle that
    expresses that isomorphic structures are identical. We aim to
    prove a general abstract result which can be applied to a wide
    family of notions of structure, where structures may be
    many-sorted or even dependently-sorted, in-finitary, or even
    higher order.

    The simplest kind of single-sorted structure consists of a type
    with no additional structure. The univalence axiom expresses the
    structure identity principle for that notion of structure in a
    strong form: for types [A], [B], the canonical function [(A = B) →
    (A ≃ B)] is an equivalence.  We start with a precategory [X]. In
    our application to single-sorted first order structures, [X] will
    be the category of [U]-small sets, where [U] is a univalent type
    universe. *)

(** *** Notion of Structure *)
(** Definition: A _notion of structure_ [(P,H)] over [X] consists of
    the following.  We use [X₀] to denote the objects of [X], and
    [homₓ(x, y)] to denote the morphisms [morphism X x y] of [X].

    (i) A type family [P : X₀ → Type].  For each [x : X₀] the elements
        of [P x] are called _[(P, H)]-structures_ on [x].

    (ii) For [x y : X₀] and [α : P x], [β : P y], to each [f : homₓ(x,
         y)] a mere proposition [H_{αβ}(f)].

         If [H_{αβ}(f)] is true, we say that [f] is a _[(P,
         H)]-homomorphism_ from [α] to [β].

    (iii) For [x : X₀] and [α : P x], we have [H_{αα}(1ₓ)].

    (iv) For [x y z : X₀] and [α : P x], [β : P y], [γ : P z], if [f :
         homₓ(x, y)], we have

         [H_{αβ}(f)→ H_{βγ}(g) → H_{αγ}(g ∘ f)].
 *)

(** Note: We rearrange some parameters to [H] to ease Coq's
    unification engine and typeclass machinery. *)

Record NotionOfStructure (X : PreCategory) :=
  {
    structure :> X -> Type;
    is_structure_homomorphism : forall x y
                                       (f : morphism X x y)
                                       (a : structure x) (b : structure y),
                               Type;
    istrunc_is_structure_homomorphism : forall x y a b f,
                                          IsHProp (@is_structure_homomorphism x y a b f);
    is_structure_homomorphism_identity : forall x (a : structure x),
                                           is_structure_homomorphism (identity x) a a;
    is_structure_homomorphism_composition : forall x y z
                                                   (a : structure x)
                                                   (b : structure y)
                                                   (c : structure z)
                                                   (f : morphism X x y)
                                                   (g : morphism X y z),
                                              is_structure_homomorphism f a b
                                              -> is_structure_homomorphism g b c
                                              -> is_structure_homomorphism (g o f) a c
  }.

(** It would be nice to make this a class, but we can't:

<<
    Existing Class is_structure_homomorphism.
>>

    gives

<<
    Toplevel input, characters 0-41:
    Anomaly: Mismatched instance and context when building universe substitution.
    Please report.
>>

    When we move to polyproj, it won't anymore. *)

Global Existing Instance istrunc_is_structure_homomorphism.

Create HintDb structure_homomorphisms discriminated.

Hint Resolve is_structure_homomorphism_identity is_structure_homomorphism_composition : structure_homomorphisms.

(** When [(P, H)] is a notion of structure, for [α β : P x] we define

    [(α ≤ₓ β) := H_{αβ}(1ₓ)].

*)

Local Notation "a <=_{ x } b" := (is_structure_homomorphism _ x x (identity x) a b) : long_structure_scope.
Local Notation "a <= b" := (a <=_{ _ } b)%long_structure : structure_scope.

(** By (iii) and (iv), this is a preorder with [P x] its type of objects. *)


(** *** Being a structure homomorphism is a preorder *)
Global Instance preorder_is_structure_homomorphism
       X (P : NotionOfStructure X) x
: PreOrder (is_structure_homomorphism P x x (identity x)).
Proof.
  split; repeat intro; eauto with structure_homomorphisms.
  rewrite <- identity_identity.
  eauto with structure_homomorphisms.
Defined.

(** *** Standard notion of structure *)
(** We say that [(P, H)] is a _standard notion of structure_ if this
    preorder is in fact a partial order, for all [x : X]. *)

(** A partial order is an antisymmetric preorder, i.e., we must have
    [a <= b <= a -> a = b]. *)

Class IsStandardNotionOfStructure X (P : NotionOfStructure X) :=
  antisymmetry_structure : forall x (a b : P x),
                             a <= b -> b <= a -> a = b.

(** Note that for a standard notion of structure, each type [P x] must
    actually be a set. *)

Global Instance istrunc_homomorphism_standard_notion_of_structure
       X P `{@IsStandardNotionOfStructure X P} x
: IsHSet (P x).
Proof.
  eapply (@isset_hrel_subpaths
            _ (fun a b => (a <= b) * (b <= a)));
  try typeclasses eauto.
  - repeat intro; split; apply reflexivity.
  - intros ? ? [? ?]; apply antisymmetry_structure; assumption.
Defined.

(** *** Precategory of structures *)
(** We now define, for any notion of structure [(P, H)], a
    _precategory of [(P, H)]-structures_,

    [A = Str_{(P, H)}(X)].

    - The type of objects of [A] is the type [A₀ := ∑ₓ P x].  If [a ≡
      (x; α)], we may write [|a| := x].

    - For [(x; α) : A₀] and [(y; β) : A₀], we define

      [hom_A((x; α), (y; β)) := { f : x → y | H_{αβ}(f) }].

    The composition and identities are inherited from [X]; conditions
    (iii) and (iv) ensure that these lift to [A]. *)

Module PreCategoryOfStructures.

  Section precategory.
    (** We use [Records] because they are faster than sigma types. *)

    Variable X : PreCategory.
    Variable P : NotionOfStructure X.

    Local Notation object := { x : X | P x }.

    (*Lemma issig_object
    : { x : X | P x } <~> object.
    Proof.
      issig Build_object x a.
    Defined.

    Lemma path_object
    : forall xa yb (H : x xa = x yb),
        transport P H (a xa) = a yb
        -> xa = yb.
    Proof.
      intros [? ?] [? ?] H H'; simpl in *; path_induction; reflexivity.
    Defined.*)

    Record morphism (xa yb : object) :=
      { f : Category.Core.morphism X xa.1 yb.1;
        h : is_structure_homomorphism _ _ _ f xa.2 yb.2 }.

    Lemma issig_morphism (xa yb : object)
    : { f : Category.Core.morphism X xa.1 yb.1
      | is_structure_homomorphism _ _ _ f xa.2 yb.2 }
        <~> morphism xa yb.
    Proof.
      issig (@Build_morphism xa yb) (@f xa yb) (@h xa yb).
    Defined.

    Lemma path_morphism
    : forall xa yb (fh gi : morphism xa yb),
        f fh = f gi -> fh = gi.
    Proof.
      intros ? ? [? ?] [? ?] H; simpl in *; path_induction; apply ap.
      apply path_ishprop.
    Defined.
  End precategory.

  (*Global Arguments path_object {X P xa yb} H _.*)
  Global Arguments path_morphism {X P xa yb fh gi} H.
End PreCategoryOfStructures.

Section precategory.
  Import PreCategoryOfStructures.

  Definition precategory_of_structures X (P : NotionOfStructure X) : PreCategory.
  Proof.
    refine (@Build_PreCategory
              _
              (@morphism _ P)
              (fun xa => {| f := identity xa.1;
                            h := is_structure_homomorphism_identity _ _ xa.2 |})
              (fun xa yb zc gi fh => {| f := (f gi) o (f fh);
                                        h := is_structure_homomorphism_composition _ _ _ _ _ _ _ _ _ (h fh) (h gi) |})
              _
              _
              _
              (fun s d => trunc_equiv' _ (issig_morphism P s d)));
    simpl;
    abstract (
        repeat match goal with
                 | |- @morphism _ P _ _ -> _ => intros [? ?]; simpl in *
                 | |- _ -> _ => intro
               end;
        first [ apply path_morphism; exact (associativity _ _ _ _ _ _ _ _)
              | apply path_morphism; exact (left_identity _ _ _ _)
              | apply path_morphism; exact (right_identity _ _ _ _) ]
      ).
  Defined.
End precategory.

Module Export StructureCoreNotations.
  Notation "a <=_{ x } b" := (is_structure_homomorphism _ x x (identity x) a b) : long_structure_scope.
  Notation "a <= b" := (a <=_{ _ } b)%long_structure : structure_scope.
End StructureCoreNotations.
