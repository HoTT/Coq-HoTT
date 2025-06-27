(** * Universal objects *)
Require Import Basics.Contractible.
Require Import Category.Core Category.Morphisms.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Definition of "unique up to unique isomorphism" *)

Definition unique_up_to_unique_isomorphism (C : PreCategory) (P : C -> Type) :=
  forall x (_ : P x) x' (_ : P x'),
    { c : Contr (morphism C x x')
    | IsIsomorphism (center (morphism C x x')) }.

(** ** Terminal objects *)
(** A terminal object is an object with a unique morphism from every
    other object. *)
Notation IsTerminalObject C x :=
  (forall x' : object C, Contr (morphism C x' x)).

Class TerminalObject (C : PreCategory) :=
  {
    object_terminal : C;
    isterminal_object_terminal :: IsTerminalObject C object_terminal
  }.

Coercion object_terminal : TerminalObject >-> object.

(** ** Initial objects *)
(** An initial object is an object with a unique morphism from every
    other object. *)
Notation IsInitialObject C x :=
  (forall x' : object C, Contr (morphism C x x')).

Class InitialObject (C : PreCategory) :=
  {
    object_initial : C;
    isinitial_object_initial :: IsInitialObject C object_initial
  }.

Coercion object_initial : InitialObject >-> object.

Arguments unique_up_to_unique_isomorphism [C] P.

(** ** Canonical morphisms *)
  
(** The unique morphism from an initial object. *)
Definition morphism_from_initial {C : PreCategory} {I : InitialObject C}
  (Y : object C)
  : morphism C I Y
  := center (morphism C I Y).

(** The unique morphism to a terminal object. *)
Definition morphism_to_terminal {C : PreCategory} {T : TerminalObject C}
  (X : object C)
  : morphism C X T
  := center (morphism C X T).

(** ** Initial and terminal objects are unique up to unique isomorphism *)
Section CategoryObjectsTheorems.
  Variable C : PreCategory.

  Ltac unique :=
    repeat first [ intro
                 | exists _
                 | exists (center (morphism C _ _))
                 | apply path_contr ].

  (** The terminal object is unique up to unique isomorphism. *)
  Theorem terminal_object_unique
    : unique_up_to_unique_isomorphism (fun x => IsTerminalObject C x).
  Proof.
    unique.
  Qed.

  (** The initial object is unique up to unique isomorphism. *)
  Theorem initial_object_unique
    : unique_up_to_unique_isomorphism (fun x => IsInitialObject C x).
  Proof.
    unique.
  Qed.

  (** Any two morphisms from an initial object are equal. *)
  Definition initial_morphism_unique {I X : object C}
    `{IsInitialObject C I} (f g : morphism C I X)
    : f = g
    := path_contr f g.
    
  (** Any two morphisms to a terminal object are equal. *)
  Definition terminal_morphism_unique {T X : object C}
    `{IsTerminalObject C T} (f g : morphism C X T)
    : f = g
    := path_contr f g.

End CategoryObjectsTheorems.
