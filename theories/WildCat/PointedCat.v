Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** A wild category is pointed if the initial and terminal object are the same. *)
Class IsPointedCat (A : Type) `{Is1Cat A} := {
  zero_object : A;
  isinitial_zero_object : IsInitial zero_object;
  isterminal_zero_object : IsTerminal zero_object;
}.

Global Existing Instance isinitial_zero_object.
Global Existing Instance isterminal_zero_object.

(** The zero morphism between objects [a] and [b] of a pointed category [A] is the unique morphism that factors throguh the zero object. *)
Definition zero_morphism {A : Type} `{IsPointedCat A} {a b : A} : a $-> b
  := (mor_initial _ b) $o (mor_terminal a _).

Section ZeroLaws.

  Context {A : Type} `{IsPointedCat A} {a b c : A}
    (f : a $-> b) (g : b $-> c).

  Definition cat_zero_source (h : zero_object $-> a) : h $== zero_morphism
    := (mor_initial_unique _ _ _)^$ $@ (mor_initial_unique _ _ _).

  Definition cat_zero_target (h : a $-> zero_object) : h $== zero_morphism
    := (mor_terminal_unique _ _ _)^$ $@ (mor_terminal_unique _ _ _).

  (** We show the last two arguments so that end pointes can easily be specified. *)
  Arguments zero_morphism {_ _ _ _ _ _} _ _.

  Definition cat_zero_l : zero_morphism b c $o f $== zero_morphism a c.
  Proof.
    refine (cat_assoc _ _ _ $@ (_ $@L _^$)).
    apply mor_terminal_unique.
  Defined.

  Definition cat_zero_r : g $o zero_morphism a b $== zero_morphism a c.
  Proof.
    refine ((_ $@R _) $@ cat_assoc _ _ _)^$.
    apply mor_initial_unique.
  Defined.

  (** Any morphism which factors through an object equivalent to the zero object is homotopic to the zero morphism. *)
  Definition cat_zero_m `{!HasEquivs A} (be : b $<~> zero_object)
    : g $o f $== zero_morphism a c.
  Proof.
    refine (_ $@L (compose_V_hh be f)^$ $@ _).
    refine (cat_assoc_opp _ _ _ $@ _).
    refine (_ $@L (mor_terminal_unique a _ _)^$ $@ _).
    exact ((mor_initial_unique _ _ _)^$ $@R _).
  Defined.

End ZeroLaws.

(** We show the last two arguments so that end pointes can easily be specified. We had to do this again, since the section encapsulated the previous attempt. *)
Local Arguments zero_morphism {_ _ _ _ _ _} _ _.

(** A functor is pointed if it preserves the zero object. *)
Class IsPointedFunctor {A B : Type} (F : A -> B) `{Is1Functor A B F} :=
{
  preservesinitial_pfunctor : PreservesInitial F ;
  preservesterminal_pfunctor : PreservesTerminal F ;
}.
Global Existing Instances preservesinitial_pfunctor preservesterminal_pfunctor.

(** Here is an alternative construct using preservation of the zero object. This requires more structure on the categories however. *)
Definition Build_IsPointedFunctor' {A B : Type} (F : A -> B)
  `{Is1Cat A, Is1Cat B, !Is0Functor F, !Is1Functor F}
  `{!IsPointedCat A, !IsPointedCat B, !HasEquivs A, !HasEquivs B}
  (p : F zero_object $<~> zero_object)
  : IsPointedFunctor F.
Proof.
  apply Build_IsPointedFunctor.
  + intros x inx.
    rapply isinitial_cate.
    symmetry.
    refine (p $oE _).
    rapply (emap F _).
    rapply cate_isinitial.
  + intros x tex.
    rapply isterminal_cate.
    symmetry.
    refine (p $oE _).
    rapply (emap F _).
    rapply cate_isterminal.
Defined.

(** Pointed functors preserve the zero object upto isomorphism. *)
Lemma pfunctor_zero {A B : Type} (F : A -> B)
  `{IsPointedCat A, IsPointedCat B, !HasEquivs B,
    !Is0Functor F, !Is1Functor F, !IsPointedFunctor F}
  : F zero_object $<~> zero_object.
Proof.
  rapply cate_isinitial.
Defined.

(** Pointed functors preserve the zero morphism upto homotopy *)
Lemma fmap_zero_morphism {A B : Type} (F : A -> B)
  `{IsPointedCat A, IsPointedCat B, !HasEquivs B,
    !Is0Functor F, !Is1Functor F, !IsPointedFunctor F} {a b : A}
  : fmap F (zero_morphism a b) $== zero_morphism (F a) (F b).
Proof.
  refine (fmap_comp F _ _ $@ _).
  refine (_ $@R _ $@ _).
  1: nrapply fmap_initial; [exact _].
  refine (_ $@L _ $@ _).
  1: nrapply fmap_terminal; [exact _].
  rapply cat_zero_m.
  rapply pfunctor_zero.
Defined.
