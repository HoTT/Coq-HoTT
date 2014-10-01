(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import types.Empty types.Sum.
Require Import ReflectiveSubuniverse Modality hit.Truncations.
Open Scope equiv_scope.

(** * Generic Logic parametrized by a modality *)

(** A logic is essentially determined by a modality.  We include one extra piece of information: whether the modality contains [Empty].  This enables us to define [hfalse] more simply in that case. *)
Class Logic :=
  { logic_modality : Modality ;
    logic_contains_empty : inO Empty + Unit
  }.

Global Coercion logic_modality : Logic >-> Modality.

Definition Build_Logic_easy (mod : Modality) : Logic
  := Build_Logic mod (inr tt).

(** This declaration allows an assumed logic _in this file_ to be automatically noticed as a modality. *)
Local Existing Instance logic_modality.

Global Notation IsGenericProp P := (@inO (_:Logic) P).

(** A logic comes with connectives and quantifiers.  There is a distinction between those connectives and quantifiers which automatically preserve modal types, which are just given by the restriction of the ordinary type formers, and those which do not, to which the modal reflection has to be applied.  Those which automatically preserve modal types are:

- true (Unit or True)
- conjunction (prod, *, or /\)
- implies (->)
- universal quantification (forall)

Those which have to be modally reflected are

- false (Empty)
- disjunction (sum or +)
- existential quantification (sigT or {x:A & B x})

For the former, the fact that they preserve generic-propositions (modal types) has already been proven and placed in the instance database by [ReflectiveSubuniverse.v].  We don't need to modify their names or notations, but for completeness, we may define one abbreviation that is similar to the new ones we will define below. *)

Notation htrue := Unit (only parsing).

(** For the latter, we define the reflected versions with "logical" names and notations, and also their elimination principles. *)

(** ** False

The extra data in the definiton [Logic] allows [hfalse] to denote the actual type [Empty] whenever possible, rather than its modal reflection (e.g. [Trunc -1 Empty] or [~~Empty], both of which are equivalent, but not judgmentally equal to, [Empty]).  *)

Section HFalse.
  Context {log : Logic}.

  Definition hfalse : Type :=
    match logic_contains_empty with
      | inl _ => Empty
      | inr _ => O Empty
    end.
  Notation False := hfalse (only parsing).

  Global Instance inO_hfalse : IsGenericProp (hfalse).
  Proof.
    unfold hfalse; destruct logic_contains_empty; exact _.
  Defined.
    
  Definition hfalse_elim (Q : Type) `{IsGenericProp Q}
  : hfalse -> Q.
  Proof.
    unfold hfalse; destruct logic_contains_empty.
    - apply Empty_rect.
    - apply O_rect; [ exact _ | apply Empty_rect ].
  Defined.

  Global Instance ishprop_hfalse : IsHProp hfalse.
  Proof.
    unfold hfalse; destruct logic_contains_empty; exact _.
  Defined.    

  (** *** Negation *)
  Definition hnot : Type -> Type
    := fun P => P -> hfalse.

End HFalse.

(** ** Disjunction

We could play a similar game for [hor] as we did for [hfalse], but it would be less useful since fewer logics are closed under sums. *)
Section HOr.
  Context {log : Logic}.

  Definition hor (P Q : Type) : Type := O (P + Q).

  Global Instance inO_hor P Q : IsGenericProp (hor P Q).
  Proof.
    exact _.
  Defined.

  Definition hor_inl {P Q} (p : P) : hor P Q
    := (O_unit (P + Q) (inl p)).

  Definition hor_inr {P Q} (q : Q) : hor P Q
    := (O_unit (P + Q) (inr q)).
  
  Definition hor_elim {P Q R} `{IsGenericProp R}
  : (P -> R) -> (Q -> R) -> (hor P Q -> R).
  Proof.
    intros p q.
    apply O_rect; try exact _.
    apply sum_rect; assumption.
  Defined.

End HOr.

(** ** Existential quantification

Here there would be no point at all in playing the game, since a nonidentity modality cannot be closed under all existential quantification. *)
Section HExists.
  Context {log : Logic}.

  Definition hex {A : Type} (P : A -> Type) : Type
    := O { a : A & P a }.

  Global Instance inO_hex A P : inO (@hex A P) := _.

  Definition hexist A P (a : A) (p :  P a) : hex P
    := O_unit { a : A & P a } (a ; p).

  Definition hexists_elim (A : Type) (P : A -> Type)
             (Q : Type) `{IsGenericProp Q}
  : (forall a, P a -> Q) -> hex P -> Q
    := fun f => O_rectnd (sig_rect (fun _ => Q) f).

End HExists.

(** ** Some useful logics *)

Definition PAT_logic :=
  Build_Logic identity_modality (inl _).

Definition truncated_logic (n : trunc_index) : Logic.
Proof.
  refine (Build_Logic (truncation_modality n) _).
  - destruct n.
    + exact (inr tt).
    + apply inl; simpl; exact _.
Defined.

Coercion truncated_logic : trunc_index >-> Logic.

Notation oo := PAT_logic.

Definition notnot_logic `{Funext} : Logic
  := Build_Logic notnot_modality (inl _).

(** Far and away the most important logic is (-1)-truncated logic.  So if you don't specify a logic or assume a generic one, you get that one. *)
Global Instance hprop_logic : Logic | 100
  := truncated_logic -1.
