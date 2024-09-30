(** * Impredicative truncations *)

(** In this file, under the assumptions of propositional resizing [PropResizing] and function extensionality [Funext], we define the proposition truncation in any universe. In the main library, these are constructed using HITs. The definitions here are meant to be for illustration. *)

Require Import HoTT.Basics.
Require Import Universes.Smallness.
Local Open Scope path_scope.

(** Using only function extensionality, we can define a "propositional truncation" [Trm A] of a type [A] in universe [i] which eliminates into propositions in universe [j].  It lands in [max(i,j+1)].  So if we want it to land in universe [i], then we can only eliminate into propositions in a strictly smaller universe [j].  Or, if we want it to eliminate into propositions in universe [i], then it must land in a strictly larger universe. *)
Definition Trm@{i j | } (A : Type@{i})
  := forall P:Type@{j}, IsHProp P -> (A -> P) -> P.

Definition trm@{i j | } {A : Type@{i}} : A -> Trm@{i j} A
  := fun a P HP f => f a.

(** Here [k] plays the role of [max(i,j+1)]. *)
Global Instance ishprop_Trm@{i j k | i <= k, j < k} `{Funext} (A : Type@{i})
  : IsHProp (Trm@{i j} A).
Proof.
  nrapply istrunc_forall@{k k k}; intro B.
  nrapply istrunc_forall@{j k k}; intro ishp.
  apply istrunc_forall@{k j k}.
Defined.

(** As mentioned above, it eliminates into propositions in universe [j]. *)
Definition Trm_rec@{i j | } {A : Type@{i}}
  {P : Type@{j}} {p : IsHProp@{j} P} (f : A -> P)
  : Trm@{i j} A -> P
  := fun ma => ma P p f.

(** This computes definitionally. *)
Definition Trm_rec_beta@{i j | } {A : Type@{i}}
  {P : Type@{j}} `{IsHProp P} (f : A -> P)
  : Trm_rec@{i j} f o trm == f
  := fun _ => idpath.

(** Because of the universe constraints, we can't make this into a functor on [Type@{i}].  We have a universe constraint [i' <= j] and [Trm@{i j} A] lands in [max(i,j+1)], which is strictly larger. *)
Definition functor_Trm@{i j i' j' | i' <= j, j' < j} `{Funext}
  {A : Type@{i}} {A' : Type@{i'}} (f : A -> A')
  : Trm@{i j} A -> Trm@{i' j'} A'
  := Trm_rec (trm o f).

(** We also record the dependent induction principle.  But it only computes propositionally. *)
Definition Trm_ind@{i j k | i <= k, j < k} {A : Type@{i}} `{Funext}
  {P : Trm@{i j} A -> Type@{j}} {p : forall x, IsHProp@{j} (P x)} (f : forall a, P (trm a))
  : forall x, P x.
Proof.
  unfold Trm.
  intro x.
  rapply x.
  intro a.
  refine (transport P _ (f a)).
  rapply path_ishprop@{k}.
Defined.

(** The universe constraints go away if we assume propositional resizing. *)

Section AssumePropResizing.
  Context `{PropResizing}.

  (** If we assume propositions resizing, then we may as well quantify over propositions in the lowest universe [Set] when defining the truncation.  This reduces the number of universe variables.  We also assume that [Set < i], so that the construction lands in universe [i]. *)
  Definition imp_Trm@{i | Set < i} (A : Type@{i}) : Type@{i}
    := Trm@{i Set} A.

  (** Here we use propositional resizing to resize a arbitrary proposition [P] from an arbitrary universe [j] to universe [Set], so there is no constraint on the universe [j].  In particular, we can take [j = i], which shows that [imp_Trm] is a reflective subuniverse of [Type@{i}], since any two maps into a proposition agree. *)
  Definition imp_Trm_rec@{i j | Set < i} {A : Type@{i}}
    {P : Type@{j}} `{IsHProp P} (f : A -> P)
    : imp_Trm@{i} A -> P
    := fun ma => (equiv_smalltype@{Set j} P)
                 (ma (smalltype@{Set j} P) _ ((equiv_smalltype@{Set j} P)^-1 o f)).

  (** Similarly, there are no constraints between [i] and [i'] in the next definition, so they could be taken to be equal. *)
  Definition functor_imp_Trm@{i i' | Set < i, Set < i'} `{Funext}
    {A : Type@{i}} {A' : Type@{i'}} (f : A -> A')
    : imp_Trm@{i} A -> imp_Trm@{i'} A'
    := imp_Trm_rec (trm o f).

  (** Note that [imp_Trm_rec] only computes propositionally. *)
  Definition imp_Trm_rec_beta@{i j | Set < i} {A : Type@{i}}
    {P : Type@{j}} `{IsHProp P} (f : A -> P)
    : imp_Trm_rec@{i j} f o trm == f.
  Proof.
    intro a.
    unfold imp_Trm_rec, trm; cbn beta.
    apply eisretr@{Set j}.
  Defined.

End AssumePropResizing.

(** Above, we needed the constraint [Set < i].  But one can use propositional resizing again to make [imp_Trm] land in the lowest universe, if that is needed.  (We'll in fact let it land in any universe [u].)  To do this, we need to assume [Funext] in the definition of the truncation itself. *)

Section TruncationWithFunext.
  Context `{PropResizing} `{Funext}.

  (** [Funext] implies that [Trm A] is a proposition, so [PropResizing] can be used to put it in any universe. The construction passes through universe [k], which represents [max(i,Set+1)]. *)
  Definition resized_Trm@{i k u | i <= k, Set < k} (A : Type@{i})
    : Type@{u}
    := smalltype@{u k} (Trm@{i Set} A).

  Definition resized_trm@{i k u | i <= k, Set < k} {A : Type@{i}}
    : A -> resized_Trm@{i k u} A
    := (equiv_smalltype _)^-1 o trm.

  Definition resized_Trm_rec@{i j k u | i <= k, Set < k} {A : Type@{i}}
    {P : Type@{j}} `{IsHProp P} (f : A -> P)
    : resized_Trm@{i k u} A -> P.
  Proof.
    refine (_ o (equiv_smalltype@{u k} _)).
    exact (fun ma => (equiv_smalltype@{Set j} P)
                 (ma (smalltype@{Set j} P) _ ((equiv_smalltype@{Set j} P)^-1 o f))).
  Defined.

  (** The beta rule is again propositional. *)
  Definition resized_Trm_rec_beta@{i j k u | i <= k, Set < k} {A : Type@{i}}
    {P : Type@{j}} `{IsHProp P} (f : A -> P)
    : resized_Trm_rec@{i j k u} f o resized_trm == f.
  Proof.
    intro a.
    unfold resized_Trm_rec, resized_trm, Trm, trm; cbn beta.
    rewrite eisretr@{u k}.
    apply eisretr@{Set j}.
  Defined.

End TruncationWithFunext.
