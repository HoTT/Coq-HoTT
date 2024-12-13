(** * Injectivity for Sigma types and examples of Injective Types which use this setup *)

(** Many proofs guided by original Agda formalization in the Type Topology Library which can be found at: https://martinescardo.github.io/TypeTopology/InjectiveTypes.Sigma and InjectiveTypes.MathematicalStructuresMoreGeneral. *)

Require Import Basics.
Require Import Types.Forall Types.Sigma Types.Universe.
Require Import Modalities.ReflectiveSubuniverse.
Require Import Truncations.Core.
Require Import InjectiveTypes.InjectiveTypes InjectiveTypes.TypeFamKanExt.

Section AlgFlabSigma.
  Context {X : Type} (A : X -> Type) (Xaf : IsAlgebraicFlabbyType X).

  (** The condition for a sigma type over an algebraically flabby type to be algebraically flabby can be described as the existence of a section to the following map for every [P] and [f]. *)
  Definition alg_flab_map (P : HProp) (f : P -> X)
    : (A (center_af f)) -> (forall h, A (f h))
    := fun a h => contr_af f h # a.

  (** Here is the condition.  (It would in fact be enough to assume that [s] is section up to homotopies in its domain.) *)
  Definition alg_flab_sigma_condition
    := forall P f, {s : _ & alg_flab_map P f o s == idmap}.

  (** A sigma type over an algebraically flabby type is also algebraically flabby, and thus algebraically injective, when the above condition holds. *)
  Definition alg_flab_sigma (cond : alg_flab_sigma_condition)
    : IsAlgebraicFlabbyType {x : X & A x}.
  Proof.
    snrapply Build_IsAlgebraicFlabbyType; intros P f.
    all: pose (C := cond P (pr1 o f)).
    - (* We need to give a point in [{x : X * A x}].  Since [X] is algebraically flabby, we get a point in [X]: *)
      exists (center_af (pr1 o f)).
      (* For the point in [A (above)], we use the section component of [cond P (pr1 o f)]: *)
      exact (C.1 (pr2 o f)).
    - intros h; cbn.
      change (cond P (fun x : P => (f x).1)) with C.
      (* We need to show that the point we gave is equal to [f h]. *)
      snrapply path_sigma; cbn.
      + nrapply contr_af.
      + exact (apD10 (C.2 (pr2 o f)) h).
  Defined.

  Definition alg_inj_sigma (cond : alg_flab_sigma_condition)
    : IsAlgebraicInjectiveType {x : X & A x}
    := alg_inj_alg_flab (alg_flab_sigma cond).

End AlgFlabSigma.

(** Taking our algebraically flabby type [X] to be [Type], we introduce our primary examples (the types of pointed types, monoids, etc.), and give a few simplifying lemmas. *)
Section AlgFlabUniverse.
  (** [T] is a version of transport in the type family [A].  It could be defined to be transport combined with univalence, but we allow the user to choose different "implementations" of transport that might be more convenient. *)
  Context (A : Type -> Type) (T : forall {X Y}, X <~> Y -> A X -> A Y)
    (Trefl : forall X, (T (equiv_idmap X) == idmap)).
  Arguments T {X Y} _ _. (* This is needed, despite the braces above. *)

  (** When studying the sigma type [{X : Type & A X}], the map [alg_flab_map] can be exchanged for either of these simpler maps.  This first one will turn out to be homotopic to [alg_flab_map] when [Type] is given its "forall" flabiness structure. *)
  Definition alg_flab_map_forall `{Funext}
    (P : HProp) (f : P -> Type)
    : A (forall h, f h) -> (forall h, A (f h)).
  Proof.
    intros a h.
    srefine (T _ a).
    apply (@equiv_contr_forall _ _ (contr_inhabited_hprop _ _)).
  Defined.

  (** And this one is homotopic to [alg_flab_map] when [Type] is given its "sigma" flabiness structure. *)
  Definition alg_flab_map_sigma
    (P : HProp) (f : P -> Type)
    : A {h : P & f h} -> (forall h, A (f h)).
  Proof.
    intros a h.
    srefine (T _ a).
    apply (@equiv_contr_sigma _ _ (contr_inhabited_hprop _ _)).
  Defined.

  (** The following conditions can be thought of as closure conditions under pi or sigma types for the type family [A]. *)
  Definition alg_flab_sigma_condition_forall `{Funext}
    := forall P f, {s : _ & alg_flab_map_forall P f o s == idmap}.

  Definition alg_flab_sigma_condition_sigma
    := forall P f, {s : _ & alg_flab_map_sigma P f o s == idmap}.

  Definition homotopic_alg_flab_map_alg_flab_map_forall `{Univalence}
    (P : HProp) (f : P -> Type)
    : alg_flab_map_forall P f == alg_flab_map A alg_flab_Type_forall P f.
  Proof.
    intros a. funext h.
    srefine (homotopic_trequiv A (@T) (@univalent_transport H A) Trefl _ _ a).
    apply univalent_transport_idequiv.
  Defined.

  Definition homotopic_alg_flab_map_alg_flab_map_sigma `{Univalence}
    (P : HProp) (f : P -> Type)
    : alg_flab_map_sigma P f == alg_flab_map A alg_flab_Type_sigma P f.
  Proof.
    intros s. funext h.
    srefine (homotopic_trequiv A (@T) (@univalent_transport H A) Trefl _ _ s).
    apply univalent_transport_idequiv.
  Defined.

  (** The original [sigma_condition] is implied by our reformulated conditions [alg_flab_sigma_condition_forall] and [alg_flab_sigma_condition_sigma]. *)
  Definition sigma_condition_sigma_condition_forall `{Univalence}
    (condf : alg_flab_sigma_condition_forall)
    : alg_flab_sigma_condition A _.
  Proof.
    intros P f.
    destruct (condf _ f) as [s J].
    exists s.
    intro g.
    lhs_V nrapply (homotopic_alg_flab_map_alg_flab_map_forall P f (s g)).
    apply J.
  Defined.

  Definition alg_flab_sigma_forall `{Univalence} (condf : alg_flab_sigma_condition_forall)
    : IsAlgebraicFlabbyType {X : Type & A X}.
  Proof.
    nrapply alg_flab_sigma.
    exact (sigma_condition_sigma_condition_forall condf).
  Defined.

  Definition sigma_condition_sigma_condition_sigma `{Univalence}
    (condf : alg_flab_sigma_condition_sigma)
    : alg_flab_sigma_condition A alg_flab_Type_sigma.
  Proof.
    intros P f.
    destruct (condf _ f) as [s J].
    exists s.
    intro g.
    lhs_V nrapply (homotopic_alg_flab_map_alg_flab_map_sigma P f (s g)).
    apply J.
  Defined.

  Definition alg_flab_sigma_sigma `{Univalence} (conds : alg_flab_sigma_condition_sigma)
    : IsAlgebraicFlabbyType {X : Type & A X}.
  Proof.
    nrapply alg_flab_sigma.
    exact (sigma_condition_sigma_condition_sigma conds).
  Defined.

End AlgFlabUniverse.

(** The type of pointed types is algebraically flabby. *)
Definition alg_flab_pType `{Univalence}
  : IsAlgebraicFlabbyType {X : Type & X}.
Proof.
  rapply (alg_flab_sigma_forall _ (@equiv_fun)).
  - reflexivity.
  - intros P f.
    exists idmap.
    reflexivity.
Defined.

(** The following results are adapted from section 7 of Injective Types in Univalent Mathematics by Martin Escardo, using the above results. *)

(** For a subuniverse, the flabbiness condition is equivalent to closure under proposition indexed pi types (or sigma types), so using this we can state a simpler theorem for proving flabbiness of subuniverses. *)
Definition alg_flab_subuniverse_forall `{Univalence} (O : Subuniverse)
  (condForall : forall (P : HProp) A, (forall h : P, In O (A h)) -> In O (forall h : P, A h))
  : IsAlgebraicFlabbyType@{u su} (Type_ O).
Proof.
  rapply (alg_flab_sigma_forall _ (fun X Y f H => @inO_equiv_inO' O X Y H f)).
  - intros X A. apply path_ishprop.
  - intros P A.
    exists _.
    intros s. apply path_ishprop.
Defined.

Definition alg_flab_subuniverse_sigma `{Univalence} (O : Subuniverse)
  (condSigma : forall (P : HProp) A, (forall h : P, In O (A h)) -> In O {h : P & A h})
  : IsAlgebraicFlabbyType@{u su} (Type_ O).
Proof.
  rapply (alg_flab_sigma_sigma _ (fun X Y f H => @inO_equiv_inO' O X Y H f)).
  - intros X A. apply path_ishprop.
  - intros P A.
    exists _.
    intros s. apply path_ishprop.
Defined.

(** As an immediate corollary, we get that reflective subuniverses are algebraically flabby. *)
Definition alg_flab_reflective_subuniverse `{Univalence} (O : ReflectiveSubuniverse)
  : IsAlgebraicFlabbyType@{u su} (Type_ O)
  := alg_flab_subuniverse_forall _ _.
