Require Import Paths Fibrations Contractible Equivalences.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** Every path between spaces gives an equivalence. *)

Definition path_to_equiv {U V} : (U == V) -> (U <~> V).
Proof.
  intros U V.
  path_induction.
  apply idequiv.
Defined.

(** This is functorial in the appropriate sense. *)

Lemma path_to_equiv_map {A} (P : A -> Type) (x y : A) (p : x == y) :
  projT1 (path_to_equiv (map P p)) == transport (P := P) p.
Proof.
  path_induction.
Defined.

Lemma concat_to_compose {A B C} (p : A == B) (q : B == C) :
  path_to_equiv q o path_to_equiv p == projT1 (path_to_equiv (p @ q)).
Proof.
  path_induction.
Defined.

Ltac undo_concat_to_compose_in s :=
  match s with  
    | context cxt [ equiv_coerce_to_function _ _ (path_to_equiv ?p) o equiv_coerce_to_function _ _ (path_to_equiv ?q) ] =>
      let mid := context cxt [ equiv_coerce_to_function _ _ (path_to_equiv (q @ p)) ] in
        path_via mid;
        [ repeat first [ apply happly | apply map | apply concat_to_compose ] | ] 
  end.

Ltac undo_concat_to_compose :=
  repeat progress (
    match goal with
      | |- ?s == ?t =>
        first [ undo_concat_to_compose_in s | undo_concat_to_compose_in t ]
    end
  ).

Lemma opposite_to_inverse {A B} (p : A == B) :
  (path_to_equiv p)^-1 == path_to_equiv (!p).
Proof.
  path_induction.
Defined.

Ltac undo_opposite_to_inverse_in s :=
  match s with  
    | context cxt [ (path_to_equiv ?p) ^-1 ] =>
      let mid := context cxt [ equiv_coerce_to_function _ _ (path_to_equiv (! p)) ] in
        path_via mid;
        [ repeat apply map; apply opposite_to_inverse | ]
  end.

Ltac undo_opposite_to_inverse :=
  repeat progress (
    match goal with
      | |- ?s == ?t =>
        first [ undo_opposite_to_inverse_in s | undo_opposite_to_inverse_in t ]
    end
  ).

(** The statement of the univalence axiom. *)

Definition univalence_statement := forall (U V : Type), is_equiv (@path_to_equiv U V).

Section Univalence.

  Hypothesis univalence : univalence_statement.

  Definition path_to_equiv_equiv (U V : Type) := (@path_to_equiv U V ; univalence U V).

  (** Assuming univalence, every equivalence yields a path. *)

  Definition equiv_to_path {U V} : U <~> V -> U == V :=
    inverse (path_to_equiv_equiv U V).

  (** The map [equiv_to_path] is a section of [path_to_equiv]. *)

  Definition equiv_to_path_section U V :
    forall (w : U <~> V), path_to_equiv (equiv_to_path w) == w :=
    inverse_is_section (path_to_equiv_equiv U V).

  Definition equiv_to_path_retraction U V :
    forall (p : U == V), equiv_to_path (path_to_equiv p) == p :=
    inverse_is_retraction (path_to_equiv_equiv U V).

  Definition equiv_to_path_triangle U V : forall (p : U == V),
      map path_to_equiv (equiv_to_path_retraction U V p) == equiv_to_path_section U V (path_to_equiv p) :=
    inverse_triangle (path_to_equiv_equiv U V).

  (** We can do better than [equiv_to_path]: we can turn a fibration
     fibered over equivalences to one fiberered over paths. *)

  Definition pred_equiv_to_path U V : (U <~> V -> Type) -> (U == V -> Type).
  Proof.
    intros U V.
    intros Q p.
    apply Q.
    apply path_to_equiv.
    exact p.
  Defined.

  (** The following theorem is of central importance. Just like there
     is an induction principle for paths, there is a corresponding one
     for equivalences. In the proof we use [pred_equiv_to_path] to
     transport the predicate [P] of equivalences to a predicate [P']
     on paths. Then we use path induction and transport back to [P]. *)

  Theorem equiv_induction (P : forall U V, U <~> V -> Type) :
    (forall T, P T T (idequiv T)) -> (forall U V (w : U <~> V), P U V w).
  Proof.
    intros P.
    intro r.
    pose (P' := (fun U V => pred_equiv_to_path U V (P U V))).
    assert (r' : forall T : Type, P' T T (idpath T)).
    intro T.
    exact (r T).
    intros U V w.
    apply (transport (equiv_to_path_section _ _ w)).
    exact (paths_rect _ P' r' U V (equiv_to_path w)).
  Defined.

End Univalence.
