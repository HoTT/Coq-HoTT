(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics HoTT.Types.

Local Open Scope nat_scope.
Local Open Scope path_scope.

Generalizable Variables A B f.

(** * Relational equivalences *)

(** This definition is due to Peter LeFanu Lumsdaine on the HoTT mailing list.  This definition gives more judgmental properties, though has the downside of jumping universe levels. *)

Record RelEquiv A B :=
  { equiv_rel : A -> B -> Type;
    relequiv_contr_f : forall a, Contr { b : B & equiv_rel a b };
    relequiv_contr_g : forall b, Contr { a : A & equiv_rel a b } }.

Arguments equiv_rel {A B} _ _ _.
Global Existing Instance relequiv_contr_f.
Global Existing Instance relequiv_contr_g.

Definition issig_relequiv {A B}
  : { equiv_rel : A -> B -> Type
    | { f : forall a, Contr { b : B & equiv_rel a b }
      | forall b, Contr { a : A & equiv_rel a b } } }
      <~> RelEquiv A B.
Proof.
  issig.
Defined.

Definition relequiv_of_equiv {A B} (e : A <~> B) : RelEquiv A B.
Proof.
  refine {| equiv_rel a b := e a = b |}.
  (** The rest is found by typeclass inference! *)
Defined.

Definition equiv_of_relequiv {A B} (e : RelEquiv A B) : A <~> B.
Proof.
  refine (equiv_adjointify
            (fun a => (center { b : B & equiv_rel e a b}).1)
            (fun b => (center { a : A & equiv_rel e a b}).1)
            _ _);
    intro x; cbn.
  { refine (ap pr1 (contr _) : _.1 = (x; _).1).
    exact (center {a : A & equiv_rel e a x}).2. }
  { refine (ap pr1 (contr _) : _.1 = (x; _).1).
    exact (center {b : B & equiv_rel e x b}).2. }
Defined.

Definition RelIsEquiv {A B} (f : A -> B)
  := { r : RelEquiv A B | forall x, (center { b : B & equiv_rel r x b }).1 = f x }.

(** TODO: Prove [ishprop_relisequiv `{Funext} {A B} f : IsHProp (@RelIsEquiv A B f)] *)

(** * Judgmental property *)
Definition inverse_relequiv {A B} (e : RelEquiv A B) : RelEquiv B A
  := {| equiv_rel a b := equiv_rel e b a |}.

Definition reinv_V {A B} (e : RelEquiv A B)
  : inverse_relequiv (inverse_relequiv e) = e
  := 1.

(** TODO: Is there a definition of this that makes [inverse_relequiv (relequiv_idmap A)] be [relequiv_idmap A], judgmentally? *)
Definition relequiv_idmap A : RelEquiv A A
  := {| equiv_rel a b := a = b |}.

(** TODO: Define composition; we probably need truncation to do this? *)
