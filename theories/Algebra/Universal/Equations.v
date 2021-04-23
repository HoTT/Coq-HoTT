(** This file introduces formal equations [Equations], interpretation of equations [InterpEquations], and model of equational theory [IsEquationalModel]. *)

Require Export
  HoTT.Algebra.Universal.Algebra
  HoTT.Algebra.Universal.TermAlgebra.

Unset Elimination Schemes.

Local Open Scope Algebra_scope.

(** A formal σ-equation [Equation], for [σ : Signature], consists of a context set [context_equation] and two terms [left_equation] and [right_equations], both of some sort [sort_equation]. This can be written as
<<
  Γ ⊢ ℓ ≈ r
>>
where [Γ] is the context set and [ℓ], [r], the terms. *)

Record Equation {σ : Signature} : Type :=
  Build_Equation
  { context_equation : Carriers σ
  ; hset_context_equation : forall s, IsHSet (context_equation s)
  ; sort_equation : Sort σ
  ; left_equation : CarriersTermAlgebra context_equation sort_equation
  ; right_equation : CarriersTermAlgebra context_equation sort_equation }.

Global Arguments Equation : clear implicits.

Global Arguments Build_Equation
  {σ} context_equation {hset_context_equation}.

Global Existing Instance hset_context_equation.

(** A collection of σ-equations indexed by [I]: *)

Record Equations (σ : Signature) (I : Type) : Type
  := Build_Equations { equations : I -> Equation σ }.

Arguments equations {σ} {I}.

Global Coercion equations : Equations >-> Funclass.

(** Note: the type [{σ : Signature | {I : Type | Equations σ I}}] is commonly referred to as equational theory or algebraic theory.

For example the theory of monoids is an algebraic theory. Here [σ] is a one sorted signature with a nullary operation symbol [u] and a binary operation symbol [m]. The index type [I] is [Fin 3], and the three equations are
<<
  {x} ⊢ m (u, x) ≈ x
  {x} ⊢ m (x, u) ≈ x
  {x,y,z} ⊢ m (m (x, y), z) ≈ m (x, m (y, z))
>>
We are abusing notation in the above equations by writing [m] in the equations rather than [ops_term_algebra {x,y,z} m], and [x] rather than [var_term_algebra {x,y,z} _ x], etc. *)

Section InterpEquations.
  Context {σ} (A : Algebra σ).

(** The interpretation of a σ-equation [Γ ⊢ ℓ ≈ r] in [A] is a type
<<
  forall (f : forall s, Γ s -> A s), t f ℓ = t f r
>>
where
<<
  t : (forall s, Γ s -> A s) -> forall {s}, CarriersTermAlgebra Γ s -> A s
>>
returns the canonical homomorphism out of the term algebra, interpreting the terms [ℓ] and [r]. *)

  Definition InterpEquation (e : Equation σ) : Type
    := forall (f : forall s, context_equation e s -> A s),
       map_term_algebra A f (sort_equation e) (left_equation e)
       = map_term_algebra A f (sort_equation e) (right_equation e).

(** The interpretation of a collection of σ-equations: *)

  Definition InterpEquations {I : Type} (e : Equations σ I)
    := forall (i:I), InterpEquation (e i).

End InterpEquations.

(** An algebra [A] for signature [σ] is a model of the equational theory [e : Equations σ I] if the interpretation of the equations [InterpEquations A e] holds. *)

Class IsEquationalModel {σ : Signature}
  (A : Algebra σ) {I : Type} (e : Equations σ I)
  := equations_model : InterpEquations A e.

