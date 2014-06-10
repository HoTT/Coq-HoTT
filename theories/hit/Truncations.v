(* -*- mode: coq; mode: visual-line -*- *)

(** * Truncations of types, in all dimensions. *)

Require Import Overture PathGroupoids Equivalences Trunc types.Sigma.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A X n.

(** ** Definition. *)

(** The definition of [Trunc n], the n-truncation of a type.

If Coq supported higher inductive types natively, we would construct this as somthing like:

   Inductive Truncation n (A : Type) : Type :=
   | truncation_incl : A -> Truncation n A
   | istrunc_truncation : forall (f : Sphere (trunc_S n) -> Truncation n A)
       (x : Sphere (trunc_S n)), f x = f North.

However, while we are faking our higher-inductives anyway, we can take some shortcuts, rather than translating the definition above.  Firstly, we directly posit a “constructor” giving truncatedness, rather than rephrasing it in terms of maps of spheres.  Secondly, we omit the “computation rule” for this constructor, since it is implied by truncatedness of the result type (and, for essentially that reason, is never wanted in practice anyway).
*)

Module Export Truncation.

Private Inductive Truncation (n : trunc_index) (A :Type) : Type :=
  truncation_incl : A -> Truncation n A.
Arguments truncation_incl {n A} a.
Axiom istrunc_truncation : forall n A, IsTrunc n (Truncation n A).
Global Existing Instance istrunc_truncation.

Definition Truncation_rect {n A}
  (P : Truncation n A -> Type) `{forall aa, IsTrunc n (P aa)}
  : (forall a, P (truncation_incl a)) -> (forall aa, P aa)
:= (fun f aa => match aa with truncation_incl a => f a end).

End Truncation.

(** The non-dependent version of the eliminator. *)

Definition Truncation_rect_nondep {n A X} `{IsTrunc n X}
  : (A -> X) -> (Truncation n A -> X)
:= Truncation_rect (fun _ => X).

(** ** Functoriality *)
Definition functor_Truncation {n : trunc_index} {X Y} (f : X -> Y)
  : Truncation n X -> Truncation n Y.
Proof.
  apply Truncation_rect_nondep. exact (fun x => truncation_incl (f x)).
Defined.

Definition functor_Truncation_idmap `{Funext} {n : trunc_index} (X : Type)
  : @functor_Truncation n X X idmap == idmap.
Proof.
  unfold pointwise_paths. apply @Truncation_rect.
    intros ?; apply trunc_succ.
  intros a; exact 1.
Defined.

Definition isequiv_functor_Truncation {n : trunc_index} {X Y} (f : X -> Y)
  `{IsEquiv _ _ f} : IsEquiv (functor_Truncation (n:=n) f).
Proof.
  refine (isequiv_adjointify _ (functor_Truncation (f ^-1)) _ _);
    unfold Sect; apply @Truncation_rect;
    try (intros ?; apply trunc_succ).
  intros y; simpl. apply ap, eisretr.
  intros x; simpl. apply ap, eissect.
Defined.
