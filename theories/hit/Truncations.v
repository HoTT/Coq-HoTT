(* -*- mode: coq; mode: visual-line -*- *)

(** * Truncations of types, in all dimensions. *)

Require Import Basics types.Sigma HProp ReflectiveSubuniverse Modality.
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
Delimit Scope trunc_scope with trunc.

Private Inductive Truncation (n : trunc_index) (A :Type) : Type :=
  truncation_incl : A -> Truncation n A.
Bind Scope trunc_scope with Truncation.
Arguments truncation_incl {n A} a.
(** Make the priority 1, so that we don't override, e.g., [Unit]. *)
Instance istrunc_truncation : forall n A, IsTrunc n (Truncation n A) | 1.
Admitted.

Definition Truncation_rect {n A}
  (P : Truncation n A -> Type) `{forall aa, IsTrunc n (P aa)}
  : (forall a, P (truncation_incl a)) -> (forall aa, P aa)
:= (fun f aa => match aa with truncation_incl a => f a end).

End Truncation.

(** The non-dependent version of the eliminator. *)

Definition Truncation_rect_nondep {n A X} `{IsTrunc n X}
  : (A -> X) -> (Truncation n A -> X)
:= Truncation_rect (fun _ => X).

(** Truncation is a modality *)

Section TruncationModality.
  Context {fs : Funext}.
  Context (n : trunc_index).

  Local Instance truncation_modality : Modality.
  Proof.
    refine (Build_Modality
              (Build_UnitSubuniverse
                (fun A => hp (IsTrunc n A) _)
                (Truncation n)
                _
                (@truncation_incl n))
              _
              (@Truncation_rect n)
              (fun A B B_inO f a => 1)
              _); cbn; try exact _.
    intros A B ? f ?; cbn in *.
    apply trunc_equiv with f; exact _.
  Defined.

  Definition trunc_iff_isequiv_truncation (A : Type)
  : IsTrunc n A <~> IsEquiv (@truncation_incl n A)
  := inO_iff_isequiv_O_unit A.

  (** ** Functoriality *)

  Definition Truncation_functor {X Y} (f : X -> Y)
  : Truncation n X -> Truncation n Y
  := O_functor f.

  Definition Truncation_functor_compose {X Y Z} (f : X -> Y) (g : Y -> Z)
  : Truncation_functor (g o f) == Truncation_functor g o Truncation_functor f
  := ap10 (O_functor_compose f g).

  Definition Truncation_functor_idmap (X : Type)
  : @Truncation_functor X X idmap == idmap
  := ap10 (O_functor_idmap X).

  Definition isequiv_Truncation_functor {X Y} (f : X -> Y) `{IsEquiv _ _ f}
  : IsEquiv (Truncation_functor f)
  := isequiv_O_functor f.

  Definition equiv_Truncation_prod_cmp {X Y}
  : Truncation n (X * Y) <~> Truncation n X * Truncation n Y
  := equiv_O_prod_cmp X Y.

End TruncationModality.

(** This coercion allows us to use truncation indices where a modality is expected and refer to the corresponding truncation modality.  For instance, the general theory of O-connected maps specializes to the theory of n-connected maps. *)
(* Coercion truncation_modality : trunc_index >-> Modality. *)

(** It's sometimes convenient to use "infinity" to refer to the identity modality in a similar way.  This clashes with some uses in higher topos theory, where "oo-truncated" means instead "hypercomplete", but this has not yet been a big problem. *)
Notation oo := identity_modality.
