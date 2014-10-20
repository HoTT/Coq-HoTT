(* -*- mode: coq; mode: visual-line -*- *)

(** * Truncations of types, in all dimensions. *)

Require Import HoTT.Basics Types.Sigma ReflectiveSubuniverse Modality TruncType.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A X n.

(** ** Definition. *)

(** The definition of [Trunc n], the n-truncation of a type.

If Coq supported higher inductive types natively, we would construct this as somthing like:

   Inductive Trunc n (A : Type) : Type :=
   | tr : A -> Trunc n A
   | istrunc_truncation : forall (f : Sphere n.+1 -> Trunc n A)
       (x : Sphere n.+1), f x = f North.

However, while we are faking our higher-inductives anyway, we can take some shortcuts, rather than translating the definition above.  Firstly, we directly posit a “constructor” giving truncatedness, rather than rephrasing it in terms of maps of spheres.  Secondly, we omit the “computation rule” for this constructor, since it is implied by truncatedness of the result type (and, for essentially that reason, is never wanted in practice anyway).
*)

Module Export Trunc.
Delimit Scope trunc_scope with trunc.

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A -> Trunc n A.
Bind Scope trunc_scope with Trunc.
Arguments tr {n A} a.
(** Make the priority 1, so that we don't override, e.g., [Unit]. *)
Global Instance istrunc_truncation : forall n A, IsTrunc n (Trunc n A) | 1.
Admitted.

Definition Trunc_ind {n A}
  (P : Trunc n A -> Type) {Pt : forall aa, IsTrunc n (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => fun _ => f a end Pt).

End Trunc.

(** The non-dependent version of the eliminator. *)

Definition Trunc_rec {n A X} `{IsTrunc n X}
  : (A -> X) -> (Trunc n A -> X)
:= Trunc_ind (fun _ => X).

(** Trunc is a modality *)

Section TruncationModality.
  Context (n : trunc_index).

  Local Instance truncation_modality : Modality.
  Proof.
    refine (Build_Modality
              (Build_UnitSubuniverse
                (fun A => IsTrunc n A)
                (Trunc n)
                _
                (@tr n)
                _)
              _
              (@Trunc_ind n)
              (fun A B B_inO f a => 1)
              _); cbn; try exact _.
    intros A B ? f ?; cbn in *.
    refine (trunc_equiv _ f); exact _.
  Defined.

  Definition trunc_iff_isequiv_truncation (A : Type)
  : IsTrunc n A <-> IsEquiv (@tr n A)
  := inO_iff_isequiv_O_unit A.

  Global Instance isequiv_tr A `{IsTrunc n A} : IsEquiv (@tr n A)
  := fst (trunc_iff_isequiv_truncation A) _.

  Definition equiv_tr (A : Type) `{IsTrunc n A}
  : A <~> Trunc n A
  := BuildEquiv _ _ (@tr n A) _.

  Definition untrunc_istrunc {A : Type} `{IsTrunc n A}
  : Trunc n A -> A
  := (@tr n A)^-1.

  (** ** Functoriality *)

  Definition Trunc_functor {X Y} (f : X -> Y)
  : Trunc n X -> Trunc n Y
  := Trunc_rec (tr o f).

  Definition Trunc_functor_compose {X Y Z} (f : X -> Y) (g : Y -> Z)
  : Trunc_functor (g o f) == Trunc_functor g o Trunc_functor f
  := O_functor_compose f g.

  Definition Trunc_functor_idmap (X : Type)
  : @Trunc_functor X X idmap == idmap
  := O_functor_idmap X.

  Definition isequiv_Trunc_functor {X Y} (f : X -> Y) `{IsEquiv _ _ f}
  : IsEquiv (Trunc_functor f)
  := isequiv_O_functor f.

  Definition equiv_Trunc_prod_cmp `{Funext} {X Y}
  : Trunc n (X * Y) <~> Trunc n X * Trunc n Y
  := equiv_O_prod_cmp X Y.

End TruncationModality.

(** This coercion allows us to use truncation indices where a modality is expected and refer to the corresponding truncation modality.  For instance, the general theory of O-connected maps specializes to the theory of n-connected maps. *)
Coercion truncation_modality : trunc_index >-> Modality.

(** It's sometimes convenient to use "infinity" to refer to the identity modality in a similar way.  This clashes with some uses in higher topos theory, where "oo-truncated" means instead "hypercomplete", but this has not yet been a big problem. *)
Notation oo := identity_modality.

(** ** A few special things about the (-1)-truncation. *)

Definition merely A : hProp := BuildhProp (Trunc -1 A).

Definition hexists {X} (P : X -> Type) : hProp := merely (sigT P).

Definition hor (P Q : Type) : hProp := merely (P + Q).

(** ** Tactic to remove truncations in hypotheses if possible. *)
Ltac strip_truncations :=
  (** search for truncated hypotheses *)
  progress repeat match goal with
                    | [ T : _ |- _ ]
                      => revert T;
                        refine (@Trunc_ind _ _ _ _ _);
                        (** ensure that we didn't generate more than one subgoal, i.e. that the goal was appropriately truncated *)
                        [];
                        intro T
                  end.
