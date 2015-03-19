(* -*- mode: coq; mode: visual-line -*- *)

(** * Homotopy coequalizers *)

Require Import HoTT.Basics UnivalenceImpliesFunext.
Require Import Types.Paths Types.Forall Types.Sigma Types.Arrow Types.Universe.
Local Open Scope path_scope.

Module Export Coeq.

  Private Inductive Coeq {B A : Type} (f g : B -> A) : Type :=
  | coeq : A -> Coeq f g.

  Arguments coeq {B A f g} a.

  Axiom cp : forall {B A f g} (b:B), @coeq B A f g (f b) = coeq (g b).

  Definition Coeq_ind {B A f g} (P : @Coeq B A f g -> Type)
             (coeq' : forall a, P (coeq a))
             (cp' : forall b, (cp b) # (coeq' (f b)) = coeq' (g b))
  : forall w, P w
    := fun w => match w with coeq a => fun _ => coeq' a end cp'.

  Axiom Coeq_ind_beta_cp
  : forall {B A f g} (P : @Coeq B A f g -> Type)
           (coeq' : forall a, P (coeq a))
           (cp' : forall b, (cp b) # (coeq' (f b)) = coeq' (g b)) (b:B),
      apD (Coeq_ind P coeq' cp') (cp b) = cp' b.

End Coeq.

Definition Coeq_rec {B A f g} (P : Type) (coeq' : A -> P)
  (cp' : forall b, coeq' (f b) = coeq' (g b))
  : @Coeq B A f g -> P
  := Coeq_ind (fun _ => P) coeq' (fun b => transport_const _ _ @ cp' b).

Definition Coeq_rec_beta_cp {B A f g} (P : Type) (coeq' : A -> P)
  (cp' : forall b:B, coeq' (f b) = coeq' (g b)) (b:B)
  : ap (Coeq_rec P coeq' cp') (cp b) = cp' b.
Proof.
  unfold Coeq_rec.
  (** Use [eapply] rather than [refine] so that we don't get evars as goals, and don't have to shelve any goals with [shelve_unifiable]. *)
  eapply (cancelL (transport_const (cp b) _)).
  refine ((apD_const (@Coeq_ind B A f g (fun _ => P) coeq' _) (cp b))^ @ _).
  refine (Coeq_ind_beta_cp (fun _ => P) _ _ _).
Defined.
