Require Import Basics.
Require Import Types.
Require Import Diagrams.Span.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.

(* We require this now, but will import later. *)
Require HIT.Pushout.

Local Open Scope path_scope.

(** * Pushout as a colimit *)

(** In this file, we define [PO] the pushout of two maps as the colimit of a particular diagram, and then show that it is equivalent to [pushout] the primitive pushout defined as an HIT. *)


(** ** [PO] *)
Section PO.

  Context {A B C : Type}.

  Definition Build_span_cocone {f : A -> B} {g : A -> C} {Z : Type}
             (inl' : B -> Z) (inr' : C -> Z)
             (pp' : inl' o f == inr' o g)
    : Cocone (span f g) Z.
  Proof.
    serapply Build_Cocone.
    - intros [|[]]; [ exact (inr' o g) | exact inl' | exact inr' ].
    - intros [] [] []; cbn. destruct b.
      + exact pp'.
      + reflexivity.
  Defined.


  Definition pol' {f : A -> B} {g : A -> C} {Z} (Co : Cocone (span f g) Z)
    : B -> Z
    := legs Co (inr true).
  Definition por' {f : A -> B} {g : A -> C} {Z} (Co : Cocone (span f g) Z)
    : C -> Z
    := legs Co (inr false).
  Definition popp' {f : A -> B} {g : A -> C} {Z} (Co : Cocone (span f g) Z)
    : pol' Co o f == por' Co o g
    := fun x => legs_comm Co (inl tt) (inr true) tt x
                @ (legs_comm Co (inl tt) (inr false) tt x)^.

  Definition is_PO (f : A -> B) (g : A -> C) := IsColimit (span f g).
  Definition PO (f : A -> B) (g : A -> C) := Colimit (span f g).

  Context {f : A -> B} {g : A -> C}.

  Definition pol : B -> PO f g := colim (D:=span f g) (inr true).
  Definition por : C -> PO f g := colim (D:=span f g) (inr false).

  Definition popp (a : A) : pol (f a) = por (g a)
    := colimp (D:=span f g) (inl tt) (inr true) tt a
          @ (colimp (D:=span f g) (inl tt) (inr false) tt a)^.

  (** The eliminators [PO_ind], [PO_rec], ... can be proven. *)
  Definition PO_ind (P : PO f g -> Type) (l' : forall b, P (pol b))
    (r' : forall c, P (por c)) (pp' : forall a, popp a # l' (f a) = r' (g a))
    : forall w, P w.
  Proof.
    serapply Colimit_ind.
    - intros [[]|[]] x; cbn.
      + exact (@colimp _ (span f g) (inl tt) (inr true) tt x # l' (f x)).
      + exact (l' x).
      + exact (r' x).
    - intros [] [] []; cbn.
      destruct u, b; cbn.
      1: reflexivity.
      unfold popp in pp'.
      intro a. apply moveR_transport_p.
      etransitivity; [|apply transport_pp].
      symmetry; apply pp'.
  Defined.

  Definition PO_ind_beta_pp (P : PO f g -> Type) (l' : forall b, P (pol b))
    (r' : forall c, P (por c)) (pp' : forall a, popp a # l' (f a) = r' (g a))
    : forall x, apD (PO_ind P l' r' pp') (popp x) = pp' x.
  Proof.
    intro x.
    etransitivity.
    1: eapply apD_pp.
    assert (apD (PO_ind P l' r' pp')
      (@colimp _ (span f g) (inl tt) (inr true) tt x) = 1).
    { unfold PO_ind.
      match goal with
      | |- apD (Colimit_ind P ?qq1 ?qq2) _ = _ =>
        exact (Colimit_ind_beta_colimp P qq1 qq2 (inl tt) (inr true) tt x)
      end. }
    rewrite X; clear X; cbn.
    rewrite concat_p1, apD_V.
    unfold PO_ind.
    match goal with
    | |- _ @ moveR_transport_V
          _ _ _ _ (apD (Colimit_ind P ?qq1 ?qq2) _)^ = _ =>
      rewrite (Colimit_ind_beta_colimp P qq1 qq2 (inl tt) (inr false) tt x); cbn
    end.
    match goal with
    | |- ?pp @ moveR_transport_V P _ _ _ (moveR_transport_p P _ _ _ ?qq)^ = _
      => set (q := qq); set (p := pp) in *
    end.
    rewrite moveR_transport_p_V, moveR_moveL_transport_p.
    subst q.
    rewrite inv_pp.
    hott_simpl.
  Defined.

  Definition PO_rec (P: Type) (l': B -> P) (r': C -> P)
    (pp': l' o f == r' o g) : PO f g -> P
    := Colimit_rec P (Build_span_cocone l' r' pp').

  Definition PO_rec_beta_pp (P: Type) (l': B -> P)
    (r': C -> P) (pp': l' o f == r' o g)
    : forall x, ap (PO_rec P l' r' pp') (popp x) = pp' x.
  Proof.
    intro x.
    pose (X := Colimit_rec_beta_colimp P (Build_span_cocone l' r' pp')
                                    (inl tt) (inr true) tt x).
    pose (X0 := Colimit_rec_beta_colimp P (Build_span_cocone l' r' pp')
                                    (inl tt) (inr false) tt x).
    unfold popp; cbn in *.
    refine (ap_pp _ _ _ @ _ @ concat_p1 _).
    refine (X @@ _).
    refine (_ @ inverse2 X0).
    exact (ap_V _ _).
  Defined.

  (** A nice property: the pushout of an equivalence is an equivalence. *)
  Global Instance PO_of_equiv (Hf : IsEquiv f)
    : IsEquiv por.
  Proof.
    serapply isequiv_adjointify.
    - serapply PO_rec.
      + exact (g o f^-1).
      + exact idmap.
      + intro x.
        apply ap, eissect.
    - serapply PO_ind; cbn.
      + intro.
        refine ((popp _)^ @ _).
        apply ap, eisretr.
      + reflexivity.
      + intro a; cbn.
        rewrite transport_paths_FlFr, ap_idmap.
        rewrite ap_compose, PO_rec_beta_pp.
        rewrite eisadj.
        destruct (eissect f a); cbn.
        rewrite concat_1p, concat_p1.
        apply concat_Vp.
    - cbn; reflexivity.
  Defined.

End PO.


(** ** Equivalence with [pushout] *)

Section is_PO_pushout.

  Import HIT.Pushout.

  Context `{Funext} {A B C : Type} {f : A -> B} {g : A -> C}.

  Definition is_PO_pushout : is_PO f g (pushout f g).
  Proof.
    serapply Build_IsColimit.
    - serapply Build_span_cocone.
      + exact (push o inl).
      + exact (push o inr).
      + exact pp.
    - serapply Build_UniversalCocone.
      intro Y; serapply isequiv_adjointify.
      + intro Co.
        serapply pushout_rec.
        * exact (pol' Co).
        * exact (por' Co).
        * exact (popp' Co).
      + intros [Co Co'].
        serapply path_cocone; cbn.
        * intros [[]|[]] x; simpl.
          1: apply (Co' (inl tt) (inr false) tt).
          all: reflexivity.
        * intros [[]|[]] [[]|[]] [] x; simpl.
          2: reflexivity.
          refine (_ @ (concat_1p _)^).
          rewrite pushout_rec_beta_pp.
          hott_simpl.
      + intro h.
        apply path_forall.
        serapply pushout_ind; cbn.
        1,2: reflexivity.
        intro a; cbn.
        rewrite transport_paths_FlFr, concat_p1.
        rewrite pushout_rec_beta_pp.
        eapply moveR_Vp.
        unfold popp'.
        by rewrite 2 concat_p1.
  Defined.

  Definition equiv_pushout_PO : pushout f g <~> PO f g.
  Proof.
    serapply colimit_unicity.
    3: eapply is_PO_pushout.
    eapply iscolimit_colimit.
  Defined.

End is_PO_pushout.
