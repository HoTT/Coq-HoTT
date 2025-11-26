From HoTT Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.Span.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.

(* We require this now, but will import later. *)
Require Colimits.Pushout.

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
    srapply Build_Cocone.
    - intros [|[]]; [ exact (inr' o g) | exact inl' | exact inr' ].
    - intros [u|b] [u'|b'] []; cbn. destruct b'.
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

  (** We next define the eliminators [PO_ind] and [PO_rec]. To make later proof terms smaller, we define two things we'll need. *)
  Definition PO_ind_obj (P : PO f g -> Type) (l' : forall b, P (pol b))
    (r' : forall c, P (por c))
    : forall (i : span_graph) (x : obj (span f g) i), P (colim i x).
  Proof.
    intros [u|[]] x; cbn.
    - exact (@colimp _ (span f g) (inl u) (inr true) tt x # l' (f x)).
    - exact (l' x).
    - exact (r' x).
  Defined.

  Definition PO_ind_arr (P : PO f g -> Type) (l' : forall b, P (pol b))
    (r' : forall c, P (por c)) (pp' : forall a, popp a # l' (f a) = r' (g a))
    : forall (i j : span_graph) (e : span_graph i j) (ar : span f g i),
      transport P (colimp i j e ar) (PO_ind_obj P l' r' j (((span f g) _f e) ar)) =
        PO_ind_obj P l' r' i ar.
  Proof.
    intros [u|b] [u'|b'] []; cbn.
    destruct b'; cbn.
    1: reflexivity.
    unfold popp in pp'.
    intro a. apply moveR_transport_p.
    rhs_V napply transport_pp.
    destruct u.
    symmetry; apply pp'.
  Defined.

  Definition PO_ind (P : PO f g -> Type) (l' : forall b, P (pol b))
    (r' : forall c, P (por c)) (pp' : forall a, popp a # l' (f a) = r' (g a))
    : forall w, P w
    := Colimit_ind P (PO_ind_obj P l' r') (PO_ind_arr P l' r' pp').

  Definition PO_ind_beta_pp (P : PO f g -> Type) (l' : forall b, P (pol b))
    (r' : forall c, P (por c)) (pp' : forall a, popp a # l' (f a) = r' (g a))
    : forall x, apD (PO_ind P l' r' pp') (popp x) = pp' x.
  Proof.
    intro x.
    lhs napply apD_pp.
    rewrite (Colimit_ind_beta_colimp P _ _ (inl tt) (inr true) tt x).
    rewrite concat_p1, apD_V.
    rewrite (Colimit_ind_beta_colimp P _ _ (inl tt) (inr false) tt x).
    rewrite moveR_transport_p_V, moveR_moveL_transport_p.
    rewrite inv_pp, inv_V.
    apply concat_p_Vp.
  Defined.

  Definition PO_rec (P: Type) (l': B -> P) (r': C -> P)
    (pp': l' o f == r' o g) : PO f g -> P
    := Colimit_rec P (Build_span_cocone l' r' pp').

  Definition PO_rec_beta_pp (P: Type) (l': B -> P)
    (r': C -> P) (pp': l' o f == r' o g)
    : forall x, ap (PO_rec P l' r' pp') (popp x) = pp' x.
  Proof.
    intro x.
    unfold popp.
    refine (ap_pp _ _ _ @ _ @ concat_p1 _).
    refine (_ @@ _).
    1: exact (Colimit_rec_beta_colimp P (Build_span_cocone l' r' pp')
                (inl tt) (inr true) tt x).
    lhs napply ap_V.
    apply (inverse2 (q:=1)).
    exact (Colimit_rec_beta_colimp P (Build_span_cocone l' r' pp')
             (inl tt) (inr false) tt x).
  Defined.

  (** A nice property: the pushout of an equivalence is an equivalence. *)
  #[export] Instance PO_of_equiv (Hf : IsEquiv f)
    : IsEquiv por.
  Proof.
    srapply isequiv_adjointify.
    - srapply PO_rec.
      + exact (g o f^-1).
      + exact idmap.
      + intro x.
        apply ap, eissect.
    - srapply PO_ind; cbn.
      + intro.
        refine ((popp _)^ @ _).
        apply ap, eisretr.
      + reflexivity.
      + intro a; cbn.
        transport_paths FFlr.
        refine (concat_p1 _ @ _).
        rewrite PO_rec_beta_pp.
        rewrite eisadj.
        destruct (eissect f a); cbn.
        rewrite concat_p1.
        symmetry; apply concat_Vp.
    - cbn; reflexivity.
  Defined.

End PO.


(** ** Equivalence with [pushout] *)

Section is_PO_pushout.

  Import Colimits.Pushout.

  Context `{Funext} {A B C : Type} {f : A -> B} {g : A -> C}.

  Definition is_PO_pushout : is_PO f g (Pushout f g).
  Proof.
    srapply Build_IsColimit.
    - srapply Build_span_cocone.
      + exact (push o inl).
      + exact (push o inr).
      + exact pglue.
    - srapply Build_UniversalCocone.
      intro Y; srapply isequiv_adjointify.
      + intro Co.
        srapply Pushout_rec.
        * exact (pol' Co).
        * exact (por' Co).
        * exact (popp' Co).
      + intros [Co Co'].
        srapply path_cocone.
        * intros [[]|[]] x; simpl.
          1: apply (Co' (inl tt) (inr false) tt).
          all: reflexivity.
        * cbn beta.
          intros [u|b] [u'|b'] [] x.
          destruct u, b'; cbn.
          2: reflexivity.
          rhs napply concat_1p.
          lhs refine (_ @@ 1).
          1: napply Pushout_rec_beta_pglue.
          unfold popp', legs_comm.
          apply concat_pV_p.
      + intro h.
        apply path_forall.
        srapply Pushout_ind; cbn.
        1,2: reflexivity.
        intro a; cbn beta.
        transport_paths FlFr; apply equiv_p1_1q.
        unfold popp'; cbn.
        rhs_V napply concat_p1.
        napply Pushout_rec_beta_pglue.
  Defined.

  Definition equiv_pushout_PO : Pushout f g <~> PO f g.
  Proof.
    srapply colimit_unicity.
    3: eapply is_PO_pushout.
    eapply iscolimit_colimit.
  Defined.

  Definition equiv_pushout_PO_beta_pglue (a : A)
    : ap equiv_pushout_PO (pglue a) = popp a.
  Proof.
    cbn.
    refine (_ @ _).
    1: napply Pushout_rec_beta_pglue.
    unfold popp'; cbn.
    rewrite 2 concat_1p.
    reflexivity.
  Defined.

  Definition Pushout_rec_PO_rec (P : Type) (pushb : B -> P) (pushc : C -> P)
    (pusha : forall a : A, pushb (f a) = pushc (g a))
    : Pushout_rec P pushb pushc pusha == PO_rec P pushb pushc pusha o equiv_pushout_PO.
  Proof.
    snapply Pushout_ind.
    1, 2: reflexivity.
    intro a; cbn beta.
    transport_paths FlFr; apply equiv_p1_1q.
    lhs exact (Pushout_rec_beta_pglue P pushb pushc pusha a).
    symmetry.
    lhs napply (ap_compose equiv_pushout_PO _ (pglue a)).
    lhs napply (ap _ (equiv_pushout_PO_beta_pglue a)).
    napply PO_rec_beta_pp.
  Defined.

End is_PO_pushout.
