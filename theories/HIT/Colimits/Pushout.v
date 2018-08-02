Require Import HoTT.Basics HoTT.Types HIT.Pushout.
Require Import Colimits.Diagram Colimits.Colimit.
Local Open Scope path_scope.

(** * Pushout as a colimit *)

(** In this file, we define [PO] the pushout of two maps as the colimit of a particuliar diagram, and then show that it is equivalent to [pushout] the primitive pushout defined as an HIT. *)


(** ** [PO] *)

(** The shape of a pushout diagram. *)

Definition PO_graph : graph.
Proof.
  simple refine (Build_graph _ _).
  - exact (Unit + Bool).
  - intros [i|i] [j|j]. exact Empty. exact Unit. exact Empty. exact Empty.
Defined.

Section PO.
  Context {A B C : Type}.

  (** The pushout diagram of two maps is called a span. *)

  Definition span (f : A -> B) (g : A -> C) : diagram PO_graph.
  Proof.
    simple refine (Build_diagram _ _ _).
    - intros [i|i]. exact A. exact (if i then B else C).
    - intros [i|i] [j|j] u; cbn; try contradiction.
      destruct j. exact f. exact g.
  Defined.

  Definition Build_span_cocone {f : A -> B} {g : A -> C} {Z : Type}
             (inl' : B -> Z) (inr' : C -> Z)
             (pp' : inl' o f == inr' o g)
    : cocone (span f g) Z.
  Proof.
    unshelve econstructor.
    - intros []; cbn. intros _. exact (inr' o g).
      intros []. exact inl'. exact inr'.
    - intros [] [] []; cbn. destruct b.
      exact pp'. reflexivity.
  Defined.

  Definition pol' {f : A -> B} {g : A -> C} {Z} (Co : cocone (span f g) Z)
    : B -> Z
    := q Co (inr true).
  Definition por' {f : A -> B} {g : A -> C} {Z} (Co : cocone (span f g) Z)
    : C -> Z
    := q Co (inr false).
  Definition popp' {f : A -> B} {g : A -> C} {Z} (Co : cocone (span f g) Z)
    : pol' Co o f == por' Co o g
    := fun x => qq Co (inl tt) (inr true) tt x
                @ (qq Co (inl tt) (inr false) tt x)^.



  Definition is_PO (f : A -> B) (g : A -> C) := is_colimit (span f g).
  Definition PO (f : A -> B) (g : A -> C) := colimit (span f g).

  Context {f : A -> B} {g : A -> C}.

  Definition pol : B -> PO f g := colim (D:=span f g) (inr true).
  Definition por : C -> PO f g := colim (D:=span f g) (inr false).

  Definition popp (a : A) : pol (f a) = por (g a)
    := colimp (D:=span f g) (inl tt) (inr true) tt a
          @ (colimp (D:=span f g) (inl tt) (inr false) tt a)^.

  (** The eliminators [PO_ind], [PO_rec], ... can be proven. *)
  Definition PO_ind (P : PO f g -> Type) (l' : forall b, P (pol b))
             (r' : forall c, P (por c))
             (pp' : forall a, popp a # l' (f a) = r' (g a))
    : forall w, P w.
  Proof.
    simple refine (colimit_ind P _ _).
    - intros []; cbn.
      intros [] x.
      exact (@colimp _ (span f g) (inl tt) (inr true) tt x # l' (f x)).
      intros []; cbn. exact l'. exact r'.
    - intros [] [] []; cbn.
      destruct u, b; cbn. reflexivity.
      unfold popp in pp'.
      intro a. apply moveR_transport_p.
      etransitivity; [|apply transport_pp].
      symmetry; apply pp'.
  Defined.

  Definition PO_ind_beta_pp (P : PO f g -> Type) (l' : forall b, P (pol b))
             (r' : forall c, P (por c))
             (pp' : forall a, popp a # l' (f a) = r' (g a))
    : forall x, apD (PO_ind P l' r' pp') (popp x) = pp' x.
  Proof.
    intro x. etransitivity. eapply apD_pp.
    assert (apD (PO_ind P l' r' pp')
                (@colimp _ (span f g) (inl tt) (inr true) tt x) = 1). {
      unfold PO_ind.
      match goal with
      | |- apD (colimit_ind P ?qq1 ?qq2) _ = _ =>
        exact (colimit_ind_beta_colimp P qq1 qq2 (inl tt) (inr true) tt x)
      end. }
    rewrite X. clear X. cbn. rewrite concat_p1.
    rewrite apD_V. unfold PO_ind.
    match goal with
    | |- _ @ moveR_transport_V
          _ _ _ _ (apD (colimit_ind P ?qq1 ?qq2) _)^ = _ =>
        rewrite (colimit_ind_beta_colimp P qq1 qq2 (inl tt) (inr false) tt x); cbn
    end.
    match goal with
    | |- ?pp @ moveR_transport_V P _ _ _ (moveR_transport_p P _ _ _ ?qq)^ = _
      => set (q := qq); set (p := pp) in *
    end.
    rewrite moveR_transport_p_V. rewrite moveR_moveL_transport_p.
    subst q. rewrite inv_pp. hott_simpl.
  Defined.

  Definition PO_rec (P: Type) (l': B -> P) (r': C -> P)
             (pp': l' o f == r' o g)
    : PO f g -> P
    := colimit_rec P (Build_span_cocone l' r' pp').

  Definition PO_rec_beta_pp (P: Type) (l': B -> P) (r': C -> P)
             (pp': l' o f == r' o g)
    : forall x, ap (PO_rec P l' r' pp') (popp x) = pp' x.
  Proof.
    intro x.
    pose proof (colimit_rec_beta_colimp P (Build_span_cocone l' r' pp')
                                    (inl tt) (inr true) tt x).
    pose proof (colimit_rec_beta_colimp P (Build_span_cocone l' r' pp')
                                    (inl tt) (inr false) tt x).
    unfold popp; cbn in *.
    refine (ap_pp _ _ _ @ _). refine (_ @ concat_p1 _).
    refine (X @@ _). refine (_ @ inverse2 X0).
    exact (ap_V _ _).
  Defined.


  (** A nice property: the pushout of an equivalence is an equivalence. *)
  Definition PO_of_equiv (Hf : IsEquiv f)
    : IsEquiv por.
  Proof.
    serapply isequiv_adjointify.
    serapply PO_rec. exact (g o f^-1). exact idmap.
    intro x. apply ap. apply eissect.
    serapply PO_ind; cbn.
    intro. refine ((popp _)^ @ _). apply ap.
    apply eisretr. reflexivity.
    intro a; cbn. rewrite transport_paths_FlFr, ap_idmap.
    rewrite ap_compose. rewrite PO_rec_beta_pp.
    rewrite eisadj. destruct (eissect f a). cbn.
    rewrite concat_1p, concat_p1. apply concat_Vp.
    intro; reflexivity.
  Defined.
End PO.


(** ** Equivalence with [pushout] *)

Section is_PO_pushout.
  Import HIT.Pushout.
  Context `{Funext} {A B C : Type} {f : A -> B} {g : A -> C}.

  Definition is_PO_pushout : is_PO f g (pushout f g).
  Proof.
    unshelve econstructor.
    - serapply Build_span_cocone.
      exact (push o inl). exact (push o inr). exact pp.
    - intro Y; serapply isequiv_adjointify.
      + intro Co. serapply pushout_rec.
        exact (pol' Co). exact (por' Co). exact (popp' Co).
      + intros [Co Co']. serapply path_cocone; cbn.
        * intros [[]|[]] x; simpl.
          apply (Co' (inl tt) (inr false) tt).
          all: reflexivity.
        * intros [[]|[]] [[]|[]] [] x; simpl.
          2: reflexivity.
          refine (_ @ (concat_1p _)^).
          rewrite pushout_rec_beta_pp.
          unfold popp'. cbn. hott_simpl.
      + intro h. apply path_forall.
        serapply pushout_ind; cbn.
        * intros b; reflexivity.
        * intros c; reflexivity.
        * intro a; cbn.
          rewrite transport_paths_FlFr. rewrite concat_p1.
          rewrite pushout_rec_beta_pp. eapply moveR_Vp.
          unfold popp'. cbn. by rewrite !concat_p1.
  Defined.

  Definition equiv_pushout_PO
    : pushout f g <~> PO f g.
  Proof.
    serapply colimit_unicity.
    3: eapply is_PO_pushout.
    eapply is_colimit_colimit.
  Defined.

End is_PO_pushout.