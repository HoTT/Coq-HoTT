Require Import Basics Types Pointed HSpace.Core HSpace.Coherent HSpace.HGroup.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

(** * Pointwise H-space structures *)

(** Whenever [X] is an H-space, so is the type of maps into [X]. *)
Global Instance ishspace_map `{Funext} (X : pType) (Y : Type)
  `{IsHSpace X} : IsHSpace [Y -> X, const pt].
(* Note: When writing [f * g], Coq only finds this instance if [f] is explicitly in the pointed type [[Y -> X, const pt]]. *)
Proof.
  snrapply Build_IsHSpace.
  - exact (fun f g y => (f y) * (g y)).
  - intro g; funext y.
    apply hspace_left_identity.
  - intro f; funext y.
    apply hspace_right_identity.
Defined.

(** If [X] is coherent, so is [[Y -> X, const pt]]. *)
Global Instance iscoherent_ishspace_map `{Funext} (X : pType) (Y : Type)
  `{IsCoherent X} : IsCoherent [Y -> X, const pt].
Proof.
  hnf; cbn.
  refine (ap _ _).
  funext y; apply iscoherent.
Defined.

(** If [X] is left-invertible, so is [[Y -> X, const pt]]. *)
Global Instance isleftinvertible_hspace_map `{Funext} (X : pType) (Y : Type)
  `{IsHSpace X} `{forall x, IsEquiv (x *.)}
  : forall f : [Y -> X, const pt], IsEquiv (f *.).
Proof.
  intro f; cbn.
  (** Left multiplication by [f] unifies with [functor_forall]. *)
  exact (isequiv_functor_forall (P:=const X) (f:=idmap)
           (g:=fun y gy => (f y) * gy)).
Defined.

(** For the type of pointed maps [Y ->** X], coherence of [X] is needed even to get a noncoherent H-space structure on [Y ->** X]. *)
Global Instance ishspace_pmap `{Funext} (X Y : pType) `{IsCoherent X}
  : IsHSpace (Y ->** X).
Proof.
  snrapply Build_IsHSpace.
  - intros f g.
    snrapply Build_pMap.
    + exact (fun y => hspace_op (f y) (g y)).
    + cbn.
      refine (ap _ (point_eq g) @ _); cbn.
      refine (ap (.* pt) (point_eq f) @ _).
      apply hspace_left_identity.
  - intro g.
    apply path_pforall.
    snrapply Build_pHomotopy.
    + intro y; cbn.
      apply hspace_left_identity.
    + cbn.
      apply moveL_pV.
      exact (1 @@ concat_1p _ @ concat_A1p _ _)^.
  - intro f.
    apply path_pforall.
    snrapply Build_pHomotopy.
    + intro y; cbn.
      apply hspace_right_identity.
    + pelim f; cbn.
      symmetry.
      lhs nrapply (concat_p1 _ @ concat_1p _ @ concat_1p _).
      apply iscoherent.
Defined.

Global Instance iscoherent_hspace_pmap `{Funext} (X Y : pType) `{IsCoherent X}
  : IsCoherent (Y ->** X).
Proof.
  (* Note that [pt] sometimes means the constant map [Y ->* X]. *)
  unfold IsCoherent.
  (* Both identities are created using [path_pforall]. *)
  refine (ap path_pforall _).
  apply path_pforall.
  snrapply Build_pHomotopy.
  - intro y; cbn.
    apply iscoherent.
  - cbn.
    generalize iscoherent as isc.
    unfold left_identity, right_identity.
    (* The next line is essentially the same as [generalize], but for some reason that tactic doesn't work here. *)
    set (p := hspace_left_identity pt); clearbody p.
    intros [].
    induction p.
    reflexivity.
Defined.

(** If the H-space structure on [X] is left-invertible, so is the one induced on [Y ->** X]. *)
Global Instance isleftinvertible_hspace_pmap `{Funext} (X Y : pType)
  `{IsCoherent X} `{forall x, IsEquiv (x *.)}
  : forall f : Y ->** X, IsEquiv (f *.).
Proof.
  intro f.
  srefine (isequiv_homotopic (equiv_functor_pforall_id _ _) _).
  - exact (fun a => equiv_hspace_left_op (f a)).
  - cbn. exact (right_identity _ @ point_eq f).
  - intro g.
    apply path_pforall; snrapply Build_pHomotopy.
    + intro y; cbn.
      reflexivity.
    + cbn. apply (moveR_1M _ _)^-1.
      apply whiskerL.
      refine (whiskerL _ iscoherent @ _).
      exact (concat_A1p right_identity (point_eq f)).
Defined.

(** If the H-space structure on [X] is right-invertible, so is the one induced on [Y ->** X]. *)
Global Instance isrightinvertible_hspace_pmap `{Funext} (X Y : pType)
  `{IsCoherent X} `{forall x, IsEquiv (.* x)}
  : forall f : Y ->** X, IsEquiv (.* f).
Proof.
  intro f.
  srefine (isequiv_homotopic (equiv_functor_pforall_id _ _) _).
  - exact (fun a => equiv_hspace_right_op (f a)).
  - cbn. exact (left_identity _ @ point_eq f).
  - intro g.
    apply path_pforall; snrapply Build_pHomotopy.
    + intro y; cbn.
      reflexivity.
    + cbn. apply (moveR_1M _ _)^-1.
      pelim f g.
      simpl.
      nrapply whiskerL.
      apply concat_1p_p1.
Defined.

(** If the H-space structure on [X] is coherently commutative, then the H-space structure on [Y ->** X] is commutative. *)
Global Instance commutative_hspace_pmap `{Funext} (X Y : pType)
  `{IsCoherent X} `{!IsCohCommutative X}
  : @Commutative (Y ->** X) _ (.*.).
Proof.
  intros f g.
  snrapply path_pforall.
  snrapply Build_pHomotopy.
  - intros x.
    nrapply commutativity.
    exact _.
  - pelim f g.
    nrefine (iscohcommutative @ _).
    symmetry.
    apply concat_pV.
Defined.

(** If the H-space structure on [X] is coherently associative, then the H-space structure on [Y ->** X] is associative. *)
Global Instance associative_hspace_pmap `{Funext} (X Y : pType)
  `{IsCoherent X} `{!IsCohAssociative X}
  : @Associative (Y ->** X) (.*.).
Proof.
  hnf.
  intros f g h.
  snrapply path_pforall.
  snrapply Build_pHomotopy.
  - intros x.
    nrapply simple_associativity.
    exact _.
  - simpl.
    pelim f g h.
    simpl.
    hott_simpl.
    rewrite inv_pp.
    simpl.
    hott_simpl.
    rewrite <- (ap_V (.* pt)).
    apply associative_iscohassoc_coh.
Defined.

(** If the H-space structure on [X] is a coherent H-space, then the H-space structure on [Y ->** X] is a H-monoid. *)
Global Instance ishmonoid_hspace_pmap `{Funext} (X Y : pType) `{IsCohHMonoid X}
  : IsHMonoid (Y ->** X) := {}.

(** If the H-space structure on [X] is a coherent H-group, then the H-space structure on [Y ->** X] is a H-group. *)
Global Instance ishgroup_hspace_pmap `{Funext} (X Y : pType) `{IsCohHGroup X}
  : IsHGroup (Y ->** X).
Proof.
  snrapply Build_IsHGroup.
  1: exact _.
  - intro f.
    snrapply Build_pMap.
    + exact (fun y => negate (f y)).
    + nrefine (ap _ (point_eq f) @ _).
      apply negate_coh.
  - intro f.
    snrapply path_pforall.
    snrapply Build_pHomotopy.
    + intro y.
      cbn; apply left_inverse.
    + pelim f.
      simpl.
      hott_simpl.
      apply left_inverse_coh.
  - intro f.
    snrapply path_pforall.
    snrapply Build_pHomotopy.
    + intro y.
      cbn; apply right_inverse.
    + pelim f.
      simpl.
      hott_simpl.
      apply right_inverse_coh.
Defined.

(** If the H-space structure on [X] is a coherent H-abelian group, then the H-space structure on [Y ->** X] is a H-AbGroup. *)
Global Instance ishabgroup_hspace_pmap `{Funext} (X Y : pType) `{IsCohHAbGroup X}
  : IsHAbGroup (Y ->** X) := {}.
