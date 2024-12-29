Require Import Basics Types Pointed HSpace.Core HSpace.Coherent.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

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
