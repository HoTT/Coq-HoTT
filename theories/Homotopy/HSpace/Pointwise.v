From HoTT Require Import Basics Types Pointed HSpace.Core HSpace.Coherent.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * Pointwise H-space structures *)

(** Whenever [X] is an H-space, so is the type of maps into [X].  Note: When writing [f * g], Coq only finds this instance if [f] is explicitly in the pointed type [[Y -> X, const pt]]. *)
Instance ishspace_map `{Funext} (X : pType) (Y : Type)
  `{IsHSpace X} : IsHSpace [Y -> X, const pt].
Proof.
  snapply Build_IsHSpace.
  - exact (fun f g y => (f y) * (g y)).
  - intro g; funext y.
    apply hspace_left_identity.
  - intro f; funext y.
    apply hspace_right_identity.
Defined.

(** If [X] is coherent, so is [[Y -> X, const pt]]. *)
Instance iscoherent_ishspace_map `{Funext} (X : pType) (Y : Type)
  `{IsCoherent X} : IsCoherent [Y -> X, const pt].
Proof.
  hnf; cbn.
  refine (ap _ _).
  funext y; exact iscoherent.
Defined.

(** If [X] is left-invertible, so is [[Y -> X, const pt]]. *)
Instance isleftinvertible_hspace_map `{Funext} (X : pType) (Y : Type)
  `{IsHSpace X} `{forall x, IsEquiv (x *.)}
  : forall f : [Y -> X, const pt], IsEquiv (f *.).
Proof.
  intro f; cbn.
  (* Left multiplication by [f] unifies with [functor_forall]. *)
  exact (isequiv_functor_forall (P:=const X) (f:=idmap)
           (g:=fun y gy => (f y) * gy)).
Defined.

(** The pointwise product of two pointed maps into an H-space. This is the operation underlying the H-space structure [ishspace_pmap] on [Y ->** X], but requires no coherence. *)
Definition sgop_pmap {X Y : pType} `{IsHSpace X} (f g : Y ->* X) : Y ->* X.
Proof.
  snapply Build_pMap.
  - exact (fun y => (f y) * (g y)).
  - cbn beta.
    lhs napply (ap _ (point_eq g)).
    lhs napply (ap (.* pt) (point_eq f)).
    apply hspace_left_identity.
Defined.

(** The constant map is a left unit for the pointwise product; this needs no coherence. *)
Definition leftidentity_pmap {X Y : pType} `{IsHSpace X} (g : Y ->* X)
  : sgop_pmap pconst g ==* g.
Proof.
  snapply Build_pHomotopy.
  - intro y; cbn.
    apply hspace_left_identity.
  - cbn.
    apply moveL_pV.
    exact (1 @@ concat_1p _ @ concat_A1p _ _)^.
Defined.

(** The constant map is a right unit for the pointwise product; the base-point coherence forces [right_identity pt = left_identity pt], so this needs [X] coherent. *)
Definition rightidentity_pmap {X Y : pType} `{IsCoherent X} (f : Y ->* X)
  : sgop_pmap f pconst ==* f.
Proof.
  snapply Build_pHomotopy.
  - intro y; cbn.
    apply hspace_right_identity.
  - pelim f; cbn.
    symmetry.
    lhs napply (concat_p1 _ @ concat_1p _ @ concat_1p _).
    exact iscoherent.
Defined.

(** For the type of pointed maps [Y ->** X], coherence of [X] is needed even to get a non-coherent H-space structure on [Y ->** X]. *)
Instance ishspace_pmap `{Funext} (X Y : pType) `{IsCoherent X}
  : IsHSpace (Y ->** X).
Proof.
  snapply Build_IsHSpace.
  - exact sgop_pmap.
  - intro g; exact (path_pforall (leftidentity_pmap g)).
  - intro f; exact (path_pforall (rightidentity_pmap f)).
Defined.

Instance iscoherent_hspace_pmap `{Funext} (X Y : pType) `{IsCoherent X}
  : IsCoherent (Y ->** X).
Proof.
  (* Note that [pt] sometimes means the constant map [Y ->* X]. *)
  unfold IsCoherent.
  (* Both identities are created using [path_pforall]. *)
  refine (ap path_pforall _).
  apply path_pforall.
  snapply Build_pHomotopy.
  - intro y; cbn.
    exact iscoherent.
  - cbn.
    generalize iscoherent as isc.
    unfold left_identity, right_identity.
    generalize (hspace_left_identity pt).
    intros p [].
    by destruct p.
Defined.

(** Since [sgop_pmap] is defined pointwise, it commutes with precomposition. *)
Definition sgop_pmap_precompose {X Y W : pType} `{IsHSpace X}
  (f g : Y ->* X) (h : W ->* Y)
  : sgop_pmap f g o* h ==* sgop_pmap (f o* h) (g o* h).
Proof.
  snapply Build_pHomotopy.
  - reflexivity.
  - pelim h f g; cbn.  symmetry; apply concat_pp_V.
Defined.

(** [sgop_pmap] respects pointed homotopy in each argument. *)
Definition sgop_pmap_phomotopy {X Y : pType} `{IsHSpace X}
  {f f' g g' : Y ->* X} (p : f ==* f') (q : g ==* g')
  : sgop_pmap f g ==* sgop_pmap f' g'.
Proof.
  snapply Build_pHomotopy.
  - intro y; exact (ap011 sg_op (p y) (q y)).
  - pelim p f f' q g g'; cbn.  symmetry; apply concat_pV.
Defined.

(** If the H-space structure on [X] is left-invertible, so is the one induced on [Y ->** X]. *)
Instance isleftinvertible_hspace_pmap `{Funext} (X Y : pType)
  `{IsCoherent X} `{forall x, IsEquiv (x *.)}
  : forall f : Y ->** X, IsEquiv (f *.).
Proof.
  intro f.
  srefine (isequiv_homotopic (equiv_functor_pforall_id _ _) _).
  - exact (fun a => equiv_hspace_left_op (f a)).
  - cbn. exact (right_identity _ @ point_eq f).
  - intro g.
    apply path_pforall; snapply Build_pHomotopy.
    + intro y; cbn.
      reflexivity.
    + cbn. apply (moveR_1M _ _)^-1.
      apply whiskerL.
      refine (whiskerL _ iscoherent @ _).
      exact (concat_A1p right_identity (point_eq f)).
Defined.
