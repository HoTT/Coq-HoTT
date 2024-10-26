Require Import HoTT.Basics HoTT.Types.
Require Import Constant.
Require Import HoTT.Truncations.
Require Import ObjectClassifier Homotopy.ExactSequence Pointed.

Local Open Scope type_scope.
Local Open Scope path_scope.

(** * BAut(X) *)

(** ** Basics *)

(** [BAut X] is the type of types that are merely equal to [X]. It is connected, by [is0connected_component] and any two points are merely equal by [merely_path_component]. *)
Definition BAut (X : Type@{u}) := { Z : Type@{u} & merely (Z = X) }.

Coercion BAut_pr1 X : BAut X -> Type := pr1.

Global Instance ispointed_baut {X : Type} : IsPointed (BAut X) := (X; tr 1).

(** We also define a pointed version [pBAut X], since the coercion [BAut_pr1] doesn't work if [BAut X] is a [pType]. *)
Definition pBAut (X : Type) : pType
  := [BAut X, _].

Definition path_baut `{Univalence} {X} (Z Z' : BAut X)
: (Z <~> Z') <~> (Z = Z' :> BAut X)
  := equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.

Definition ap_pr1_path_baut `{Univalence} {X}
           {Z Z' : BAut X} (f : Z <~> Z')
: ap (BAut_pr1 X) (path_baut Z Z' f) = path_universe f.
Proof.
  unfold path_baut, BAut_pr1; simpl.
  apply ap_pr1_path_sigma_hprop.
Defined.

Definition transport_path_baut `{Univalence} {X}
           {Z Z' : BAut X} (f : Z <~> Z') (z : Z)
: transport (fun (W:BAut X) => W) (path_baut Z Z' f) z = f z.
Proof.
  refine (transport_compose idmap (BAut_pr1 X) _ _ @ _).
  refine (_ @ transport_path_universe f z).
  apply ap10, ap, ap_pr1_path_baut.
Defined.

(** The following tactic, which applies when trying to prove an hprop, replaces all assumed elements of [BAut X] by [X] itself. With [Univalence], this would work for any 0-connected type, but using [merely_path_component] we can avoid univalence. *)
Ltac baut_reduce :=
  progress repeat
    match goal with
      | [ Z : BAut ?X |- _ ]
        => let Zispoint := fresh "Zispoint" in
           assert (Zispoint := merely_path_component (point (BAut X)) Z);
           revert Zispoint;
           refine (@Trunc_ind _ _ _ _ _);
           intro Zispoint;
           destruct Zispoint
    end.

(** ** Truncation *)

(** If [X] is an [n.+1]-type, then [BAut X] is an [n.+2]-type. *)
Global Instance trunc_baut `{Univalence} {n X} `{IsTrunc n.+1 X}
: IsTrunc n.+2 (BAut X).
Proof.
  apply istrunc_S.
  intros Z W.
  baut_reduce.
  exact (@istrunc_equiv_istrunc _ _ (path_baut _ _) n.+1 _).
Defined.

(** If [X] is truncated, then so is every element of [BAut X]. *)
Global Instance trunc_el_baut {n X} `{Funext} `{IsTrunc n X} (Z : BAut X)
  : IsTrunc n Z
  := ltac:(by baut_reduce).

(** ** Operations on [BAut] *)

(** Multiplying by a fixed type *)

Definition baut_prod_r (X A : Type)
  : BAut X -> BAut (X * A)
  := fun Z:BAut X =>
       (Z * A ; Trunc_functor (-1) (ap (fun W => W * A)) (pr2 Z))
       : BAut (X * A).

Definition ap_baut_prod_r `{Univalence} (X A : Type)
           {Z W : BAut X} (e : Z <~> W)
  : ap (baut_prod_r X A) (path_baut Z W e)
    = path_baut (baut_prod_r X A Z) (baut_prod_r X A W) (equiv_functor_prod_r e).
Proof.
  cbn.
  apply moveL_equiv_M; cbn; unfold pr1_path.
  rewrite <- (ap_compose (baut_prod_r X A) pr1 (path_sigma_hprop Z W _)).
  rewrite <- ((ap_compose pr1 (fun Z => Z * A) (path_sigma_hprop Z W _))^).
  rewrite ap_pr1_path_sigma_hprop.
  apply moveL_equiv_M; cbn.
  apply ap_prod_r_path_universe.
Qed.

(** ** Centers *)

(** The following lemma says that to define a section of a family [P] of hsets over [BAut X], it is equivalent to define an element of [P X] which is fixed by all automorphisms of [X]. *)
Lemma baut_ind_hset `{Univalence} X
      (** It ought to be possible to allow more generally [P : BAut X -> Type], but the proof would get more complicated, and this version suffices for present applications. *)
      (P : Type -> Type) `{forall (Z : BAut X), IsHSet (P Z)}
: { e : P (point (BAut X)) &
    forall g : X <~> X, transport P (path_universe g) e = e }
  <~> (forall (Z:BAut X), P Z).
Proof.
  refine (equiv_sig_ind _ oE _).
  (** We use the fact that maps out of a propositional truncation into an hset are equivalent to weakly constant functions. *)
  refine ((equiv_functor_forall'
             (P := fun Z => { f : (Z=X) -> P Z & WeaklyConstant f })
             1
             (fun Z => equiv_merely_rec_hset_if_domain _ _)) oE _); simpl.
  { intros p. change (IsHSet (P (BAut_pr1 X (Z ; tr p)))). exact _. }
  unfold WeaklyConstant.
  (** Now we peel away a bunch of contractible types. *)
  refine (equiv_sig_coind _ _ oE _).
  srapply equiv_functor_sigma'.
  1:apply (equiv_paths_ind_r X (fun x _ => P x)).
  intros p; cbn.
  refine (equiv_paths_ind_r X _ oE _).
  srapply equiv_functor_forall'.
  1:apply equiv_equiv_path.
  intros e; cbn.
  refine (_ oE equiv_moveL_transport_V _ _ _ _). 
  apply equiv_concat_r.
  rewrite path_universe_transport_idmap, paths_ind_r_transport.
  reflexivity.
Defined.

(** This implies that if [X] is a set, then the center of [BAut X] is the set of automorphisms of [X] that commute with every other automorphism (i.e. the center, in the usual sense, of the group of automorphisms of [X]). *)

Definition center_baut `{Univalence} X `{IsHSet X}
: { f : X <~> X & forall g:X<~>X, g o f == f o g }
  <~> (forall Z:BAut X, Z = Z).
Proof.
  refine (equiv_functor_forall_id
            (fun Z => equiv_path_sigma_hprop Z Z) oE _).
  refine (baut_ind_hset X (fun Z => Z = Z) oE _).
  simpl.
  refine (equiv_functor_sigma' (equiv_path_universe X X) _); intros f.
  apply equiv_functor_forall_id; intros g; simpl.
  refine (_ oE equiv_path_arrow _ _).
  refine (_ oE equiv_path_equiv (g oE f) (f oE g)).
  revert g. equiv_intro (equiv_path X X) g.
  revert f. equiv_intro (equiv_path X X) f.
  refine (_ oE equiv_concat_l (equiv_path_pp _ _) _).
  refine (_ oE equiv_concat_r (equiv_path_pp _ _)^ _).
  refine (_ oE (equiv_ap (equiv_path X X) _ _)^-1).
  refine (equiv_concat_l (transport_paths_lr _ _) _ oE _).
  refine (equiv_concat_l (concat_pp_p _ _ _) _ oE _).
  refine (equiv_moveR_Vp _ _ _ oE _).
  refine (equiv_concat_l _ _ oE equiv_concat_r _ _).
  - apply concat2; apply eissect.
  - symmetry; apply concat2; apply eissect.
Defined.

(** We show that this equivalence takes the identity equivalence to the identity in the center.  We have to be careful in this proof never to [simpl] or [unfold] too many things, or Coq will produce gigantic terms that take it forever to compute with. *)
Definition id_center_baut `{Univalence} X `{IsHSet X}
: center_baut X (exist
                   (fun (f:X<~>X) => forall (g:X<~>X), g o f == f o g)
                   (equiv_idmap X)
                   (fun (g:X<~>X) (x:X) => idpath (g x)))
  = fun Z => idpath Z.
Proof.
  apply path_forall; intros Z.
  assert (IsHSet (Z.1 = Z.1)) by exact _.
  baut_reduce.
  exact (ap (path_sigma_hprop _ _) path_universe_1
            @ path_sigma_hprop_1 _).
Defined.

(** Similarly, if [X] is a 1-type, we can characterize the 2-center of [BAut X]. *)

(** Coq is too eager about unfolding some things appearing in this proof. *)
Section Center2BAut.
  Local Arguments equiv_path_equiv : simpl never.
  Local Arguments equiv_path2_universe : simpl never.

  Definition center2_baut `{Univalence} X `{IsTrunc 1 X}
  : { f : forall x:X, x=x & forall (g:X<~>X) (x:X), ap g (f x) = f (g x) }
      <~> (forall Z:BAut X, (idpath Z) = (idpath Z)).
  Proof.
    refine ((equiv_functor_forall_id
               (fun Z => (equiv_concat_lr _ _)
                           oE (equiv_ap (equiv_path_sigma_hprop Z Z) 1%path 1%path))) oE _).
    { symmetry; apply path_sigma_hprop_1. }
    { apply path_sigma_hprop_1. }
    assert (forall Z:BAut X, IsHSet (idpath Z.1 = idpath Z.1)) by exact _.
    refine (baut_ind_hset X (fun Z => idpath Z = idpath Z) oE _).
    simple refine (equiv_functor_sigma' _ _).
    { refine (_ oE equiv_path2_universe 1 1).
      apply equiv_concat_lr.
      - symmetry; apply path_universe_1.
      - apply path_universe_1. }
    intros f.
    apply equiv_functor_forall_id; intros g.
    refine (_ oE equiv_path3_universe _ _).
    refine (dpath_paths2 (path_universe g) _ _ oE _).
    cbn.
    change (equiv_idmap X == equiv_idmap X) in f.
    refine (equiv_concat_lr _ _).
    - refine (_ @ (path2_universe_postcompose_idmap f g)^).
      abstract (rewrite !whiskerR_pp, !concat_pp_p; reflexivity).
    - refine (path2_universe_precompose_idmap f g @ _).
      abstract (rewrite !whiskerL_pp, !concat_pp_p; reflexivity).
  Defined.

  (** Once again we compute it on the identity.  In this case it seems to be unavoidable to do some [simpl]ing (or at least [cbn]ing), making this proof somewhat slower. *)
  Definition id_center2_baut `{Univalence} X `{IsTrunc 1 X}
  : center2_baut X (exist
                      (fun (f:forall x:X, x=x) =>
                         forall (g:X<~>X) (x:X), ap g (f x) = f (g x))
                      (fun x => idpath x)
                      (fun (g:X<~>X) (x:X) => idpath (idpath (g x))))
    = fun Z => idpath (idpath Z).
  Proof.
    apply path_forall; intros Z.
    assert (IsHSet (idpath Z.1 = idpath Z.1)) by exact _.
    baut_reduce.
    cbn. unfold functor_forall, sig_rect, merely_rec_hset. cbn.
    rewrite equiv_path2_universe_1.
    rewrite !concat_p1, !concat_Vp.
    simpl.
    rewrite !concat_p1, !concat_Vp.
    reflexivity.
  Defined.

End Center2BAut.

Section ClassifyingMaps.

  (** ** Maps into [BAut F] classify bundles with fiber [F] *)

  (** The property of being merely equivalent to a given type [F] defines a subuniverse. *)
  Definition subuniverse_merely_equiv (F : Type) : Subuniverse.
  Proof.
    rapply (Build_Subuniverse (fun E => merely (E <~> F))).
    intros T U mere_eq f iseq_f.
    strip_truncations.
    pose (feq:=Build_Equiv _ _ f iseq_f).
    exact (tr (mere_eq oE feq^-1)).
  Defined.

  (** The universe of O-local types for [subuniverse_merely_equiv F] is equivalent to [BAut F]. *)
  Proposition equiv_baut_typeO `{Univalence} {F : Type}
    :  BAut F <~> Type_ (subuniverse_merely_equiv F).
  Proof.
    srapply equiv_functor_sigma_id; intro X; cbn.
    rapply Trunc_functor_equiv.
    exact (equiv_path_universe _ _)^-1%equiv.
  Defined.

  (** Consequently, maps into [BAut F] correspond to bundles with fibers merely equivalent to [F]. *)
  Corollary equiv_map_baut_fibration `{Univalence} {Y : pType} {F : Type}
    : (Y -> BAut F) <~> { p : Slice Y & forall y:Y, merely (hfiber p.2 y <~> F) }.
  Proof.
    refine (_ oE equiv_postcompose' equiv_baut_typeO).
    refine (_ oE equiv_sigma_fibration_O).
    snrapply equiv_functor_sigma_id; intro p.
    rapply equiv_functor_forall_id; intro y.
    by apply Trunc_functor_equiv.
  Defined.

  (** The pointed version of [equiv_baut_typeO] above. *)
  Proposition pequiv_pbaut_typeOp@{u v +} `{Univalence} {F : Type@{u}}
    : pBAut@{u v} F <~>* [Type_ (subuniverse_merely_equiv F), (F; tr equiv_idmap)].
  Proof.
    snrapply Build_pEquiv'; cbn.
    1: exact equiv_baut_typeO.
    by apply path_sigma_hprop.
  Defined.

  Definition equiv_pmap_pbaut_pfibration `{Univalence} {Y F : pType@{u}}
    : (Y ->* pBAut@{u v} F) <~> { p : { q : pSlice Y & forall y:Y, merely (hfiber q.2 y <~> F) } &
                                      pfiber p.1.2 <~>* F }
    := (equiv_sigma_pfibration_O (subuniverse_merely_equiv F))
         oE pequiv_pequiv_postcompose pequiv_pbaut_typeOp.

  (** When [Y] is connected, pointed maps into [pBAut F] correspond to maps into the universe sending the base point to [F]. *)
  Proposition equiv_pmap_pbaut_type_p `{Univalence}
              {Y : pType@{u}} {F : Type@{u}} `{IsConnected 0 Y}
    : (Y ->* pBAut F) <~> (Y ->* [Type@{u}, F]).
  Proof.
    refine (_ oE pequiv_pequiv_postcompose pequiv_pbaut_typeOp).
    rapply equiv_pmap_typeO_type_connected.
  Defined.

  (** When [Y] is connected, [pBAut F] classifies fiber sequences over [Y] with fiber [F]. *)
  Definition equiv_pmap_pbaut_pfibration_connected `{Univalence} {Y F : pType} `{IsConnected 0 Y}
    : (Y ->* pBAut F) <~> { X : pType & FiberSeq F X Y }
    := classify_fiberseq oE equiv_pmap_pbaut_type_p.

End ClassifyingMaps.
