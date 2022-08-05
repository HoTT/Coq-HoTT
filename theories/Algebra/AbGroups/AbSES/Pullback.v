Require Import Basics Types HSet HFiber Limits.Pullback Cubical.PathSquare.
Require Import WildCat Pointed Homotopy.ExactSequence.
Require Import AbGroups.AbelianGroup AbGroups.AbPullback AbSES.Core.

Local Open Scope abses_scope.

(** * Pullbacks of short exact sequences *)

(** A short exact sequence [A -> E -> B] can be pulled back along a map [B' -> B]. We start by defining the underlying map, then the pointed version. *)
Definition abses_pullback0 {A B B' : AbGroup} (f : B' $-> B)
  : AbSES B A -> AbSES B' A.
Proof.
  intro E.
  snrapply (Build_AbSES (ab_pullback (projection E) f)
                        (grp_pullback_corec _ _ (inclusion _) grp_homo_const _)
                        (grp_pullback_pr2 (projection _) f)).
  - intro x.
    nrefine (_ @ (grp_homo_unit f)^).
    apply isexact_inclusion_projection.
  - exact (cancelL_isembedding (g:= grp_pullback_pr1 _ _)).
  - rapply conn_map_pullback'.
  - snrapply Build_IsExact.
    + srapply Build_pHomotopy.
      * reflexivity.
      * apply path_ishprop.
    + nrefine (cancelR_equiv_conn_map
                 _ _ (hfiber_pullback_along_pointed f (projection _) (grp_homo_unit _))).
      nrefine (conn_map_homotopic _ _ _ _ (conn_map_isexact (IsExact:=isexact_inclusion_projection _))).
      intro a.
      by apply path_sigma_hprop.
Defined.

(** ** The universal property of [abses_pullback_morphism] *)

(** The natural map from the pulled back sequence. *)
Definition abses_pullback_morphism {A B B' : AbGroup} (E : AbSES B A) (f : B' $-> B)
  : AbSESMorphism (abses_pullback0 f E) E.
Proof.
  snrapply (Build_AbSESMorphism grp_homo_id _ f).
  - apply grp_pullback_pr1.
  - reflexivity.
  - apply pullback_commsq.
Defined.

(** Any map [f : E -> F] of short exact sequences factors (uniquely) through [abses_pullback F f3]. *)
Definition abses_pullback_morphism_corec {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : AbSESMorphism E (abses_pullback0 (component3 f) F).
Proof.
  snrapply (Build_AbSESMorphism (component1 f) _ grp_homo_id).
  - apply (grp_pullback_corec (projection F) (component3 f)
                              (component2 f) (projection E)).
    apply right_square.
  - intro x; cbn.
    apply equiv_path_pullback_hset; cbn; split.
    + apply left_square.
    + symmetry; apply iscomplex_abses.
  - reflexivity.
Defined.

(** The original map factors via the induced map. *)
Definition abses_pullback_morphism_corec_beta `{Funext} {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : f = absesmorphism_compose (abses_pullback_morphism F (component3 f))
                              (abses_pullback_morphism_corec f).
Proof.
  apply (equiv_ap issig_AbSESMorphism^-1 _ _).
  srapply path_sigma_hprop.
  apply path_prod.
  1: apply path_prod.
  all: by apply equiv_path_grouphomomorphism.
Defined.

Definition abses_component1_trivial_pullback' `{Funext} {A B B' : AbGroup}
           {E : AbSES B A} {F : AbSES B' A} (f : AbSESMorphism E F)
           (h : component1 f == grp_homo_id)
  : E $== abses_pullback0 (component3 f) F.
Proof.
  pose (g := abses_pullback_morphism_corec f).
  nrapply abses_path_data_to_iso.
  exists (component2 g); split.
  - exact (fun a => (left_square g a)^ @ ap _ (h a)).
  - reflexivity.
Defined.

(** In particular, if [component1] of a morphism is the identity, then it exhibits the domain as the pullback of the codomain. *)
Definition abses_component1_trivial_pullback `{Univalence} {A B B' : AbGroup}
           {E : AbSES B A} {F : AbSES B' A}
           (f : AbSESMorphism E F) (h : component1 f == grp_homo_id)
  : E = abses_pullback0 (component3 f) F
  := equiv_path_abses_iso (abses_component1_trivial_pullback' f h).

(** ** Functoriality of [abses_pullback0 f] for [f : B' $-> B] *)

(** As any function, [abses_pullback0 f] acts on paths. By explicitly describing the analogous action on path data we get an action which computes, this turn out to be useful. *)

Global Instance is0functor_abses_pullback {A B B' : AbGroup} (f : B' $-> B)
  : Is0Functor (abses_pullback0 (A:=A) f).
Proof.
  srapply Build_Is0Functor;
    intros E F p.
  snrefine (_; (_,_)).
  - srapply equiv_functor_grp_pullback.
    1,3: exact grp_iso_id.
    1: exact p.1.
    2: reflexivity.
    intro x.
    exact (snd p.2 x)^.
  - intro x.
    srapply equiv_path_pullback_hset; split; cbn.
    2: reflexivity.
    exact (fst p.2 x).
  - reflexivity.
Defined.

Global Instance is1functor_abses_pullback {A B B' : AbGroup} (f : B' $-> B)
  : Is1Functor (abses_pullback0 (A:=A) f).
Proof.
  snrapply Build_Is1Functor.
  - intros E F p q h x.
    srapply equiv_path_pullback_hset; split; cbn.
    2: reflexivity.
    exact (h _).
  - intros E x.
    by srapply equiv_path_pullback_hset.
  - intros E F G p q x.
    by srapply equiv_path_pullback_hset.
Defined.

Lemma ap_abses_pullback `{Univalence} {A B B' : AbGroup} (f : B' $-> B)
      {E F : AbSES B A} (p : E = F)
  : ap (abses_pullback0 f) p
    = equiv_path_abses_iso (fmap (abses_pullback0 f) (equiv_path_abses_iso^-1 p)).
Proof.
  induction p.
  nrefine (_ @ ap equiv_path_abses_iso _).
  2: refine ((fmap_id_strong _ _)^ @ ap _ equiv_path_absesV_1^).
  exact equiv_path_abses_1^.
Defined.

Lemma ap_abses_pullback_data `{Univalence} {A B B' : AbGroup} (f : B' $-> B) {E F : AbSES B A}
      (p : abses_path_data_iso E F)
  : ap (abses_pullback0 f) (equiv_path_abses_iso p)
    = equiv_path_abses_iso (fmap (abses_pullback0 f) p).
Proof.
  refine (ap_abses_pullback _ _ @ _).
  apply (ap (equiv_path_abses_iso o _)).
  apply eissect.
Defined.

Definition abses_pullback_point' {A B B' : AbGroup} (f : B' $-> B)
  : (abses_pullback0 f (point _)) $== (point (AbSES B' A)).
Proof.
  snrefine (_; (_, _)).
  - snrapply Build_GroupIsomorphism.
    + srapply ab_biprod_corec.
      * refine (ab_biprod_pr1 $o _).
        apply grp_pullback_pr1.
      * apply projection.
    + srapply isequiv_adjointify.
      * snrapply grp_pullback_corec.
        -- exact (functor_ab_biprod grp_homo_id f).
        -- exact ab_biprod_pr2.
        -- reflexivity.
      * reflexivity.
      * intros [[a b] [b' c]].
        srapply equiv_path_pullback_hset; split; cbn.
        2: reflexivity.
        exact (path_prod' idpath c^).
  - reflexivity.
  - reflexivity.
Defined.

Definition abses_pullback' {A B B' : AbGroup} (f : B' $-> B)
  : AbSES B A -->* AbSES B' A
  := Build_BasepointPreservingFunctor (abses_pullback0 f) (abses_pullback_point' f).

(** Pullback of short exact sequences as a pointed map. *)
Definition abses_pullback `{Univalence} {A B B' : AbGroup} (f : B' $-> B)
  : AbSES B A ->* AbSES B' A
  := to_pointed (abses_pullback' f).

(** ** Functoriality of [abses_pullback0] *)

(** [abses_pullback0] is psuedo-functorial, and we can state this in terms of actual homotopies or "path data homotopies." We decorate the latter with the suffix ('). *)

Definition abses_pullback_compose' {A B0 B1 B2 : AbGroup}
           (f : B0 $-> B1) (g : B1 $-> B2)
  : abses_pullback0 (A:=A) f o abses_pullback0 g $=> abses_pullback0 (g $o f).
Proof.
  intro E; srefine (_; (_,_)).
  - apply equiv_grp_pullback_compose_r.
  - intro a.
    by srapply equiv_path_pullback_hset.
  - reflexivity.
Defined.

(** The analog of [abses_pullback_compose'] with actual homotopies. *)
Definition abses_pullback_compose `{Univalence} {A B0 B1 B2 : AbGroup}
           (f : B0 $-> B1) (g : B1 $-> B2)
  : abses_pullback (A:=A) f o abses_pullback g == abses_pullback (g $o f)
  := fun x => equiv_path_abses_iso (abses_pullback_compose' f g x).

(** We now work towards *pointed* composition of pullback ([abses_pullback_pcompose]). The proof of pointedness will matter when we later prove that pulling back along a short exact sequence is exact (i.e. that the complex [iscomplex_pullback_abses] below is exact). For this reason we carefully construct the proof of pointedness in terms of the analog [abses_pullback_pcompose'] on path data, which computes. *)

Definition abses_pullback_pcompose' {B0 B1 B2 A : AbGroup}
           (f : B0 $-> B1) (g : B1 $-> B2)
  : abses_pullback' f $o* abses_pullback' g $=>* abses_pullback' (A:=A) (g $o f).
Proof.
  exists (abses_pullback_compose' f g).
  intros [[[a b2] [b1 c]] [b0 c']]; cbn in c, c'.
  srapply equiv_path_pullback_hset; split; cbn.
  2: reflexivity.
  exact (path_prod' idpath (c @ ap g c')).
Defined.

Definition abses_pullback_pcompose `{Univalence} {A B0 B1 B2 : AbGroup}
           (f : B0 $-> B1) (g : B1 $-> B2)
  : abses_pullback (A:=A) f o* abses_pullback g ==* abses_pullback (g $o f).
Proof.
  refine (to_pointed_compose _ _ @* _).
  apply equiv_ptransformation_phomotopy.
  apply abses_pullback_pcompose'.
Defined.

(** *** Pulling back along constant maps *)

Lemma abses_pullback_const' `{Funext} {A B B' : AbGroup}
  : const (point _) $=> (@abses_pullback0 A B B' grp_homo_const).
Proof.
  intro E.
  simpl.
  nrapply abses_path_data_to_iso.
  srefine (_;(_,_)); cbn.
  - srapply grp_pullback_corec.
    + exact (inclusion _ $o ab_biprod_pr1).
    + exact ab_biprod_pr2.
    + intro x; cbn.
      apply iscomplex_abses.
  - intro a; cbn.
    by srapply equiv_path_pullback_hset; split.
  - reflexivity.
Defined.

Definition abses_pullback_const `{Univalence} {A B B' : AbGroup}
  : const (point _) == @abses_pullback0 A B B' grp_homo_const
  := fun x => (equiv_path_abses_iso (abses_pullback_const' x)).

Lemma abses_pullback_pconst' `{Funext} {A B B' : AbGroup}
  : @pmap_abses_const B' A B A $=>* abses_pullback' grp_homo_const.
Proof.
  srefine (_; _).
  1: rapply abses_pullback_const'.
  lazy beta.
  intro x; reflexivity.
Defined.

Definition abses_pullback_pconst `{Univalence} {A B B' : AbGroup}
  : pconst ==* @abses_pullback _ A B B' grp_homo_const.
Proof.
  refine (pmap_abses_const_to_pointed @* _).
  rapply equiv_ptransformation_phomotopy.
  exact abses_pullback_pconst'.
Defined.

(** *** Pulling back along homotopic maps *)

Lemma abses_pullback_homotopic' {A B B' : AbGroup}
      (f f' : B $-> B') (h : f == f')
  : abses_pullback0 (A:=A) f $=> abses_pullback0 f'.
Proof.
  intro E.
  srefine (_; (_, _)).
  - srapply equiv_functor_grp_pullback.
    1-3: exact grp_iso_id.
    1: reflexivity.
    apply h.
  - intro a; cbn.
    by srapply equiv_path_pullback_hset; split.
  - reflexivity.
Defined.

Lemma abses_pullback_phomotopic' {A B B' : AbGroup}
      (f f' : B $-> B') (h : f == f')
  : abses_pullback' (A:=A) f $=>* abses_pullback' f'.
Proof.
  exists (abses_pullback_homotopic' f f' h); cbn.
  intros [[a b'] [b c]]; cbn in c.
  srapply equiv_path_pullback_hset; split; cbn.
  2: reflexivity.
  exact (path_prod' idpath (c @ h b)).
Defined.

Definition abses_pullback_phomotopic `{Univalence} {A B B' : AbGroup}
      (f f' : B $-> B') (h : f == f')
  : abses_pullback (A:=A) f ==* abses_pullback f'
  := equiv_ptransformation_phomotopy (abses_pullback_phomotopic' f f' h).

(** *** Pulling back along a complex *)

Definition iscomplex_abses_pullback' `{Univalence} {A B0 B1 B2 : AbGroup}
           (f : B0 $-> B1) (g : B1 $-> B2) (h : g $o f == grp_homo_const)
  : abses_pullback' f $o* abses_pullback' g $=>* @pmap_abses_const _ _ _ A.
Proof.
  refine (abses_pullback_pcompose' _ _ $@* _).
  refine (abses_pullback_phomotopic' _ _ h $@* _).
  exact abses_pullback_pconst'^*$.
Defined.

Definition iscomplex_abses_pullback `{Univalence} {A B0 B1 B2 : AbGroup}
           (f : B0 $-> B1) (g : B1 $-> B2) (h : g $o f == grp_homo_const)
  : IsComplex (abses_pullback (A:=A) g) (abses_pullback f).
Proof.
  refine (_ @* _).
  2: symmetry; exact pmap_abses_const_to_pointed.
  refine (to_pointed_compose _ _ @* _).
  apply equiv_ptransformation_phomotopy.
  by rapply iscomplex_abses_pullback'.
Defined.

(** A consequence is that pulling back along a short exact sequence forms a complex. *)

Definition iscomplex_pullback_abses `{Univalence} {A B C : AbGroup} (E : AbSES C B)
  : IsComplex (abses_pullback (A:=A) (projection E)) (abses_pullback (inclusion E)).
Proof.
  rapply iscomplex_abses_pullback.
  rapply iscomplex_abses.
Defined.

(** In fact, pulling back along a short exact sequence is (purely) exact. See [AbSES.PullbackFiberSequence]. *)

(** *** Fibers of pullback in terms of path data *)

Definition equiv_hfiber_abses `{Univalence} {X : Type} {A B : AbGroup}
           (f : X -> AbSES B A) (E : AbSES B A)
  : graph_hfiber f E <~> hfiber f E
  := equiv_functor_sigma_id (fun _ => equiv_path_abses_iso).

Definition hfiber_abses_path {A B B' : AbGroup} {f : B' $-> B} {X : AbSES B' A}
           (E F : graph_hfiber (abses_pullback0 f) X)
  := {p : E.1 $-> F.1 & (fmap (abses_pullback0 f) p)^$ $@ E.2 $-> F.2}.

Definition transport_path_data_hfiber_abses_pullback_l `{Univalence} {A B B' : AbGroup} {f : B' $-> B}
           {Y : AbSES B' A} {X0 : graph_hfiber (abses_pullback0 f) Y} {X1 : AbSES B A} (p : X0.1 = X1)
  : transport (fun x : AbSES B A => abses_pullback0 f x $== Y) p X0.2
    = fmap (abses_pullback0 f) (equiv_path_abses_iso^-1 p^) $@ X0.2.
Proof.
  induction p.
  refine (transport_1 _ _ @ _).
  nrefine (_ @ (ap (fun x => x $@ _)) _).
  2: { refine (_ @ ap _ equiv_path_absesV_1^).
       exact (fmap_id_strong _ _)^. }
  exact (cat_idr_strong _)^.
Defined.

Definition equiv_hfiber_abses_pullback `{Univalence} {A B B' : AbGroup} {f : B' $-> B}
           (Y : AbSES B' A) (U V : graph_hfiber (abses_pullback0 f) Y)
  : hfiber_abses_path U V <~> U = V.
Proof.
  refine (equiv_path_sigma _ _ _ oE _).
  srapply (equiv_functor_sigma' equiv_path_abses_iso);
    intro p; lazy beta.
  refine (equiv_concat_l _ _ oE _).
  { refine (transport_path_data_hfiber_abses_pullback_l _ @ _).
    refine (ap (fun x => (fmap (abses_pullback0 f) x) $@ _) _ @ _).
    { refine (ap _ (abses_path_data_V p) @ _).
      apply eissect. }
    refine (ap (fun x => x $@ _) _).
    rapply gpd_strong_1functor_V. }
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_groupisomorphism.
Defined.
