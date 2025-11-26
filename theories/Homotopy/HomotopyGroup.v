From HoTT Require Import Basics Types Pointed HSet.
Require Import Modalities.Modality.
Require Import Truncations.Core Truncations.SeparatedTrunc.
Require Import Algebra.AbGroups.
Require Import WildCat.

Local Open Scope nat_scope.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** The type that the nth homotopy group will have. *)
Definition HomotopyGroup_type (n : nat) : Type
  := match n with
      | 0 => pType
      | n.+1 => Group
     end.

(** Every homotopy group is, in particular, a pointed type. *)
Definition HomotopyGroup_type_ptype (n : nat) : HomotopyGroup_type n -> pType
  := match n return HomotopyGroup_type n -> pType with
     | 0 => fun X => X
     (* This works because [ptype_group] is already a coercion. *)
     | n.+1 => fun G => G
     end.

Coercion HomotopyGroup_type_ptype : HomotopyGroup_type >-> pType.

(** We construct the wildcat structure on [HomotopyGroup_type] in the obvious way. *)
Instance isgraph_homotopygroup_type (n : nat)
  : IsGraph (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Instance is2graph_homotopygroup_type (n : nat)
  : Is2Graph (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Instance is01cat_homotopygroup_type (n : nat)
  : Is01Cat (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Instance is1cat_homotopygroup_type (n : nat)
  : Is1Cat (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Instance is0functor_homotopygroup_type_ptype (n : nat)
  : Is0Functor (HomotopyGroup_type_ptype n)
  := ltac:(destruct n; exact _).
Instance is1functor_homotopygroup_type_ptype (n : nat)
  : Is1Functor (HomotopyGroup_type_ptype n)
  := ltac:(destruct n; exact _).

(** We first define [Pi 1 X], and use this to define [Pi n X].
  The reason is to make it easier for Coq to see that [Pi (n.+1) X] is
  definitionally equal to [Pi 1 (iterated_loops n X)] *)
Definition Pi1 (X : pType) : Group.
Proof.
  srapply (Build_Group (Tr 0 (loops X)));
    repeat split.
  (** Operation *)
  - intros x y.
    strip_truncations.
    exact (tr (x @ y)).
  (** Unit *)
  - exact (tr 1).
  (** Inverse *)
  - srapply Trunc_rec; intro x.
    exact (tr x^).
  (** [IsHSet] *)
  - exact _.
  (** Associativity *)
  - intros x y z.
    strip_truncations.
    cbn; apply ap.
    apply concat_p_pp.
  (** Left identity *)
  - intro x.
    strip_truncations.
    cbn; apply ap.
    apply concat_1p.
  (** Right identity *)
  - intro x.
    strip_truncations.
    cbn; apply ap.
    apply concat_p1.
  (** Left inverse *)
  - intro x.
    strip_truncations.
    apply (ap tr).
    apply concat_Vp.
  (** Right inverse *)
  - intro x.
    strip_truncations.
    apply (ap tr).
    apply concat_pV.
Defined.

(** Definition of the nth homotopy group *)
Definition Pi (n : nat) (X : pType) : HomotopyGroup_type n.
Proof.
  destruct n.
  1: exact (pTr 0 X).
  exact (Pi1 (iterated_loops n X)).
Defined.

(** See [pi_loops] below for an alternate unfolding. *)
Definition pi_succ n X : Pi n.+1 X $<~> Pi 1 (iterated_loops n X)
  := grp_iso_id.

Module PiUtf8.
  Notation "'π'" := Pi.
End PiUtf8.

Instance ishset_pi {n : nat} {X : pType}
  : IsHSet (Pi n X)
  := ltac:(destruct n; exact _).

(** When n >= 2 we have that the nth homotopy group is an abelian group. Note that we don't actually define it as an abelian group but merely show that it is one. This would cause lots of complications with the typechecker. *)
Instance commutative_pi (n : nat) (X : pType)
  : Commutative (A:=Pi n.+2 X) sg_op.
Proof.
  intros x y.
  strip_truncations.
  cbn; apply (ap tr).
  apply eckmann_hilton.
Defined.

(** For the same reason as above, we make [Pi1] a functor before making [Pi] a functor. *)
Instance is0functor_pi1 : Is0Functor Pi1.
Proof.
  apply Build_Is0Functor.
  intros X Y f.
  snapply Build_GroupHomomorphism.
  { tapply (fmap (Tr 0)).
    tapply (fmap loops).
    assumption. }
  (** Note: we don't have to be careful about which paths we choose here since we are trying to inhabit a proposition. *)
  intros x y.
  strip_truncations.
  apply (ap tr); cbn.
  rewrite 2 concat_pp_p.
  apply whiskerL.
  rewrite 2 concat_p_pp.
  rewrite (concat_pp_p (ap f x)).
  rewrite concat_pV, concat_p1.
  rewrite concat_p_pp.
  apply whiskerR.
  apply ap_pp.
Defined.

Instance is0functor_pi (n : nat) : Is0Functor (Pi n)
  := ltac:(destruct n; exact _).

Definition fmap_pi_succ {X Y : pType} (f : X $-> Y) (n : nat)
  : fmap (Pi n.+1) f $== fmap (Pi 1) (fmap (iterated_loops n) f).
Proof.
  reflexivity.
Defined.

Instance is1functor_pi1 : Is1Functor Pi1.
Proof.
  (** The conditions for [Pi1] to be a 1-functor only involve equalities of maps between groups, which reduce to equalities of maps between types.  Type inference shows that [Tr 0 o loops] is a 1-functor, and so it follows that [Pi1] is a 1-functor. *)
  assert (is1f : Is1Functor (Tr 0 o loops)) by exact _.
  apply Build_Is1Functor; intros;
    [ by rapply (fmap2 _ (is1functor_F := is1f))
    | by rapply (fmap_id _ (is1functor_F := is1f))
    | by rapply (fmap_comp _ (is1functor_F := is1f)) ].
Defined.

Instance is1functor_pi (n : nat) : Is1Functor (Pi n)
  := ltac:(destruct n; exact _).

(** Sometimes it is convenient to regard [Pi n] as landing in pointed types.  On objects, this is handled by the coercion [HomotopyGroup_type_ptype], but on morphisms it doesn't seem possible to define a coercion.  So we explicitly name the composite functor. *)
Definition pPi (n : nat) : pType -> pType := HomotopyGroup_type_ptype n o Pi n.
Instance is0functor_ppi (n : nat) : Is0Functor (pPi n) := _.
Instance is1functor_ppi (n : nat) : Is1Functor (pPi n) := _.

(** [pPi] is equal to a more explicit map.  These are definitional for [n = 0] and [n] a successor; it would be nice to make them definitional for generic [n]. *)
Definition ppi_ptr_iterated_loops (n : nat)
  : pPi n = pTr 0 o iterated_loops n
  := ltac:(destruct n; reflexivity).

(** Here is the associated object-wise equivalence, which is the identity map for [0] and successors. *)
Definition pequiv_ppi_ptr_iterated_loops (n : nat) (X : pType)
  : pPi n X <~>* pTr 0 (iterated_loops n X)
  := ltac:(destruct n; exact pequiv_pmap_idmap).

(** These equivalences are natural. Put another way, we can compute [fmap Pi] in terms of the composite functor, up to the equivalences above. For [n = 0] or [n] a successor, we can omit the equivalences; for [n = 0], the induced maps are definitionally equal as pointed maps; for [n] a successfor the underlying unpointed maps are definitionally equal, but the pointedness proofs are not, and this is handled by [phomotopy_homotopy_hset]. *)
Definition fmap_ppi_ptr_iterated_loops (n : nat) {X Y : pType} (f : X ->* Y)
  : pequiv_ppi_ptr_iterated_loops n Y o* fmap (pPi n) f
     ==* fmap (pTr 0) (fmap (iterated_loops n) f) o* pequiv_ppi_ptr_iterated_loops n X.
Proof.
  destruct n; unfold pequiv_ppi_ptr_iterated_loops.
  1: exact (pmap_postcompose_idmap _ @* (pmap_precompose_idmap _)^*).
  refine (pmap_postcompose_idmap _ @* _ @* (pmap_precompose_idmap _)^*).
  srapply phomotopy_homotopy_hset; reflexivity.
Defined.

(** [Pi n.+1] sends equivalences to group isomorphisms. *)
Definition groupiso_pi_functor (n : nat) {X Y : pType} (e : X <~>* Y)
  : Pi n.+1 X $<~> Pi n.+1 Y
  := emap (Pi n.+1) e.

(** The homotopy groups of a loop space are those of the space shifted.  *)
Definition pi_loops n X : Pi n.+1 X <~>* Pi n (loops X).
Proof.
  destruct n.
  1: reflexivity.
  tapply (emap (pTr 0 o loops)).
  apply unfold_iterated_loops'.
Defined.

(** Except in the lowest case, this can be expressed as an isomorphism of groups. *)
Definition groupiso_pi_loops n X : Pi n.+2 X $<~> Pi n.+1 (loops X).
Proof.
  snapply (groupiso_pi_functor 0).
  apply unfold_iterated_loops'.
Defined.

(** Naturality of [pi_loops]. *)
Definition fmap_pi_loops (n : nat) {X Y : pType} (f : X ->* Y)
  : (pi_loops n Y) o* (fmap (Pi n.+1) f)
    ==* (fmap (pPi n o loops) f) o* (pi_loops n X).
Proof.
  destruct n; srapply phomotopy_homotopy_hset; intros x.
  1: reflexivity.
  refine ((O_functor_compose 0 _ _ _)^ @ _ @ (O_functor_compose 0 _ _ _)).
  apply O_functor_homotopy.
  exact (pointed_htpy (unfold_iterated_fmap_loops n.+1 f)).
Defined.

(** Homotopy groups preserve products.  This is a direct proof, but below we give a second proof whose underlying map is the natural one. *)
Definition pi_prod' {n : nat} (X Y : pType)
  : pPi n (X * Y) <~>* (pPi n X) * (pPi n Y).
Proof.
  (* First we re-express this in terms of the composite [pTr 0 o iterated_loops n]. *)
  refine (_ o*E pequiv_ppi_ptr_iterated_loops _ _).
  refine ((equiv_functor_pprod (pequiv_ppi_ptr_iterated_loops _ _)
                               (pequiv_ppi_ptr_iterated_loops _ _))^-1* o*E _).
  (* For this composite, the proof is straightforward. *)
  refine (_ o*E pequiv_ptr_functor 0 _).
  1: napply iterated_loops_prod.
  snapply Build_pEquiv'; cbn.
  - exact (equiv_O_prod_cmp 0 _ _).
  - reflexivity.
Defined.

(** The pointed map from left-to-right below, coming from functoriality, is an equivalence. *)
Definition pi_prod {n : nat} (X Y : pType)
  : pPi n (X * Y) <~>* (pPi n X) * (pPi n Y).
Proof.
  snapply Build_pEquiv.
  (* This describes the natural map. *)
  - rapply (equiv_pprod_coind (pfam_const _) (pfam_const _)); split.
    + exact (fmap (pPi n) (@pfst X Y)).
    + exact (fmap (pPi n) (@psnd X Y)).
  (* To see that it is an equivalence, we show that it is homotopic to [pi_prod']. *)
  - snapply (isequiv_homotopic' (pi_prod' X Y)).
    intro xy.
    destruct n; strip_truncations.
    + apply path_prod; reflexivity.
    + apply path_prod.
      1,2: apply (ap tr).  (* Not obvious, but unfolding makes things cluttered. *)
      * exact (pfst_iterated_loops_prod X Y (n:=n.+1) xy).
      * exact (psnd_iterated_loops_prod X Y (n:=n.+1) xy).
Defined.

(** For positive [n], this equivalence is an isomorphism of groups. *)
Lemma grp_iso_pi_prod {n : nat} (X Y : pType)
  : GroupIsomorphism (Pi n.+1 (X * Y)) (grp_prod (Pi n.+1 X) (Pi n.+1 Y)).
Proof.
  snapply Build_GroupIsomorphism.
  (* The underlying map is the natural one, so it is automatically a group homomorphism. *)
  - apply grp_prod_corec.
    + exact (fmap (Pi n.+1) (@pfst X Y)).
    + exact (fmap (Pi n.+1) (@psnd X Y)).
  (* This is also the underlying map of [pi_prod], so we can reuse the proof that it is an equivalence. *)
  - exact (equiv_isequiv (pi_prod X Y (n:=n.+1))).
Defined.

(** Homotopy groups of truncations *)

(** An [n]-connected map induces an equivalence on the nth homotopy group.  We first state this for [pTr 0 o iterated_loops n], since the proof works for general [n], and then we deduce the result for [pPi n] afterwards. *)
Definition isequiv_pi_connmap' `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  `{!IsConnMap n f}
  : IsEquiv (fmap (pTr 0) (fmap (iterated_loops n) f)).
Proof.
  rapply O_inverts_conn_map.
  rapply conn_map_iterated_fmap_loops.
  rewrite 2 trunc_index_inc'_succ.
  rewrite <- trunc_index_inc_agree.
  assumption.
Defined.

(** The same holds for [pPi n]. *)
Instance isequiv_pi_connmap `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  `{!IsConnMap n f}
  : IsEquiv (fmap (pPi n) f).
Proof.
  (* For [n = 0] and [n] a successor, [fmap (pPi n) f] is definitionally equal to the map in the previous result as a map of types. *)
  destruct n; tapply isequiv_pi_connmap'.
Defined.

Definition pequiv_pi_connmap `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  `{!IsConnMap n f}
  : Pi n X <~>* Pi n Y
  := Build_pEquiv (fmap (pPi n) f) _.

(** For positive [n], it is a group isomorphism. *)
Definition grp_iso_pi_connmap `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  `{!IsConnMap n.+1 f}
  : GroupIsomorphism (Pi n.+1 X) (Pi n.+1 Y)
  := Build_GroupIsomorphism _ _ (fmap (Pi n.+1) f) (isequiv_pi_connmap n.+1 f).

(** As a consequence, the truncation map [ptr : X -> pTr n X] induces an equivalence on [Pi n].  We don't make this an instance, since it is found by typeclass search. *)
Definition isequiv_pi_Tr `{Univalence} (n : nat) (X : pType)
  : IsEquiv (fmap (pPi n) ptr : Pi n X -> Pi n (pTr n X))
  := _.

Definition pequiv_pi_Tr `{Univalence} (n : nat) (X : pType)
  : Pi n X <~>* Pi n (pTr n X)
  := Build_pEquiv (fmap (pPi n) ptr) _.

(** For positive [n], it is a group isomorphism. *)
Definition grp_iso_pi_Tr `{Univalence} (n : nat) (X : pType)
  : GroupIsomorphism (Pi n.+1 X) (Pi n.+1 (pTr n.+1 X))
  := grp_iso_pi_connmap n ptr.

(** An [n]-connected map induces a surjection on [n+1]-fold loop spaces and [Pi (n+1)]. *)
Definition issurj_iterated_loops_connmap `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  {C : IsConnMap n f}
  : IsSurjection (fmap (iterated_loops (n.+1)) f).
Proof.
  apply conn_map_iterated_fmap_loops. cbn.
  rewrite trunc_index_inc'_0n; assumption.
Defined.

Definition issurj_pi_connmap `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  {C : IsConnMap n f}
  : IsConnMap (Tr (-1)) (fmap (pPi n.+1) f).
Proof.
  rapply conn_map_O_functor_strong_leq.
  by apply issurj_iterated_loops_connmap.
Defined.

(** Pointed sections induce embeddings on homotopy groups. *)
Proposition isembedding_pi_psect {n : nat} {X Y : pType}
  (s : X ->* Y) (r : Y ->* X) (k : r o* s ==* pmap_idmap)
  : IsEmbedding (fmap (pPi n) s).
Proof.
  apply isembedding_isinj_hset.
  tapply (isinj_section (r:=fmap (pPi n) r)).
  intro x.
  lhs_V exact (fmap_comp (pPi n) s r x).
  lhs exact (fmap2 (pPi n) k x).
  exact (fmap_id (pPi n) X x).
Defined.

