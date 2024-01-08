Require Import Basics Types Pointed.
Require Import Modalities.ReflectiveSubuniverse Modalities.Modality.
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

(* Every homotopy group is, in particular, a pointed type. *)
Definition HomotopyGroup_type_ptype (n : nat) : HomotopyGroup_type n -> pType
  := match n return HomotopyGroup_type n -> pType with
     | 0 => fun X => X
     (* This works because [ptype_group] is already a coercion. *)
     | n.+1 => fun G => G
     end.

Coercion HomotopyGroup_type_ptype : HomotopyGroup_type >-> pType.

(** We construct the wildcat structure on HomotopyGroup_type in the obvious way. *)
Global Instance isgraph_homotopygroup_type (n : nat)
  : IsGraph (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Global Instance is2graph_homotopygroup_type (n : nat)
  : Is2Graph (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Global Instance is01cat_homotopygroup_type (n : nat)
  : Is01Cat (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Global Instance is1cat_homotopygroup_type (n : nat)
  : Is1Cat (HomotopyGroup_type n) := ltac:(destruct n; exact _).
Global Instance is0functor_homotopygroup_type_ptype (n : nat)
  : Is0Functor (HomotopyGroup_type_ptype n)
  := ltac:(destruct n; exact _).
Global Instance is1functor_homotopygroup_type_ptype (n : nat)
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
  + intros x y.
    strip_truncations.
    exact (tr (x @ y)).
  (** Unit *)
  + exact (tr 1).
  (** Inverse *)
  + srapply Trunc_rec; intro x.
    exact (tr x^).
  (** IsHSet *)
  + exact _.
  (** Associativity *)
  + intros x y z.
    strip_truncations.
    cbn; apply ap.
    apply concat_p_pp.
  (** Left identity *)
  + intro x.
    strip_truncations.
    cbn; apply ap.
    apply concat_1p.
  (** Right identity *)
  + intro x.
    strip_truncations.
    cbn; apply ap.
    apply concat_p1.
  (** Left inverse *)
  + intro x.
    strip_truncations.
    apply (ap tr).
    apply concat_Vp.
  (** Right inverse *)
  + intro x.
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

Definition pi_succ n X : Pi n.+1 X $<~> Pi 1 (iterated_loops n X).
Proof.
  reflexivity.
Defined.

Module PiUtf8.
  Notation "'π'" := Pi.
End PiUtf8.

(** When n >= 2 we have that the nth homotopy group is an abelian group. Note that we don't actually define it as an abelian group but merely show that it is one. This would cause lots of complications with the typechecker. *)
Global Instance isabgroup_pi (n : nat) (X : pType)
  : IsAbGroup (Pi n.+2 X).
Proof.
  nrapply Build_IsAbGroup.
  1: exact _.
  intros x y.
  strip_truncations.
  cbn; apply (ap tr).
  apply eckmann_hilton.
Defined.

(** The nth homotopy group is in fact a functor. We now give the type this functor ought to have. For n = 0, this will simply be a pointed map, for n >= 1 this should be a group homomorphism. *)
Definition pi_functor_type (n : nat) (X Y : pType) : Type
  := match n with
     | 0 => pTr 0 X ->* pTr 0 Y
     | n.+1 => GroupHomomorphism (Pi n.+1 X) (Pi n.+1 Y)
     end.

(* Every such map is, in particular, a pointed map. *)
Definition pi_functor_type_pmap {n X Y}
  : pi_functor_type n X Y -> Pi n X ->* Pi n Y
  := match n return pi_functor_type n X Y -> (Pi n X ->* Pi n Y) with
     | 0 => fun f => f
     (* This works because [pmap_GroupHomomorphism] is already a coercion. *)
     | n.+1 => fun f => f
     end.
Coercion pi_functor_type_pmap : pi_functor_type >-> pForall.

(** For the same reason as for [Pi1] we make [Pi1] a functor before making [Pi] a functor. *)
Global Instance is0functor_pi1 : Is0Functor Pi1.
Proof.
  apply Build_Is0Functor.
  intros X Y f.
  snrapply Build_GroupHomomorphism.
  { rapply (fmap (Tr 0)).
    rapply (fmap loops).
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

Global Instance is0functor_pi (n : nat) : Is0Functor (Pi n)
  := ltac:(destruct n; exact _).

Definition fmap_pi_succ {X Y : pType} (f : X $-> Y) (n : nat)
  : fmap (Pi n.+1) f $== fmap (Pi 1) (fmap (iterated_loops n) f).
Proof.
  reflexivity.
Defined.

Global Instance is1functor_pi1 : Is1Functor Pi1.
Proof.
  (** The conditions for [Pi1] to be a 1-functor only involve equalities of maps between groups, which reduce to equalities of maps between types.  Type inference shows that [Tr 0 o loops] is a 1-functor, and so it follows that [Pi1] is a 1-functor. *)
  assert (is1f : Is1Functor (Tr 0 o loops)) by exact _.
  apply Build_Is1Functor; intros;
    [ by rapply (fmap2 _ (is1functor_F := is1f))
    | by rapply (fmap_id _ (is1functor_F := is1f))
    | by rapply (fmap_comp _ (is1functor_F := is1f)) ].
Defined.

Global Instance is1functor_pi (n : nat) : Is1Functor (Pi n)
  := ltac:(destruct n; exact _).

(** Sometimes it is convenient to regard [Pi n] as landing in pointed types.  On objects, this is handled by the coercion [HomotopyGroup_type_ptype], but on morphisms it doesn't seem possible to define a coercion.  So we explicitly name the composite functor. *)
Definition pPi (n : nat) : pType -> pType := HomotopyGroup_type_ptype n o Pi n.
Global Instance is0functor_ppi (n : nat) : Is0Functor (pPi n) := _.
Global Instance is1functor_ppi (n : nat) : Is1Functor (pPi n) := _.

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
  1: refine (pmap_postcompose_idmap _ @* (pmap_precompose_idmap _)^*).
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
  rapply (emap (pTr 0 o loops)).
  apply unfold_iterated_loops'.
Defined.

(** Except in the lowest case, this can be expressed as an isomorphism of groups. *)
Definition groupiso_pi_loops n X : Pi n.+2 X $<~> Pi n.+1 (loops X).
Proof.
  snrapply (groupiso_pi_functor 0).
  apply unfold_iterated_loops'.
Defined.

(** Naturality of [pi_loops]. *)
Definition fmap_pi_loops (n : nat) {X Y : pType} (f : X ->* Y)
  : (pi_loops n Y) o* (fmap (Pi n.+1) f)
    ==* (fmap (HomotopyGroup_type_ptype n o Pi n o loops) f)
        o* (pi_loops n X).
Proof.
  destruct n; srapply phomotopy_homotopy_hset; intros x.
  1: reflexivity.
  refine ((O_functor_compose 0 _ _ _)^ @ _ @ (O_functor_compose 0 _ _ _)).
  apply O_functor_homotopy.
  exact (pointed_htpy (unfold_iterated_fmap_loops n.+1 f)).
Defined.

(** Homotopy groups preserve products *)
Lemma pi_prod (X Y : pType) {n : nat}
  : GroupIsomorphism (Pi n.+1 (X * Y))
      (grp_prod (Pi n.+1 X) (Pi n.+1 Y)).
Proof.
  srapply Build_GroupIsomorphism'.
  { refine (equiv_O_prod_cmp _ _ _ oE _).
    apply Trunc_functor_equiv.
    refine (iterated_loops_prod (n := n.+1) _ _). }
  intros x y.
  strip_truncations; simpl.
  set (Z := (iterated_loops_prod X Y)).
  apply path_prod.
  1,2: apply (ap tr).
  1: set (q := ap fst); unfold fst; unfold q; clear q.
  2: set (q := ap snd); unfold snd; unfold q; clear q.
  1,2: rewrite 8 ap_pp.
  1,2: rewrite ? concat_p_pp.
  1,2: do 2 apply whiskerR.
  1,2: rewrite ? ap_V.
  1,2: rewrite concat_pp_p.
  1,2: rewrite concat_pV.
  1,2: rewrite concat_p1.
  1,2: reflexivity.
Defined.

(** Can we make this reflexivity? *)
Lemma pmap_pi_functor {X Y : pType} (f : X ->* Y) (n : nat) 
  : fmap (Pi n.+1) f
    ==* fmap (pTr 0) (fmap (iterated_loops n.+1) f).
Proof.
  srapply phomotopy_homotopy_hset; reflexivity.
Defined.

(** Homotopy groups of truncations *)

(** An [n]-connected map induces an equivalence on the nth homotopy group.  We first state this for [pTr 0 o iterated_loops n], since the proof works for general [n], and then we deduce the result for [pPi n] afterwards. *)
Definition isequiv_pi_connmap' `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  `{!IsConnMap n f}
  : IsEquiv (fmap (pTr 0) (fmap (iterated_loops n) f)).
Proof.
  rapply O_inverts_conn_map.
  rapply isconnected_iterated_fmap_loops.
  rewrite 2 trunc_index_inc'_succ.
  rewrite <- trunc_index_inc_agree.
  assumption.
Defined.

(** The same holds for [pPi n]. *)
Global Instance isequiv_pi_connmap `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  `{!IsConnMap n f}
  : IsEquiv (fmap (pPi n) f).
Proof.
  (* For [n = 0] and [n] a successor, [fmap (pPi n) f] is definitionally equal to the map in the previous result as a map of types. *)
  destruct n; rapply isequiv_pi_connmap'.
Defined.

(** For positive [n], it is a group isomorphism. *)
Definition grp_iso_pi_connmap `{Univalence} (n : nat) {X Y : pType} (f : X ->* Y)
  `{!IsConnMap n.+1 f}
  : GroupIsomorphism (Pi n.+1 X) (Pi n.+1 Y)
  := Build_GroupIsomorphism _ _ (fmap (Pi n.+1) f) (isequiv_pi_connmap n.+1 f).

(** As a consequence, the truncation map [ptr : X -> pTr n X] induces an equivalence on [Pi n].  We don't make this an instance, since it is found by typeclass search. *)
Definition isequiv_pi_Tr `{Univalence} (n : nat) (X : pType)
  : IsEquiv (fmap (pPi n) ptr : Pi n X -> Pi n (pTr n X))
  := _.

(** For positive [n], it is a group isomorphism. *)
Definition grp_iso_pi_Tr `{Univalence} (n : nat) (X : pType)
  : GroupIsomorphism (Pi n.+1 X) (Pi n.+1 (pTr n.+1 X))
  := grp_iso_pi_connmap n ptr.
