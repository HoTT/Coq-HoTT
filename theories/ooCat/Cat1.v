(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Cat0.

(** * 1-coherent oo-categories *)

Generalizable Variables m n p A B C.

(** ** 1-coherent oo-functors *)

CoInductive IsFunctor1 {m A n B} `{IsCat0 m A} `{HasEquivs n B}
            (F : A -> B) {ff : IsFunctor0 F} : Type :=
{
  fmap_id : forall (a : A), fmap F (cat_id a) $<~> cat_id (F a) ;
  fmap_comp : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      fmap F (g $o f) $<~> fmap F g $o fmap F f ;
  isfunctor1_fmap : forall (a b : A),
      @IsFunctor1 _ (a $-> b) _ (F a $-> F b) _ _ _ _ _ (fmap' F a b) _ ;
}.

(** TODO: Generalize to sections.  Requires having displayed categories with equivalences. *)

Existing Class IsFunctor1.
Arguments fmap_id {m A n B _ _ _ _ _} F {_ _} a.
Arguments fmap_comp {m A n B _ _ _ _ _} F {_ _ a b c} f g.
Global Existing Instance isfunctor1_fmap.

Hint Extern 1 (@IsFunctor1 ?m (Hom _ _ _) _ _ _ _ _ _ _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@IsFunctor1 ?m (Hom _ _ _) _ _ _ _ _ _ _ _ _) => change_dim_0 m : typeclass_instances.
Hint Extern 1 (@IsFunctor1 _ _ ?n _ _ _ _ _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@IsFunctor1 _ _ ?n _ _ _ _ _ _ _ _) => change_dim_0 n : typeclass_instances.


(** ** 1-coherent oo-categories *)

(** As before, we have to choose what "1-coherent" means.  At the moment we are choosing "whatever is necessary to have a good theory of equivalences", which is somewhere in between the two principled choices. *)
CoInductive IsCat1 (n : nat) (A : Type) `{HasEquivs n A} :=
{
  cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $<~> h $o (g $o f) ;
  cat_idl : forall (a b : A) (f : a $-> b), cat_id b $o f $<~> f ;
  cat_idr : forall (a b : A) (f : a $-> b), f $o cat_id a $<~> f ;
  gpd_issect : forall (isz : IsZeroNat n) (a b : A) (f : a $-> b),
      f^$ $o f $<~> cat_id a ;
  gpd_isretr : forall (isz : IsZeroNat n) (a b : A) (f : a $-> b),
      f $o f^$ $<~> cat_id b ;
  isfunctor1_postcomp : forall (a b c : A) (g : b $-> c),
      IsFunctor1 (cat_postcomp a g) ;
  isfunctor1_precomp : forall (a b c : A) (f : a $-> b),
      IsFunctor1 (cat_precomp c f) ;
  iscat1_hom : forall (a b : A), @IsCat1 (pred n) (a $-> b) _ _ _ ;
}.

Existing Class IsCat1.
Arguments cat_assoc {n A _ _ _ _ a b c d} f g h.
Arguments cat_idl {n A _ _ _ _ a b} f.
Arguments cat_idr {n A _ _ _ _ a b} f.
Arguments gpd_issect {n A _ _ _ _ _ a b} f.
Arguments gpd_isretr {n A _ _ _ _ _ a b} f.
Global Existing Instances
       iscat1_hom isfunctor1_postcomp isfunctor1_precomp.

Hint Extern 1 (IsCat1 ?n _) => change_dim n : typeclass_instances.
Hint Extern 1 (IsCat1 ?n _) => change_dim_0 n : typeclass_instances.


(** ** Equivalences *)

(** Now we can prove more about equivalences. *)

(** Every morphism in a groupoid is an equivalence *)
Global Instance isqiso_gpd `{IsCat1 0 A}
       {a b : A} (f : a $-> b)
  : IsQIso f.
Proof.
  unshelve econstructor.
  - exact (gpd_inv f).
  - exact (gpd_issect f).
  - exact (gpd_isretr f).
  - exact _.
  - exact _.
Defined.

Global Instance catie_gpd `{IsCat1 0 A}
       {a b : A} (f : a $-> b)
  : CatIsEquiv f.
Proof.
  apply catie_isqiso; exact _.
Defined.

(** We can "adjointify" in the usual way with equivalences in the next dimension.  Note that the possibility of adjointification was basically built into the definition of [HasEquivs]; in concrete cases it needs to be proven. *)
Definition catie_adjointify `{HasEquivs n A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (s : g $o f $<~> cat_id a) (r : f $o g $<~> cat_id b)
  : CatIsEquiv f.
Proof.
  apply catie_isqiso; unshelve econstructor; intros.
  - exact g.
  - exact s.
  - exact r.
  - exact _.
  - exact _.
Defined.

Definition cate_adjointify `{HasEquivs n A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (s : g $o f $<~> cat_id a) (r : f $o g $<~> cat_id b)
  : a $<~> b
  := Build_CatEquiv f (catie_adjointify f g s r).

(** The identity is an equivalence. *)
Global Instance catie_id `{IsCat1 n A} (a : A)
  : CatIsEquiv (cat_id a).
Proof.
  srapply catie_adjointify.
  1:apply cat_id.
  all:apply cat_idl.
Defined.

Definition cate_id `{IsCat1 n A} (a : A)
  : a $<~> a
  := Build_CatEquiv (cat_id a) _.

Global Instance reflexive_cate `{IsCat1 n A}
  : Reflexive (@CatEquiv n A _ _ _)
  := cate_id.

(** We use the equivalence inverse notation only in the bundled case. *)
Notation "f ^-1$" := (cate_inverse f).

Global Instance symmetric_cate `{IsCat1 n A}
  : Symmetric (@CatEquiv n A _ _ _)
  := @cate_inverse n A _ _ _.

(** TODO: Consider adjointifying one the following two lemmas so that they satisfy an [isadj] coherence.  If we do that, it would be nice to give the user a way to specify that a particular notion of equivalence (e.g. [IsEquiv] for [Type]) is already adjointified, so that in that case these lemmas can preserve the homotopies supplied by the user. *)

Definition cate_issect `{HasEquivs n A} {a b : A} (f : a $<~> b)
  : f^-1$ $o f $<~> cat_id a.
Proof.
  exists (qiso_issect f).
  rapply catie_isqiso.
Defined.

Definition cate_isretr `{HasEquivs n A} {a b : A} (f : a $<~> b)
  : f $o f^-1$ $<~> cat_id b.
Proof.
  exists (qiso_isretr f).
  rapply catie_isqiso.
Defined.

(** Equivalences are closed under composition and preserved by 1-coherent functors.  Note that for this to go through, we need [IsCat1] to include 1-coherent functoriality of composition.

This is a mutual induction on [n], which of course requires [n] to be finite.  It can also be proven for (oo,oo)-categories using coinduction rather than induction, but that would require some complicated shenanigans to convince Coq to accept because Coq's guardedness checker for cofixpoints is more rudimentary.

Note also that like many "chaining equivalence" proofs, this proof is substantially simpler when written for bundled [CatEquiv]s rather than unbundled [CatIsEquiv]s.  Below we will deduce the corresponding results for the latter -- and, for technical reasons, redefine these afterwards. *)
Local Fixpoint cate_compose_temp {n : nat} `{IsCat1 n A}
         {a b c : A} (f : a $<~> b) (g : b $<~> c) {struct n}
  : a $<~> c
with cate_fmap_temp {m n : nat} `{HasEquivs m A} `{IsCat1 n B}
               (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
               {a b : A} (f : a $<~> b) {struct n}
     : F a $<~> F b.
Proof.
  - snrapply Build_CatEquiv.
    1:exact (g $o f).
    destruct n; [ by apply catie_gpd | snrapply catie_adjointify ].
    + exact (f^-1$ $o g^-1$).
    + refine (cate_compose_temp _ _ _ _ _ _ _ _ _ (cat_assoc _ _ _) _).
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ _ (cate_issect f)).
      refine (cate_fmap_temp _ _ _ _ _ _ _ _ _ _ _
                        (cat_postcomp _ _) _ _ _ _ _).
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ (cat_assoc _ _ _)^-1$ _).
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ _ (cat_idl f)).
      refine (cate_fmap_temp _ _ _ _ _ _ _ _ _ _ _
                        (cat_precomp _ _) _ _ _ _ _).
      apply cate_issect.
    + refine (cate_compose_temp _ _ _ _ _ _ _ _ _ (cat_assoc _ _ _) _).
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ _ (cate_isretr g)).
      refine (cate_fmap_temp _ _ _ _ _ _ _ _ _ _ _
                        (cat_postcomp _ _) _ _ _ _ _).
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ (cat_assoc _ _ _)^-1$ _).
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ _ (cat_idl g^-1$)).
      refine (cate_fmap_temp _ _ _ _ _ _ _ _ _ _ _
                        (cat_precomp _ _) _ _ _ _ _).
      apply cate_isretr.
  - snrapply Build_CatEquiv.
    1:exact (fmap F f).
    destruct n; [ by apply catie_gpd | snrapply catie_adjointify ].
    + exact (fmap F f^-1$).
    + refine (cate_compose_temp _ _ _ _ _ _ _ _ _ (fmap_comp _ _ _)^-1$ _). 
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ _ (fmap_id _ _)). 
      refine (cate_fmap_temp _ _ _ _ _ _ _ _ _ _ _ (fmap F) _ _ _ _ _).
      apply cate_issect.
    + refine (cate_compose_temp _ _ _ _ _ _ _ _ _ (fmap_comp _ _ _)^-1$ _). 
      refine (cate_compose_temp _ _ _ _ _ _ _ _ _ _ (fmap_id _ _)). 
      refine (cate_fmap_temp _ _ _ _ _ _ _ _ _ _ _ (fmap F) _ _ _ _ _).
      apply cate_isretr.
Defined.

(** Because the underlying morphism of [g $oE f] is, by definition [g $o f] -- at least after [n] is destructed -- we can easily deduce the corresponding facts about unbundled equivalences. *)
Global Instance catie_compose `{IsCat1 n A}
       {a b c : A} (f : a $-> b) (g : b $-> c)
       `{!CatIsEquiv f} `{!CatIsEquiv g}
  : CatIsEquiv (g $o f).
Proof.
  destruct n; [ apply catie_gpd | ].
  pose (f' := Build_CatEquiv f _).
  pose (g' := Build_CatEquiv g _).
  change (CatIsEquiv (cate_compose_temp f' g')).
  exact _.
Defined.

(** Now we redefine [cate_compose] globally by re-bundling this up.  The point of this is so that its underlying function computes definitionally without having to destruct [n] first.  (I'm not sure whether there is a way to set it up so that the underlying *inverse* function also computes definitionally.) *)
Definition cate_compose {n : nat} `{IsCat1 n A}
         {a b c : A} (f : a $<~> b) (g : b $<~> c)
  : a $<~> c.
Proof.
  snrapply Build_CatEquiv.
  - exact (g $o f).
  - exact _.
Defined.

Notation "g $oE f" := (cate_compose f g).

Global Instance transitive_cate `{IsCat1 n A}
  : Transitive (@CatEquiv n A _ _ _)
  := @cate_compose n A _ _ _ _.

(** We do the same for functors. *)

Global Instance catie_fmap `{HasEquivs m A} `{IsCat1 n B}
       (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
       {a b : A} (f : a $-> b) `{!CatIsEquiv f}
  : CatIsEquiv (fmap F f).
Proof.
  destruct n; [ apply catie_gpd | ].
  pose (f' := Build_CatEquiv f _).
  change (CatIsEquiv (cate_fmap_temp F f')).
  exact _.
Defined.

Definition cate_fmap {m n : nat} `{HasEquivs m A} `{IsCat1 n B}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
           {a b : A} (f : a $<~> b)
  : F a $<~> F b.
Proof.
  snrapply Build_CatEquiv.
  - exact (fmap F f).
  - exact _.
Defined.

Notation cate_fmap' F a b := (@cate_fmap _ _ _ _ _ _ _ _ _ _ _ F _ _ a b) (only parsing).

(** Hence equivalences are also closed under whiskering. *)
Definition cate_postwhisker `{IsCat1 n A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $<~> g)
  : h $o f $<~> h $o g
  := cate_fmap (cat_postcomp a h) p.

Notation "h $<oE p" := (cate_postwhisker h p) (at level 30).

Definition cate_prewhisker `{IsCat1 n A} {a b c : A}
           {f g : b $-> c} (p : f $<~> g) (h : a $-> b)
  : f $o h $<~> g $o h
  := cate_fmap (cat_precomp c h) p.

Notation "p $o>E h" := (cate_prewhisker p h) (at level 30).

Definition cate_postcomp `{IsCat1 n A}
           (a : A) {b c : A} (g : b $<~> c)
  : (a $<~> b) -> (a $<~> c)
  := fun f => g $oE f.

Definition cate_precomp `{IsCat1 n A}
           {a b : A} (c : A) (f : a $<~> b)
  : (b $<~> c) -> (a $<~> c)
  := fun g => g $oE f.

Global Instance isfunctor0_cate_postcompose
       {n : nat} `{IsCat1 n A}
       {a b c : A} (g : b $<~> c)
  : IsFunctor0 (cate_postcomp a g).
Proof.
  snrapply Build_IsFunctor0.
  - intros p q r; cbn.
    exact (g $<o r).
  - intros; cbn; exact _.
Defined.

Global Instance isfunctor0_cate_precompose
       {n : nat} `{IsCat1 n A}
       {a b c : A} (f : a $<~> b)
  : IsFunctor0 (cate_precomp c f).
Proof.
  snrapply Build_IsFunctor0.
  - intros p q r; cbn.
    exact (r $o> f).
  - intros g h; cbn.
    rapply isfunctor0_fmap.
Defined.

Global Instance isfunctor1_cate_postcompose
       {n : nat} `{IsCat1 n A}
       {a b c : A} (g : b $<~> c)
  : IsFunctor1 (cate_postcomp a g).
Proof.
  snrapply Build_IsFunctor1.
  - intros f. cbn.
    nrapply fmap_id; exact _.
  - intros f h k p q. cbn.
    nrapply fmap_comp; exact _.
  - intros; cbn.
    nrapply isfunctor1_fmap.
    exact _.
Defined.

Global Instance isfunctor1_cate_precompose
       {n : nat} `{IsCat1 n A}
       {a b c : A} (f : a $<~> b)
  : IsFunctor1 (cate_precomp c f).
Proof.
  snrapply Build_IsFunctor1.
  - intros g. cbn.
    rapply (fmap_id (cat_precomp c f)).
  - intros g h k p q. cbn.
    rapply (fmap_comp (cat_precomp c f)).
  - intros; cbn.
    nrapply isfunctor1_fmap.
    exact _.
Defined.

Global Instance isfunctor0_cate_fmap
       {m n : nat} `{HasEquivs m A} `{IsCat1 n B}
       (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F} (a b : A)
  : IsFunctor0 (cate_fmap' F a b).
Proof.
  snrapply Build_IsFunctor0.
  - intros f g p; cbn.
    exact (fmap (fmap F) p).
  - intros; cbn; exact _.
Defined.

Global Instance isfunctor1_cate_fmap
       {m n : nat} `{HasEquivs m A} `{IsCat1 n B}
       (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F} (a b : A)
  : IsFunctor1 (cate_fmap' F a b).
Proof.
  snrapply Build_IsFunctor1.
  - intros f; cbn.
    apply fmap_id. exact _.
  - intros f g h p q; cbn.
    apply fmap_comp. exact _.
  - intros f g.
    change (IsFunctor1 (fmap' (fmap' F a b) f g)).
    exact _.
Defined.

(** ** Constant 1-coherent functors *)

CoFixpoint isfunctor1_const `{IsCat0 m A} `{IsCat1 n B} (x : B)
  : IsFunctor1 (@const A B x).
Proof.
  snrapply Build_IsFunctor1.
  { intro a.
    reflexivity. }
  { intros a b c f g.
    symmetry.
    cbn.
    apply cat_idl. }
  intros a b.
  rapply isfunctor1_const.
Defined.

Global Existing Instance isfunctor1_const.


(** ** Composition of 1-coherent functors *)

CoFixpoint isfunctor1_idmap `{IsCat1 m A}
  : @IsFunctor1 m A m A _ _ _ _ _ idmap _.
Proof.
  rapply Build_IsFunctor1; intros; reflexivity.
Defined.

(** We can now prove that 1-coherent functors compose.  *)
CoFixpoint isfunctor1_compose `{IsCat1 m A} `{IsCat1 n B} `{IsCat1 p C}
           (G : B -> C) `{!IsFunctor0 G, !IsFunctor1 G}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
  : IsFunctor1 (G o F).
Proof.
  unshelve econstructor.
  - intros a.
    refine (_ $oE cate_fmap (fmap G) (fmap_id F a)).
    exact (fmap_id G (F a)).
  - intros a b c f g.
    refine (_ $oE cate_fmap (fmap G) (fmap_comp F f g)).
    exact (fmap_comp G (fmap F f) (fmap F g)).
  - intros a b; cbn. 
    exact (isfunctor1_compose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmap G) _ _ (fmap F) _ _).
Defined.

Global Existing Instances isfunctor1_idmap isfunctor1_compose.


(** ** Induced 1-coherent categories *)

(** This requires that identity maps are equivalences! *)
Global Instance isfunctor1_induced {A} `{IsCat1 n B} (F : A -> B)
  : @IsFunctor1 n A n B _ (iscat0_induced F) _ _ _ F _.
Proof.
  srapply Build_IsFunctor1; cbn; intros; reflexivity.
Defined.

Definition iscat1_induced {A} `{IsCat1 n B} (F : A -> B)
  : @IsCat1 n A _ _ (hasequivs_induced F).
Proof.
  unshelve econstructor; cbn; intros.
  - apply cat_assoc.
  - apply cat_idl.
  - apply cat_idr.
  - apply gpd_issect.
  - apply gpd_isretr.
  - apply (@isfunctor1_postcomp n B _ _ _ _ (F _)).
  - apply (@isfunctor1_precomp n B _ _ _ _ _ _ (F _)).
  - exact _.
Defined.

Global Instance iscat1_catequiv `{IsCat1 m A} (a b : A)
  : IsCat1 (pred m) (a $<~> b)
  := iscat1_induced (@cate_fun _ _ _ _ _ a b).



(** ** Bi-invertible maps revisited *)

(** Bi-invertible maps are equivalences *)
Fixpoint catie_biinv {n : nat} {A : Type} `{IsCat1 n A}
         {a b : A} (f : a $-> b) (fe : CatBiInv f) {struct n}
  : CatIsEquiv f.
Proof.
  destruct n as [|n].
  1:exact _.
  assert (fissect : catbiinv_retr f fe $o f $<~> cat_id a).
  { snrapply Build_CatEquiv.
    + apply catbiinv_issect.
    + nrapply catie_biinv; try exact _.
      apply catbiinv_catbiinv_issect. }
  assert (fisretr : f $o catbiinv_sect f fe $<~> cat_id b).
  { snrapply Build_CatEquiv.
    + apply catbiinv_isretr.
    + nrapply catie_biinv; try exact _.
      apply catbiinv_catbiinv_isretr. }
  snrapply catie_adjointify.
  - exact (catbiinv_retr f fe).
  - apply fissect.
  - refine (fisretr $oE _).
    refine (f $<oE _).
    refine (cat_idl _ $oE _ $oE (cat_idr _)^-1$).
    refine ((fissect $o>E _) $oE _ $oE (_ $<oE fisretr)^-1$).
    symmetry; apply cat_assoc.
Defined.

(** This gives us the "default" instance of [HasEquivs] that uses bi-invertibility. *)
CoFixpoint hasequivs_nudge_to_biinv `{IsCat1 n A}
  : HasEquivs n A.
Proof.
  unshelve econstructor.
  - intros a b f; exact (CatBiInv f).
  - intros a b f ?; apply biinv_isqiso; assumption.
  - intros a b f ?; apply isqiso_catie, catie_biinv; assumption.
  - intros a b; rapply hasequivs_nudge_to_biinv.
Defined.

CoFixpoint isfunctor1_nudge_to_biinv `{IsCat1 m A, IsCat1 n B}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
  : @IsFunctor1 _ _ _ _ _ _ _ _ hasequivs_nudge_to_biinv F _.
Proof.
  unshelve econstructor; intros.
  3: rapply isfunctor1_nudge_to_biinv.
  all: snrapply Build_CatEquiv.
  1: apply fmap_id; exact _.
  2: apply fmap_comp; exact _.
  all: cbn; apply catie_isqiso.
  all: apply isqiso_catie; exact _.
Defined.

CoFixpoint iscat1_nudge_to_biinv `{IsCat1 n A}
  : @IsCat1 n A _ _ hasequivs_nudge_to_biinv.
Proof.
  unshelve econstructor; intros.
  1-5: snrapply Build_CatEquiv.
  1: apply cat_assoc.
  2: apply cat_idl.
  3: apply cat_idr.
  4: apply gpd_issect.
  5: apply gpd_isretr.
  1-5: cbn; apply catie_isqiso.
  1-5: cbn; apply isqiso_catie; exact _.
  1-2: rapply isfunctor1_nudge_to_biinv.
  cbn. (** This does something to the invisible implicit arguments; without it the corecursive call ends up unguarded. *)
  apply iscat1_nudge_to_biinv.
Defined.

(** If you want to use the default biinv as the [HasEquivs] for some wild category, after defining the [IsGlob] and [IsCat0] instances, construct an instance of the following class.  Its field is an [IsCat1] but is *not* declared as an instance; instead we have the following two instances that extract the intended structure. *)

Class IsCat1_Default n A `{IsCat0 n A}
  := { iscat1_default : @IsCat1 n A _ _ (hasequivs_with_isqiso n A) }.

Global Instance hasequivs_with_biinv `(ac : IsCat1_Default n A)
  : HasEquivs n A | 100.
Proof.
  rapply hasequivs_nudge_to_biinv. 
  apply iscat1_default.
Defined.

Global Instance iscat1_with_biinv `(ac : IsCat1_Default n A)
  : @IsCat1 n A _ _ (hasequivs_with_biinv ac) | 100. 
Proof.
  rapply iscat1_nudge_to_biinv.
Defined.
