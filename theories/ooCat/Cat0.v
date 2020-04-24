(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Glob.

(** * 0-coherent oo-categories *)

Generalizable Variables m n p A B C.

(** ** Basic definition *)

(** The implicit oo-category convention is in effect: [IsCat0 n] means "is an (oo,n)-category".  The postfix "0" means "0-coherent".  There are different choices about what this could mean:

- It could mean "having only the structure of a (0,n)-category at each dimension": composition, identities, and in the case [n=0] inversion, but no axioms.
- It could mean the maximal difference in dimension between the inputs and outputs of operations is 0, so it has all operations but no axioms.

We currently choose the latter, which happens to also be "everything that can be stated without referring to equivalences". *)
CoInductive IsCat0 (n : nat) (A : Type) `{IsGlob n A} : Type :=
{
  cat_id : forall (a : A), a $-> a ;
  cat_comp : forall {a b c : A},
      (b $-> c) -> (a $-> b) -> (a $-> c) where "g $o f" := (cat_comp g f);
  isfunctor0_postcomp : forall (a b c : A) (g : b $-> c),
      IsFunctor0 (fun f : a $-> b => g $o f) ;
  isfunctor0_precomp : forall (a b c : A) (f : a $-> b),
      IsFunctor0 (fun g : b $-> c => g $o f) ;
  gpd_inv : forall (isz : IsZeroNat n) (a b : A),
      (a $-> b) -> (b $-> a) ;
  iscat0_hom : forall (a b : A), @IsCat0 (pred n) (a $-> b) _ ;
}.

Existing Class IsCat0.
Arguments cat_id {n A _ _} a.
Arguments cat_comp {n A _ _ a b c} g f.
Notation "g $o f" := (cat_comp g f).

(** When we're in a groupoid dimension, we use path-like syntax. *)
Arguments gpd_inv {n A _ _ _ a b} f.
Notation "f ^$" := (gpd_inv f).
Notation "f $@ g" := (@cat_comp 0 _ _ _ _ _ _ g f).

Global Existing Instances
       iscat0_hom isfunctor0_postcomp isfunctor0_precomp.

Hint Extern 1 (IsCat0 ?n (Hom _ _ _)) => change_dim n : typeclass_instances.
Hint Extern 1 (IsCat0 ?n (Hom _ _ _)) => change_dim_0 n : typeclass_instances.

Definition cat_postcomp `{IsCat0 n A}
           (a : A) {b c : A} (g : b $-> c)
  : (a $-> b) -> (a $-> c)
  := fun f => g $o f.

Definition cat_precomp `{IsCat0 n A}
           {a b : A} (c : A) (f : a $-> b)
  : (b $-> c) -> (a $-> c)
  := fun g => g $o f.

Definition cat_postwhisker `{IsCat0 n A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $-> g)
  : h $o f $-> h $o g
  := fmap (cat_postcomp a h) p.
Notation "h $<o p" := (cat_postwhisker h p).

Definition cat_prewhisker `{IsCat0 n A} {a b c : A}
           {f g : b $-> c} (p : f $-> g) (h : a $-> b)
  : f $o h $-> g $o h
  := fmap (cat_precomp c h) p.
Notation "p $o> h" := (cat_prewhisker p h).

(* These seem to be unnecessary; I guess [cat_postcomp] and [cat_precomp] are sufficiently transparent to typeclass search. *)
(*
Global Instance isfunctor0_postcomp' `{IsCat0 n A}
       {a b c : A} (g : b $-> c)
  : IsFunctor0 (cat_postcomp a g).
Proof. 
  exact _.
Defined.

Global Instance isfunctor0_precomp' `{IsCat0 n A}
       {a b c : A} (f : a $-> b)
  : IsFunctor0 (cat_precomp c f).
Proof.
  exact _.
Defined.
*)

Definition iscat0_induced {A} `{IsCat0 n B} (F : A -> B)
  : @IsCat0 n A (isglob_induced F).
Proof.
  unshelve econstructor; cbn; intros.
  - eapply cat_comp; eassumption.
  - apply cat_id.
  - exact _.
  - exact _.
  - apply gpd_inv; assumption.
  - exact _.
Defined.

(** ** Constant functors *)

CoFixpoint isfunctor0_const `{IsGlob m A} `{IsCat0 n B} (x : B)
  : IsFunctor0 (@const A B x).
Proof.
  simple notypeclasses refine (Build_IsFunctor0 _ _ _).
  { intros a b f.
    apply cat_id. }
  intros a b.
  rapply isfunctor0_const.
Defined.

Global Existing Instance isfunctor0_const.


(** ** Truncatedness and invertibility *)

(** Truncatedness can be used as a cap on the invertibility dimension *)
CoFixpoint iscat0_cattrunc
       {n : nat} `{IsCat0 m A} `{!CatTrunc n.-1 A}
  : @IsCat0 n A isglob_reindex.
Proof.
  unshelve econstructor.
  1: clear iscat0_cattrunc; intros a b c; cbn; apply cat_comp.
  1: clear iscat0_cattrunc; intros; cbn; apply cat_id.
  1-2: intros; cbn;
    apply (@isfunctor0_reindex (pred m) (pred m) (pred n) (pred n));
    exact _.
  - destruct n as [|[|n]]; cbn in *.
    1:intros; rapply cat_center.
    1-2:intros [].
  - intros; cbn.
    rapply (iscat0_cattrunc (pred n) (pred m) (a $-> b)).
    destruct n as [|n]; cbn in *.
    + apply cattrunc_pred.
    + exact _.
Defined.

(** ** Quasi-isomorphisms *)

(** A morphism in an (oo,n)-category is an equivalence if either [n=0] or if it has an inverse up to equivalence.  Since this is not a coherent structure, we denigrate it with the name "quasi-isomorphism".  We define it coinductively, but in practice it suffices to reason about it inductively since all our categories are (oo,n)-categories for some finite n. *)

CoInductive IsQIso `{IsCat0 n A} {a b : A} (f : a $-> b) :=
{
  qiso_inv : b $-> a ;
  qiso_issect : (qiso_inv $o f) $-> (cat_id a) ;
  qiso_isretr : (f $o qiso_inv) $-> (cat_id b) ;
  isqiso_qiso_issect : @IsQIso _ (a $-> a) _ _ _ _ qiso_issect ;
  isqiso_qiso_isretr : @IsQIso _ (b $-> b) _ _ _ _ qiso_isretr ;
}.
Existing Class IsQIso.
Arguments qiso_inv {n A _ _ a b} f {_}.
Arguments qiso_issect {n A _ _ a b} f {_}.
Arguments qiso_isretr {n A _ _ a b} f {_}.
Global Existing Instances isqiso_qiso_issect isqiso_qiso_isretr.

Hint Extern 1 (@IsQIso ?n (Hom _ _ _) _ _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@IsQIso ?n (Hom _ _ _) _ _ _ _ _) => change_dim_0 n : typeclass_instances.

(** The inverse of a quasi-isomorphism is a quasi-isomorphism. *)
Global Instance isqiso_inv `{IsCat0 n A}
       {a b : A} (f : a $-> b) `{!IsQIso f}
  : IsQIso (qiso_inv f).
Proof.
  unshelve econstructor.
  1: exact f.
  1: exact (qiso_isretr f).
  1: exact (qiso_issect f).
  all: exact _.
Defined.

(** Every morphism in a (-2)- or (-1)-truncated category is a quasi-isomorphism. *)
CoFixpoint isqiso_catcontr `{IsCat0 n A, !CatContr A}
           {a b : A} (f : a $-> b)
  : IsQIso f.
Proof.
  unshelve econstructor.
  1-3:apply cat_center.
  1-2:rapply isqiso_catcontr.
Defined.
Global Existing Instance isqiso_catcontr.

Global Instance isqiso_catprop `{IsCat0 n A, !CatProp A}
       {a b : A} (f : a $-> b)
  : IsQIso f.
Proof.
  unshelve econstructor.
  1-3:apply cat_center.
  1-2:apply isqiso_catcontr.
Defined.

(** It follows that in a 0-truncated category, having maps back and forth suffices. *)
Global Instance isqiso_catposet `{IsCat0 n A, !CatPoset A}
       {a b : A} (f : a $-> b) (g : b $-> a)
  : IsQIso f.
Proof.
  unshelve econstructor.
  1:exact g.
  1-2:apply cat_center.
  1-2:apply isqiso_catprop.
Defined.

(** And in a truncated (1,1)-category, an ordinary "isomorphism" suffices. *)
Global Instance isqiso_cat1cat `{IsCat0 1 A, !Cat1Cat A}
       {a b : A} (f : a $-> b) (g : b $-> a)
       (s : g $o f $== cat_id a) (r : f $o g $== cat_id b)
  : IsQIso f.
Proof.
  unshelve econstructor.
  - exact g.
  - exact s.
  - exact r.
  - apply isqiso_catposet.
    exact (s^$).
  - apply isqiso_catposet.
    exact (r^$).
Defined.

(** To prove much of anything else about quasi-isomorphisms (even that the identity is one!) requires more coherence. *)


(** ** Equivalences *)

(** There are various possible coherent definitions of equivalence, some generally applicable and others more specifiec.  Rather than mandate a particular one in all cases, we give the user the freedom to choose whichever they prefer for a particular category by instantiating the following typeclass.  Note though that we don't actually *require* any coherence of the notion of equivalence, only that it is logically equivalent to quasi-isomorphism.  *)

CoInductive HasEquivs (n : nat) (A : Type) `{IsCat0 n A} :=
{
  CatIsEquiv' : forall {a b : A}, (a $-> b) -> Type ;
  catie_isqiso' : forall (a b : A) (f : a $-> b), IsQIso f -> CatIsEquiv' f ;
  isqiso_catie' : forall (a b : A) (f : a $-> b), CatIsEquiv' f -> IsQIso f ;
  hasequivs_hom : forall (a b : A), @HasEquivs (pred n) (a $-> b) _ _ ;
}.
Existing Class HasEquivs.
Global Existing Instance hasequivs_hom.

Hint Extern 1 (HasEquivs ?n (Hom _ _ _)) => change_dim n : typeclass_instances.
Hint Extern 1 (HasEquivs ?n (Hom _ _ _)) => change_dim_0 n : typeclass_instances.

(** A field can't be a working [Existing Class] due to a bug in Coq. *)
Class CatIsEquiv `{HasEquivs n A} {a b : A} (f : a $-> b)
  := catie_catie : @CatIsEquiv' n A _ _ _ a b f.

Hint Extern 1 (CatIsEquiv ?n (Hom _ _ _)) => change_dim n : typeclass_instances.
Hint Extern 1 (CatIsEquiv ?n (Hom _ _ _)) => change_dim_0 n : typeclass_instances.

Arguments CatIsEquiv : simpl never.

Global Instance isqiso_catie `{HasEquivs n A}
       {a b : A} (f : a $-> b) `{!CatIsEquiv f}
  : IsQIso f.
Proof.
  rapply isqiso_catie'; assumption.
Defined.

Definition catie_isqiso `{HasEquivs n A}
       {a b : A} (f : a $-> b) `{!IsQIso f}
  : CatIsEquiv f.
Proof.
  rapply catie_isqiso'; assumption.
Defined.

Record CatEquiv `{HasEquivs n A} (a b : A) :=
{
  cate_fun : a $-> b ;
  catie_cate : CatIsEquiv cate_fun ;
}.
Notation "a $<~> b" := (CatEquiv a b).
Arguments cate_fun {n A _ _ _ a b} f : rename.
Arguments Build_CatEquiv {n A _ _ _ a b} f fe : rename.
Coercion cate_fun : CatEquiv >-> Hom.
Global Existing Instance catie_cate.

Definition cate_inverse `{HasEquivs n A}
           {a b : A} (f : a $<~> b)
  : b $<~> a.
Proof.
  exists (qiso_inv f).
  rapply catie_isqiso.
Defined.

(** Because equivalences don't have to be coherent, it's technically possible to just use quasi-isomorphisms.  However, this should never be used as "the" definition of equivalences; we only define it as a stepping stone on the way to bi-invertibility as the "default" notion. *)
CoFixpoint hasequivs_with_isqiso (n : nat) (A : Type) `{IsCat0 n A}
  : HasEquivs n A.
Proof.
  unshelve econstructor.
  1:intros a b f; exact (IsQIso f).
  1-2:intros; assumption.
  intros; apply hasequivs_with_isqiso.
Defined.

(** In truncated cases, however, things are easier. *)
CoFixpoint hasequivs_catcontr `{IsCat0 n A, !CatContr A}
  : HasEquivs n A.
Proof.
  unshelve econstructor; intros.
  - exact Unit.
  - exact tt.
  - exact _.
  - rapply hasequivs_catcontr.
Defined.
Global Existing Instance hasequivs_catcontr | 1000.

Global Instance hasequivs_catprop `{IsCat0 n A, !CatProp A}
  : HasEquivs n A.
Proof.
  unshelve econstructor; intros.
  - exact Unit.
  - exact tt.
  - exact _.
  - rapply hasequivs_catcontr.
Defined.
Global Existing Instance hasequivs_catprop | 1000.

Global Instance hasequivs_catposet `{IsCat0 n A, !CatPoset A}
  : HasEquivs n A.
Proof.
  unshelve econstructor; intros.
  - exact (b $-> a).
  - cbn. exact (qiso_inv f).
  - apply isqiso_catposet. assumption.
  - rapply hasequivs_catprop.
Defined.
Global Existing Instance hasequivs_catposet | 1000.

Class CatIsIso `{IsCat0 1 A, !CatTrunc 1 A} {a b : A} (f : a $-> b) :=
{
  catiso_inv : b $-> a ;
  catiso_issect : catiso_inv $o f $== cat_id a ;
  catiso_isretr : f $o catiso_inv $== cat_id b ;
}.
Arguments catiso_inv {A _ _ _ a b} f {_}.
Arguments catiso_issect {A _ _ _ a b} f {_}.
Arguments catiso_isretr {A _ _ _ a b} f {_}.

Global Instance hasequivs_cat1cat `{IsCat0 1 A, !Cat1Cat A}
  : HasEquivs 1 A | 1000.
Proof.
  unshelve econstructor. 
  - intros a b f; exact (CatIsIso f).
  - intros a b f ?; unshelve econstructor.
    + exact (qiso_inv f).
    + exact (qiso_issect f).
    + exact (qiso_isretr f).
  - cbn; intros a b f ?; srapply isqiso_cat1cat.
    + exact (catiso_inv f).
    + exact (catiso_issect f).
    + exact (catiso_isretr f).
  - intros; apply hasequivs_catposet.
Defined.


(** ** Conservative Functors *)

(** A functor can be conservative at any collection of dimensions but not others, which we represent by a stream of booleans. *)
CoInductive IsConservative (bs : Stream Bool)
            `{HasEquivs m A, HasEquivs n B} (F : A -> B) `{!IsFunctor0 F} :=
{
  catie_conservative : forall {bt : IsTrue (head bs)} (a b : A) (f : a $-> b),
    CatIsEquiv (fmap F f) -> CatIsEquiv f ;
  catie_hom : forall (a b : A),
      @IsConservative (tail bs) (pred m) (a $-> b) _ _ _
                      (pred n) (F a $-> F b) _ _ _ (fmap F) _ ;
}.

Existing Class IsConservative.
Global Existing Instance catie_hom.

(** [catie_conservative] can't be an [Instance] because it would go into infinite loops. *)
Hint Immediate catie_conservative : typeclass_instances.

(** The identity functor is conservative. *)
CoFixpoint isconservative_idmap `{HasEquivs m A}
  : @IsConservative (const_stream true) m A _ _ _ m A _ _ _ idmap _.
Proof.
  unshelve econstructor; intros.
  - apply catie_isqiso, isqiso_catie; assumption.
  - exact _.
Defined.
Global Existing Instance isconservative_idmap.

(** The functor from an induced category structure to the original category should be conservative.  First we prove that it reflects quasi-isomorphisms. *)
Local Instance isqiso_induced {A} `{HasEquivs n B} (F : A -> B)
           {a b : A} (f : a $-> b) `{!IsQIso (fmap F f)}
  : @IsQIso n A _ (iscat0_induced F) a b f.
Proof.
  unshelve econstructor; cbn.
  - exact (qiso_inv (fmap F f)).
  - apply qiso_issect.
  - apply qiso_isretr.
  - exact (isqiso_qiso_issect (fmap F f) _).
  - exact (isqiso_qiso_isretr (fmap F f) _).
Defined.

(** You might think that's all we have to do, since "clearly" it also preserves quasi-isomorphisms.  But actually we have to prove this clear fact, since we don't yet know that arbitrary functors preserve quasi-isomorphisms (which actually requires 1-coherence!). *)
Local Instance isqiso_fmap_induced {A} `{HasEquivs n B} (F : A -> B)
      {a b : A} (f : a $-> b)
      {fe : @IsQIso n A _ (iscat0_induced F) a b f}
  : IsQIso (fmap F f).
Proof.
  unshelve econstructor; cbn.
  - exact (@qiso_inv _ _ _ _ _ _ f fe).
  - exact (@qiso_issect _ _ _ _ _ _ f fe).
  - exact (@qiso_isretr _ _ _ _ _ _ f fe).
  - exact (@isqiso_qiso_issect _ _ _ _ _ _ f fe).
  - exact (@isqiso_qiso_isretr _ _ _ _ _ _ f fe).
Defined.

(** In order to actually state that the inducing functor is conservative, we need to first prove that the induced category [HasEquivs]. *)
Definition hasequivs_induced {A} `{HasEquivs n B} (F : A -> B)
  : @HasEquivs n A _ (iscat0_induced F).
Proof.
  unshelve econstructor.
  - intros; eapply CatIsEquiv; eassumption.
  - cbn; intros. rapply catie_isqiso.
  - cbn; intros. apply isqiso_induced, isqiso_catie. exact _.
  - intros. cbn. exact _.
Defined.

Definition isconservative_induced {A} `{HasEquivs n B} (F : A -> B)
  : @IsConservative (const_stream true)
                    n A _ _ (hasequivs_induced F) n B _ _ _ F _.
Proof.
  unshelve econstructor; cbn; intros.
  - apply catie_isqiso, isqiso_induced, isqiso_catie.
    assumption.
  - exact _.
Defined.


(** ** Categories of equivalences *)

(** We induce a category structure on [a $<~> b] from [a $-> b]. *)

Global Instance isglob_catequiv `{HasEquivs m A} (a b : A)
  : IsGlob (pred m) (a $<~> b)
  := isglob_induced (@cate_fun _ _ _ _ _ a b).

Global Instance iscat0_catequiv `{HasEquivs m A} (a b : A)
  : IsCat0 (pred m) (a $<~> b)
  := iscat0_induced (@cate_fun _ _ _ _ _ a b).

Global Instance hasequivs_catequiv `{HasEquivs m A} (a b : A)
  : HasEquivs (pred m) (a $<~> b)
  := hasequivs_induced (@cate_fun _ _ _ _ _ a b).


(** ** Bi-invertible maps *)

(** The simplest general coherent definition of equivalence is a bi-invertible map.  We will supply this as a default definition that the user can override if desired, by making it an instance with high cost (low priority). *)

CoInductive CatBiInv `{IsCat0 n A} {a b : A} (f : a $-> b) :=
{
  catbiinv_retr : b $-> a ;
  catbiinv_issect : (catbiinv_retr $o f) $-> (cat_id a) ;
  catbiinv_sect : b $-> a ;
  catbiinv_isretr : (f $o catbiinv_sect) $-> (cat_id b) ;
  catbiinv_catbiinv_issect :
      @CatBiInv _ (a $-> a) _ _ _ _ catbiinv_issect ;
  catbiinv_catbiinv_isretr :
      @CatBiInv _ (b $-> b) _ _ _ _ catbiinv_isretr ;
}.

(** Every quasi-isomorphism is bi-invertible. *)
CoFixpoint biinv_isqiso `{IsCat0 n A} {a b : A} (f : a $-> b) `{!IsQIso f}
  : CatBiInv f.
Proof.
  unshelve econstructor; intros.
  1,3: rapply (qiso_inv f).
  1: apply (qiso_issect f).
  1: apply (qiso_isretr f).
  1-2: apply biinv_isqiso; exact _.
Defined.

(** However, to prove the converse requires more coherence. *)

(** ** Displayed 0-coherent oo-categories *)

(** It's not entirely clear what restrictions there should be on [m] and [n], and how they interact.  The following definition amounts to saying that if [n=0] then the projection functor represented by a displayed category is conservative (equivalence-reflecting), and otherwise corecurses into hom-categories.  This seems at least reasonable, since it restricts to the correct meaning of [n] when [A=Unit].  *)

CoInductive IsDCat0 {m A} n B
            `{IsDGlob m A n B} `{!IsCat0 m A} : Type :=
{
  dcat_id : forall (a : A) (u : B a), DHom (cat_id a) u u ;
  dcat_comp : forall (a b c : A) (u : B a) (v : B b) (w : B c)
                     (g : b $-> c) (f : a $-> b),
      DHom g v w -> DHom f u v -> DHom (g $o f) u w ;
  isdfunctor0_postcomp : forall (a b c : A) (u : B a) (v : B b) (w : B c)
                                (g : b $-> c) (q : DHom g v w),
      IsDFunctor0 (fun f => g $o f) (fun f p => dcat_comp a b c u v w g f q p) ;
  isdfunctor0_precomp : forall (a b c : A) (u : B a) (v : B b) (w : B c)
                              (f : a $-> b) (p : DHom f u v),
      IsDFunctor0 (fun g => g $o f) (fun g q => dcat_comp a b c u v w g f q p) ;
  dgpd_inv : forall (iszn : IsZeroNat n)
                    (a b : A) (u : B a) (v : B b)
                    (f : a $-> b) (fe : IsQIso f),
      DHom f u v -> DHom (qiso_inv f) v u ;
  isdcat0_dhom : forall (a b : A) (u : B a) (v : B b),
      @IsDCat0 (pred m) (a $-> b) (pred n) (fun f => DHom f u v) _ _ _ ;
}.

Existing Class IsDCat0.
Arguments dcat_id {m A n B _ _ _ _ a} u.
Arguments dcat_comp {m A n B _ _ _ _ a b c u v w g f} q p.
Notation "q $oD p" := (dcat_comp q p).
Arguments dgpd_inv {m A n B _ _ _ _ _ a b u v f fe} p.
Notation "p ^D$" := (dgpd_inv p).
Global Existing Instances
       isdcat0_dhom isdfunctor0_postcomp isdfunctor0_precomp.

Hint Extern 1 (@IsDCat0 ?m (Hom _ _ _) _ _ _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@IsDCat0 ?m (Hom _ _ _) _ _ _ _ _) => change_dim_0 m : typeclass_instances.
Hint Extern 1 (@IsDCat0 _ _ ?n _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@IsDCat0 _ _ ?n _ _ _ _) => change_dim_0 n : typeclass_instances.

Definition dcat_postcomp `{IsDCat0 m A n B}
           {a b c : A} (u : B a) {v : B b} {w : B c}
           {g : b $-> c} (f : a $-> b) (q : DHom g v w)
  : DHom f u v -> DHom (g $o f) u w
  := fun p => q $oD p.

Definition dcat_precomp `{IsDCat0 m A n B}
           {a b c : A} {u : B a} {v : B b} (w : B c)
           (g : b $-> c) {f : a $-> b} (p : DHom f u v)
  : DHom g v w -> DHom (g $o f) u w
  := fun q => q $oD p.

Definition dcat_postwhisker `{IsDCat0 m A n B}
           {a b c : A} {u : B a} {v : B b} {w : B c}
           {f g : a $-> b} {h : b $-> c} {p : f $-> g}
           {f' : DHom f u v} {g' : DHom g u v}
           (h' : DHom h v w) (p' : DHom p f' g')
  : DHom (h $<o p) (h' $oD f') (h' $oD g')
  := dfmap (cat_postcomp a h) (fun k => dcat_postcomp u k h') p'.

Notation "h' $<oD p'" := (dcat_postwhisker h' p').

Definition dcat_prewhisker `{IsDCat0 m A n B}
           {a b c : A} {u : B a} {v : B b} {w : B c}
           {f g : b $-> c} {p : f $-> g} {h : a $-> b}
           {f' : DHom f v w} {g' : DHom g v w} (p' : DHom p f' g') (h' : DHom h u v)
  : DHom (p $o> h) (f' $oD h') (g' $oD h')
  := dfmap (cat_precomp c h) (fun k => dcat_precomp w k h') p'.

Notation "p $o>D h" := (dcat_prewhisker p h).

(** ** Displayed quasi-isomorphisms *)

CoInductive IsDQIso `{IsDCat0 m A n B}
            {a b : A} {f : a $-> b} {fe : IsQIso f}
            {u : B a} {v : B b} (g : DHom f u v) : Type :=
{
  dqiso_inv : DHom (qiso_inv f) v u ;
  dqiso_issect : DHom (qiso_issect f) (dqiso_inv $oD g) (dcat_id u) ;
  dqiso_isretr : DHom (qiso_isretr f) (g $oD dqiso_inv) (dcat_id v) ;
  isdqiso_issect : @IsDQIso (pred m) (a $-> a) (pred n) (fun h => DHom h u u)
                            _ _ _ _ _ _ _ _ _ _ dqiso_issect ;
  isdqiso_isretr : @IsDQIso (pred m) (b $-> b) (pred n) (fun h => DHom h v v)
                            _ _ _ _ _ _ _ _ _ _ dqiso_isretr ;
}.

Existing Class IsDQIso.
Arguments dqiso_inv {m A n B _ _ _ _ a b f _ u v} g {_}.
Arguments dqiso_issect {m A n B _ _ _ _ a b f _ u v} g {_}.
Arguments dqiso_isretr {m A n B _ _ _ _ a b f _ u v} g {_}.
Global Existing Instances isdqiso_issect isdqiso_isretr.

Hint Extern 1 (@IsDQIso ?m (Hom _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@IsDQIso ?m (Hom _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim_0 m : typeclass_instances.
Hint Extern 1 (@IsDQIso _ _ ?n _ _ _ _ _ _ _ _ _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@IsDQIso _ _ ?n _ _ _ _ _ _ _ _ _ _ _ _) => change_dim_0 n : typeclass_instances.

Global Instance isdqiso_inv `{IsDCat0 m A n B}
       {a b : A} (f : a $-> b) `{!IsQIso f}
       {u : B a} {v : B b} (g : DHom f u v) `{!IsDQIso g}
  : IsDQIso (dqiso_inv g).
Proof.
  unshelve econstructor.
  - exact g.
  - srapply dqiso_isretr.
  - srapply dqiso_issect.
  - exact _.
  - exact _.
Defined.

(** TODO: [IsDQIso] in truncated dcats  *)

(** ** Displayed categories with equivalences *)

CoInductive DHasEquivs {m} {A} (n : nat) (B : A -> Type)
            `{IsDCat0 m A n B, !HasEquivs m A} :=
{
  DCatIsEquiv' : forall {a b : A} {f : a $-> b} {fe : CatIsEquiv f}
                        {u : B a} {v : B b}, DHom f u v -> Type ;
  dcatie_isdqiso' : forall {a b : A} {f : a $-> b} {fe : IsQIso f}
                           {u : B a} {v : B b} (g : DHom f u v),
      IsDQIso g -> DCatIsEquiv' (fe := catie_isqiso f) g ;
  isdqiso_dcatie' : forall {a b : A} {f : a $-> b} {fe : CatIsEquiv f}
                           {u : B a} {v : B b} (g : DHom f u v),
      DCatIsEquiv' g -> IsDQIso g;
  dhasequivs_dhom : forall (a b : A) (u : B a) (v : B b),
      @DHasEquivs (pred m) (a $-> b) (pred n) (fun f => DHom f u v) _ _ _ _ _ ;
}.
Existing Class DHasEquivs.
Global Existing Instance dhasequivs_dhom.

Hint Extern 1 (@DHasEquivs ?m (Hom _ _ _) _ _ _ _ _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@DHasEquivs ?m (Hom _ _ _) _ _ _ _ _ _ _) => change_dim_0 m : typeclass_instances.
Hint Extern 1 (@DHasEquivs _ _ ?n _ _ _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@DHasEquivs _ _ ?n _ _ _ _ _ _) => change_dim_0 n : typeclass_instances.

Class DCatIsEquiv `{DHasEquivs m A n B} {a b f fe u v} (g : DHom f u v)
  := dcatie_dcatie : @DCatIsEquiv' m A n B _ _ _ _ _ _ a b f fe u v g.

Arguments DCatIsEquiv : simpl never.

Hint Extern 1 (@DCatIsEquiv ?m (Hom _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@DCatIsEquiv ?m (Hom _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim_0 m : typeclass_instances.
Hint Extern 1 (@DCatIsEquiv _ _ ?n _ _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@DCatIsEquiv _ _ ?n _ _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim_0 n : typeclass_instances.

Global Instance isdqiso_dcatie `{DHasEquivs m A n B}
       {a b f} {u : B a} {v : B b} (g : DHom f u v)
       `{!CatIsEquiv f, !DCatIsEquiv g}
  : IsDQIso g.
Proof.
  rapply isdqiso_dcatie'; assumption.
Defined.

Definition dcatie_isdqiso `{DHasEquivs m A n B}
           {a b f} {u : B a} {v : B b} (g : DHom f u v)
           `{!IsQIso f, !IsDQIso g}
  : DCatIsEquiv (fe := catie_isqiso f) g.
Proof.
  rapply dcatie_isdqiso'; assumption.
Defined.

Record DCatEquiv `{DHasEquivs m A n B} {a b} (f : a $<~> b) u v :=
{
  dcate_fun : DHom f u v ;
  dcatie_dcate : DCatIsEquiv dcate_fun ;
}.
Arguments Build_DCatEquiv {m A n B _ _ _ _ _ _ a b f u v} g ge : rename.
Arguments dcate_fun {m A n B _ _ _ _ _ _ a b f u v} g : rename.
Coercion dcate_fun : DCatEquiv >-> DHom.
Global Existing Instance dcatie_dcate.

Definition dcate_inverse `{DHasEquivs m A n B} {a b} {f : a $<~> b} {u v}
           (g : DCatEquiv f u v)
  : DCatEquiv (cate_inverse f) v u.
Proof.
  exists (dqiso_inv g).
  apply dcatie_isdqiso.
  exact _.
Defined.

CoFixpoint dhasequivs_with_isdqiso {m A} n B
           `{IsDCat0 m A n B}
  : @DHasEquivs m A n B _ _ _ _ (hasequivs_with_isqiso m A).
Proof.
  unshelve econstructor.
  1:intros a b f fe u v g; exact (IsDQIso g).
  1-2:intros; assumption.
  intros; apply dhasequivs_with_isdqiso.
Defined.

(** TODO: [DHasEquivs] in truncated categories  *)
