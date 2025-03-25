Require Import Basics.Overture Basics.Tactics Basics.Equivalences Basics.PathGroupoids.
Require Import Types.Equiv.
Require Import WildCat.Core WildCat.Equiv WildCat.NatTrans WildCat.Bifunctor WildCat.TwoOneCat.

(** ** The (1-)category of types *)

Instance isgraph_type@{u v} : IsGraph@{v u} Type@{u}
  := Build_IsGraph Type@{u} (fun a b => a -> b).

Instance is01cat_type : Is01Cat Type.
Proof.
  econstructor.
  + intro; exact idmap.
  + exact (fun a b c g f => g o f).
Defined.

Instance is2graph_type : Is2Graph Type
  := fun x y => Build_IsGraph _ (fun f g => f == g).

Instance is01cat_arrow {A B : Type} : Is01Cat (A $-> B).
Proof.
  econstructor.
  - exact (fun f a => idpath).
  - exact (fun f g h p q a => q a @ p a).
Defined.

Instance is0gpd_arrow {A B : Type}: Is0Gpd (A $-> B).
Proof.
  apply Build_Is0Gpd.
  intros f g p a ; exact (p a)^.
Defined.

Instance is0functor_type_postcomp {A B C : Type} (h : B $-> C):
  Is0Functor (cat_postcomp A h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (ap h (p a)).
Defined.

Instance is0functor_type_precomp {A B C : Type} (h : A $-> B):
  Is0Functor (cat_precomp C h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (p (h a)).
Defined.

Instance is0bifunctor_type_comp {A B C : Type} :
  Is0Bifunctor (cat_comp (a:=A) (b:=B) (c:=C))
  := Build_Is0Bifunctor'' _.

Instance is1cat_strong_type : Is1Cat_Strong Type.
Proof.
  srapply Build_Is1Cat_Strong; cbn; intros; reflexivity.
Defined.

Instance hasmorext_type `{Funext} : HasMorExt Type.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  refine (isequiv_homotopic (@apD10 A (fun _ => B) f g) _).
  intros p.
  destruct p; reflexivity.
Defined.

Instance hasequivs_type : HasEquivs Type.
Proof.
  srefine (Build_HasEquivs Type _ _ _ _ Equiv (@IsEquiv) _ _ _ _ _ _ _ _); intros A B.
  all:intros f.
  - exact f.
  - exact _.
  - apply Build_Equiv.
  - intros; reflexivity.
  - intros; exact (f^-1).
  - cbn. intros ?; apply eissect.
  - cbn. intros ?; apply eisretr.
  - intros g r s; exact (isequiv_adjointify f g r s).
Defined.

Instance hasmorext_core_type `{Funext} : HasMorExt (core Type) := _.

Definition catie_isequiv {A B : Type} {f : A $-> B}
       `{IsEquiv A B f} : CatIsEquiv f.
Proof.
  assumption.
Defined.

#[export]
Hint Immediate catie_isequiv : typeclass_instances.

Instance isinitial_zero : IsInitial (A:=Type) Empty.
Proof.
  intro A.
  exists (Empty_rec _).
  intros g.
  rapply Empty_ind.
Defined.

Instance isterminal_unit : IsTerminal (A:=Type) Unit.
Proof.
  intros A.
  exists (fun _ => tt).
  intros f x.
  by destruct (f x).
Defined.

(** ** The 2-category of types *)

Instance is3graph_type : Is3Graph Type.
Proof.
  intros A B f g.
  apply Build_IsGraph.
  intros p q.
  exact (p == q).
Defined.

Instance is1cat_type_hom A B : Is1Cat (A $-> B).
Proof.
  repeat unshelve esplit.
  - intros f g h p q x.
    exact (q x @ p x).
  - intros; by symmetry.
  - intros f h p x.
    exact (p x @@ 1).
  - intros g h p x.
    exact (1 @@ p x).
  - intros ? ? ? ? ? ? ? ?; apply concat_p_pp.
  - intros ? ? ? ? ? ? ? ?; apply concat_pp_p.
  - intros ? ? ? ?. apply concat_p1.
  - intros ? ? ? ?. apply concat_1p.
Defined.

Instance is1gpd_type_hom (A B : Type) : Is1Gpd (A $-> B).
Proof.
  repeat unshelve esplit.
  - intros ? ? ? ?; apply concat_pV.
  - intros ? ? ? ?; apply concat_Vp.
Defined.

Instance is1functor_cat_postcomp {A B C : Type} (g : B $-> C)
  : Is1Functor (cat_postcomp A g).
Proof.
  repeat unshelve esplit.
  - intros ? ? ? ? p ?; exact (ap _ (p _)).
  - intros ? ? ? ? ? ?; cbn; apply ap_pp.
Defined.

Instance is1functor_cat_precomp {A B C : Type} (f : A $-> B)
  : Is1Functor (cat_precomp C f).
Proof.
  repeat unshelve esplit.
  intros ? ? ? ? p ?; exact (p _).
Defined.

Instance is1bifunctor_cat_comp {A B C :Type}:
  Is1Bifunctor (cat_comp (A:=Type) (a:=A) (b:=B) (c:=C)).
Proof.
  apply Build_Is1Bifunctor''.
  1-2: exact _.
  intros g g' h_g f f' h_f a; cbn.
  symmetry; apply concat_Ap.
Defined.

Instance isTruncatedBicat_Type : IsTruncatedBicat Type.
Proof.
  snapply Build_IsTruncatedBicat; intros; cbn.
  1-2: exact _.
  all: reflexivity.
Defined.

Instance is21cat_type : Is21Cat Type.
Proof.
  snapply Build_Is21Cat; [snapply Build_IsBicategory | | ].
  1-3, 12-13: exact _.
  1-3: intros; constructor; reflexivity.
  - intros A B C D. snapply Build_Is1Natural.
    intros ((h,g),f) ((h',g'),f').
    intros ((gamma,beta),alpha) a; simpl.
    unfold fmap11; simpl.
    rewrite concat_1p.
    rewrite concat_p1.
    rewrite concat_p_pp.
    apply (ap (fun z => z @ gamma (g' (f' a)))).
    rewrite ap_compose.
    rewrite ap_pp.
    reflexivity.
  - intros A B; snapply Build_Is1Natural.
    intros f f' h a; simpl.
    rewrite ap_idmap.
    exact (concat_p1_1p _).
  - intros A B; snapply Build_Is1Natural.
    intros f f' h a. exact (concat_p1_1p _).
  - reflexivity.
  - reflexivity.
Defined.
